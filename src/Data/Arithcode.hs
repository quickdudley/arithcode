{-# LANGUAGE RankNTypes #-}
module Data.Arithcode (
  Interval,
  ArithcodeT,
  (...),
  narrow,
  widen,
  overlap,
  runArithcodeT,
  runArithcodeT',
  element,
  integralInRange,
  encodeIntegral,
  eof,
  exhaust,
  exhaust',
  decodeByte,
  toBytes,
  fromProportion
 ) where

import Control.Monad.Trans.Class
import Data.Char
import Data.Functor.Identity
import Data.List
import Data.Ratio
import Data.Word

data Interval = Interval Rational Rational

instance Show Interval where
  showsPrec p ~(Interval l h) = let
    m = showsPrec 7 l . ("..."++) . showsPrec 7 h
    in if p >= 6 then ('(':) . m . (')':) else m

instance Read Interval where
  readsPrec p' = go p' . filter (not . isSpace) where
    go p ('(':r1) = do
      (a,')':r2) <- go 0 r1
      return (a,r2)
    go p r1
      | p > 6 = []
      | otherwise = do
        (l,'.':'.':'.':r2) <- readsPrec 7 r1
        (h,r3) <- readsPrec 7 r2
        return (Interval l h, r3)

infixl 6 ...
(...) :: Rational -> Rational -> Interval
a ... b
  | b < a = error "lower bound must not be greater than upper bound"
  | otherwise = Interval a b

narrow :: Interval -> Interval -> Interval
narrow ~(Interval al ah) ~(Interval bl bh) = let
  f = ah - al
  s x = al + f * x
  in Interval (s bl) (s bh)

widen :: Interval -> Interval -> Interval
widen ~(Interval al ah) ~(Interval bl bh) = let
  f = ah - al
  s x = (x - al) / f
  in Interval (s bl) (s bh)

overlap :: Interval -> Interval -> Bool
overlap a@(Interval al ah) b@(Interval bl bh)
  | al > bl = overlap b a
  | otherwise = ah > bl

wantNext :: Interval -> Bool
wantNext (Interval a b) = case a `compare` 0 of
  LT -> True
  EQ -> b >= 1
  GT -> b > 1

exhausted :: Interval -> Bool
exhausted (Interval a b) = a <= 0 && b >= 1

data RangeTree a = Leaf a | Node Rational (RangeTree a) (RangeTree a)

reduceTree :: Bool -> Interval -> RangeTree a -> (Interval, RangeTree a)
reduceTree _ i l@(Leaf _) = (i,l)
reduceTree e i n@(Node m l r) = let
  leftBranch = reduceTree e (widen (Interval 0 m) i) l
  rightBranch = reduceTree e (widen (Interval m 1) i) r
  in case (overlap i (Interval 0 m), overlap i (Interval m 1)) of
    (True,True)
      | e -> leftBranch
      | otherwise -> (i,n)
    (True,False) -> leftBranch
    (False,True) -> rightBranch
    (False,False) -> error "Interval is outside \"0...1\""

data Step m a =
  R a |
  A (m (Step m a)) |
  I (Interval -> Bool -> (Interval,Step m a))

newtype ArithcodeT m a = ACT (forall b . (a -> Step m b) -> Step m b)

instance Functor (ArithcodeT m) where
  fmap f (ACT d) = ACT (d . (. f))

instance Applicative (ArithcodeT m) where
  pure a = ACT (\c -> c a)
  ACT f <*> ACT a = ACT (f . ((.) a . (.)))
  ACT a *> ACT b = ACT (a . (const . b))
  ACT a <* ACT b = ACT (a . ((b .) . (const .)))

instance Monad (ArithcodeT m) where
  return = pure
  ACT a >>= f = ACT (\c -> a (\a' -> let ACT b = f a' in b c))

instance MonadTrans ArithcodeT where
   lift a = ACT (A . (<$> a))

runArithcodeT :: Monad m => ArithcodeT m a -> [Interval] -> m a
runArithcodeT (ACT z) = go (z R) where
  go (R a) _ = return a
  go (A a) l = a >>= flip go l
  go s@(I _) [] = go s [Interval 0 1]
  go (I c) (i:r) = let
    (i',n) = c i (null r)
    l = if wantNext i'
      then case r of
        [] -> [i']
        (i2:z) -> narrow i' i2 : z
      else i' : r
    in go n l

runArithcodeT' :: Monad m => ArithcodeT m a -> m (Maybe Interval) -> m a
runArithcodeT' (ACT z) s = go False (z R) (Interval 0 1) where
  go e (R a) _ = return a
  go e (A a) i = a >>= flip (go e) i
  go e t@(I c) i = let
   (i',n) = c i e
   in if wantNext i' && not e
     then s >>= \mi -> case mi of
       Nothing -> go True n i'
       Just i2 -> go e n (narrow i' i2)
     else go e n i'

element :: [(Rational,a)] -> ArithcodeT m a
element [] = error "\'element\' requires non-empty list"
element l = let
  mergePairs [] = []
  mergePairs a@[_] = a
  mergePairs ((a,at):(b,bt):r) = let
    t = at + bt
    in (Node (at / t) a b, t) : mergePairs r
  mergeAll [a] = a
  mergeAll l = mergeAll (mergePairs l)
  (tree,_) = mergeAll $
    map (\(p,v) -> (Leaf v,p)) $
    filter (\(p,_) -> p > 0) l
  in ACT (\c -> let
    go e i n = case reduceTree e i n of
      (Interval 0 1, Leaf a) -> c a
      (i1, Leaf a) -> I (\i2 _ -> (narrow i1 i2, c a))
      (i1, n@(Node _ _ _)) -> I (\i2 e' ->
        (Interval 0 1, go e' (narrow i1 i2) n)
       )
    in go False (Interval 0 1) tree
   )

integralInRange :: Integral n => n -> n -> ArithcodeT m n
integralInRange l h = ACT (\c -> let
  go e a b = let
    [a',b'] = map floor [a,b] :: [Integer]
    in if a' == b' || e
      then let
        r = c (fromIntegral a')
        in case map (subtract (fromIntegral a')) [a,b] of
          [0,1] -> r
          [ar,br] -> I (\i' _ -> (narrow (Interval ar br) i',r))
      else I (\i' e' -> let
        Interval ar br = narrow (Interval a b) i'
        in (Interval 0 1, go e' ar br)
       )
  in go False (fromIntegral l) ((fromIntegral h) + 1)
 )

encodeIntegral :: Integral n => n -> n -> ArithcodeT m n
encodeIntegral l h = ACT (\c -> let
  go e a b = let
    [a0,b'] = map floor [a,b] :: [Integer]
    in if a0 == b' || e
      then let
        a' = if e
          then ceiling a
          else a0
        r = c (fromIntegral a')
        in case map (subtract (fromIntegral a')) [a,b] of
          _ | e -> r
          [0,1] -> r
          [ar,br] -> I (\i' _ -> (narrow (Interval ar br) i',r))
      else I (\i' e' -> let
        Interval ar br = narrow (Interval a b) i'
        in (Interval 0 1, go e' ar br)
       )
  in go False (fromIntegral l) ((fromIntegral h) + 1)
 )

eof :: ArithcodeT m Bool
eof = ACT (\c ->
  I (\i e -> (i,c (e && wantNext i)))
 )

exhaust :: ArithcodeT m a -> ArithcodeT m [a]
exhaust d = go where
  go = eof >>= \e -> if e
    then return []
    else d >>= \a -> go >>= \r -> return (a:r)

-- | Version of 'exhaust' which is tail-recursive in strict monads
exhaust' :: ArithcodeT m a -> ArithcodeT m [a]
exhaust' d = go id where
  go acc = eof >>= \e -> if e
    then return (acc [])
    else d >>= \a -> go (acc . (a:))

decodeByte :: Word8 -> Interval
decodeByte b = let
  v = toRational b / 0x100
  in v ... (v + (1 / 0x100))

toBytes :: [Interval] -> [Word8]
toBytes = runIdentity . (runArithcodeT $ exhaust $ encodeIntegral 0 0xFF)

fromProportion :: Rational -> Rational -> Rational -> Interval
fromProportion b r a = let
  f = b + r
  total = f + a
  [i1,i2] = map (/ total) [b,f]
  in Interval i1 i2
