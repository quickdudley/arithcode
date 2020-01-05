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
overlap a@(Interval al ah) b@(Interval bl bh) = case al `compare` bl of
  LT -> ah > bl
  EQ -> True
  GT -> bh > al

wantNext :: Interval -> Bool
wantNext (Interval a b) = case a `compare` 0 of
  LT -> True
  EQ -> b >= 1
  GT -> b > 1

exhausted :: Interval -> Bool
exhausted (Interval a b) = a <= 0 && b >= 1

data RangeTree a = Leaf a | Node Rational (RangeTree a) (RangeTree a)

reduceTree :: Interval -> RangeTree a -> (Interval, RangeTree a)
reduceTree i l@(Leaf _) = (i,l)
reduceTree i n@(Node m l r) = let
  leftBranch = reduceTree (widen (Interval 0 m) i) l
  rightBranch = reduceTree (widen (Interval m 1) i) r
  in case (overlap i (Interval 0 m), overlap i (Interval m 1)) of
    (True,True) -> (i,n)
    (True,False) -> leftBranch
    (False,True) -> rightBranch
    (False,False) -> error "Interval is outside \"0...1\""

data Step m a =
  R a |
  A (m (Step m a)) |
  I (Maybe Interval -> Step m a)

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

step :: Functor m => Step m a -> Interval -> Step m a
step s@(R _) _ = s
step (A a) i = A $ fmap (flip step i) a
step (I s) i = s (Just i)

starve :: Functor m => Step m a -> Step m a
starve s@(R _) = s
starve (A a) = A $ fmap starve a
starve (I s) = s Nothing

runArithcodeT :: Monad m => ArithcodeT m a -> [Interval] -> m a
runArithcodeT (ACT z) = go (z R) where
  go (R a) _ = return a
  go (A a) l = a >>= flip go l
  go (I s) [] = go (s Nothing) []
  go (I c) (i:r) = go (c $ Just i) r

runArithcodeT' :: Monad m => ArithcodeT m a -> m (Maybe Interval) -> m a
runArithcodeT' (ACT z) src = go (z R) where
  go (R a) = return a
  go (A a) = a >>= go
  go (I s) = src >>= (go . s)

element :: Functor m => [(Rational,a)] -> ArithcodeT m a
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
    fin (Leaf a) _ = starve $ c a
    fin (Node m l r) i@(Interval a _) = if m < a
      then fin l (widen i (Interval 0 m))
      else fin r (widen i (Interval m 1))
    go i n = case reduceTree i n of
      (Interval 0 1, Leaf a) -> c a
      (i1, Leaf a) -> step (c a) i1
      (i1, n@(Node _ _ _)) -> I (\mi2 -> case mi2 of
        Just i2 -> go (narrow i1 i2) n
        Nothing -> starve $ step (fin n i1) i1
       )
    in go (Interval 0 1) tree
   )

integralInRange :: (Functor m,Integral n) => n -> n -> ArithcodeT m n
integralInRange l h = ACT (\c -> let
  go a b = let
    [a',b'] = map floor [a,b] :: [Integer]
    in if a' == b'
      then let
        r = c (fromIntegral a')
        in case map (subtract (fromIntegral a')) [a,b] of
          [0,1] -> r
          [ar,br] -> step r (Interval ar br)
      else I (\mi' -> case mi' of
        Just i' -> let
          Interval ar br = narrow (Interval a b) i'
          in go ar br
        Nothing -> starve $ c $ fromIntegral a'
       )
  in go (fromIntegral l) ((fromIntegral h) + 1)
 )

encodeIntegral :: (Functor m,Integral n) => n -> n -> ArithcodeT m n
encodeIntegral l h = ACT (\c -> let
  go a b = let
    [a',b'] = map floor [a,b] :: [Integer]
    in if a' == b'
      then let
        r = c (fromIntegral a')
        in case map (subtract (fromIntegral a')) [a,b] of
          [0,1] -> r
          [ar,br] -> step r (Interval ar br)
      else I (\mi' -> case mi' of
        Just i' -> let
          Interval ar br = narrow (Interval a b) i'
          in go ar br
        Nothing -> starve $ c $ ceiling a
       )
  in go (fromIntegral l) ((fromIntegral h) + 1)
 )

eof :: Functor m => ArithcodeT m Bool
eof = ACT (\c -> I (\m -> case m of
  Nothing -> starve $ c True
  Just i -> step (c False) i
 ))

exhaust :: Functor m => ArithcodeT m a -> ArithcodeT m [a]
exhaust d = go where
  go = eof >>= \e -> if e
    then return []
    else d >>= \a -> go >>= \r -> return (a:r)

-- | Version of 'exhaust' which is tail-recursive in strict monads
exhaust' :: Functor m => ArithcodeT m a -> ArithcodeT m [a]
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
