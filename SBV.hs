{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module SBV where

import Data.SBV.Bridge.Yices hiding (inRange)
import Data.SBV.Internals

import Data.Bits

import Prelude hiding ((>>))

--import Prelude hiding (Ord(..))
--import qualified Prelude as P

-- * Ranges

data Range a = Range { lb :: a , ub :: a }

isEmpty (Range lb ub) = lb .> ub

inRange v (Range lb ub) = lb .<= v &&& v .<= ub

range a b = Range a b

fullRange :: (Bounded a) => Range a
fullRange = Range minBound maxBound

negativeRange :: (Bounded a,Num a) => Range a
negativeRange = Range minBound (-1)

(??) :: SymWord a => SBV Bool -> (Range (SBV a),Range (SBV a)) -> Range (SBV a)
b ?? (Range l1 u1,Range l2 u2) = range (ite b l1 l2) (ite b u1 u2)

singletonRange a = range a a

rangeLess (Range l1 u1) (Range l2 u2) = u1 .< l2

mapMonotonic2 :: (SBV a -> SBV b -> SBV c)
              -> Range (SBV a) -> Range (SBV b) -> Range (SBV c)
mapMonotonic2 f (Range l1 u1) (Range l2 u2) = Range (f l1 l2) (f u1 u2)

(Range l u) `isSingletonRange` v = l .== v &&& u .== v

rangeOp f r  = isEmpty r ?? (r,f r)

isSubRangeOf r1@(Range l1 u1) r2@(Range l2 u2) = fun
    [ isEmpty r1 :=* true
    , isEmpty r2 :=* false
    , true       :=* ((l1 .>= l2) &&& (u1 .<= u2))]

isNatural (Range l u) = l .>= 0

isNegative (Range l u) = u .<= 0

-- * Clauses

data Clause b = SBV Bool :=* SBV b
data ClauseR b = SBV Bool := Range b
data ClauseO bool r = bool :=+ r

infix 1 :=
infix 1 :=*

fun :: SymWord b => [Clause b] -> SBV b
fun cs = foldr (\(c :=* b) r -> ite c b r) d (init cs)
  where (_ :=* d) = last cs


funR :: SymWord b => [ClauseR (SBV b)] -> Range (SBV b)
funR cs = foldr (\(c := r) res -> c ?? (r,res)) d (init cs)
  where (_ := d) = last cs
{-
funO :: Mergeable b bool => [ClauseO bool r] -> r
funO cs = foldr (\(c :=+ r) res -> c ?? (r,res)) d (init cs)
  where (_ := d) = last cs

instance Mergeable a bool => Mergeable (Range a) bool where
  symbolicMerge b (Range l1 u1) (Range l2 u2)
      = range (symbolicMerge b l1 l2) (symbolicMerge b u1 u2)
-}
-- * Helper function

(<<),(>>) :: Bits a => a -> Int -> a
(<<) = shiftL
(>>) = shiftR

boolToInt True  = 1
boolToInt False = 0

bits v = r4 .|. (v4 >> 1)
  where r1     = boolToInt (v > 0xFFFF) << 4
        v1     = v >> r1
        shift1 = boolToInt (v1 > 0xFF  ) << 3
        v2     = v1 >> shift1
        r2     = r1 .|. shift1
        shift2 = boolToInt (v2 > 0xFF  ) << 3
        v3     = v2 >> shift2
        r3     = r2 .|. shift2
        shift3 = boolToInt (v3 > 0x3   ) << 1
        v4     = v3 >> shift3
        r4     = r3 .|. shift3


{- Not sure how to implement this function in Yices.
   It's needed for multiplication

bits :: Bits b => b -> Int
bits b = loop b 0
    where loop 0 c = c
          loop n c = loop (n `shiftR` 1) (c+1)
-}
{-
bits :: SInt8 -> SInt8
bits v = result
  where r1 :: SInt8 = ite (v .> 0xF) (1 `shiftL` 2) 0
        v1 = v `shiftR` r1
        shift :: SInt8 = ite (v .> 0x3) (1 `shiftL` 1) 0
        v2 = v1 `shiftR` shift
        r2 = r1 .|. shift
        result = r2 .|. (v2 `shiftR` 1)
-}
-- * Yices verification
{-
rangePropSafetyPre :: (Yices.Painless.Type.IsScalar t,
                       Yices.Painless.Type.IsScalar t1) =>
                      t 
                   -> (Exp t -> Exp t -> Exp t1) -- Op
                   -> (Range t -> Range t -> Range t1) -- Range Prop
                   -> (Exp t -> Exp t -> Exp Bool) -- Precondition
                   -> Exp a1 -> Exp a1 -- Range 1
                   -> Exp a -> Exp a   -- Range 2
                   -> Exp a1 -> Exp a  -- Test values
                   -> Exp Bool
-}
rangePropSafetyPre {- t -} op rop pre r1l r1u r2l r2u v1 v2 =
  bnot (isEmpty r1) &&& bnot (isEmpty r2) ==>
      v1 `inRange` r1 ==>
      v2 `inRange` r2 ==>
         pre v1 v2 ==>
         op v1 v2 `inRange` rop r1 r2
  where r1 = range r1l r1u
        r2 = range r2l r2u

rangePropSafety1 op rop l u val =
    bnot (isEmpty ran) ==>
    val `inRange` ran  ==>
        op val `inRange` rop ran
  where ran = range l u

handleSign :: forall a b . (Bits a, Num a, Bounded a) =>
    (Range a -> b) -> (Range a -> b) -> (Range a -> b)
handleSign u s
    | isSigned (minBound::a) = s
    | otherwise              = u

-- ------------------------------------------------------------
-- Addition
-- ------------------------------------------------------------

-- rangeAdd = handleSign rangeAddUnsigned rangeAddSigned

rangeAddUnsigned :: Range SWord32 -> Range SWord32 -> Range SWord32
rangeAddUnsigned (Range l1 u1) (Range l2 u2) = funR
    [ (s .>= l1 &&& t .< u1) := fullRange
    , true                   := range s t]
  where
    s = l1 + l2
    t = u1 + u2
-- Code from Hacker's Delight

rangeAddSigned :: Range SInt32 -> Range SInt32 -> Range SInt32
rangeAddSigned (Range l1 u1) (Range l2 u2) = funR
    [ ((u .|. v) .< 0) := fullRange
    , true             := range s t]
  where
    s = l1 + l2
    t = u1 + u2
    u = l1 .&. l2 .&. complement s .&.
        complement (u1 .&. u2 .&. complement t)
    v = ((xor l1 l2) .|. complement (xor l1 s)) .&.
        (complement u1 .&. complement u2 .&. t)
-- Code from Hacker's Delight

prop_addU = rangePropSafetyPre (+) rangeAddUnsigned (\_ _ -> true)
prop_addS = rangePropSafetyPre (+) rangeAddSigned (\_ _ -> true)

-- ------------------------------------------------------------
-- Subtraction
-- ------------------------------------------------------------

rangeSubUnsigned :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeSubUnsigned (Range l1 u1) (Range l2 u2) = funR
    [ (s .> l1 &&& t .<= u1) := fullRange
    , true                   := range s t]
  where
    s = l1 - u2
    t = u1 - l2

prop_subU = rangePropSafetyPre (-) rangeSubUnsigned (\_ _ -> true)

-- ------------------------------------------------------------
-- Min/Max
-- ------------------------------------------------------------

rangeMax :: Range SWord32 -> Range SWord32 -> Range SWord32
rangeMax r1 r2 = funR
    [ isEmpty r1        := r2
    , isEmpty r2        := r1
    , r1 `rangeLess` r2 := r2
    , r2 `rangeLess` r1 := r1
    , true              := mapMonotonic2 smax r1 r2
    ]

prop_maxU = rangePropSafetyPre smax rangeMax (\_ _ -> true)

-- | Analogous to 'rangeMax'
rangeMin :: Range SInt32 -> Range SInt32 -> Range SInt32
rangeMin r1 r2 = funR
    [ isEmpty r1        := r2
    , isEmpty r2        := r1
    , r1 `rangeLess` r2 := r1
    , r2 `rangeLess` r1 := r2
    , true              := mapMonotonic2 smin r1 r2
    ]

prop_minU = rangePropSafetyPre smin rangeMin (\_ _ -> true)

-- ------------------------------------------------------------
-- Abs
-- ------------------------------------------------------------

rangeAbs :: (SymWord a, Ord a, Num a, Bounded a) => 
            Range (SBV a) -> Range (SBV a)
rangeAbs = rangeOp $ rAbs
  where rAbs r@(Range l u) = funR
          [ isNatural  r                  := r
          , r `isSingletonRange` minBound := r
          , minBound `inRange` r          := range minBound maxBound
          , isNegative r                  := range (abs u) (abs l)
          , true                          := range 0 (abs l `smax` abs u)]

prop_rangeAbs = rangePropSafety1 abs rangeAbs

-- ------------------------------------------------------------
-- Multiplication
-- ------------------------------------------------------------

-- | Unsigned case for 'rangeMul'.
rangeMulUnsigned :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeMulUnsigned r1 r2 = funR
    [ up .== 0
        := mapMonotonic2 (*) r1 r2
    , true := fullRange]
  where e1 = extend (ub r1)
        e2 = extend (ub r2)
        (up,_) = split (e1 * e2) :: (SWord8,SWord8)

-- Trying to verify this for any size above 8 will take *alot* of time.
-- I killed the verification of 16 bit after 71 minutes
prop_mulU = rangePropSafetyPre (*) rangeMulUnsigned (\_ _ -> true)

rangeMulUnsignedD :: Range SWord16 -> Range SWord16 -> Range SWord16
rangeMulUnsignedD r1 r2 = funR
    [ d .== u2
        := mapMonotonic2 (*) r1 r2
    , true := fullRange]
  where u1 = ub r1
        u2 = ub r2
        (d,_) = sQuotRem (u1*u2) u1

prop_mulUD = rangePropSafetyPre (*) rangeMulUnsignedD (\_ _ -> true)

{- It seems that my naive implementation of bvQuotRem didn't work for signed
   types. The question is if Yices supports it at all.

rangeMulSignedD :: Range SInt8 -> Range SInt8 -> Range SInt8
rangeMulSignedD r1 r2 = funR
    [ r1 `isSingletonRange` 0 ||| r1 `isSingletonRange` 0
        := singletonRange 0
    , lb r1 .== minBound ||| lb r2 .== minBound
        := fullRange
    , d .== m2
        := range (sminimum [b1,b2,b3,b4]) (smaximum [b1,b2,b3,b4])
    , true := fullRange]
  where maxAbs (Range l u) = smax (abs l) (abs u)
        m1 = maxAbs r1
        m2 = maxAbs r2
        (d,_) = bvQuotRem (m1*m2) m1
        b1 = lb r1 * lb r2
        b2 = lb r1 * ub r2
        b3 = ub r1 * lb r2
        b4 = ub r1 * ub r2
-}

sminimum ss = foldr1 smin ss
smaximum ss = foldr1 smax ss

{-
Falsifiable. Counter-example:
  s0 = -17 :: SInt8
  s1 = 16 :: SInt8
  s2 = -15 :: SInt8
  s3 = -8 :: SInt8
  s4 = 15 :: SInt8
  s5 = -15 :: SInt8
-}

-- prop_mulSD = rangePropSafetyPre (*) rangeMulSignedD (\_ _ -> true)

-- ------------------------------------------------------------
-- Mod/Rem
-- ------------------------------------------------------------

-- | Propagates range information through 'mod'.
-- Note that we assume Haskell semantics for 'mod'.
rangeMod :: Range SInt8 -> Range SInt8 -> Range SInt8
rangeMod d r = funR
    [ fromBool (isSigned (lb d)) &&& 
      minBound `inRange` d &&& (-1) `inRange` r       := fullRange
    , d `rangeLess` r &&& isNatural r &&& isNatural d := d
    , isNatural r := range 0 (pred (ub r))
    , r `rangeLess` d &&& isNeg r &&& isNeg d         := d
    , isNeg r     := range (succ (lb r)) 0
    , true        := range (succ (lb r)) (pred (ub r))
    ]
    where
      isNeg = (`isSubRangeOf` negs)
      negs  = range minBound 0

-- | Propagates range information through 'rem'.
-- Note that we assume Haskell semantics for 'rem'.
--rangeRem :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeRem :: Range SInt8 -> Range SInt8 -> Range SInt8
rangeRem d r = funR
    [ fromBool (isSigned (lb d)) &&&
      minBound `inRange` d &&& (-1) `inRange` r := fullRange
    , d `rangeLessAbs` r &&& isNatural d := d
    , isNatural d := range 0 (pre (ub (rangeAbs r)))
    , d `absRangeLessAbs` r &&& isNeg d := d
    , isNeg d := range (negate (ub (rangeAbs r))) 0
    , abs l .>= abs u ||| l .== minBound := range (suc $ negate $ abs l) (predAbs l)
    , true := range (suc $ negate $ abs u) (predAbs u)
    ]
    where
      isNeg = (`isSubRangeOf` negs)
      negs  = range minBound 0
      l     = lb r
      u     = ub r

suc a = a + 1
pre a = a - 1

prop_rem = rangePropSafetyPre sRem rangeRem (\_ r -> r ./= 0)

predAbs l = fun [ l .== minBound :=* abs (suc l)
                , true           :=* pre (abs l) ]

-- | Writing @d \`rangeLess\` abs r@ doesn't mean what you think it does because
-- 'r' may contain minBound which doesn't have a positive representation.
-- Instead, this function should be used.
rangeLessAbs d r = fun
    [ r `isSingletonRange` minBound
        :=* lb d ./= minBound
    , lb r .== minBound
        :=* d `rangeLess` (rangeAbs (range (suc (lb r)) (ub r)))
    , true :=* d `rangeLess` (rangeAbs r)
    ]

-- | Similar to 'rangeLessAbs' but replaces the expression 
--   @abs d \`rangeLess\` abs r@ instead.
absRangeLessAbs d r = fun
    [ lb d .== minBound :=* false
    , true              :=* rangeAbs d `rangeLessAbs` r
    ]

-- ------------------------------------------------------------
-- And
-- ------------------------------------------------------------

rangeAndUnsignedCheap :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeAndUnsignedCheap (Range l1 u1) (Range l2 u2) = range 0 (smin u1 u2)
-- Code from Hacker's Delight.

prop_andU = rangePropSafetyPre (.&.) rangeAndUnsignedCheap (\_ _ -> true)

-- ------------------------------------------------------------
-- Or
-- ------------------------------------------------------------

rangeOrUnsignedCheap :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeOrUnsignedCheap (Range l1 u1) (Range l2 u2) =
    range (smax l1 l2) (maxPlus u1 u2)
-- Code from Hacker's Delight.

-- | @a \`maxPlus\` b@ adds @a@ and @b@ but if the addition overflows then
--   'maxBound' is returned.
maxPlus :: (Mergeable a, OrdSymbolic a, Num a, Bounded a) => a -> a -> a
maxPlus b d = symbolicMerge (sum .< b) maxBound sum
  where sum = b + d

prop_OrCheapU = rangePropSafetyPre (.|.) rangeOrUnsignedCheap (\_ _ -> true)

-- | Accurate lower bound for '.|.' on unsigned numbers.
--minOrUnsigned :: BoundedInt a => a -> a -> a -> a -> a
minOrUnsigned a b c d = loop (bit (bitSize a - 1))
  where loop 0 = fun [true :=* a .|. c]
        loop m = fun
            [ (complement a .&. c .&. m) .> 0 :=*
                let temp = (a .|. m) .&. negate m
                in ite (temp .<= b)
                       (temp .|. c)
                       (loop (shiftR m 1))
            , a .&. complement c .&. m .> 0 :=*
                let temp = (c .|. m) .&. negate m
                in ite (temp .<= d)
                       (a .|. temp)
                       (loop (shiftR m 1))
            , true :=* loop (shiftR m 1)]
-- Code from Hacker's Delight.

-- | Accurate upper bound for '.|.' on unsigned numbers.
--maxOrUnsigned :: BoundedInt a => a -> a -> a -> a -> a
maxOrUnsigned a b c d = loop (bit (bitSize a - 1))
  where loop 0 = fun [true :=* b .|. d]
        loop m = fun
             [ (b .&. d .&. m) .> 0 :=*
                 let temp = (b - m) .|. (m - 1)
                 in ite (temp .>= a)
                    (temp .|. d)
                    (let temp = (d - m) .|. (m - 1)
                     in ite (temp .>= c)
                            (b .|. temp)
                            (loop (shiftR m 1)))
             , true :=* loop (shiftR m 1)]
-- Code from Hacker's Delight.

-- | Accurate range propagation through '.|.' for unsigned types.
rangeOrUnsignedAccurate :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeOrUnsignedAccurate (Range l1 u1) (Range l2 u2) =
    range (minOrUnsigned l1 u1 l2 u2) (maxOrUnsigned l1 u1 l2 u2)
-- Code from Hacker's Delight.

prop_orU = rangePropSafetyPre (.|.) rangeOrUnsignedAccurate (\_ _ -> true)

-- ------------------------------------------------------------
-- Xor
-- ------------------------------------------------------------

rangeXorUnsigned :: Range SWord8 -> Range SWord8 -> Range SWord8
rangeXorUnsigned (Range l1 u1) (Range l2 u2) = range 0 (maxPlus u1 u2)
-- Code from Hacker's Delight.

prop_xorU = rangePropSafetyPre (xor) rangeXorUnsigned (\_ _ -> true)


-- Use this instead of prove to get names in the counterexample which match
-- the names in the rangePropSafetyPre property

pp prop = prove (do r1l <- free "r1l"
                    r1u <- free "r1u"
                    r2l <- free "r2l"
                    r2u <- free "r2u"
                    v1  <- free "v1"
                    v2  <- free "v2"
                    return $ prop r1l r1u r2l r2u v1 v2)




-- * Testing at different types

{-
data SupportedType
    = Int8
    | Int16
    | Int32
    | Int64

    | Word8
    | Word16
    | Word32
    | Word64
-}

data TInt8  = Int8
data TInt16 = Int16
data TInt32 = Int32
data TInt64 = Int64

data TWord8  = Word8
data TWord16 = Word16
data TWord32 = Word32
data TWord64 = Word64

class Ty t where
  type Type t

instance Ty TInt8  where
  type Type TInt8  = Int8
instance Ty TInt16 where
  type Type TInt16 = Int16
instance Ty TInt32 where
  type Type TInt32 = Int32
instance Ty TInt64 where
  type Type TInt64 = Int64

instance Ty TWord8 where
  type Type TWord8  = Word8
instance Ty TWord16 where
  type Type TWord16 = Word16
instance Ty TWord32 where
  type Type TWord32 = Word32
instance Ty TWord64 where
  type Type TWord64 = Word64

-- * Overloaded Syntax
{-
class Analysis t where
  (?)   :: t Bool -> (t a, t a) -> t a

  (<)   :: t a -> t a -> t Bool
  (<=)  :: t a -> t a -> t Bool
  (>)   :: t a -> t a -> t Bool
  (>=)  :: t a -> t a -> t Bool
  min   :: t a -> t a -> t a
  max   :: t a -> t a -> t a

  (&&)  :: t Bool -> t Bool -> t Bool
  (||)  :: t Bool -> t Bool -> t Bool

  (+)   :: t a -> t a -> t a
  (-)   :: t a -> t a -> t a
  (*)   :: t a -> t a -> t a
  (/)   :: t a -> t a -> t a

  (.&.) :: t a -> t a -> t a
  (.|.) :: t a -> t a -> t a
  (<<)  :: t a -> t a -> t a
  (>>)  :: t a -> t a -> t a
  xor   :: t a -> t a -> t a
  compl :: t a -> t a -> t a
-}

-- Experiments

foo = fromBitsLE [true,false,false,false,false,false,false] :: SWord8

-- bar = sat (\x -> let (a,_) = bvQuotRem (8 :: SInt8) (-4) in a .== x)

