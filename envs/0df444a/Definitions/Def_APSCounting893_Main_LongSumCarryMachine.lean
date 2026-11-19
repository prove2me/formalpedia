-- Prove2me | Definitions.Def_APSCounting893_Main_LongSumCarryMachine
-- name    : APSCounting893_Main_LongSumCarryMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T21:43:12.178933+00:00
-- url     : https://prove2.me/theorems/abbb0811-8ba8-4f48-9947-24780e87ec23
-- title:
--   Finite binary carry-certificate query machine
-- statement:
--   For a finite implicit sum with $2^{a(|x|+1)^b}$ summands, split each summand into blocks of width $a(|x|+1)^b+1$. A carry certificate contains a carry bit, a proposed generating position, a universally selected position, a counterexample position, and six proposed block-sum values.
--   The query function reads these fields from polynomial-width binary chunks. It checks the arithmetic carry conditions and returns either a tagged query to the actual block-sum value graph or a Boolean constant. Selectors $0,\ldots,5$ check the six values; selectors $6,7$ return true. Malformed root bit queries return false.
--   This file defines only the encodings, field operations and explicit query function. Its polynomial-time implementation and its equivalence to the carry criterion are separate proof targets.
-- source:
--   Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, Section 3, iterated addition discussion, author manuscript p. 7, and Section 4, Lemma 4.3, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Explicit finite-machine carry-certificate implementation for the coefficient arithmetic in Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26.

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString
def readWordField (W i : ℕ) (w : Word) : Word := (w.drop (i*W)).take W

def readNatField (W i : ℕ) (w : Word) : ℕ := ofBits (readWordField W i w)

def encodeFixedNatFields (W : ℕ) (values : List ℕ) : Word := values.flatMap (lowBits W)

def parseNaturalBitQuery (z : Word) : Option (Word × ℕ) :=
  (decodeNat (Turing.MultiTapeTM.dropFrame z)).bind fun qr =>
    if qr.2=[] ∧ z=Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++Turing.MultiTapeTM.dropFrame z
      then some (Turing.MultiTapeTM.unframe z,qr.1) else none

def carryBaseValue (B index previous : ℕ) : ℕ := if index=0 then 0 else previous/B

def carryGenerateTest (B index current previous : ℕ) : Bool :=
  decide (B ≤ current%B+carryBaseValue B index previous)

def carryPropagateTest (B index current previous : ℕ) : Bool :=
  decide (current%B+carryBaseValue B index previous+1=B)

def carryOutputTest (B index current previous c pos : ℕ) : Bool :=
  ((current+carryBaseValue B index previous+c)%B).testBit pos

abbrev CarryMatrixInput := Word × ℕ × ℕ × ℕ × ℕ × ℕ × Word × Word × Word × Word × Word × Word

def encCarryMatrixInput : CarryMatrixInput ↪ Word := encPair encBits (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encBits (encPair encBits (encPair encBits (encPair encBits (encPair encBits (encBits)))))))))))

def CarryMatrixInput.x (p : CarryMatrixInput) : Word := p.1

def CarryMatrixInput.q (p : CarryMatrixInput) : ℕ := p.2.1

def CarryMatrixInput.carry (p : CarryMatrixInput) : ℕ := p.2.2.1

def CarryMatrixInput.generator (p : CarryMatrixInput) : ℕ := p.2.2.2.1

def CarryMatrixInput.universal (p : CarryMatrixInput) : ℕ := p.2.2.2.2.1

def CarryMatrixInput.counter (p : CarryMatrixInput) : ℕ := p.2.2.2.2.2.1

def CarryMatrixInput.current (p : CarryMatrixInput) : Word := p.2.2.2.2.2.2.1

def CarryMatrixInput.previous (p : CarryMatrixInput) : Word := p.2.2.2.2.2.2.2.1

def CarryMatrixInput.gen (p : CarryMatrixInput) : Word := p.2.2.2.2.2.2.2.2.1

def CarryMatrixInput.genPrevious (p : CarryMatrixInput) : Word := p.2.2.2.2.2.2.2.2.2.1

def CarryMatrixInput.prop (p : CarryMatrixInput) : Word := p.2.2.2.2.2.2.2.2.2.2.1

def CarryMatrixInput.propPrevious (p : CarryMatrixInput) : Word := p.2.2.2.2.2.2.2.2.2.2.2

def carryMatrixWidth (a b : ℕ) (p : CarryMatrixInput) : ℕ := polyBound a b p.x.length+1

def carryMatrixBase (a b : ℕ) (p : CarryMatrixInput) : ℕ := 2^carryMatrixWidth a b p

def carryMatrixIndex (a b : ℕ) (p : CarryMatrixInput) : ℕ := p.q/carryMatrixWidth a b p

def carryMatrixPosition (a b : ℕ) (p : CarryMatrixInput) : ℕ := p.q%carryMatrixWidth a b p

def carryMatrixGenIndex (p : CarryMatrixInput) : ℕ := if p.carry=1 then p.generator else p.universal

def carryMatrixPropIndex (p : CarryMatrixInput) : ℕ := if p.carry=1 then p.universal else p.counter

def carryMatrixGeneration (a b : ℕ) (p : CarryMatrixInput) : Bool :=
  carryGenerateTest (carryMatrixBase a b p) (carryMatrixGenIndex p)
    (ofBits p.gen) (ofBits p.genPrevious)

def carryMatrixPropagation (a b : ℕ) (p : CarryMatrixInput) : Bool :=
  carryPropagateTest (carryMatrixBase a b p) (carryMatrixPropIndex p)
    (ofBits p.prop) (ofBits p.propPrevious)

def carryMatrixOutput (a b : ℕ) (p : CarryMatrixInput) : Bool :=
  carryOutputTest (carryMatrixBase a b p) (carryMatrixIndex a b p)
    (ofBits p.current) (ofBits p.previous) p.carry (carryMatrixPosition a b p)

def carryMatrixGuard (a b : ℕ) (p : CarryMatrixInput) : Bool :=
  let k := carryMatrixIndex a b p
  let mode := decide (p.carry=1)
  (decide (p.carry ≤ 1) && carryMatrixOutput a b p) &&
    ((!mode || decide (p.generator < k)) &&
      (if mode then carryMatrixGeneration a b p &&
        (!(decide (p.generator < p.universal) && decide (p.universal < k)) || carryMatrixPropagation a b p)
       else !decide (p.universal < k) ||
        (!carryMatrixGeneration a b p ||
          ((decide (p.universal < p.counter) && decide (p.counter < k)) && !carryMatrixPropagation a b p))))

def carryGraphWord (x : Word) (index : ℕ) (candidate : Word) : Word :=
  [false,false]++Turing.MultiTapeTM.frame (Turing.MultiTapeTM.frame x++index.bits)++candidate

def carryMatrixQuery (a b : ℕ) (v : CarryMatrixInput × ℕ) : Word :=
  let p := v.1
  if carryMatrixGuard a b p then
    if v.2=0 then carryGraphWord p.x (carryMatrixIndex a b p) p.current
    else if v.2=1 then carryGraphWord p.x (carryMatrixIndex a b p-1) p.previous
    else if v.2=2 then carryGraphWord p.x (carryMatrixGenIndex p) p.gen
    else if v.2=3 then carryGraphWord p.x (carryMatrixGenIndex p-1) p.genPrevious
    else if v.2=4 then carryGraphWord p.x (carryMatrixPropIndex p) p.prop
    else if v.2=5 then carryGraphWord p.x (carryMatrixPropIndex p-1) p.propPrevious
    else [true,true]
  else [true,false]

def longSumFieldWidth (a b : ℕ) (z : Word) : ℕ :=
  polyBound (2*a+3) (b+1) z.length

def longSumRoot (z : Word) : Word := unframe (unframe (unframe (unframe z)))

def longSumOuter (z : Word) : Word := dropFrame (unframe (unframe (unframe z)))

def longSumUniversal (z : Word) : Word := dropFrame (unframe (unframe z))

def longSumInner (z : Word) : Word := dropFrame (unframe z)

def longSumSelector (z : Word) : ℕ := ofBits (dropFrame z)

def longSumMatrixData (a b : ℕ) (z : Word) (xq : Word × ℕ) : CarryMatrixInput :=
  let W := longSumFieldWidth a b (longSumRoot z)
  (xq.1,xq.2,
    readNatField W 0 (longSumOuter z),readNatField W 1 (longSumOuter z),
    readNatField W 0 (longSumUniversal z),readNatField W 0 (longSumInner z),
    readWordField W 2 (longSumOuter z),readWordField W 3 (longSumOuter z),
    readWordField W 1 (longSumInner z),readWordField W 2 (longSumInner z),
    readWordField W 3 (longSumInner z),readWordField W 4 (longSumInner z))

def longSumMatrixQuery (a b : ℕ) (z : Word) : Word :=
  match parseNaturalBitQuery (longSumRoot z) with
  | none => [true,false]
  | some xq => carryMatrixQuery a b (longSumMatrixData a b z xq,longSumSelector z)
end APSCounting893.Main


