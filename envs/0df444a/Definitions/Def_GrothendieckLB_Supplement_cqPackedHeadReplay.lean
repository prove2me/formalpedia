-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqPackedHeadReplay
-- name    : GrothendieckLB_Supplement_cqPackedHeadReplay
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:10:20.960508+00:00
-- url     : https://prove2.me/theorems/1304c4c2-9702-4599-b6fd-0d7f97dfa34c
-- title:
--   Packed integer witnesses for the cubic–quintic coefficient certificate
-- statement:
--   Integer witnesses record the sextic-moment recurrence, factorials, the initial Hermite transform, every sixteenth row of the cubic Hermite recurrence, the rational polynomial powers, and row sums in the degree extraction. Signed integers are packed in power-of-two limbs. A strip check compares each recovered neighboring row with the prescribed integer recurrence and each weight with its prescribed square. Witness generation supplies data; all claimed equalities have separate Boolean predicates.
-- source:
--   Integer replay of Saha et al., arXiv:2608.11158v2, coefficient formula (13) and Appendix C.1. The input intervals come from the published GrothendieckLB.Supplement.cqNonlinearHeadCheck.

import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck
import Mathlib.Tactic.Eval

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadReplay

def encode (x : ℤ) : ℕ := if x < 0 then 2*x.natAbs-1 else 2*x.natAbs
def decode (n : ℕ) : ℤ := if n%2=0 then (n/2:ℕ) else -((n/2+1:ℕ):ℤ)
def numeral (width : ℕ) (field : ℕ → ℤ) (n : ℕ) : ℕ :=
  (List.range n).foldr (fun i acc => encode (field i)+(acc <<< width)) 0
def vfield (x : MomentCombination) (k : ℕ) : ℤ :=
  match k with | 0 => x.e0.lo | 1 => x.e0.hi | 2 => x.e2.lo | 3 => x.e2.hi | 4 => x.e4.lo | _ => x.e4.hi
structure Packed where
  width : ℕ
  blocks : Array ℕ
  deriving Lean.ToExpr, Inhabited, DecidableEq

def packed (n stride batch : ℕ) (f : ℕ → ℕ → ℤ) : Packed :=
  let bits := (List.range n).foldl (fun mx i => (List.range stride).foldl (fun m k => max m (encode (f i k)).log2) mx) 0 + 1
  ⟨bits,tab ((n+batch-1)/batch) fun c => numeral bits (fun j => f (c*batch+j/stride) (j%stride)) (batch*stride)⟩

def getN (p : Packed) (stride batch n k : ℕ) : ℤ :=
  decode (((entry 0 p.blocks (n/batch)) >>> (p.width*(stride*(n%batch)+k))) % (2^p.width))
def packA (par : ℕ) (xs : Array MomentCombination) : Packed :=
  packed ((xs.size+1-par)/2) 6 8 fun i k => vfield (entry zeroCombination xs (2*i+par)) k

def getA (p : Packed) (par i : ℕ) : MomentCombination :=
  if i%2=par then
    let f := getN p 6 8 (i/2)
    ⟨⟨f 0,f 1⟩,⟨f 2,f 3⟩,⟨f 4,f 5⟩⟩
  else zeroCombination

def packB (par : ℕ) (xs : Array Interval) : Packed :=
  packed ((xs.size+1-par)/2) 2 16 fun i k =>
    let x := entry zeroInterval xs (2*i+par)
    if k=0 then x.lo else x.hi
def getB (p : Packed) (par i : ℕ) : Interval :=
  if i%2=par then ⟨getN p 2 16 (i/2) 0,getN p 2 16 (i/2) 1⟩ else zeroInterval

def rawData : Packed := eval% packA 0 (momentRows 748)
def raw (n : ℕ) := getA rawData 0 n

/-- Generate a candidate initial Hermite row with a cached factorial table. Its entries are checked separately. -/
def startCandidate : Array MomentCombination :=
  let tabF := tab 754 fun n => (n.factorial,n.doubleFactorial)
  let vals := momentRows 748
  tab 754 fun b => if b%2=0 then sumCombinations (fun k =>
    let f (i : ℕ) := (entry (0,0) tabF i).1
    let d := (entry (0,0) tabF (b-k-1)).2
    let c := if (b+k)%2=0 then (-1:ℤ)^((b-k)/2)*d*(f b/(f k*f (b-k)):ℕ) else 0
    scaleCombination c (entry zeroCombination vals k)) (b+1) else zeroCombination

def startData : Packed := eval% packA 0 startCandidate
def first (n : ℕ) := getA startData 0 n

def factsData : Packed := eval% packed 756 2 8 fun n k => if k=0 then (n.factorial:ℤ) else (n.doubleFactorial:ℤ)
def fac (n : ℕ) := (getN factsData 2 8 n 0).toNat
def dfac (n : ℕ) := (getN factsData 2 8 n 1).toNat

def hc (n k : ℕ) : ℤ :=
  if (n+k)%2=0 then (-1:ℤ)^((n-k)/2)*dfac (n-k-1)*(fac n/(fac k*fac (n-k)):ℕ) else 0

def rawStep (n : ℕ) (x y z : MomentCombination) : MomentCombination :=
  if n%2=0 then divideCombination (3*slopeNumerator) (addCombination
    (subCombination (scaleCombination (((n:ℤ)+1)*slopeDenominator) x)
      (scaleCombination (slopeDenominator+9*slopeNumerator) y)) (scaleCombination (12*slopeNumerator) z)) else zeroCombination
def rawOK (n : ℕ) : Bool := decide (raw (n+6) = rawStep n (raw n) (raw (n+2)) (raw (n+4)))
def factOK (n : ℕ) : Bool := decide (fac (n+1)=(n+1)*fac n ∧ dfac (n+2)=(n+2)*dfac n)
def startOK (b : ℕ) : Bool := if b%2=0 then decide (first b = sumCombinations (fun k => scaleCombination (hc b k) (raw k)) (b+1))
  else decide (first b=zeroCombination)




/-- Sparse checkpoints allow the verifier to replay short strips of consecutive Hermite rows. -/
def rowLength (p : ℕ) := 754-3*p
def rowAt (p : ℕ) (d : Packed) := tab (rowLength p) (getA d (p%2))
def roll (start count : ℕ) (prev cur : Array MomentCombination)
    (keep : ℕ → Bool) : Array (Packed × Packed) := Id.run do
  let mut left := prev
  let mut right := cur
  let mut out := #[]
  for k in [:count] do
    let p := start+k
    if keep p then
      out := out.push (packA ((p-1)%2) left, packA (p%2) right)
    let r := nextRow p left right
    left := right
    right := r
  return out

def checkpoints : Array (Packed × Packed) := eval%
  let x := rowAt 0 startData
  roll 0 252 x x fun p => p%16=0 || p=251

def cpRow (p : ℕ) := (entry default checkpoints (p/16)).2
def cpPrev (p : ℕ) := (entry default checkpoints (p/16)).1

/-- Internal rows of a certificate strip, starting at its two published checkpoint rows. -/
def makeStrip (start count : ℕ) : Array Packed := Id.run do
  let mut l := rowAt (start-1) (cpPrev start)
  let mut r := rowAt start (cpRow start)
  let mut out := #[]
  for k in [:count] do
    out := out.push (packA ((start+k)%2) r)
    let s := nextRow (start+k) l r
    l := r
    r := s
  return out

def shiftAt (f : ℕ → MomentCombination) (b : ℕ) : MomentCombination :=
  addCombination (f (b+1)) (scaleCombination b (f (b-1)))
def nextAt (p : ℕ) (l r : ℕ → MomentCombination) (b : ℕ) :=
  subCombination (multiplyByParityFactor p (subCombination (scaleCombination 3 (shiftAt r b))
    (shiftAt (shiftAt (shiftAt r)) b))) (scaleCombination p (l b))

def rowTest (p : ℕ) (prev cur next : Packed) (b : ℕ) : Bool :=
  decide (getA next ((p+1)%2) b = nextAt p (getA prev ((p-1)%2)) (getA cur (p%2)) b)


def weightsData : Array Packed := eval%
  let ws := (grid 251 (rowAt 0 startData) 251).weights
  tab 252 fun a => packB ((a+1)%2) (entry #[] ws a)
def weight (a b : ℕ) : Interval := getB (entry default weightsData a) ((a+1)%2) b

def powersData : Array Packed := eval%
  let rs := rhoPowers 251 251
  tab 252 fun a => packB (a%2) (entry #[] rs a)
def power (a j : ℕ) : Interval := getB (entry default powersData a) (a%2) j

def weightAt (p b : ℕ) (x : MomentCombination) : Interval :=
  let base : ℤ := (fac (p+1):ℤ)*(fac b:ℤ)
  if p%2=0 then scaledSq 1 base x else scaledSq slopeNumerator (slopeDenominator*base) x

def zeroWeightAt (b : ℕ) : Interval := if b=0 then zeroInterval else
  scaledSq (9*slopeNumerator) (slopeDenominator*fac b)
    (subCombination (shiftAt (shiftAt first) (b-1)) (first (b-1)))

def powerAt (a j : ℕ) : Interval :=
  let s (k : ℕ) := if k≤j then power a (j-k) else zeroInterval
  divideOut rhoDen (addInterval (subInterval (scaleInterval rho1 (s 1)) (scaleInterval rho3 (s 3)))
    (scaleInterval rho5 (s 5)))

def stripLen (c : ℕ) : ℕ := min 16 (251-16*c)
def checkpoint (c : ℕ) := entry default checkpoints c

def inStrip (c : ℕ) (xs : Array Packed) (k : ℕ) : Packed :=
  if k=0 then (checkpoint c).2 else if k=stripLen c then (checkpoint (c+1)).2 else entry default xs k

def beforeStrip (c : ℕ) (xs : Array Packed) (k : ℕ) : Packed :=
  if k=0 then (checkpoint c).1 else inStrip c xs (k-1)

def stripChecks (c : ℕ) (xs : Array Packed) : Bool :=
  decide (inStrip c xs (stripLen c-1) = (checkpoint (c+1)).1) &&
  (List.range (stripLen c)).all fun k =>
    let p := 16*c+k
    let cur := inStrip c xs k
    ((List.range (rowLength (p+1))).all
      (rowTest p (beforeStrip c xs k) cur (inStrip c xs (k+1)))) &&
    (List.range (251-p)).all fun b => decide (weight (p+1) b=weightAt p b (getA cur (p%2) b))

def rawChecks : Bool := (List.range 748).all rawOK

def factChecks : Bool :=
  decide (fac 0=1 ∧ dfac 0=1 ∧ dfac 1=1) && (List.range 753).all factOK

def firstChecks (c : ℕ) : Bool := (List.range 16).all fun j =>
  let b := 2*(16*c+j)
  if b < 754 then startOK b else true

def initialChecks : Bool :=
  decide ((checkpoint 0).1=startData ∧ (checkpoint 0).2=startData) &&
  (List.range 6).all (fun b => decide (raw b=entry zeroCombination (momentRows 0) b)) &&
  (List.range 252).all fun b => decide (weight 0 b=zeroWeightAt b ∧ power 0 b=(if b=0 then fixed coefficientScale else zeroInterval))

def powerChecks (c : ℕ) : Bool := (List.range (min 16 (251-16*c))).all fun k =>
  (List.range 252).all fun j => decide (power (16*c+k+1) j=powerAt (16*c+k) j)

def term (m a b : ℕ) : Interval :=
  scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale (weight a b) (power a (m-b)))

def part (m a : ℕ) : Interval := sumIntervals (term m a) (m+1-a)

def partialData : Array Packed := eval%
  let ws := (grid 251 (rowAt 0 startData) 251).weights
  let rs := rhoPowers 251 251
  tab 125 fun j =>
    let m := 2*j+3
    let res := tab (m+1) fun a =>
      let w := entry #[] ws a
      let r := entry #[] rs a
      sumIntervals (fun b => scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale
        (entry zeroInterval w b) (entry zeroInterval r (m-b)))) (m+1-a)
    packed (m+1) 2 16 fun a k => if k=0 then (entry zeroInterval res a).lo else (entry zeroInterval res a).hi

def savedPart (j a : ℕ) : Interval :=
  let p := entry default partialData j
  ⟨getN p 2 16 a 0, getN p 2 16 a 1⟩

def partialChecks (j : ℕ) : Bool :=
  (List.range (2*j+4)).all fun a => decide (savedPart j a=part (2*j+3) a)

def totalChecks : Bool := (List.range 125).all fun j =>
  let v := sumIntervals (savedPart j) (2*j+4)
  max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0)

end GrothendieckLB.Supplement.CQHeadReplay


