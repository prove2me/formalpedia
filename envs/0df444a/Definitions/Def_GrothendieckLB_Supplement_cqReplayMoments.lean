-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments
-- name    : GrothendieckLB_Supplement_cqReplayMoments
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:36:33.72592+00:00
-- url     : https://prove2.me/theorems/55849de8-a106-4193-af36-2ed8a3dcf5ca
-- title:
--   Integer sextic moments and their initial Hermite transform
-- statement:
--   Candidate starting data record the raw three-term sextic moment rows, factorials and double factorials, and the initial change of basis to monic Hermite polynomials. The predicates compare these integers with their initial conditions and recurrence steps.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayPacking

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def rawData : Packed := eval% packA 0 (momentRows 748)

def raw (n : ℕ) := getA rawData 0 n

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

def rowLength (p : ℕ) := 754-3*p

def rowAt (p : ℕ) (d : Packed) := tab (rowLength p) (getA d (p%2))

def shiftAt (f : ℕ → MomentCombination) (b : ℕ) : MomentCombination :=
  addCombination (f (b+1)) (scaleCombination b (f (b-1)))

def rawChecks : Bool := (List.range 748).all rawOK

def factChecks : Bool :=
  decide (fac 0=1 ∧ dfac 0=1 ∧ dfac 1=1) && (List.range 753).all factOK

def firstChecks (c : ℕ) : Bool := (List.range 16).all fun j =>
  let b := 2*(16*c+j)
  if b < 754 then startOK b else true

end GrothendieckLB.Supplement.CQHeadCertificate


