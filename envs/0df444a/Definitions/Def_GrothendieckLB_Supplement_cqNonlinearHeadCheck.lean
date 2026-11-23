-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck
-- name    : GrothendieckLB_Supplement_cqNonlinearHeadCheck
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T18:07:30.693138+00:00
-- url     : https://prove2.me/theorems/b7c90c6d-7f40-4894-8551-9bf8c85a8040
-- title:
--   Integer certificate for the 125 nonlinear cubic–quintic head bounds
-- statement:
--   This Boolean is the conjunction of 125 finite integer inequalities for the nonlinear Taylor numerators of the cubic–quintic scheme. It propagates three linear coefficients for each sextic moment using outward rounding with denominator $2^{2560}$. The identity $xH_b=H_{b+1}+bH_{b-1}$ acts on Hermite-indexed rows by a shift. Three shifts give multiplication by $x^3$, allowing the threshold Hermite polynomials to be evaluated recursively. The starting moment intervals are inserted before squaring. A second fixed denominator $2^{144}$ is used to accumulate the squared moments and the polynomial coefficients of the correlation powers. The output checks the integer endpoints of all odd degrees from 3 through 251.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Theorem 5.1 and Appendix C.1. Independent finite calculation using the sextic moment recurrence.

import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits

namespace GrothendieckLB.Supplement.CQHeadArithmetic

def slopeNumerator : ℤ := 744407106630625
def slopeDenominator : ℤ := 268577376128344728
def hermiteCoeff (n k : ℕ) : ℤ :=
  if (n+k)%2=0 then (-1:ℤ)^((n-k)/2)*(n-k-1).doubleFactorial*
    (n.factorial/(k.factorial*(n-k).factorial):ℕ) else 0


/-- Integer endpoints of an interval with a common denominator fixed by the surrounding calculation. -/
structure Interval where
  lo : ℤ
  hi : ℤ
  deriving Inhabited, DecidableEq

def zeroInterval : Interval := ⟨0,0⟩
def fixed (t : ℤ) : Interval := ⟨t,t⟩
def addInterval (x y : Interval) : Interval := ⟨x.lo+y.lo,x.hi+y.hi⟩
def subInterval (x y : Interval) : Interval := ⟨x.lo-y.hi,x.hi-y.lo⟩
def scaleInterval (k : ℤ) (x : Interval) : Interval :=
  if k = 0 then zeroInterval else if 0 ≤ k then ⟨k*x.lo,k*x.hi⟩ else ⟨k*x.hi,k*x.lo⟩
def divideOut (d : ℤ) (x : Interval) : Interval := ⟨x.lo/d,-((-x.hi)/d)⟩
def mulInterval (d : ℤ) (x y : Interval) : Interval :=
  let a := x.lo*y.lo
  let b := x.lo*y.hi
  let c := x.hi*y.lo
  let e := x.hi*y.hi
  divideOut d ⟨min (min a b) (min c e),max (max a b) (max c e)⟩
def sqInterval (x : Interval) : Interval :=
  let lo := if x.lo ≤ 0 ∧ 0 ≤ x.hi then 0 else min (x.lo*x.lo) (x.hi*x.hi)
  ⟨lo,max (x.lo*x.lo) (x.hi*x.hi)⟩

/-- Three coefficient intervals retain linear dependence on the initial moments until squaring. -/
structure MomentCombination where
  e0 : Interval
  e2 : Interval
  e4 : Interval
  deriving Inhabited, DecidableEq

def zeroCombination : MomentCombination := ⟨zeroInterval,zeroInterval,zeroInterval⟩
def addCombination (a b : MomentCombination) : MomentCombination := ⟨addInterval a.e0 b.e0, addInterval a.e2 b.e2, addInterval a.e4 b.e4⟩
def subCombination (a b : MomentCombination) : MomentCombination := ⟨subInterval a.e0 b.e0, subInterval a.e2 b.e2, subInterval a.e4 b.e4⟩
def scaleCombination (k : ℤ) (a : MomentCombination) : MomentCombination := ⟨scaleInterval k a.e0,scaleInterval k a.e2,scaleInterval k a.e4⟩
def divideCombination (d : ℤ) (a : MomentCombination) : MomentCombination := ⟨divideOut d a.e0,divideOut d a.e2,divideOut d a.e4⟩
def momentScale : ℤ := 2^2560
def coefficientScale : ℤ := 2^144
def seedBox (lower : ℤ) : Interval := ⟨lower*2^2176,(lower+1)*2^2176⟩
def seed0 := seedBox 98100829642129577717705252461250802877285043994588462406870607474137489297660729170734376455389328977175112900544138
def seed2 := seedBox 95020680131779427752407447234488278202461530610309981184152310885588522728819096259031464439548105786990997297548714
def seed4 := seedBox 262876500006536681973879627718902500274060155065983995563998798928285304964789315907500644382597812284962670046502317
def collapse (x : MomentCombination) : Interval :=
  addInterval (addInterval (mulInterval momentScale x.e0 seed0) (mulInterval momentScale x.e2 seed2)) (mulInterval momentScale x.e4 seed4)

def tab {α : Type} (n : ℕ) (f : ℕ → α) : Array α := Array.ofFn (fun i : Fin n => f i)
def entry {α : Type} (default : α) (xs : Array α) (n : ℕ) := xs[n]?.getD default
def basis (i : ℕ) : MomentCombination := ⟨if i=0 then fixed momentScale else zeroInterval,
  if i=2 then fixed momentScale else zeroInterval,if i=4 then fixed momentScale else zeroInterval⟩

/-- Exact rational recurrence, evaluated with outward integer rounding. -/
def momentRows : ℕ → Array MomentCombination
  | 0 => #[basis 0,zeroCombination,basis 2,zeroCombination,basis 4,zeroCombination]
  | n+1 =>
    let xs := momentRows n
    let step := divideCombination (3*slopeNumerator) (addCombination (subCombination (scaleCombination (((n:ℤ)+1)*slopeDenominator) (entry zeroCombination xs n))
          (scaleCombination (slopeDenominator+9*slopeNumerator) (entry zeroCombination xs (n+2)))) (scaleCombination (12*slopeNumerator) (entry zeroCombination xs (n+4))))
    xs.push (if n%2=0 then step else zeroCombination)

def sumCombinations (f : ℕ → MomentCombination) : ℕ → MomentCombination
  | 0 => zeroCombination
  | n+1 => addCombination (sumCombinations f n) (f n)
def sumIntervals (f : ℕ → Interval) : ℕ → Interval
  | 0 => zeroInterval
  | n+1 => addInterval (sumIntervals f n) (f n)
def hStart (raw : Array MomentCombination) (b : ℕ) : MomentCombination :=
  if b%2=0 then sumCombinations (fun k => scaleCombination (hermiteCoeff b k) (entry zeroCombination raw k)) (b+1) else zeroCombination

def shift (x : Array MomentCombination) : Array MomentCombination :=
  tab (x.size-1) fun b => addCombination (entry zeroCombination x (b+1)) (scaleCombination b (entry zeroCombination x (b-1)))
def multiplyByParityFactor (p : ℕ) (x : MomentCombination) : MomentCombination :=
  if p%2=0 then x else divideCombination slopeDenominator (scaleCombination slopeNumerator x)
/-- Multiplication by the cubic threshold acts by three shifts in the Hermite basis. -/
def nextRow (p : ℕ) (prev cur : Array MomentCombination) : Array MomentCombination :=
  let x1 := shift cur
  let x3 := shift (shift x1)
  tab x3.size fun b => subCombination (multiplyByParityFactor p (subCombination (scaleCombination 3 (entry zeroCombination x1 b)) (entry zeroCombination x3 b)))
    (scaleCombination p (entry zeroCombination prev b))

def scaledSq (num den : ℤ) (x : MomentCombination) : Interval :=
  divideOut (momentScale*momentScale*den) (scaleInterval (coefficientScale*num) (sqInterval (collapse x)))

def toWeight (a b : ℕ) (x : MomentCombination) : Interval :=
  let base : ℤ := (a.factorial:ℤ)*(b.factorial:ℤ)
  if (a-1)%2=0 then scaledSq 1 base x else scaledSq slopeNumerator (slopeDenominator*base) x
def zeroWeights (N : ℕ) (x : Array MomentCombination) : Array Interval :=
  let x2 := shift (shift x)
  tab (N+1) fun b => if b=0 then zeroInterval else
    scaledSq (9*slopeNumerator) (slopeDenominator*b.factorial) (subCombination (entry zeroCombination x2 (b-1)) (entry zeroCombination x (b-1)))

structure Grid where
  prev : Array MomentCombination
  cur : Array MomentCombination
  weights : Array (Array Interval)

def grid (N : ℕ) (x : Array MomentCombination) : ℕ → Grid
  | 0 => ⟨x,x,#[zeroWeights N x]⟩
  | p+1 =>
    let st := grid N x p
    let w := tab (N-p) fun b => toWeight (p+1) b (entry zeroCombination st.cur b)
    ⟨st.cur,nextRow p st.prev st.cur,st.weights.push w⟩

def rho1 : ℤ := 10^16
def rho3 : ℤ := 34101124^2
def rho5 : ℤ := 5276111^2
def rhoDen : ℤ := rho1+rho3+rho5
def shifted (x : Array Interval) (k j : ℕ) := if k≤j then entry zeroInterval x (j-k) else zeroInterval
def rhoNext (N : ℕ) (x : Array Interval) : Array Interval :=
  tab (N+1) fun j => divideOut rhoDen (addInterval (subInterval (scaleInterval rho1 (shifted x 1 j)) (scaleInterval rho3 (shifted x 3 j)))
      (scaleInterval rho5 (shifted x 5 j)))
def rhoPowers (N : ℕ) : ℕ → Array (Array Interval)
  | 0 => #[tab (N+1) (fun j => if j=0 then fixed coefficientScale else zeroInterval)]
  | a+1 => let xs := rhoPowers N a; xs.push (rhoNext N (entry #[] xs a))

def fullSum (w r : Array (Array Interval)) (m : ℕ) : Interval :=
  sumIntervals (fun a =>
    let wa := entry #[] w a
    let ra := entry #[] r a
    sumIntervals (fun b => scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale (entry zeroInterval wa b) (entry zeroInterval ra (m-b)))) (m+1-a)) (m+1)

def startAt (N : ℕ) : Array MomentCombination := tab (3*N+1) (hStart (momentRows (3*N-5)))
/-- Check the unnormalized nonlinear numerators at the specified odd-degree indices. -/
def verifyList (N : ℕ) (indices : List ℕ) : Bool :=
  let w := (grid N (startAt N) N).weights
  let r := rhoPowers N N
  indices.all fun j =>
    let v := fullSum w r (2*j+3)
    max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0)

end GrothendieckLB.Supplement.CQHeadArithmetic

namespace GrothendieckLB.Supplement

/-- The finite cubic–quintic certificate for the 125 odd nonlinear head coefficients. -/
def cqNonlinearHeadCheck : Bool := CQHeadArithmetic.verifyList 251 (List.range 125)

end GrothendieckLB.Supplement


