-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics
-- name    : ZLIPPadding_Padding_Supplement_Statistics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:15:07.902223+00:00
-- url     : https://prove2.me/theorems/cc57ce3f-7039-4080-8e8e-6a4f92840ad0
-- title:
--   Signed shell statistics, estimators, and flat proportions
-- statement:
--   For a shell law $\mu$ and hidden orthogonal matrix $O$, define the actual fourth-moment matrix, pairwise fourth moment, coordinate matrix, and their empirical counterparts. With $x$ the prescribed query and $v_i=Oe_i$, the population objects are
--
--   $$C_x=\mathbb E[YY^\top\langle x,Y\rangle^2],\quad K_x=mI+2xx^\top,\quad D_x=\sum_i a_i^2v_iv_i^\top.$$
--
--   The pairwise statistic sums all ordered unequal sample pairs. The signed square-root estimator retains the sign of $\kappa$ and the positive part. The definition also records both explicit sample thresholds, the integer shell recurrence with its zero-dimensional initial condition, the rational counting formulas, the flat proportions and the exact short-shell range. These are computed quantities and predicates, with no concentration or recovery conclusions assumed.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 15–21, 24–26 (PDF pp. 16–22, 25–27), equations (4.1)–(4.20), (6.1)–(6.3)

import Definitions.Def_ZLIPPadding_Padding_Supplement_Geometry

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def cN (n : ℕ) : ℝ := (n : ℝ)*(n-1)/(n+2)
def bNM (n m : ℕ) : ℝ := 3*(m : ℝ)^4/((n : ℝ)*(n+2))
def momentC {n : ℕ} (O : RMat n) (m : ℕ) (μ : PMF (ZVec n))
    (x : EVec n) : RMat n := fun i j =>
  expectShell m μ (fun z => let y := rotate O (liftZ z)
    y i*y j*(inner ℝ x y)^2)
def queryK {n : ℕ} (m : ℕ) (x : EVec n) : RMat n :=
  (m : ℝ) • (1 : RMat n) + 2 • outer x
def coordinateD {n : ℕ} (O : RMat n) (a : ZVec n) : RMat n :=
  fun i j => ∑ k, (a k : ℝ)^2*O i k*O j k
def pairMoment {n : ℕ} (O : RMat n) (m : ℕ) (μ : PMF (ZVec n)) : ℝ :=
  expectShell m μ (fun u => expectShell m μ (fun v =>
    (inner ℝ (rotate O (liftZ u)) (rotate O (liftZ v)))^4))
def empiricalPair {n : ℕ} (ys : List (EVec n)) : ℝ :=
  (∑ i : Fin ys.length, ∑ j : Fin ys.length,
    if i = j then 0 else (inner ℝ ys[i] ys[j])^4) /
    ((ys.length : ℝ)*(ys.length-1))
def estimateKappa (n m : ℕ) (sign muHat : ℝ) : ℝ :=
  sign * Real.sqrt (max 0 ((muHat-bNM n m)/cN n))
def estimateBeta (n m : ℕ) (kapHat : ℝ) : ℝ :=
  ((m : ℝ)^2/n-kapHat)/(n+2)
def empiricalC {n : ℕ} (x : EVec n) (ys : List (EVec n)) : RMat n :=
  fun i j => (ys.map (fun y => y i*y j*(inner ℝ x y)^2)).sum / ys.length
def estimateD {n : ℕ} (m : ℕ) (x : EVec n) (cHat : RMat n)
    (kapHat : ℝ) : RMat n :=
  kapHat⁻¹ • (cHat - estimateBeta n m kapHat • queryK m x)
def ambientBatch {n : ℕ} (O : RMat n) (zs : List (ZVec n)) : List (EVec n) :=
  zs.map (fun z => rotate O (liftZ z))
def labelSamples (n m : ℕ) (kap0 eta : ℝ) (N4 Nx : ℕ) : Prop :=
  2 ≤ N4 ∧ 0 < Nx ∧
  (N4 : ℝ) ≥ 1024*(m : ℝ)^10/(cN n^2*kap0^4)*Real.log (4/eta) ∧
  (Nx : ℝ) ≥ 512*(m : ℝ)^6/kap0^2*Real.log (4*n/eta)

/-- Exact finite recurrence (4.9), including the zero-dimensional boundary. -/
def shellCount : ℕ → ℕ → ℕ
  | 0, t => if t = 0 then 1 else 0
  | j+1, t => shellCount j t + 2 *
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt t), shellCount j (t-k*k)
def countQ4 (n m : ℕ) : ℕ :=
  2 * ∑ k ∈ Finset.Icc 1 (Nat.sqrt m), k^4*shellCount (n-1) (m-k*k)
def countQ22 (n m : ℕ) : ℤ :=
  ((m : ℤ)^2*shellCount n m - (n : ℤ)*countQ4 n m) / ((n : ℤ)*(n-1))
def countedParameters (n m : ℕ) : Option (ℚ × ℚ × ℚ) :=
  if shellCount n m = 0 then none else
    let alpha : ℚ := (countQ4 n m : ℚ)/shellCount n m
    let beta : ℚ := (countQ22 n m : ℚ)/shellCount n m
    some (alpha, beta, alpha-3*beta)
def flatRatio (n m : ℕ) : ℝ := (flat n m).card / (shell n m).card
def flatError (n m : ℕ) : ℝ :=
  4*(m : ℝ)^4/(31*((n : ℝ)-m+1)^3)
def shortRange (n m : ℕ) : Prop :=
  256 ≤ n ∧ 1 ≤ m ∧ (m : ℝ) ≤ (n : ℝ)^(3/4 : ℝ)

end
end ZLIPPadding.Padding.Supplement


