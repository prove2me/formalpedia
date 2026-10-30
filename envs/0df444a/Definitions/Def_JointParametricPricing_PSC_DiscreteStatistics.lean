-- Prove2me | Definitions.Def_JointParametricPricing_PSC_DiscreteStatistics
-- name    : JointParametricPricing_PSC_DiscreteStatistics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:46:42.180198+00:00
-- url     : https://prove2.me/theorems/645a1291-5ea2-422e-baf8-3865c827da91
-- title:
--   Discrete probability families, Fisher regularity, and IID MLE tails
-- statement:
--   A discrete family on an arbitrary outcome type $Y$ has a nonempty compact Euclidean parameter set and nonnegative real masses summing to one. The sample space is not restricted to be finite. Its IID likelihood is the finite product of single-observation masses. MLE selectors maximize this likelihood on the parameter set. Regularity for Theorem EC.1 includes positive parameter dimension, $r>q$, convexity of the parameter set, identifiability, a uniform finite $r$-moment of the Euclidean log score, differentiability of square-root masses within the parameter set (including its boundary), and symmetric positive-definite Fisher information. The log mass has a genuine ambient derivative and the displayed second coordinate derivatives only on positive statistical support; expected negative log-Hessian entries are required to be summable so that they are actual finite expectations. The uniform score-moment bound is an extended-nonnegative sum bounded by a finite real number. The tail probability is the extended-nonnegative sum of IID sample masses over the estimation-error event. No positive-mass requirement is imposed on impossible outcomes.
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); Theorem EC.1, printed ec1 / PDF 25

import Definitions.Def_JointParametricPricing_PSC_Optimization

open scoped BigOperators ENNReal
noncomputable section

namespace JointParametricPricing.PSC

/-- General discrete probability family; the outcome type need not be finite. -/
structure DiscreteFamily (q : ℕ) (Y : Type*) where
  Θ : Set (Vec q)
  nonempty : Θ.Nonempty
  compact : IsCompact Θ
  mass : Vec q → Y → ℝ
  mass_nonneg : ∀ θ ∈ Θ, ∀ y, 0 ≤ mass θ y
  mass_total : ∀ θ ∈ Θ, HasSum (mass θ) 1

namespace DiscreteFamily
variable {q : ℕ} {Y : Type*}
def score (F : DiscreteFamily q Y) (θ : Vec q) (y : Y) : Vec q :=
  WithLp.toLp 2 (fun i => coordDeriv (fun z => Real.log (F.mass z y)) θ i)

def fisher (F : DiscreteFamily q Y) (θ : Vec q) (i j : Fin q) : ℝ :=
  ∑' y, F.mass θ y * (-secondPartial (fun z => Real.log (F.mass z y)) θ i j)

/-- The four regularity conditions printed in Theorem EC.1, including the meaning of
finite Fisher expectations and derivatives on positive statistical support. -/
def Regular (F : DiscreteFamily q Y) (r : ℝ) : Prop :=
  0 < q ∧ (q : ℝ) < r ∧ Convex ℝ F.Θ ∧
  (∀ θ ∈ F.Θ, ∀ θ' ∈ F.Θ, θ ≠ θ' → F.mass θ ≠ F.mass θ') ∧
  (∃ γ : ℝ, 0 ≤ γ ∧ ∀ θ ∈ F.Θ,
    (∑' y, ENNReal.ofReal (F.mass θ y * ‖F.score θ y‖ ^ r)) ≤ ENNReal.ofReal γ) ∧
  (∀ y θ, θ ∈ F.Θ →
    DifferentiableWithinAt ℝ (fun z => Real.sqrt (F.mass z y)) F.Θ θ) ∧
  (∀ θ ∈ F.Θ, ∀ y, 0 < F.mass θ y →
    DifferentiableAt ℝ (fun z => Real.log (F.mass z y)) θ ∧
    ∀ i j, DifferentiableAt ℝ (fun t : ℝ => coordDeriv (fun z => Real.log (F.mass z y))
      (θ + t • coordinate i) j) 0) ∧
  (∀ θ ∈ F.Θ, ∀ i j, Summable (fun y =>
    F.mass θ y * (-secondPartial (fun z => Real.log (F.mass z y)) θ i j))) ∧
  (∀ θ ∈ F.Θ, (∀ i j, F.fisher θ i j = F.fisher θ j i) ∧
    ∀ z : Vec q, z ≠ 0 → 0 < ∑ i, ∑ j, z i * F.fisher θ i j * z j)

def likelihood (F : DiscreteFamily q Y) (t : ℕ) (y : Fin t → Y) (θ : Vec q) : ℝ :=
  ∏ s, F.mass θ (y s)

structure MLESelector (F : DiscreteFamily q Y) where
  choose : (t : ℕ) → (Fin t → Y) → F.Θ
  maximizes : ∀ t y z, z ∈ F.Θ → F.likelihood t y z ≤ F.likelihood t y (choose t y)

/-- Probability under the IID product law, as a nonnegative sum. -/
def tail (F : DiscreteFamily q Y) (S : F.MLESelector) (t : ℕ) (θ : F.Θ) (δ : ℝ) : ℝ≥0∞ :=
  ∑' y : Fin t → Y, if δ < ‖(S.choose t y : Vec q) - θ‖
    then ENNReal.ofReal (F.likelihood t y θ) else 0
end DiscreteFamily
end JointParametricPricing.PSC


