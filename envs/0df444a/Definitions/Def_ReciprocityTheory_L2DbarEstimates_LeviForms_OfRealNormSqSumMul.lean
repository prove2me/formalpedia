-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:56.438716+00:00
-- url     : https://prove2.me/theorems/b0bc7dd4-8671-4251-a222-213617a2ae83
-- title:
--   Of Real Norm Sq Sum Mul
-- statement:
--   Definitions and structural lemmas for Of Real Norm Sq Sum Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
namespace ReciprocityTheory.L2DbarEstimates
def LeviChainStatement : Prop :=
  ∀ (n : ℕ) (k : ℝ → ℝ) (v : V n → ℝ) (x : V n) (ξ : Fin n → ℂ),
    ContDiffAt ℝ 2 v x → ContDiffAt ℝ 2 k (v x) →
    leviV n (fun y => ((k (v y) : ℝ) : ℂ)) x ξ =
      ((deriv k (v x) : ℝ) : ℂ) * leviV n (fun y => ((v y : ℝ) : ℂ)) x ξ +
      ((deriv (deriv k) (v x) : ℝ) : ℂ) *
        ((Complex.normSq (∑ j, wd n j (fun y => ((v y : ℝ) : ℂ)) x * ξ j) : ℝ) : ℂ)
def LSEVStatement : Prop :=
  ∀ (n m : ℕ) (U : Set (V n)) (u : Fin m → V n → ℝ), IsOpen U →
    (∀ i, (∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ U ∧ LeviNonnegOn n φ U ∧
              ∀ y ∈ U, u i y = Real.exp (φ y)) ∨
          (∃ g : V n → ℂ, ContDiffOn ℂ 2 g U ∧ ∀ y ∈ U, u i y = Complex.normSq (g y))) →
    (∀ y ∈ U, 0 < ∑ i, u i y) →
    LeviNonnegOn n (fun y => Real.log (∑ i, u i y)) U
def LogPshAt (n : ℕ) (u : V n → ℝ) (x : V n) : Prop :=
  0 ≤ u x ∧ ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (u y : ℂ)) x ξ).re ∧
    Complex.normSq (∑ j, wd n j (fun y => (u y : ℂ)) x * ξ j) ≤
      u x * (leviV n (fun y => (u y : ℂ)) x ξ).re
variable {n : ℕ}
end ReciprocityTheory.L2DbarEstimates


