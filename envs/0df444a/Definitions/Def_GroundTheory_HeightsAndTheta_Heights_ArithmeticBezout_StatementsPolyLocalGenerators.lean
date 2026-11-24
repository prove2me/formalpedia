-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:45.557332+00:00
-- url     : https://prove2.me/theorems/a61a0b21-c486-42cd-b973-4c0cafb8ee67
-- title:
--   Statements Poly Local Generators
-- statement:
--   Definitions and structural lemmas for Statements Poly Local Generators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsPolyLocalGenerators.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
def polyTangent {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ q ∈ S, ∑ j, eval p (pderiv j q) * v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hv hw ⊢
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by simp
  smul_mem' c v hv q hq := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum] at hv ⊢
    rw [hv q hq, mul_zero]
def PolyLocalGenerators.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = m →
    ∀ p : Fin n → ℂ, (∀ q ∈ J, eval p q = 0) →
      finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) = m →
      ∃ (q : Fin (n - m) → MvPolynomial (Fin n) ℂ) (g : MvPolynomial (Fin n) ℂ),
        (∀ i, q i ∈ J) ∧ eval p g ≠ 0 ∧ finrank ℂ (polyTangent (Set.range q) p) = m ∧
        ∀ r ∈ J, g * r ∈ Ideal.span (Set.range q)
end
end GroundTheory.Heights₂.Heights


