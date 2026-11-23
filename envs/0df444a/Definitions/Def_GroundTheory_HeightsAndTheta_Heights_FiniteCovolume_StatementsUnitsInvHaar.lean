-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnitsInvHaar
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnitsInvHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:49.742122+00:00
-- url     : https://prove2.me/theorems/00eb267e-8c3e-460e-ad97-59b18b4b86f9
-- title:
--   Statements Units Inv Haar
-- statement:
--   Definitions and structural lemmas for Statements Units Inv Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsUnitsInvHaar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
instance secondCountableTopology_units_complex : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
instance borelSpace_units_complex : BorelSpace ℂˣ where
  measurable_eq := by
    rw [congrArg (@borel ℂˣ) Units.isOpenEmbedding_val.isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := ℂ)]
    rfl
def UnitsInvHaar.Statement (I : Type*) [Fintype I] : Prop :=
  ∀ (ρ : Measure (I → ℂˣ)) [ρ.IsHaarMeasure], ∃ c : ℝ≥0, c ≠ 0 ∧
    ∀ (k : ℕ) (g : (I → ℂˣ) → ℝ≥0∞) (g' : (I → ℂ) → ℝ≥0∞), Measurable g →
      (∀ (b : I → ℂ) (hb : ∀ i, b i ≠ 0), g' b = g fun i => (Units.mk0 (b i) (hb i))⁻¹) →
      ∫⁻ a, (∏ i, ‖(a i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g a ∂ρ =
        c * ∫⁻ b, (∏ i, ‖b i‖ₑ ^ (2 * k)) * g' b
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


