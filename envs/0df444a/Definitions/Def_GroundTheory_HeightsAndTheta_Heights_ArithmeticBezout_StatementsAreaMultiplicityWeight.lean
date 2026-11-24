-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:52.70981+00:00
-- url     : https://prove2.me/theorems/d86dd837-6e7b-4990-a98f-05e1f1e852e7
-- title:
--   Statements Area Multiplicity Weight
-- statement:
--   Definitions and structural lemmas for Statements Area Multiplicity Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsAreaMultiplicityWeight.lean

import Mathlib
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
open MeasureTheory
open scoped ENNReal
noncomputable section
def AreaMultiplicityWeight.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E)
    (f' : E → E →L[ℝ] E), MeasurableSet A → (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      AEMeasurable (fun y => (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞)) μ ∧
        ∀ g : E → ℝ≥0∞, Measurable g →
          ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ =
            ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ
end
end GroundTheory.Heights₂.Heights


