-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeightedAreaFormula
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeightedAreaFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:29.343851+00:00
-- url     : https://prove2.me/theorems/eae75bea-d493-4385-8115-9eb56fbdcff1
-- title:
--   St Weighted Area Formula
-- statement:
--   Definitions and structural lemmas for St Weighted Area Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StWeightedAreaFormula.lean

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
noncomputable section
def WeightedAreaFormula.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E) (H : E → ℝ),
    IsOpen A → DifferentiableOn ℝ f A → (∀ y, {x | x ∈ A ∧ f x = y}.Finite) →
    IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) A μ →
      Integrable (fun y => ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) μ ∧
        ∫ y, (∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) ∂μ = ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ
end
end GroundTheory.Heights₂.Heights


