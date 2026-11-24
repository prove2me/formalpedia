-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:39.627797+00:00
-- url     : https://prove2.me/theorems/c530c76b-e62e-48aa-b741-7ef30d87a17b
-- title:
--   Statements Area Formula Inj
-- statement:
--   Definitions and structural lemmas for Statements Area Formula Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsAreaFormulaInj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal
def AreaFormulaInj.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F) (g : F → ℝ≥0∞),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A → Measurable g →
        ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) =
          ∫⁻ x in A, g (f x) * ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
            ∂(μH[(k : ℝ)])
end GroundTheory.Heights₂.Heights


