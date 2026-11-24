-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:06.335931+00:00
-- url     : https://prove2.me/theorems/d3b4cdd6-d599-4572-80eb-4b56124700c8
-- title:
--   Statements Area Formula Local
-- statement:
--   Definitions and structural lemmas for Statements Area Formula Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsAreaFormulaLocal.lean

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
def AreaFormulaLocal.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U : Set E) (f : E → F) (x₀ : E),
      IsOpen U → ContDiffOn ℝ 1 f U → x₀ ∈ U → Function.Injective (fderiv ℝ f x₀) →
        ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
          μH[(k : ℝ)] (f '' B) =
            ∫⁻ x in B, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])
end GroundTheory.Heights₂.Heights


