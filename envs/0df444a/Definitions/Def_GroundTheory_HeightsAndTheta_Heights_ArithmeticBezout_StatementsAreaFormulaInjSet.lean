-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInjSet
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInjSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:56.440251+00:00
-- url     : https://prove2.me/theorems/698d0451-0f76-47ea-a01b-fafae6850ce2
-- title:
--   Statements Area Formula Inj Set
-- statement:
--   Definitions and structural lemmas for Statements Area Formula Inj Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsAreaFormulaInjSet.lean

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
def AreaFormulaInjSet.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A →
        μH[(k : ℝ)] (f '' A) =
          ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])
end GroundTheory.Heights₂.Heights


