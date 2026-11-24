-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageAreaSet
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageAreaSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:57.799681+00:00
-- url     : https://prove2.me/theorems/c4ce22c8-7463-4791-a328-cf029528d05f
-- title:
--   St Sheet Image Area Set
-- statement:
--   Definitions and structural lemmas for St Sheet Image Area Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetImageAreaSet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
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
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
def SheetImageAreaSet.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin d → ℂ)) (s : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen U → DifferentiableOn ℂ s U → (∀ y ∈ U, A *ᵥ s y = y) →
    ∀ B : Set (EuclideanSpace ℂ (Fin d)), MeasurableSet B → (∀ y ∈ B, WithLp.ofLp y ∈ U) →
      μH[((2 * d : ℕ) : ℝ)] ((fun y => WithLp.toLp 2 (s (WithLp.ofLp y))) '' B) =
        ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) ∂(μH[((2 * d : ℕ) : ℝ)])
end
end GroundTheory.Heights₂.Heights


