-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:24.848799+00:00
-- url     : https://prove2.me/theorems/f903de59-f0b6-4c88-8c5a-33fae16449a3
-- title:
--   St Critical Image Null
-- statement:
--   Definitions and structural lemmas for St Critical Image Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCriticalImageNull.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory
noncomputable section
def CriticalImageNull.Statement : Prop :=
  ∀ (d n : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → Fin n → ℂ), IsOpen U →
    DifferentiableOn ℂ f U →
      μH[((2 * d : ℕ) : ℝ)] (f '' {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)}) = 0
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


