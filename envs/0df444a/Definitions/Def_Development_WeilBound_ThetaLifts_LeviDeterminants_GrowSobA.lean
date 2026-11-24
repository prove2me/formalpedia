-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:45.15835+00:00
-- url     : https://prove2.me/theorems/ccb9166c-d8a6-423c-a84c-f6c4e84d3f31
-- title:
--   Grow Sob A
-- statement:
--   Definitions and structural lemmas for Grow Sob A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory
variable {X W : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
def sumSq (dd : W → (X → ℂ) → X → ℂ) (L : List (List W)) (Θ : X → ℂ) (y : X) : ℝ≥0∞ :=
  (L.map fun l => ‖l.foldr dd Θ y‖ₑ ^ 2).sum
end PositivityTheory.ThKF0.Grow


