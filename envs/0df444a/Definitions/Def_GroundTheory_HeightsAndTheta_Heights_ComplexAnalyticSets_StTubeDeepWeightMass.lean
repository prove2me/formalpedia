-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:33.46772+00:00
-- url     : https://prove2.me/theorems/e05e7c7a-3f20-4acf-bc7e-f11b8ce2d5d4
-- title:
--   St Tube Deep Weight Mass
-- statement:
--   Definitions and structural lemmas for St Tube Deep Weight Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTubeDeepWeightMass.lean

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
def poincareDeepWeight (z : ℂ) : ℝ :=
  if Real.log (‖z‖ ^ 2) < -Real.exp 1 then (‖z‖ ^ 2 * Real.log (‖z‖ ^ 2) ^ 2)⁻¹ else 0
def TubeDeepWeightMass.Statement : Prop :=
  ∀ (d : ℕ) (R : ℝ),
    ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (poincareDeepWeight (z 0)) < ⊤
end
end GroundTheory.Heights₂.Heights


