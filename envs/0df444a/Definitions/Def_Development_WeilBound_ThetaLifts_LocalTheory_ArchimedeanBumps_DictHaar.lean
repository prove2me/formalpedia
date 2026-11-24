-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:27.23778+00:00
-- url     : https://prove2.me/theorems/6e72f932-0564-4195-887b-0497181ef83d
-- title:
--   Dict Haar
-- statement:
--   Definitions and structural lemmas for Dict Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean

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
namespace PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]
def dens (c : ι → ℂ) : ℝ≥0 := ⟨(∏ w, ‖c w‖ ^ 2)⁻¹, by positivity⟩
end PositivityTheory.ThKG.Loc.Bump
end


