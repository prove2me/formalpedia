-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
-- name    : Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:13.605749+00:00
-- url     : https://prove2.me/theorems/19cb3824-8aba-46d4-93d8-ab0fea472b3b
-- title:
--   Rank Iff Right
-- statement:
--   Definitions and structural lemmas for Rank Iff Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise
noncomputable section
namespace PositivityTheory.ThKEst.W
section Rank
variable {k : Type} [Field k] {n d : ℕ}
end Rank
section Cut
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {n d : ℕ}
end Cut
end PositivityTheory.ThKEst.W
end


