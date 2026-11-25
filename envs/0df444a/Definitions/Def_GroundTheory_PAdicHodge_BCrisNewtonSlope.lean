-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonSlope
-- name    : GroundTheory_PAdicHodge_BCrisNewtonSlope
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:46.834181+00:00
-- url     : https://prove2.me/theorems/d0e10e61-b755-503a-bffd-eb02203a1e7c
-- title:
--   BCris Newton Slope
-- statement:
--   Definitions and structural lemmas for BCris Newton Slope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonSlope.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
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
namespace GroundTheory.PAdicHodge
namespace WittTilt
open _root_.WittVector Laurent Filter Topology
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝔸" => Localization.Away (p : AInf K p)
end WittTilt
end GroundTheory.PAdicHodge


