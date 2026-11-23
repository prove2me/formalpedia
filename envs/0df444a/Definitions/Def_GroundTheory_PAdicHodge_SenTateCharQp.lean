-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_SenTateCharQp
-- name    : GroundTheory_PAdicHodge_SenTateCharQp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:34.491875+00:00
-- url     : https://prove2.me/theorems/52950eac-b50d-47f7-a5c5-794d4d732682
-- title:
--   Sen Tate Char Qp
-- statement:
--   Definitions and structural lemmas for Sen Tate Char Qp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharQp.lean

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
noncomputable section
namespace GroundTheory.PAdicHodge
namespace SenTateChar
variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
end SenTateChar
end GroundTheory.PAdicHodge


