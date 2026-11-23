-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
-- name    : GroundTheory_TateCohomology_PGroupFixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:20.532505+00:00
-- url     : https://prove2.me/theorems/7f793ff4-c387-4e50-b11f-95ec899d6865
-- title:
--   PGroup Fixed
-- statement:
--   Definitions and structural lemmas for PGroup Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFixed.lean

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
namespace GroundTheory.GroupCoh
open Representation
section Fixed
variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]
end Fixed
section Nakayama
variable {k G V : Type*} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]
end Nakayama
end GroundTheory.GroupCoh


