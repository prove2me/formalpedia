-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
-- name    : GroundTheory_TateCohomology_CohTrivialPGroup
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:33:10.52451+00:00
-- url     : https://prove2.me/theorems/117c1540-e615-4d0c-9cd5-22c2adcc7995
-- title:
--   Coh Trivial PGroup
-- statement:
--   Definitions and structural lemmas for Coh Trivial PGroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialPGroup.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
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
open CategoryTheory Limits Rep
section Helpers
universe u
variable {k H : Type u} [CommRing k] [Group H] {A B : Rep.{u} k H}
end Helpers
variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
end GroundTheory.GroupCoh


