-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
-- name    : GroundTheory_TateCohomology_PGroupCohTrivial
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:15.8001+00:00
-- url     : https://prove2.me/theorems/64aaee76-dadd-4c91-95a2-7d30218eb280
-- title:
--   PGroup Coh Trivial
-- statement:
--   Definitions and structural lemmas for PGroup Coh Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivial.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
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
open scoped MonoidAlgebra
universe u
section Shift
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
end Shift
section Field
variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
end Field
end GroundTheory.GroupCoh


