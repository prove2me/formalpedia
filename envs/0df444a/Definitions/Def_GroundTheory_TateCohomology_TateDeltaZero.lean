-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateDeltaZero
-- name    : GroundTheory_TateCohomology_TateDeltaZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:15.973335+00:00
-- url     : https://prove2.me/theorems/00205615-baf6-4c08-b130-8c277710a2e9
-- title:
--   Tate Delta Zero
-- statement:
--   Definitions and structural lemmas for Tate Delta Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateDeltaZero.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)
end GroundTheory.GroupCoh


