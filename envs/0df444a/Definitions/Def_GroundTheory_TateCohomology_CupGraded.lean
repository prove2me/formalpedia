-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CupGraded
-- name    : GroundTheory_TateCohomology_CupGraded
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:33:28.310819+00:00
-- url     : https://prove2.me/theorems/ea6c8a75-6703-4f0d-82e0-6e715d9430c9
-- title:
--   Cup Graded
-- statement:
--   Definitions and structural lemmas for Cup Graded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupGraded.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
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
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology
namespace GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}
end GroundTheory.GroupCoh


