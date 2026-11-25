-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CupConnecting
-- name    : GroundTheory_TateCohomology_CupConnecting
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:21.473542+00:00
-- url     : https://prove2.me/theorems/34901973-d009-4095-9358-0557100f8f7c
-- title:
--   Cup Connecting
-- statement:
--   Definitions and structural lemmas for Cup Connecting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
namespace GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
section Whisker
variable {A A' B B' : Rep k G} {p q n : ℕ}
end Whisker
section Connecting
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
variable (B : Rep k G)
end Connecting
end GroundTheory.GroupCoh


