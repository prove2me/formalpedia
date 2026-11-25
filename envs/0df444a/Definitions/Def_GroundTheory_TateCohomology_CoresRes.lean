-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CoresRes
-- name    : GroundTheory_TateCohomology_CoresRes
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:05.744475+00:00
-- url     : https://prove2.me/theorems/4955b20f-92de-5f35-bbf8-faf44ac9d0c3
-- title:
--   Cores Res
-- statement:
--   Definitions and structural lemmas for Cores Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
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
universe u
variable {k G : Type u} [CommRing k] [Group G]
section Additive
variable [Fintype G]
instance tateCohomologyFunctor_additive (n : ℤ) :
    (tateCohomologyFunctor (R := k) (G := G) n).Additive := by
  unfold tateCohomologyFunctor
  infer_instance
end Additive
section Rep
variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
end Rep
section Tate
variable [Fintype G] (S : Subgroup G) [Fintype S]
end Tate
end GroundTheory.GroupCoh


