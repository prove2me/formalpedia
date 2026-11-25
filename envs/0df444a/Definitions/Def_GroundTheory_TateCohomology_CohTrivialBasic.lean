-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
-- name    : GroundTheory_TateCohomology_CohTrivialBasic
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:10:47.989881+00:00
-- url     : https://prove2.me/theorems/7cc6060a-1567-4add-be16-562650bf158f
-- title:
--   Coh Trivial Basic
-- statement:
--   Definitions and structural lemmas for Coh Trivial Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
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
section Def
variable {k G : Type u} [CommRing k] [Group G]
def CohTrivial (A : Rep.{u} k G) : Prop :=
  ∀ (S : Subgroup G) [Fintype S], TateAcyclic (res S.subtype A)
end Def
section Norm
variable {k G : Type u} [CommRing k] [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable [Fintype G]
end Norm
section ShortExact
variable {k G : Type u} [CommRing k] [Group G]
end ShortExact
section Rat
variable {G : Type} [Group G]
end Rat
end GroundTheory.GroupCoh


