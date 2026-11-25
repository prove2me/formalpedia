-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
-- name    : GroundTheory_TateCohomology_PGroupCohTrivialInt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:08.686438+00:00
-- url     : https://prove2.me/theorems/4e244255-63d7-4447-988e-e717d0cc0485
-- title:
--   PGroup Coh Trivial Int
-- statement:
--   Definitions and structural lemmas for PGroup Coh Trivial Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupHomology
universe u
section H1
variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
variable {A : Rep.{u} k G} {B : Rep.{u} k' G}
end H1
section Torsion
variable {k G : Type u} [CommRing k] [Group G]
end Torsion
section ZMod
variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
noncomputable def zmodRep (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) : Rep (ZMod p) G :=
  letI : Module (ZMod p) M := AddCommGroup.zmodModule hM
  Rep.of (X := M)
    { toFun := fun g => AddMonoidHom.toZModLinearMap p (M.ρ g).toAddMonoidHom
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }
variable [Fintype G]
end ZMod
end GroundTheory.GroupCoh


