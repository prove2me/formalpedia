-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
-- name    : GroundTheory_AutomorphicForms_ContragredientTranspose
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:12.1808+00:00
-- url     : https://prove2.me/theorems/943bb4fc-5fcd-5da5-a9eb-80cd3da41476
-- title:
--   Contragredient Transpose
-- statement:
--   Definitions and structural lemmas for Contragredient Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic.ContragredientTranspose
open MeasureTheory Measure GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
def subrepCompOrderIso {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (α : G ≃* G) :
    Subrepresentation (ρ.comp α.toMonoidHom) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    have := W.apply_mem_toSubmodule (α.symm g) hv
    simpa using this⟩
  invFun W := ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (α g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
noncomputable def longestWeyl : GL (Fin n) F := permGL F (Fin.revPerm (n := n))
end GroundTheory.Automorphic.ContragredientTranspose


