-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_PullbackExtension
-- name    : GroundTheory_TateCohomology_PullbackExtension
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:48:48.12588+00:00
-- url     : https://prove2.me/theorems/3cd70d30-dc77-5c88-88f1-00a42fc5f89f
-- title:
--   Pullback Extension
-- statement:
--   Definitions and structural lemmas for Pullback Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
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
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)
def pullbackSubmodule : Submodule k (S.X₂.V × Y.V) :=
  LinearMap.ker (S.g.hom.toLinearMap ∘ₗ LinearMap.fst k S.X₂.V Y.V -
    β.hom.toLinearMap ∘ₗ LinearMap.snd k S.X₂.V Y.V)
variable {S β} in
theorem mem_pullbackSubmodule {p : S.X₂.V × Y.V} :
    p ∈ pullbackSubmodule S β ↔ S.g.hom p.1 = β.hom p.2 := by
  simp [pullbackSubmodule, sub_eq_zero]
theorem pullbackSubmodule_le_comap (g : G) :
    pullbackSubmodule S β ≤ (pullbackSubmodule S β).comap ((S.X₂.ρ.prod Y.ρ) g) := by
  intro p hp
  rw [Submodule.mem_comap, mem_pullbackSubmodule]
  rw [mem_pullbackSubmodule] at hp
  simp [Rep.hom_comm_apply, hp]
noncomputable abbrev pullbackRep : Rep.{u} k G :=
  Rep.subrepresentation (Rep.of (S.X₂.ρ.prod Y.ρ)) (pullbackSubmodule S β)
    (pullbackSubmodule_le_comap S β)
noncomputable def pullbackFst : pullbackRep S β ⟶ S.X₂ :=
  Rep.ofHom ⟨LinearMap.fst k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩
noncomputable def pullbackSnd : pullbackRep S β ⟶ Y :=
  Rep.ofHom ⟨LinearMap.snd k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩
@[simp] theorem pullbackFst_apply (p : pullbackRep S β) : (pullbackFst S β).hom p = p.1.1 := rfl
@[simp] theorem pullbackSnd_apply (p : pullbackRep S β) : (pullbackSnd S β).hom p = p.1.2 := rfl
theorem g_apply_f_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by
  change (S.f ≫ S.g).hom x = 0
  rw [S.zero]
  rfl
noncomputable def pullbackιLinear : S.X₁.V →ₗ[k] pullbackSubmodule S β :=
  LinearMap.codRestrict (pullbackSubmodule S β)
    (LinearMap.prod S.f.hom.toLinearMap 0) fun x => by
      rw [mem_pullbackSubmodule]
      simp [g_apply_f_apply]
noncomputable def pullbackι : S.X₁ ⟶ pullbackRep S β :=
  Rep.ofHom ⟨pullbackιLinear S β, fun g => by
    refine LinearMap.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
    · simp [pullbackιLinear, Rep.hom_comm_apply]
    · simp [pullbackιLinear]⟩
@[simp] theorem pullbackι_apply_fst (x : S.X₁) : ((pullbackι S β).hom x).1.1 = S.f.hom x := rfl
@[simp] theorem pullbackι_apply_snd (x : S.X₁) : ((pullbackι S β).hom x).1.2 = 0 := rfl
theorem pullbackι_pullbackSnd : pullbackι S β ≫ pullbackSnd S β = 0 := by
  ext x
  rfl
noncomputable def pullbackSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (pullbackι S β) (pullbackSnd S β) (pullbackι_pullbackSnd S β)
@[simp] theorem pullbackSES_X₁ : (pullbackSES S β).X₁ = S.X₁ := rfl
@[simp] theorem pullbackSES_X₂ : (pullbackSES S β).X₂ = pullbackRep S β := rfl
@[simp] theorem pullbackSES_X₃ : (pullbackSES S β).X₃ = Y := rfl
@[simp] theorem pullbackSES_f : (pullbackSES S β).f = pullbackι S β := rfl
@[simp] theorem pullbackSES_g : (pullbackSES S β).g = pullbackSnd S β := rfl
noncomputable def pullbackSESHom : pullbackSES S β ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := pullbackFst S β
  τ₃ := β
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2
end GroundTheory.GroupCoh


