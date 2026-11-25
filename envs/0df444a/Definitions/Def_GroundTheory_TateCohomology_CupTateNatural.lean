-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CupTateNatural
-- name    : GroundTheory_TateCohomology_CupTateNatural
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:36:38.419797+00:00
-- url     : https://prove2.me/theorems/26075bf1-317b-5f33-a1e4-46395fc7d1f3
-- title:
--   Cup Tate Natural
-- statement:
--   Definitions and structural lemmas for Cup Tate Natural, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateNatural.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
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
open CategoryTheory MonoidalCategory groupCohomology
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
section Naturality
omit [Fintype G] in

theorem augTensorRight_comm₁₂ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((augIdeal k G ◁ φ) ⊗ₘ ψ) ≫ ((augIdealι k G ▷ A') ▷ B') =
      ((augIdealι k G ▷ A) ▷ B) ≫ ((Rep.leftRegular k G ◁ φ) ⊗ₘ ψ) := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul t b =>
    induction t using TensorProduct.induction_on with
    | zero => simp [TensorProduct.zero_tmul]
    | tmul i a => rfl
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add] at hs ht ⊢; rw [hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
omit [Fintype G] in

theorem augTensorRight_comm₂₃ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((Rep.leftRegular k G ◁ φ) ⊗ₘ ψ) ≫ (augX A' ▷ B') = (augX A ▷ B) ≫ (φ ⊗ₘ ψ) := by
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    augX_naturality, Category.comp_id, Category.id_comp]
omit [Fintype G] in

theorem augTensorLeft_comm₁₂ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    (φ ⊗ₘ (augIdeal k G ◁ ψ)) ≫ (A' ◁ (augIdealι k G ▷ B')) =
      (A ◁ (augIdealι k G ▷ B)) ≫ (φ ⊗ₘ (Rep.leftRegular k G ◁ ψ)) := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    induction t using TensorProduct.induction_on with
    | zero => simp [TensorProduct.tmul_zero]
    | tmul i b => rfl
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add] at hs ht ⊢; rw [hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
omit [Fintype G] in

theorem augTensorLeft_comm₂₃ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    (φ ⊗ₘ (Rep.leftRegular k G ◁ ψ)) ≫ (A' ◁ augX B') = (A ◁ augX B) ≫ (φ ⊗ₘ ψ) := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    induction t using TensorProduct.induction_on with
    | zero => simp [TensorProduct.tmul_zero]
    | tmul x b =>
      change φ.hom a ⊗ₜ[k] (augX B').hom (x ⊗ₜ[k] ψ.hom b) =
        φ.hom a ⊗ₜ[k] ψ.hom ((augX B).hom (x ⊗ₜ[k] b))
      rw [augX_tmul, augX_tmul, map_smul]
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add] at hs ht ⊢; rw [hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
noncomputable def augTensorRightMap {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((augSES k G).obj A).map (tensorRight B) ⟶ ((augSES k G).obj A').map (tensorRight B') where
  τ₁ := (augIdeal k G ◁ φ) ⊗ₘ ψ
  τ₂ := (Rep.leftRegular k G ◁ φ) ⊗ₘ ψ
  τ₃ := φ ⊗ₘ ψ
  comm₁₂ := augTensorRight_comm₁₂ φ ψ
  comm₂₃ := augTensorRight_comm₂₃ φ ψ
noncomputable def augTensorLeftMap {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((augSES k G).obj B).map (tensorLeft A) ⟶ ((augSES k G).obj B').map (tensorLeft A') where
  τ₁ := φ ⊗ₘ (augIdeal k G ◁ ψ)
  τ₂ := φ ⊗ₘ (Rep.leftRegular k G ◁ ψ)
  τ₃ := φ ⊗ₘ ψ
  comm₁₂ := augTensorLeft_comm₁₂ φ ψ
  comm₂₃ := augTensorLeft_comm₂₃ φ ψ
end Naturality
end GroundTheory.GroupCoh


