-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- name    : GroundTheory_TateCohomology_AugmentationSES
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:24:55.323234+00:00
-- url     : https://prove2.me/theorems/4456c582-e72c-4b06-9aa5-00fa36a81013
-- title:
--   Augmentation SES
-- statement:
--   Definitions and structural lemmas for Augmentation SES, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_retract
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
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
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
section Linear
end Linear
variable (k G)
noncomputable def augmentation : (Rep.leftRegular k G).V →ₗ[k] k :=
  Finsupp.linearCombination k (fun _ : G => (1 : k)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
variable {k G}
@[simp]
theorem augmentation_single (g : G) (r : k) :
    augmentation k G (MonoidAlgebra.single g r) = r := by
  simp [augmentation]
theorem augmentation_ρ (g : G) (x : (Rep.leftRegular k G).V) :
    augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single h r =>
    simp only [Representation.ofMulAction_single, smul_eq_mul]
    rw [augmentation_single, augmentation_single]
variable (k G)
theorem ker_augmentation_le_comap (g : G) :
    LinearMap.ker (augmentation k G) ≤
      (LinearMap.ker (augmentation k G)).comap ((Rep.leftRegular k G).ρ g) := by
  intro x hx
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  rw [augmentation_ρ, hx]
noncomputable abbrev augIdeal : Rep.{u} k G :=
  Rep.subrepresentation (Rep.leftRegular k G) (LinearMap.ker (augmentation k G))
    (ker_augmentation_le_comap k G)
noncomputable abbrev augIdealι : augIdeal k G ⟶ Rep.leftRegular k G :=
  Rep.subtype _ _ _
noncomputable def augIdealRetract : (Rep.leftRegular k G).V →ₗ[k] (augIdeal k G).V :=
  LinearMap.codRestrict (LinearMap.ker (augmentation k G))
    (LinearMap.id - MonoidAlgebra.lsingle 1 ∘ₗ augmentation k G) fun x => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        map_sub]
      erw [MonoidAlgebra.lsingle_apply, augmentation_single, sub_self]
variable {k G}
theorem augIdealRetract_ι (y : augIdeal k G) : augIdealRetract k G ((augIdealι k G).hom y) = y := by
  apply Subtype.ext
  have hy : augmentation k G y.1 = 0 := y.2
  change y.1 - MonoidAlgebra.single 1 (augmentation k G y.1) = y.1
  rw [hy, MonoidAlgebra.single_zero, sub_zero]
instance : Module.Flat k (augIdeal k G).V :=
  Module.Flat.of_retract (augIdealι k G).hom.toLinearMap (augIdealRetract k G)
    (LinearMap.ext fun y => augIdealRetract_ι y)
noncomputable def augX (X : Rep.{u} k G) : Rep.leftRegular k G ⊗ X ⟶ X :=
  Rep.ofHom ⟨TensorProduct.lid k X ∘ₗ TensorProduct.map (augmentation k G) LinearMap.id,
    fun g => TensorProduct.ext' fun x a => by
      change TensorProduct.lid k X (TensorProduct.map (augmentation k G) LinearMap.id
        ((Rep.leftRegular k G).ρ g x ⊗ₜ X.ρ g a)) = X.ρ g (TensorProduct.lid k X
          (TensorProduct.map (augmentation k G) LinearMap.id (x ⊗ₜ a)))
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul, map_smul]
      exact congrArg (fun r => r • X.ρ g a) (augmentation_ρ g x)⟩
theorem augX_tmul (X : Rep.{u} k G) (x : (Rep.leftRegular k G).V) (a : X) :
    (augX X).hom (x ⊗ₜ[k] a : (Rep.leftRegular k G ⊗ X : Rep k G)) = augmentation k G x • a := by
  simp [augX]
section Tensor
variable {A B : Rep.{u} k G}
section Flat
variable {W P₁ P₂ Q₁ Q₂ : Type u} [AddCommGroup W] [Module k W] [Module.Flat k W]
  [AddCommGroup P₁] [Module k P₁] [AddCommGroup P₂] [Module k P₂]
  [AddCommGroup Q₁] [Module k Q₁] [AddCommGroup Q₂] [Module k Q₂]
end Flat
section FlatRep
variable (V : Rep.{u} k G) [Module.Flat k V.V] {X₁ X₂ : Rep.{u} k G} (f : X₁ ⟶ X₂)
end FlatRep
end Tensor
section AugSES
theorem augSES_zero (X : Rep.{u} k G) : augIdealι k G ▷ X ≫ augX X = 0 := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul y a =>
    change (augX X).hom ((augIdealι k G).hom y ⊗ₜ[k] a) = 0
    rw [augX_tmul]
    have hy : augmentation k G y.1 = 0 := y.2
    exact (congrArg (· • a) hy).trans (zero_smul k a)
  | add s t hs ht => rw [map_add, map_add, hs, ht]
theorem augX_naturality {X Y : Rep.{u} k G} (f : X ⟶ Y) :
    Rep.leftRegular k G ◁ f ≫ augX Y = augX X ≫ f := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    change (augX Y).hom (x ⊗ₜ[k] f.hom a) = f.hom ((augX X).hom (x ⊗ₜ[k] a))
    rw [augX_tmul, augX_tmul, map_smul]
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht]
variable (k G) in

noncomputable def augSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj X := ShortComplex.mk (augIdealι k G ▷ X) (augX X) (augSES_zero X)
  map f :=
    { τ₁ := augIdeal k G ◁ f
      τ₂ := Rep.leftRegular k G ◁ f
      τ₃ := f
      comm₁₂ := whisker_exchange _ _
      comm₂₃ := augX_naturality f }
  map_id _ := ShortComplex.hom_ext _ _ (MonoidalCategory.whiskerLeft_id _ _)
    (MonoidalCategory.whiskerLeft_id _ _) rfl
  map_comp _ _ := ShortComplex.hom_ext _ _ (MonoidalCategory.whiskerLeft_comp _ _ _)
    (MonoidalCategory.whiskerLeft_comp _ _ _) rfl
variable [Fintype G]
end AugSES
end GroundTheory.GroupCoh


