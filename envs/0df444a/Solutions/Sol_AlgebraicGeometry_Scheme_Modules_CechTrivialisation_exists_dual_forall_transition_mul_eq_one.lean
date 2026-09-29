-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_dual_forall_transition_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1bb4c011-de3a-5a0d-8b33-ce4a35a6f681

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

set_option backward.isDefEq.respectTransparency false

namespace TT

p2m_open "AlgebraicGeometry.Scheme.Modules"

theorem leftUnitor_conj_tensorIso {C : Type*} [Category C] [MonoidalCategory C] (e e' : 𝟙_ C ≅ 𝟙_ C) :
    (λ_ (𝟙_ C)).symm ≪≫ (e ⊗ᵢ e') ≪≫ λ_ (𝟙_ C) = e ≪≫ e' := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerRight_id,
    MonoidalCategory.id_whiskerLeft, unitors_equal, unitors_inv_equal, Category.assoc, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, Category.comp_id, Category.id_comp]

variable {Y : Scheme.{u}}

theorem unitAutSection_trans (W : Y.Opens)
    (e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    unitAutSection W (e ≪≫ e') = unitAutSection W e * unitAutSection W e' := by
  simp only [unitAutSection, ← map_mul]
  congr 1
  have key : ∀ (f g : ((W : Scheme.{u}).ringCatSheaf.val.obj (Opposite.op ⊤)) →ₗ[(W : Scheme.{u}).ringCatSheaf.val.obj (Opposite.op ⊤)]
      ((W : Scheme.{u}).ringCatSheaf.val.obj (Opposite.op ⊤))), g (f 1) = f 1 * g 1 := fun f g => by
    conv_lhs => rw [← mul_one (f 1), ← smul_eq_mul, LinearMap.map_smul, smul_eq_mul]
  exact key (e.hom.val.app (Opposite.op ⊤)).hom (e'.hom.val.app (Opposite.op ⊤)).hom

theorem pullbackCongr_app_tensorObj {X : Scheme.{u}} {f g : X ⟶ Y} (p : f = g) (L M : Y.Modules) :
    (pullbackCongr p).app (L ⊗ M) =
      pullbackTensorObjIso f L M ≪≫ ((pullbackCongr p).app L ⊗ᵢ (pullbackCongr p).app M) ≪≫
        (pullbackTensorObjIso g L M).symm := by
  subst p
  ext
  simp [pullbackCongr]

theorem restrict_tensor (𝒱 : Y.OrderedAffineCover) (𝓛 𝓜 : Y.Modules)
    (τ : CechTrivialisation 𝒱 𝓛) (τ' : CechTrivialisation 𝒱 𝓜) {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    CechTrivialisation.restrict (𝓜 := 𝓛 ⊗ 𝓜)
        (fun a => pullbackTensorObjIso (𝒱.U a).ι 𝓛 𝓜 ≪≫ (τ a ⊗ᵢ τ' a) ≪≫ λ_ _) h =
      pullbackTensorObjIso W.ι 𝓛 𝓜 ≪≫ (τ.restrict h ⊗ᵢ τ'.restrict h) ≪≫ λ_ _ := by
  have hη : Functor.OplaxMonoidal.η (Scheme.Modules.pullback (Y.homOfLE h)) =
      (pullbackUnitIso (Y.homOfLE h)).hom := by
    rw [← pullbackTensorUnitObjIso_eq_pullbackUnitIso]; simp [pullbackTensorUnitObjIso]
  simp only [CechTrivialisation.restrict]
  rw [pullbackComp_app_tensorObj, pullbackCongr_app_tensorObj]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorIso_hom, tensorIso_inv, Iso.symm_inv,
    Category.assoc, pullbackTensorObjIso, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv]
  rw [← Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [hη, ← leftUnitor_naturality, ← MonoidalCategory.tensorHom_def_assoc]
  erw [Functor.Monoidal.μ_δ_assoc]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.assoc]

end TT

namespace TD

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {Y : Scheme.{u}}

theorem tensor_solve {C : Type*} [Category C] [MonoidalCategory C] {T X Mx : C}
    (P : T ≅ X ⊗ Mx) (t : X ≅ 𝟙_ C) (Cc : T ≅ 𝟙_ C) :
    P ≪≫ (t ⊗ᵢ ((λ_ Mx).symm ≪≫ (t.symm ⊗ᵢ Iso.refl Mx) ≪≫ P.symm ≪≫ Cc)) ≪≫ λ_ (𝟙_ C) = Cc := by
  apply Iso.ext
  simp [MonoidalCategory.tensorHom_def]

theorem restrict_canonical (𝒱 : Y.OrderedAffineCover) (N : Y.Modules)
    (E : N ≅ SheafOfModules.unit Y.ringCatSheaf) {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    CechTrivialisation.restrict (𝓜 := N)
        (fun a => (Scheme.Modules.pullback (𝒱.U a).ι).mapIso E ≪≫ pullbackUnitIso (𝒱.U a).ι) h =
      (Scheme.Modules.pullback W.ι).mapIso E ≪≫ pullbackUnitIso W.ι := by
  suffices H : ∀ {B : Scheme.{u}} (j : B ⟶ Y) (k : B ⟶ (𝒱.U a : Scheme.{u})) (eq : k ≫ (𝒱.U a).ι = j),
      ((pullbackCongr eq).app N).symm ≪≫ ((pullbackComp k (𝒱.U a).ι).app N).symm ≪≫
        (Scheme.Modules.pullback k).mapIso
          ((Scheme.Modules.pullback (𝒱.U a).ι).mapIso E ≪≫ pullbackUnitIso (𝒱.U a).ι) ≪≫
        pullbackUnitIso k = (Scheme.Modules.pullback j).mapIso E ≪≫ pullbackUnitIso j from
    H W.ι (Y.homOfLE h) (Y.homOfLE_ι h)
  intro B j k eq
  subst eq
  apply Iso.ext
  have nat := (pullbackComp k (𝒱.U a).ι).inv.naturality E.hom
  simp only [Functor.comp_map] at nat
  have hu := pullbackComp_hom_app_comp_pullbackUnitIso_hom k (𝒱.U a).ι
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_trans,
    Category.assoc, pullbackCongr]
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  rw [← reassoc_of% nat, ← hu, Iso.inv_hom_id_app_assoc]

noncomputable def dualTriv (𝒱 : Y.OrderedAffineCover) (𝓛 : Y.Modules) (τ : CechTrivialisation 𝒱 𝓛)
    (e : 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅ SheafOfModules.unit Y.ringCatSheaf) :
    CechTrivialisation 𝒱 (Scheme.Modules.dual 𝓛) := fun a =>
  (λ_ _).symm ≪≫ ((τ a).symm ⊗ᵢ Iso.refl _) ≪≫
    (pullbackTensorObjIso (𝒱.U a).ι 𝓛 (Scheme.Modules.dual 𝓛)).symm ≪≫
    (Scheme.Modules.pullback (𝒱.U a).ι).mapIso e ≪≫ pullbackUnitIso (𝒱.U a).ι

theorem tensor_family_eq (𝒱 : Y.OrderedAffineCover) (𝓛 : Y.Modules) (τ : CechTrivialisation 𝒱 𝓛)
    (e : 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (fun a => pullbackTensorObjIso (𝒱.U a).ι 𝓛 (Scheme.Modules.dual 𝓛) ≪≫ (τ a ⊗ᵢ dualTriv 𝒱 𝓛 τ e a) ≪≫ λ_ _) =
      (fun a => (Scheme.Modules.pullback (𝒱.U a).ι).mapIso e ≪≫ pullbackUnitIso (𝒱.U a).ι) := by
  funext a
  exact tensor_solve _ _ _

theorem Iso.eq_of_trans_eq_trans {C : Type*} [Category C] {A B B' D : C} (X : A ≅ B) (Y₁ Y₂ : B ≅ B') (Z : B' ≅ D)
    (h : X ≪≫ Y₁ ≪≫ Z = X ≪≫ Y₂ ≪≫ Z) : Y₁ = Y₂ := by
  have : X.symm ≪≫ (X ≪≫ Y₁ ≪≫ Z) ≪≫ Z.symm = X.symm ≪≫ (X ≪≫ Y₂ ≪≫ Z) ≪≫ Z.symm := by rw [h]
  simpa using this

theorem tensorIso_symm_trans {C : Type*} [Category C] [MonoidalCategory C] {A A' B B' : C}
    (e₁ e₂ : A ≅ A') (f₁ f₂ : B ≅ B') :
    (e₁ ⊗ᵢ f₁).symm ≪≫ (e₂ ⊗ᵢ f₂) = (e₁.symm ≪≫ e₂) ⊗ᵢ (f₁.symm ≪≫ f₂) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, tensorIso_inv, MonoidalCategory.tensorHom_comp_tensorHom]

end TD

open TD TT _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓛 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛) :
    ∃ σ : Scheme.Modules.CechTrivialisation 𝒱 (Scheme.Modules.dual 𝓛),
      ∀ s : 𝒱.Idx 1, σ.transition s * τ.transition s = 1 := by

  have hL : Scheme.Modules.IsInvertible 𝓛 := ⟨fun y => by
    have hy : y ∈ (⨆ i, 𝒱.U i) := by rw [𝒱.iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨𝒱.U i, hi, ⟨τ i⟩⟩⟩
  obtain ⟨e⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hL).2
  have e' : 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅ SheafOfModules.unit Y.ringCatSheaf := e
  refine ⟨dualTriv 𝒱 𝓛 τ e', fun s => ?_⟩
  set σ := dualTriv 𝒱 𝓛 τ e' with hσ
  set W : Y.Opens := 𝒱.inter s with hW

  have key : ∀ j : Fin 2,
      pullbackTensorObjIso W.ι 𝓛 (Scheme.Modules.dual 𝓛) ≪≫
          (τ.restrict (𝒱.inter_le s j) ⊗ᵢ σ.restrict (𝒱.inter_le s j)) ≪≫ λ_ _ =
        (Scheme.Modules.pullback W.ι).mapIso e' ≪≫ pullbackUnitIso W.ι := by
    intro j
    rw [← TT.restrict_tensor 𝒱 𝓛 (Scheme.Modules.dual 𝓛) τ σ (𝒱.inter_le s j), hσ, tensor_family_eq]
    exact restrict_canonical 𝒱 _ e' (𝒱.inter_le s j)
  have hpair : τ.restrict (𝒱.inter_le s 0) ⊗ᵢ σ.restrict (𝒱.inter_le s 0) =
      τ.restrict (𝒱.inter_le s 1) ⊗ᵢ σ.restrict (𝒱.inter_le s 1) :=
    TD.Iso.eq_of_trans_eq_trans _ _ _ _ ((key 0).trans (key 1).symm)
  have hT : ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1)) ⊗ᵢ
      ((σ.restrict (𝒱.inter_le s 0)).symm ≪≫ σ.restrict (𝒱.inter_le s 1)) = Iso.refl _ := by
    rw [← tensorIso_symm_trans, hpair, Iso.symm_self_id]
  have E := TT.leftUnitor_conj_tensorIso (C := ((𝒱.inter s : Y.Opens) : Scheme.{u}).Modules)
    ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1))
    ((σ.restrict (𝒱.inter_le s 0)).symm ≪≫ σ.restrict (𝒱.inter_le s 1))
  have E2 : ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1)) ≪≫
      ((σ.restrict (𝒱.inter_le s 0)).symm ≪≫ σ.restrict (𝒱.inter_le s 1)) = Iso.refl _ := by
    rw [← E, hT]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom]
    erw [Category.id_comp]
    simp only [Iso.inv_hom_id]
    rfl
  have huas := (unitAutSection_trans_and_unitAutSection_refl (𝒱.inter s)).1
    ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1))
    ((σ.restrict (𝒱.inter_le s 0)).symm ≪≫ σ.restrict (𝒱.inter_le s 1))
  rw [E2, (unitAutSection_trans_and_unitAutSection_refl (𝒱.inter s)).2] at huas
  show unitAutSection _ _ * unitAutSection _ _ = 1
  rw [mul_comm]
  exact huas.symm

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one (solution)
