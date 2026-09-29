-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_tensor_forall_transition_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0765af38-b962-5d98-be7e-8d73307454ca

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_tensor_forall_transition_eq_mul
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

open TT _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓛 𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛) (τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    ∃ σ : Scheme.Modules.CechTrivialisation 𝒱 (𝓛 ⊗ 𝓜),
      ∀ s : 𝒱.Idx 1, σ.transition s = τ.transition s * τ'.transition s := by
  refine ⟨fun a => pullbackTensorObjIso (𝒱.U a).ι 𝓛 𝓜 ≪≫ (τ a ⊗ᵢ τ' a) ≪≫ λ_ _, fun s => ?_⟩
  show unitAutSection _ _ = unitAutSection _ _ * unitAutSection _ _
  rw [TT.restrict_tensor 𝒱 𝓛 𝓜 τ τ' (𝒱.inter_le s 0), TT.restrict_tensor 𝒱 𝓛 𝓜 τ τ' (𝒱.inter_le s 1)]
  have E := TT.leftUnitor_conj_tensorIso (C := ((𝒱.inter s : Y.Opens) : Scheme.{u}).Modules)
    ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1))
    ((τ'.restrict (𝒱.inter_le s 0)).symm ≪≫ τ'.restrict (𝒱.inter_le s 1))
  rw [← TT.unitAutSection_trans, ← E]
  congr 1
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, tensorIso_hom, tensorIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_tensor_forall_transition_eq_mul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_tensor_forall_transition_eq_mul (solution)
