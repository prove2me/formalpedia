-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e2d17668-d867-54fb-b8fa-fb255ccd5f41

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace T2Aux

p2m_open "AlgebraicGeometry.Scheme.Modules"

theorem nonempty_pullback_iso_unit_of_forall_notMem {X Y : Scheme.{u}} (φ : Y ⟶ X)
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hφ : ∀ y : Y, φ.base y ∉ ((Scheme.Modules.zeroSchemeIdeal s).support : Set X)) :
    Nonempty ((Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y.Modules) := by

  let V : X.Opens := (Scheme.Modules.zeroSchemeIdeal s).support.compl
  have hdisj : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal s).support :=
    Set.disjoint_left.mpr fun x hx hx' => hx hx'
  have hfr := hM.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal s V hdisj

  have hfr' := hfr.pullbackLocalSection φ
  have hV : φ ⁻¹ᵁ V = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top,
      Set.mem_univ, iff_true]
    exact hφ y
  rw [hV] at hfr'

  set σ := Scheme.Modules.pullbackLocalSection φ (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) with hσ
  refine Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul (U := ⊤) (V := ⊤)
    (by simp) hfr' hfr' 1 (by rw [one_smul]) 1 1 isUnit_one isUnit_one (by rw [one_mul])

end T2Aux

open T2Aux _root_.AlgebraicGeometry.Scheme.Modules in

theorem solution
    {X Y : Scheme.{u}} (i₂ : Y ⟶ X)
    (J : X.IdealSheafData) (hJ : J.IsInvertible) (N : X.IdealSheafData) (hN : N.IsInvertible) (r : ℕ)
    (hJsupp : ∀ y : Y, i₂.base y ∉ (J.support : Set X))
    (hNsupp : ∀ y : Y, i₂.base y ∉ (N.support : Set X))
    (L₀ : X.Modules)
    (hL₀₂ : Nonempty ((Scheme.Modules.pullback i₂).obj L₀ ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf))) :
    Nonempty ((Scheme.Modules.pullback i₂).obj (L₀ ⊗ ((J ^ r).invModule ⊗ N.module)) ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  have hJr : (J ^ r).IsInvertible := hJ.pow r

  have hsuppJr : ((J ^ r).support : Set X) ⊆ J.support := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
      intro x hx
      exact absurd hx (by simp)
    · rw [Scheme.IdealSheafData.support_pow _ _ hr.ne']
  obtain ⟨eS⟩ : Nonempty ((Scheme.Modules.pullback i₂).obj (J ^ r).invModule ≅ 𝟙_ Y.Modules) := by
    have hz := Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection hJr
    refine nonempty_pullback_iso_unit_of_forall_notMem i₂ hJr.isInvertible_invModule (J ^ r).invModuleSection ?_
    intro y hy
    have hy' : i₂.base y ∈ ((J ^ r).support : Set X) := by
      have hs : ((Scheme.Modules.zeroSchemeIdeal (J ^ r).invModuleSection).support : Set X) = (J ^ r).support := by
        rw [hz]
      rw [← hs]; exact hy
    exact hJsupp y (hsuppJr hy')

  obtain ⟨eD'⟩ : Nonempty ((Scheme.Modules.pullback i₂).obj N.invModule ≅ 𝟙_ Y.Modules) := by
    have hz := Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection hN
    refine nonempty_pullback_iso_unit_of_forall_notMem i₂ hN.isInvertible_invModule N.invModuleSection ?_
    intro y hy
    have hy' : i₂.base y ∈ (N.support : Set X) := by
      have hs : ((Scheme.Modules.zeroSchemeIdeal N.invModuleSection).support : Set X) = N.support := by rw [hz]
      rw [← hs]; exact hy
    exact hNsupp y hy'
  have hNm : Scheme.Modules.IsInvertible N.module := hN.isInvertible_module
  have eEv : N.module ⊗ N.invModule ≅ 𝟙_ X.Modules :=
    @asIso _ _ _ _ ((ihom.ev N.module).app (𝟙_ X.Modules)) hNm.isIso_ev_app_tensorUnit
  have eN : (Scheme.Modules.pullback i₂).obj N.module ≅ 𝟙_ Y.Modules :=
    (ρ_ _).symm ≪≫ (whiskerLeftIso _ eD'.symm) ≪≫ (Scheme.Modules.pullbackTensorObjIso i₂ _ _).symm ≪≫
      (Scheme.Modules.pullback i₂).mapIso eEv ≪≫ Scheme.Modules.pullbackTensorUnitObjIso i₂

  obtain ⟨eL2⟩ := hL₀₂
  have eL : (Scheme.Modules.pullback i₂).obj L₀ ≅ 𝟙_ Y.Modules := eL2 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso i₂

  have eF : (Scheme.Modules.pullback i₂).obj (L₀ ⊗ ((J ^ r).invModule ⊗ N.module)) ≅ 𝟙_ Y.Modules :=
    Scheme.Modules.pullbackTensorObjIso i₂ _ _ ≪≫
      (eL ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso i₂ _ _ ≪≫ (eS ⊗ᵢ eN) ≪≫ λ_ _)) ≪≫ λ_ _
  exact ⟨eF ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso i₂).symm⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support (solution)
