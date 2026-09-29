-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/71b3a0a0-98b6-5262-8d23-4b2e67d39060

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback IsFinite Spec Scheme Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul"
namespace FinsetProdTwistChi
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
  (𝒲 : Y.TwoAffineOpenCover)

def chi (M : Y.Modules) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1

theorem chi_def (M : Y.Modules) :
    chi y 𝒲 M = (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1 :=
  rfl

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem chi_congr {M M' : Y.Modules} (e : M ≅ M') : chi y 𝒲 M = chi y 𝒲 M' := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  obtain rfl : 𝒱₂ = 𝒲 := cover_ext h0 h1
  rw [chi_def, chi_def, e0.finrank_eq, e1.finrank_eq]

theorem nonempty_iso_unit_of_iso_tensor_self {C : Type*} [Category C] [MonoidalCategory C] {E E' : C}
    (e : E ≅ E ⊗ E) (d : E ⊗ E' ≅ 𝟙_ C) : Nonempty (E ≅ 𝟙_ C) :=
  ⟨(ρ_ E).symm ≪≫ whiskerLeftIso E d.symm ≪≫ (α_ E E E').symm ≪≫ whiskerRightIso e.symm E' ≪≫ d⟩

theorem nonempty_invModule_one_iso (X : Scheme.{u}) :
    Nonempty ((1 : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) := by
  have h1 : (1 : X.IdealSheafData).IsInvertible := by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor h1 h1
  exact nonempty_iso_unit_of_iso_tensor_self
    (eqToIso (congrArg Scheme.IdealSheafData.invModule (one_mul (1 : X.IdealSheafData)).symm) ≪≫ em)
    (h1.isInvertible_invModule.dual).2.some

theorem nonempty_module_one_iso (X : Scheme.{u}) :
    Nonempty ((1 : X.IdealSheafData).module ≅ 𝟙_ X.Modules) := by
  have h1 : (1 : X.IdealSheafData).IsInvertible := by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor h1 h1
  exact nonempty_iso_unit_of_iso_tensor_self
    (eqToIso (congrArg Scheme.IdealSheafData.module (one_mul (1 : X.IdealSheafData)).symm) ≪≫ em)
    (h1.isInvertible_module.dual).2.some

variable {X : Scheme.{u}} (ι : Y ⟶ X) [IsProper y] {F : Type v} [DecidableEq F] (I : F → X.IdealSheafData) (a : F → ℕ) (d : F → ℕ)

omit [DecidableEq F] in
theorem isInvertible_finsetProd (S : Finset F) (hI : ∀ i ∈ S, (I i).IsInvertible) :
    (∏ i ∈ S, I i ^ a i).IsInvertible := by
  refine Finset.prod_induction _ (fun J : X.IdealSheafData => J.IsInvertible)
    (fun _ _ h h' => h.mul h') ?_ (fun i hi => (hI i hi).pow (a i))
  rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top

theorem main : ∀ (S : Finset F), (∀ i ∈ S, (I i).IsInvertible) → (∀ i ∈ S, ((I i).comap ι).IsInvertible) →
    (∀ i ∈ S, IsFinite (((I i).comap ι).subschemeι ≫ y)) →
    (∀ i ∈ S, ∀ t : Spec (CommRingCat.of k), (((I i).comap ι).subschemeι ≫ y).finrank t = d i) →
    ∀ (M : X.Modules), Scheme.Modules.IsInvertible M →
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).invModule ⊗ M)) =
          chi y 𝒲 ((Scheme.Modules.pullback ι).obj M) + ∑ i ∈ S, (a i : ℤ) * (d i : ℤ) ∧
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).module ⊗ M)) =
          chi y 𝒲 ((Scheme.Modules.pullback ι).obj M) - ∑ i ∈ S, (a i : ℤ) * (d i : ℤ) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ _ _ M hM
    obtain ⟨e1⟩ := nonempty_invModule_one_iso X
    obtain ⟨e2⟩ := nonempty_module_one_iso X
    simp only [Finset.prod_empty, Finset.sum_empty, add_zero, sub_zero]
    exact ⟨chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso e1 M ≪≫ λ_ M)),
      chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso e2 M ≪≫ λ_ M))⟩
  | insert i₀ S hi₀ ih =>
    intro hI hIY hZ hdeg M hM
    have hI' : ∀ i ∈ S, (I i).IsInvertible := fun i hi => hI i (Finset.mem_insert_of_mem hi)
    have hIY' : ∀ i ∈ S, ((I i).comap ι).IsInvertible := fun i hi => hIY i (Finset.mem_insert_of_mem hi)
    have hZ' : ∀ i ∈ S, IsFinite (((I i).comap ι).subschemeι ≫ y) := fun i hi => hZ i (Finset.mem_insert_of_mem hi)
    have hdeg' : ∀ i ∈ S, ∀ t : Spec (CommRingCat.of k), (((I i).comap ι).subschemeι ≫ y).finrank t = d i :=
      fun i hi => hdeg i (Finset.mem_insert_of_mem hi)
    have h0 : (I i₀).IsInvertible := hI i₀ (Finset.mem_insert_self _ _)
    have hP : (∏ i ∈ S, I i ^ a i).IsInvertible := isInvertible_finsetProd I a S hI'
    rw [Finset.prod_insert hi₀, Finset.sum_insert hi₀]
    obtain ⟨einv⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor (h0.pow (a i₀)) hP
    obtain ⟨emod⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor (h0.pow (a i₀)) hP
    have hPinvM : Scheme.Modules.IsInvertible ((∏ i ∈ S, I i ^ a i).invModule ⊗ M) := hP.isInvertible_invModule.tensor hM
    have hPmodM : Scheme.Modules.IsInvertible ((∏ i ∈ S, I i ^ a i).module ⊗ M) := hP.isInvertible_module.tensor hM
    obtain ⟨ih1, ih2⟩ := ih hI' hIY' hZ' hdeg' M hM
    constructor
    · rw [chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso einv M ≪≫ α_ _ _ _))]
      have h1 := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
        ι y h0 (hIY i₀ (Finset.mem_insert_self _ _)) (hZ i₀ (Finset.mem_insert_self _ _))
        (hdeg i₀ (Finset.mem_insert_self _ _)) _ hPinvM (a i₀) 𝒲
      rw [← chi_def, ← chi_def] at h1
      rw [h1, ih1]; ring
    · rw [chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso emod M ≪≫ α_ _ _ _))]
      have h2 := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
        ι y h0 (hIY i₀ (Finset.mem_insert_self _ _)) (hZ i₀ (Finset.mem_insert_self _ _))
        (hdeg i₀ (Finset.mem_insert_self _ _)) _ hPmodM (a i₀) 𝒲
      rw [← chi_def, ← chi_def] at h2
      rw [h2, ih2]; ring

end AlgebraicGeometry.FinsetProdTwistChi

end

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}} (ι : Y ⟶ X) (y : Y ⟶ Spec (CommRingCat.of k)) [IsProper y]
    {F : Type v} [DecidableEq F] (S : Finset F) (I : F → X.IdealSheafData) (a d : F → ℕ)
    (hI : ∀ i ∈ S, (I i).IsInvertible) (hIY : ∀ i ∈ S, ((I i).comap ι).IsInvertible)
    (hZ : ∀ i ∈ S, IsFinite (((I i).comap ι).subschemeι ≫ y))
    (hdeg : ∀ i ∈ S, ∀ t : Spec (CommRingCat.of k), (((I i).comap ι).subschemeι ≫ y).finrank t = d i)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒲 : Y.TwoAffineOpenCover) :
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).invModule ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).invModule ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H1
        + ∑ i ∈ S, (a i : ℤ) * (d i : ℤ)) ∧
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).module ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).module ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H1
        - ∑ i ∈ S, (a i : ℤ) * (d i : ℤ)) := by
  have h := AlgebraicGeometry.FinsetProdTwistChi.main y 𝒲 ι I a d S hI hIY hZ hdeg M hM
  simp only [AlgebraicGeometry.FinsetProdTwistChi.chi_def] at h
  exact h

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor (solution)
