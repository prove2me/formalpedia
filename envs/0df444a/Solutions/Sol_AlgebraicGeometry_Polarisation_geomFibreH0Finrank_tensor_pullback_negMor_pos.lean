-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_pullback_negMor_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/666bbe68-174c-5034-9b07-506138cf8b35

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_unit_hom_tensor_ne_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_pullback_fst_of_abelianSchemePropertyBundle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_pullback_negMor_pos
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace PosHelpers

open Opposite

theorem exists_unit_hom_ne_zero_of_section {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) (hs : s ≠ 0) :
    ∃ φ : 𝟙_ X.Modules ⟶ M, φ ≠ 0 := by
  let σ : M.val.sections := PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map (homOfLE (le_top (a := U.unop))).op s)
    (fun U V g => by
      show M.presheaf.map g (M.presheaf.map (homOfLE (le_top (a := U.unop))).op s) =
        M.presheaf.map (homOfLE (le_top (a := V.unop))).op s
      rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
      congr 1)
  refine ⟨M.unitHomEquiv.symm σ, fun h => hs ?_⟩
  have h1 := SheafOfModules.unitHomEquiv_apply_coe M (M.unitHomEquiv.symm σ) (op ⊤)
  rw [Equiv.apply_symm_apply, h] at h1

  have h2 : σ.val (op ⊤) = s := by
    show M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op s = s
    rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 (op ⊤) from Subsingleton.elim _ _, M.presheaf.map_id]
    rfl
  rw [← h2, h1]
  show ((0 : 𝟙_ X.Modules ⟶ M).app ⊤) (1 : Γ(X, ⊤)) = 0
  rw [Scheme.Modules.Hom.zero_app]
  rfl

theorem app_top_one_ne_zero {X : Scheme.{0}} {M : X.Modules} (φ : 𝟙_ X.Modules ⟶ M) (hφ : φ ≠ 0) :
    (φ.app ⊤) (1 : Γ(X, ⊤)) ≠ 0 := by
  intro h
  apply hφ
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  have hU : (1 : X.ringCatSheaf.val.obj U) =
      (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE (le_top (a := U.unop))).op (1 : X.ringCatSheaf.val.obj (op ⊤)) :=
    (PresheafOfModules.unit_map_one _ (homOfLE (le_top (a := U.unop))).op).symm
  have h' : (φ.val.app (op ⊤)) (1 : X.ringCatSheaf.val.obj (op ⊤)) = 0 := h
  have h'' : ((0 : 𝟙_ X.Modules ⟶ M).val.app (op ⊤)) (1 : X.ringCatSheaf.val.obj (op ⊤)) = 0 := by
    show ((0 : 𝟙_ X.Modules ⟶ M).app ⊤) _ = 0
    rw [Scheme.Modules.Hom.zero_app]; rfl
  rw [hU, PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  exact congrArg (fun y => (M.val.map (homOfLE (le_top (a := U.unop))).op) y) (h'.trans h''.symm)

theorem negMor_comp_negMor {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) :
    negMor f L ≫ negMor f L = 𝟙 A := by
  letI := L.pointGroup f
  have hN : negMor f L ≫ f = f := negMor_over f L

  have hnat : GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (L.inv f (idPt f)) =
      L.inv f (GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (idPt f)) := by
    have h : GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (L.inv f (idPt f)) *
        GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (idPt f) = 1 := by
      show L.mul f _ _ = L.one f
      rw [← L.mul_natural f f (negMor f L) hN, L.inv_mul_cancel, L.one_natural f f (negMor f L) hN]
    exact (inv_eq_of_mul_eq_one_left h).symm
  have hid : GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (idPt f) = L.inv f (idPt f) := by
    apply Subtype.ext; show negMor f L ≫ 𝟙 A = negMor f L; rw [Category.comp_id]
  rw [hid] at hnat
  have h2 : L.inv f (L.inv f (idPt f)) = idPt f := by
    show (idPt f)⁻¹⁻¹ = idPt f
    exact inv_inv _
  rw [h2] at hnat
  have h3 := congrArg Subtype.val hnat
  exact h3

end PosHelpers

theorem solution
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hpos : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₀ k' sk)
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') :
    0 < Scheme.Modules.geomFibreH0Finrank f (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) k' sk := by

  let g := Spec.map (CommRingCat.ofHom sk)
  let X := pullback f g
  let p₁ : X ⟶ A := pullback.fst f g
  let N := negMor f L
  haveI hGI : GeometricallyIntegral f := hA.geometricallyIntegral
  haveI : IsIntegral X := hGI.geometrically_isIntegral g p₁ (pullback.snd f g) (IsPullback.of_hasPullback f g)
  haveI : IsIso N := ⟨⟨N, PosHelpers.negMor_comp_negMor f L, PosHelpers.negMor_comp_negMor f L⟩⟩
  have hN : N ≫ f = f := negMor_over f L

  have h₁ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback p₁).obj 𝓛₀) := h₀.pullback p₁
  have h₂ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback N).obj 𝓛₀)) :=
    (h₀.pullback N).pullback p₁
  have h₃ : Scheme.Modules.IsInvertible (𝓛₀ ⊗ (Scheme.Modules.pullback N).obj 𝓛₀) :=
    Scheme.Modules.IsInvertible.tensor_monoidalV2 h₀ (h₀.pullback N)

  letI algX : Algebra k' Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ (Limits.pullback.snd f g).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI mod₀ : Module k' Γ((Scheme.Modules.pullback p₁).obj 𝓛₀, ⊤) := Module.compHom _ (algebraMap k' Γ(X, ⊤))
  letI mod₁ : Module k' Γ((Scheme.Modules.pullback p₁).obj (𝓛₀ ⊗ (Scheme.Modules.pullback N).obj 𝓛₀), ⊤) :=
    Module.compHom _ (algebraMap k' Γ(X, ⊤))

  have hpos' : 0 < Module.finrank k' Γ((Scheme.Modules.pullback p₁).obj 𝓛₀, ⊤) := hpos k' sk
  haveI : Nontrivial Γ((Scheme.Modules.pullback p₁).obj 𝓛₀, ⊤) := Module.nontrivial_of_finrank_pos hpos'
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : Γ((Scheme.Modules.pullback p₁).obj 𝓛₀, ⊤))
  obtain ⟨s, hs⟩ := PosHelpers.exists_unit_hom_ne_zero_of_section _ s₀ hs₀

  obtain ⟨hγ₁, hγ₂⟩ := Scheme.Modules.exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor k f N hN 𝓛₀ 𝓛₀ k' sk
  obtain ⟨t, ht⟩ := hγ₁ ⟨s, hs⟩
  obtain ⟨u, hu⟩ := Scheme.Modules.IsInvertible.exists_unit_hom_tensor_ne_zero _ _ h₁ h₂ ⟨s, hs⟩ ⟨t, ht⟩
  obtain ⟨v, hv⟩ := hγ₂ ⟨u, hu⟩

  have hfin : Module.Finite k' Γ((Scheme.Modules.pullback p₁).obj (𝓛₀ ⊗ (Scheme.Modules.pullback N).obj 𝓛₀), ⊤) :=
    Scheme.Modules.IsInvertible.finite_sections_pullback_fst_of_abelianSchemePropertyBundle k f hA _ h₃ k' sk
  have hne := PosHelpers.app_top_one_ne_zero v hv
  haveI : Nontrivial Γ((Scheme.Modules.pullback p₁).obj (𝓛₀ ⊗ (Scheme.Modules.pullback N).obj 𝓛₀), ⊤) :=
    nontrivial_of_ne _ _ hne
  show 0 < Module.finrank k' Γ((Scheme.Modules.pullback p₁).obj (𝓛₀ ⊗ (Scheme.Modules.pullback N).obj 𝓛₀), ⊤)
  exact Module.finrank_pos

end S_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_pullback_negMor_pos
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_pullback_negMor_pos (solution)
