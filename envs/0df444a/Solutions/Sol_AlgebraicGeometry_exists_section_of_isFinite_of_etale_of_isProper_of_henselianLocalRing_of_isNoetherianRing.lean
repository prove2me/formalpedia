-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/30d72c89-e54e-5dd3-81fc-1b44fa7fe552

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
import Theorems.Thm_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace F1Asm

private theorem etale_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [Etale π] (s : X ⟶ Y) (hs : s ≫ π = 𝟙 X) :
    Etale s := by
  have : Etale (s ≫ π) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) s π ‹_› this

private theorem isClosedImmersion_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [IsSeparated π] (s : X ⟶ Y)
    (hs : s ≫ π = 𝟙 X) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ π) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s π

private theorem isOpenImmersion_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [Etale π] (s : X ⟶ Y)
    (hs : s ≫ π = 𝟙 X) : IsOpenImmersion s := by
  have : Etale s := etale_of_section π s hs
  have : IsSplitMono s := IsSplitMono.mk' ⟨π, hs⟩
  exact IsOpenImmersion.of_flat_of_mono s

private theorem isClosedImmersion_ι_of_isClosed {Y : Scheme.{u}} (U : Y.Opens) (hU : IsClosed (U : Set Y)) :
    IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)

private theorem isIso_pullback_snd_of_preimage_eq
    {Xk X Y : Scheme.{u}} (ι : Xk ⟶ X) (π : Y ⟶ X) (U : Y.Opens) (V₀ : (pullback π ι).Opens)
    (hV₀ : IsIso (V₀.ι ≫ pullback.snd π ι)) (hUV : (pullback.fst π ι) ⁻¹ᵁ U = V₀) :
    IsIso (pullback.snd (U.ι ≫ π) ι) := by

  let e₂ := pullbackRightPullbackFstIso π ι U.ι
  have h1 : pullback.snd (U.ι ≫ π) ι = e₂.inv ≫ pullback.snd U.ι (pullback.fst π ι) ≫ pullback.snd π ι := by
    rw [← pullbackRightPullbackFstIso_hom_snd, Iso.inv_hom_id_assoc]
  have h2 : pullback.snd U.ι (pullback.fst π ι) =
      (pullbackSymmetry _ _).hom ≫ pullback.fst (pullback.fst π ι) U.ι := by
    rw [pullbackSymmetry_hom_comp_fst]
  have h3 : pullback.fst (pullback.fst π ι) U.ι =
      (pullbackRestrictIsoRestrict (pullback.fst π ι) U).hom ≫ ((pullback.fst π ι) ⁻¹ᵁ U).ι := by
    rw [pullbackRestrictIsoRestrict_hom_ι]
  have h4 : ((pullback.fst π ι) ⁻¹ᵁ U).ι = ((pullback π ι).isoOfEq hUV).hom ≫ V₀.ι := by
    rw [Scheme.isoOfEq_hom_ι]
  rw [h1, h2, h3, h4]
  simp only [Category.assoc]
  have : IsIso (V₀.ι ≫ pullback.snd π ι) := hV₀
  infer_instance

end F1Asm

open F1Asm in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : Y ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ Y)
    (hs₀ : s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    ∃ s : X ⟶ Y, s ≫ π = 𝟙 X ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ s = s₀ := by
  have hcond : s₀ ≫ π = 𝟙 _ ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by rw [hs₀, Category.id_comp]

  have ht₀ : pullback.lift s₀ (𝟙 _) hcond ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ := pullback.lift_snd _ _ _
  have ht₀fst : pullback.lift s₀ (𝟙 _) hcond ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = s₀ := pullback.lift_fst _ _ _
  haveI hopen : IsOpenImmersion (pullback.lift s₀ (𝟙 _) hcond) := isOpenImmersion_of_section _ _ ht₀
  haveI hclosed : IsClosedImmersion (pullback.lift s₀ (𝟙 _) hcond) := isClosedImmersion_of_section _ _ ht₀

  let V₀ : (pullback π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).Opens := (pullback.lift s₀ (𝟙 _) hcond).opensRange
  have hV₀c : IsClosed (V₀ : Set ↥(pullback π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))) :=
    (pullback.lift s₀ (𝟙 _) hcond).isClosedEmbedding.isClosed_range
  have hV₀i : IsIso (V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by
    have e : (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange.hom ≫ V₀.ι = pullback.lift s₀ (𝟙 _) hcond :=
      (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange_hom_ι
    have : V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange.inv := by
      rw [← cancel_epi (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange.hom, ← Category.assoc, e, ht₀,
        Iso.hom_inv_id]
    rw [this]
    infer_instance

  let V : (pullback (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).Opens := (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) π).inv ⁻¹ᵁ V₀
  have hVc : IsClosed (V : Set ↥(pullback (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := hV₀c.preimage (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) π).inv.continuous

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨Uset, hUclopen, hUVset⟩ :=
    AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_henselianLocalRing (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      (V : Set ↥(pullback (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) ⟨hVc, V.2⟩
  let U : Y.Opens := ⟨Uset, hUclopen.isOpen⟩
  have hUc : IsClosed (U : Set Y) := hUclopen.isClosed
  have hUV : (pullback.fst (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ⁻¹ᵁ U = V := TopologicalSpace.Opens.ext hUVset

  have hUV₀ : (pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) ⁻¹ᵁ U = V₀ := by
    have h : ((pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) π).inv ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) ⁻¹ᵁ U = (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) π).inv ⁻¹ᵁ V₀ := by
      rw [pullbackRightPullbackFstIso_inv_fst]; exact hUV
    rw [Scheme.Hom.comp_preimage] at h
    have h2 := congrArg (fun W => (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) π).hom ⁻¹ᵁ W) h
    simp only [← Scheme.Hom.comp_preimage, Iso.hom_inv_id] at h2
    simpa using h2

  haveI : IsClosedImmersion U.ι := isClosedImmersion_ι_of_isClosed U hUc
  have hiso : IsIso (U.ι ≫ π) :=
    AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper f (U.ι ≫ π)
      (isIso_pullback_snd_of_preimage_eq (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) π U V₀ hV₀i hUV₀)

  refine ⟨inv (U.ι ≫ π) ≫ U.ι, by rw [Category.assoc, IsIso.inv_hom_id], ?_⟩

  have hcond' : ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι) ≫ π = 𝟙 _ ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    simp only [Category.assoc, Category.id_comp, IsIso.inv_hom_id, Category.comp_id]
  have ht' : pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond' ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hr₀ : Set.range (pullback.lift s₀ (𝟙 _) hcond).base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact subset_of_eq rfl
  have hr' : Set.range (pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond').base ⊆
      Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι, ← hUV₀]
    rintro _ ⟨x, rfl⟩
    change ((pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond') ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).base x ∈
      (U : Set Y)
    rw [pullback.lift_fst]
    change U.ι.base (((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π)).base x) ∈ (U : Set Y)
    rw [← Scheme.Opens.range_ι U]
    exact ⟨_, rfl⟩
  have eq1 : IsOpenImmersion.lift V₀.ι _ hr' ≫ V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact ht'
  have eq0 : IsOpenImmersion.lift V₀.ι _ hr₀ ≫ V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact ht₀
  have hlifts : IsOpenImmersion.lift V₀.ι _ hr' = IsOpenImmersion.lift V₀.ι _ hr₀ := by
    haveI : Mono (V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by haveI := hV₀i; infer_instance
    rw [← cancel_mono (V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))]
    exact eq1.trans eq0.symm
  calc (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι
      = pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond' ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
        (pullback.lift_fst _ _ _).symm
    _ = (IsOpenImmersion.lift V₀.ι _ hr' ≫ V₀.ι) ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by rw [IsOpenImmersion.lift_fac]
    _ = (IsOpenImmersion.lift V₀.ι _ hr₀ ≫ V₀.ι) ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by rw [hlifts]
    _ = s₀ := by rw [IsOpenImmersion.lift_fac, pullback.lift_fst]

end S_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing (solution)
