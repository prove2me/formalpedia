-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/85a90a38-3d51-5395-a4bd-a8058840a0cf

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_bijective_appTop_pullback_fractionRing
import Theorems.Thm_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace Law3GC

noncomputable def awayToRat (M : ℕ) [NeZero M] : Localization.Away ((M : ℕ) : ℤ) →+* ℚ :=
  IsLocalization.lift (M := Submonoid.powers ((M : ℕ) : ℤ)) (g := algebraMap ℤ ℚ)
    (fun ⟨y, hy⟩ => by
      obtain ⟨n, rfl⟩ := hy
      exact isUnit_iff_ne_zero.2 (by simp [NeZero.ne M]))

end Law3GC

theorem solution
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hproper : IsProper πX) (hsmooth1 : SmoothOfRelativeDimension 1 πX)

    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    IsIntegral X ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))),
        IsIntegral (CategoryTheory.Limits.pullback πX s) := by
  classical
  set R := Localization.Away ((M : ℕ) : ℤ) with hR
  haveI : SmoothOfRelativeDimension 1 πX := hsmooth1
  haveI hsm : Smooth πX := SmoothOfRelativeDimension.smooth 1 πX
  haveI : IsProper πX := hproper
  haveI : Flat πX := inferInstance
  haveI : IsDomain R := IsLocalization.isDomain_localization (R := ℤ) (M := Submonoid.powers ((M : ℕ) : ℤ))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (show ((M : ℕ) : ℤ) ≠ 0 by exact_mod_cast NeZero.ne M))

  letI algRQ : Algebra R ℚ := (Law3GC.awayToRat M).toAlgebra
  haveI ist : @IsScalarTower ℤ R ℚ Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
    refine IsScalarTower.of_algebraMap_eq (R := ℤ) (S := R) (A := ℚ) (fun z => ?_)
    exact (IsLocalization.lift_eq (M := Submonoid.powers ((M : ℕ) : ℤ)) (g := algebraMap ℤ ℚ) _ z).symm
  haveI : IsFractionRing R ℚ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers ((M : ℕ) : ℤ)) R ℚ

  set XQ := pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) with hXQ
  set πQ : XQ ⟶ Spec (CommRingCat.of ℚ) := pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) with hπQ
  haveI : IsProper πQ := inferInstance
  haveI : Smooth πQ := inferInstance

  have hXC : IsIntegral (pullback πQ (Spec.map (CommRingCat.ofHom (algebraMap ℚ C)))) := by

    have hψ : Spec.preimage sC = CommRingCat.ofHom ((algebraMap ℚ C).comp (algebraMap R ℚ)) := by
      apply CommRingCat.hom_ext
      apply IsLocalization.ringHom_ext (Submonoid.powers ((M : ℕ) : ℤ))
      exact RingHom.ext_int _ _
    have hsC : sC = Spec.map (CommRingCat.ofHom (algebraMap ℚ C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ℚ)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ, Spec.map_preimage]
    haveI : IsIntegral (pullback πX sC) := hC
    let e₁ : pullback πX sC ≅ pullback πX (Spec.map (CommRingCat.ofHom (algebraMap ℚ C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) :=
      pullback.congrHom rfl hsC
    let e₂ := (pullbackLeftPullbackSndIso πX (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ C)))).symm
    exact IsIntegral.of_isIso (e₁ ≪≫ e₂).hom

  haveI : LocallyOfFiniteType πQ := inferInstance
  obtain ⟨hXQint, hQfib⟩ :=
    AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed ℚ XQ πQ C hXC

  haveI : IsIntegral XQ := hXQint
  have hXint : IsIntegral X :=
    AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing (A := R) ℚ πX
  refine ⟨hXint, ?_⟩
  intro k _ _ s

  haveI : CompactSpace ↥XQ := QuasiCompact.compactSpace_of_compactSpace πQ
  haveI : QuasiSeparatedSpace ↥XQ := quasiSeparatedSpace_of_quasiSeparated πQ
  haveI : IsIntegral ↑(pullback πQ (Spec.map (CommRingCat.ofHom (algebraMap ℚ C)))) := hXC
  have hΓC := AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral C
    (pullback.snd πQ (Spec.map (CommRingCat.ofHom (algebraMap ℚ C))))
  have hΓQ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ πQ.appTop).hom :=
    AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat πQ C hΓC

  haveI : IsDedekindDomain R := IsLocalization.isDedekindDomain ℤ
    (powers_le_nonZeroDivisors_of_noZeroDivisors (show ((M : ℕ) : ℤ) ≠ 0 by exact_mod_cast NeZero.ne M)) R
  haveI : IsIntegrallyClosed R := inferInstance
  haveI : IsNoetherianRing R := inferInstance
  have hΓ : Function.Bijective πX.appTop :=
    AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_bijective_appTop_pullback_fractionRing R ℚ X πX hΓQ

  have hred : ∀ (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback πX t) := by
    intro F _ t
    haveI : Smooth (pullback.snd πX t) := inferInstance
    exact AlgebraicGeometry.isReduced_of_smooth_over_field (g := pullback.snd πX t) inferInstance
  haveI : ConnectedSpace ↥(pullback πX s) :=
    AlgebraicGeometry.connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop M X πX hΓ k s
  haveI : Smooth (pullback.snd πX s) := inferInstance
  exact AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (pullback.snd πX s)

end S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback (solution)
