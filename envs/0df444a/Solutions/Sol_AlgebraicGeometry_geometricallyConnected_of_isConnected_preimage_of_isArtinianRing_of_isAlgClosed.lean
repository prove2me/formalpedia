-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyConnected_of_isConnected_preimage_of_isArtinianRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/467ad9a7-a46b-56ce-96a7-1e14ad49611d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isConnected_preimage_of_isArtinianRing_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

open CategoryTheory.Limits

namespace E160GEOM

theorem eq_closedPoint_of_isArtinianRing (T' : Type u) [CommRing T'] [IsLocalRing T']
    [IsArtinianRing T'] (y : PrimeSpectrum T') : y = IsLocalRing.closedPoint T' := by
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)

theorem isNilpotent_maximalIdeal (T' : Type u) [CommRing T'] [IsLocalRing T']
    [IsArtinianRing T'] : IsNilpotent (IsLocalRing.maximalIdeal T') := by
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := T')
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

theorem isLocalHom_of_isArtinianRing_field {T' : Type u} [CommRing T'] [IsLocalRing T']
    [IsArtinianRing T'] {K : Type u} [Field K] (ψ : T' →+* K) : IsLocalHom ψ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal T' := hna
  obtain ⟨n, hn⟩ := isNilpotent_maximalIdeal T'
  have han : a ^ n ∈ (IsLocalRing.maximalIdeal T') ^ n := Ideal.pow_mem_pow hmem n
  rw [hn] at han
  have ha0 : a ^ n = 0 := by simpa using han
  have := (ha.pow n)
  rw [← map_pow, ha0, map_zero] at this
  exact not_isUnit_zero this

end E160GEOM

theorem solution
    (T' : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of T')) [LocallyOfFiniteType f] [IsProper f]
    (hconn : ∀ x : Spec (CommRingCat.of T'), _root_.IsConnected (f.base ⁻¹' {x})) :
    GeometricallyConnected f := by

  have hr : Function.Surjective (IsLocalRing.residue T') := IsLocalRing.residue_surjective
  have hker : IsNilpotent (RingHom.ker (IsLocalRing.residue T')) := by
    rw [IsLocalRing.ker_residue]; exact E160GEOM.isNilpotent_maximalIdeal T'

  haveI : ConnectedSpace X := by
    have huniv : f.base ⁻¹' {IsLocalRing.closedPoint T'} = Set.univ :=
      Set.eq_univ_of_forall fun x => E160GEOM.eq_closedPoint_of_isArtinianRing T' _
    rw [connectedSpace_iff_univ, ← huniv]
    exact hconn _

  have hH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    (IsLocalRing.residue T') hr hker f
    (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T'))))
    (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T'))))
    (IsPullback.of_hasPullback _ _)
  obtain ⟨_, _, hhomeo⟩ := hH
  haveI : ConnectedSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T')))) := by
    let eH := hhomeo.homeomorph _
    exact eH.symm.surjective.connectedSpace eH.symm.continuous
  have hGC : GeometricallyConnected
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T')))) :=
    AlgebraicGeometry.geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
      (IsLocalRing.ResidueField T') _

  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
  haveI : IsLocalHom (algebraMap T' K) := E160GEOM.isLocalHom_of_isArtinianRing_field _
  let ψb : IsLocalRing.ResidueField T' →+* K := IsLocalRing.ResidueField.lift (algebraMap T' K)
  have hψ : algebraMap T' K = ψb.comp (IsLocalRing.residue T') :=
    (IsLocalRing.ResidueField.lift_comp_residue (algebraMap T' K)).symm
  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap T' K)) =
      Spec.map (CommRingCat.ofHom ψb) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue T')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
  have hc : ConnectedSpace ↥(pullback
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T'))))
      (Spec.map (CommRingCat.ofHom ψb))) :=
    pullback_of_geometrically hGC.1 K (Spec.map (CommRingCat.ofHom ψb))
  let e1 := pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T')))
    (Spec.map (CommRingCat.ofHom ψb))
  let e2 : pullback f (Spec.map (CommRingCat.ofHom ψb) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue T'))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap T' K))) :=
    pullback.congrHom rfl hSpec.symm
  let eh := Scheme.homeoOfIso (e1 ≪≫ e2)
  exact eh.surjective.connectedSpace eh.continuous

end S_AlgebraicGeometry_geometricallyConnected_of_isConnected_preimage_of_isArtinianRing_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isConnected_preimage_of_isArtinianRing_of_isAlgClosed (solution)
