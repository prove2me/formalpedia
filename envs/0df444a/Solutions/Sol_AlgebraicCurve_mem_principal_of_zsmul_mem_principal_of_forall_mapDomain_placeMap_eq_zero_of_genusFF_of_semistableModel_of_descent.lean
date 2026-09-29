-- Prove2me | solution 1 for AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3dbaad94-3359-5e62-a541-b78274cc5a64

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_balanced_of_semistableModel
import Theorems.Thm_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent
import Theorems.Thm_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel
import Theorems.Thm_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
import Theorems.Thm_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
import Theorems.Thm_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap
import Theorems.Thm_AlgebraicGeometry_isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

namespace S1MDAsm

theorem valuationRing_of_range_eq_inter {L : Type u} [Field L] (A : ValuationSubring L) {A₁ : Type u} [CommRing A₁]
    (ι₁ : A₁ →+* A) (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    haveI := Function.Injective.isDomain ι₁ hι₁; ValuationRing A₁ := by
  haveI := Function.Injective.isDomain ι₁ hι₁
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  have ha : ((ι₁ a : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨a, rfl⟩
  have hb : ((ι₁ b : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨b, rfl⟩
  by_cases hb0 : b = 0
  · exact ⟨0, Or.inl (by simp [hb0])⟩
  by_cases ha0 : a = 0
  · exact ⟨0, Or.inr (by simp [ha0])⟩
  rcases A.mem_or_inv_mem (((ι₁ b : A) : L) / ((ι₁ a : A) : L)) with h | h
  · have hK : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ (K₁ : Set L) := K₁.div_mem hb.2 ha.2
    obtain ⟨c, hc⟩ : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inl ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    have haL : ((ι₁ a : A) : L) ≠ 0 := by
      intro h; apply ha0; apply hι₁; simpa using h
    rw [hc]; field_simp
  · rw [inv_div] at h
    have hK : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ (K₁ : Set L) := K₁.div_mem ha.2 hb.2
    obtain ⟨c, hc⟩ : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inr ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    have hbL : ((ι₁ b : A) : L) ≠ 0 := by
      intro h; apply hb0; apply hι₁; simpa using h
    rw [hc]; field_simp

end S1MDAsm

open S1MDAsm in
set_option linter.unusedVariables false in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] (Fbar : ιV → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : ιE → Annulus A F) (src tgt : ιE → ιV)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : ιE → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : ιE ⊕ ιE,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + Fintype.card ιV =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card ιE + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (Gi : ιV → Divisor L F) (hGi : ∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0)
    {ι : Type*} [Fintype ι] (e : ι → ιE) (nq : ι → ℤ) (Q : ι → Fin 4 → Place L F)
    (hQ : ∀ j l, Q j l ∈ (An (e j)).dom)
    (hrad : ∀ j, ∃ u : Aˣ,
      (Q j 0).evalAt (An (e j)).param = ((u : A) : L) * (Q j 2).evalAt (An (e j)).param)
    (hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Q j 0).evalAt (An (e j)).param * (Q j 1).evalAt (An (e j)).param =
        (Q j 2).evalAt (An (e j)).param * (Q j 3).evalAt (An (e j)).param * (1 + ((t : A) : L)))
    (hkG : (k : ℤ) • (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
        - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) ∈
      Divisor.principal (K := L) (F := F)) :
    (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
        - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) ∈
      Divisor.principal (K := L) (F := F) := by
  classical

  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; rw [h0, Nat.cast_zero] at hk; exact not_isUnit_zero hk
    · exact h0
  haveI hdomA₀ : IsDomain D.A₀ := Function.Injective.isDomain D.ι D.ι_injective
  have hdim : Ring.KrullDimLE 1 D.A₀ := by
    haveI : ValuationRing D.A₀ := valuationRing_of_range_eq_inter A D.ι D.ι_injective D.K₀ D.range_ι
    haveI : IsPrincipalIdealRing D.A₀ := inferInstance
    exact Ring.KrullDimLE.mk₁' (fun I hI hp => IsPrime.to_maximal_ideal (hpi := hp) hI)

  obtain ⟨g, hg0, hgdiv⟩ := Divisor.mem_principal.mp hkG
  have hkG' : ∀ P : Place L F, P.ord g = (k : ℤ) *
      (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P := by
    intro P
    rw [← hgdiv P, Finsupp.smul_apply, smul_eq_mul]

  obtain ⟨r, U, h, hU, hh, hdiv, hcoc, hv1, hv2⟩ :=
    AlgebraicCurve.exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_balanced_of_semistableModel
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus M
      Gi hGi hred e nq Q hQ hrad hbal

  obtain ⟨c, hc0, hcunit, hcslope⟩ :=
    AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus M
      Gi hGi hred e nq Q hQ hrad hbal k hkpos g hg0 hkG' r U h hU hh hdiv hcoc

  have hΛ : ∀ s : F, ∃ Λ : Finset L, s ∈ Subfield.closure ((D.F₀ : Set F) ∪ (algebraMap L F) '' (↑Λ : Set L)) :=
    fun s => AlgebraicCurve.SemistableModel.Descent.exists_finset_mem_subfieldClosure_union_image_algebraMap M D s
  choose Λf hΛf using hΛ
  let S' : Finset F := insert g (Finset.univ.image h)
  let Λ : Finset L := S'.biUnion Λf ∪ Finset.univ.image c

  obtain ⟨K₁, hfin, hΛK, hnoeth, hhens, j₁, ι₁, hjloc, hι₁loc, hι₁inj, hcomp, hres, hpin, hdvr⟩ :=
    ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
      A D.A₀ hdim D.ι D.ι_injective D.K₀ D.range_ι D.residue_comp_surjective Λ
  have range_ι₁ : Set.range (fun a : ↥(A.comap (algebraMap K₁ L)) => ((ι₁ a : A) : L)) =
      (A : Set L) ∩ ((K₁.toSubfield : Subfield L) : Set L) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨(ι₁ a).2, ?_⟩
      show ((ι₁ a : A) : L) ∈ (K₁.toSubfield : Subfield L)
      rw [hpin a]
      exact (a : K₁).2
    · rintro ⟨hyA, hyK⟩
      have hk : (⟨y, hyK⟩ : K₁) ∈ A.comap (algebraMap K₁ L) := by
        rw [ValuationSubring.mem_comap]; exact hyA
      refine ⟨⟨⟨y, hyK⟩, hk⟩, ?_⟩
      show ((ι₁ ⟨⟨y, hyK⟩, hk⟩ : A) : L) = y
      rw [hpin]; rfl

  haveI := hι₁loc; haveI := hjloc; haveI := hnoeth; haveI := hhens; haveI := hfin
  obtain ⟨X₁, hX₁, f₁, hprop, hflat, e₁, he₁, hnorm₁, F₁, φ₁, hF₀, hK₁, halg, hgen, hcompat⟩ :=
    AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
      M D ↥(A.comap (algebraMap K₁ L)) j₁ ι₁ hι₁inj hcomp K₁.toSubfield range_ι₁
  haveI := hX₁; haveI := hprop; haveI := hflat

  have hS'F₁ : ∀ s ∈ S', s ∈ F₁ := by
    intro s hs
    refine (Subfield.closure_le.mpr ?_) (hΛf s)
    rintro z (hz | ⟨x, hx, rfl⟩)
    · exact hF₀ hz
    · refine hK₁ x ?_
      have hxΛ : x ∈ (↑Λ : Set L) := by
        simp only [Λ, Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
        exact Or.inl ⟨s, hs, hx⟩
      exact hΛK hxΛ
  have hgF₁ : g ∈ F₁ := hS'F₁ g (Finset.mem_insert_self _ _)
  have hhF₁ : ∀ a, h a ∈ F₁ := fun a =>
    hS'F₁ (h a) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem h (Finset.mem_univ a)))
  have hcK₁ : ∀ i, c i ∈ K₁ := fun i => hΛK (by
    simp only [Λ, Finset.coe_union, Set.mem_union, Finset.coe_image]
    exact Or.inr ⟨i, Finset.mem_univ i, rfl⟩)

  obtain ⟨c₀, hc₀F₁, g₁, r₁, U₁, h₁, hc₀, hg₁def, hg₁0, halgcl, hk₁, hU₁, hh₁, hdiv₁, hcoc₁, hconn₁⟩ :=
    AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus M D
      k hk Gi hGi hred e nq Q hQ hrad hbal g hg0 hkG' r U h hU hh hdiv hcoc hv1 hv2 c hc0 hcunit hcslope
      K₁ j₁ ι₁ hι₁inj hcomp hres hpin hdvr X₁ f₁ e₁ he₁ hnorm₁ F₁ φ₁ hF₀ hK₁ halg ⟨hgen, hcompat⟩ hgF₁ hhF₁ hcK₁
  haveI := halgcl

  have hC3 := AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
    f₁ hnorm₁ k hk₁ g₁ hg₁0 r₁ U₁ hU₁ h₁ hh₁ hdiv₁ hcoc₁ hconn₁
  obtain ⟨hfinπ, hetπ, s₀, hs₀⟩ := hC3
  haveI := hfinπ; haveI := hetπ

  obtain ⟨s, hs, -⟩ :=
    AlgebraicGeometry.exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
      f₁ _ s₀ hs₀

  obtain ⟨f₀, hf₀⟩ := AlgebraicGeometry.exists_pow_eq_of_section_fromNormalization_kummer k g₁ hg₁0 s hs

  let fF : F := ((φ₁.symm f₀ : F₁) : F)
  have hfF : fF ^ k = c₀ • g := by
    have h1 : φ₁.symm (f₀ ^ k) = φ₁.symm g₁ := by rw [hf₀]
    rw [map_pow, hg₁def, RingEquiv.symm_apply_apply] at h1
    have h2 := congrArg (fun x : F₁ => (x : F)) h1
    simpa using h2

  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c₀ hkpos
  have hd0 : d ≠ 0 := by
    intro h0; apply hc₀; rw [← hd, h0, zero_pow hkpos.ne']
  let uF : F := fF / algebraMap L F d
  have huF : uF ^ k = g := by
    have hdF : algebraMap L F d ≠ 0 := (map_ne_zero _).mpr hd0
    show (fF / algebraMap L F d) ^ k = g
    rw [div_pow, hfF, ← map_pow, hd, Algebra.smul_def]
    have hc₀F : algebraMap L F c₀ ≠ 0 := (map_ne_zero _).mpr hc₀
    field_simp
  have huF0 : uF ≠ 0 := by
    intro h0; apply hg0; rw [← huF, h0, zero_pow hkpos.ne']

  refine Divisor.mem_principal.mpr ⟨uF, huF0, fun P => ?_⟩
  have h1 := hkG' P
  rw [← huF] at h1
  have h2 : P.ord (uF ^ k) = (k : ℤ) * P.ord uF := by
    rw [← zpow_natCast, P.ord_zpow]
  rw [h2] at h1
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
  exact (mul_left_cancel₀ hk0 h1).symm

end S_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
end P2MW
export P2MW.S_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent (solution)
