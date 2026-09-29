-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0867e002-15b6-5ebc-9320-4cd58bbf3142

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map
import Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType MvFormalGroup.instIsCommAddMv CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex"
p2m_attr_erase "instance" "CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction CerednikDrinfeld.FormalODModule.isComm MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor"
p2m_attr_erase "instance" "AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec AlgebraicGeometry.Scheme.nilpPoints_map_val LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply"
p2m_attr_erase "simp" "LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply CerednikDrinfeld.SpecialFormal.Rigidified.mk.injEq CerednikDrinfeld.FormalODModule.actRingHom_apply CerednikDrinfeld.SpecialFormalODModule.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.Hom.mk.injEq CerednikDrinfeld.FormalODModule.map_id CerednikDrinfeld.SpecialFormal.Series.map_id CerednikDrinfeld.SpecialFormal.Rigidified.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.twist_obj CerednikDrinfeld.SpecialFormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.map_varpi CerednikDrinfeld.FormalODModule.map_act"
p2m_attr_erase "simp" "CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.injEq CerednikDrinfeld.FormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.Hom.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.map_F CerednikDrinfeld.SpecialFormal.Rigidified.map_n CerednikDrinfeld.SpecialFormal.Rigidified.map_ρ CerednikDrinfeld.SpecialFormal.IsLawHom.toHom_toPowerSeries CerednikDrinfeld.SpecialFormal.Series.map_ringHom_id CerednikDrinfeld.FormalODModule.actEnd_toPowerSeries CerednikDrinfeld.SpecialFormal.Rigidified.map_X CerednikDrinfeld.FormalODModule.varpiEnd_toPowerSeries CerednikDrinfeld.FormalODModule.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec"
p2m_attr_erase "simp" "CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd GoodReductionJacobian.BareDeformation.mk.sizeOf_spec GoodReductionJacobian.BareDeformation.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace K1NonDeg16

open _root_.AlgebraicGeometry.Scheme.Modules in

theorem transport_conj {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g) {M M' : A.Modules} (α : M ≅ M') :
    (((Scheme.Modules.pullback g).mapIso α).symm ≪≫ (transportIso h M).symm ≪≫
      (Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullback g).mapIso α) ≪≫ transportIso h M').hom = 𝟙 _ := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, transportIso, Iso.trans_inv,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  have n1 := (Scheme.Modules.pullbackComp T g).inv.naturality α.hom
  have n2 := (Scheme.Modules.pullbackCongr h).hom.naturality α.hom
  simp only [Functor.comp_map] at n1

  erw [reassoc_of% n1.symm]
  erw [Iso.inv_hom_id_app_assoc]
  erw [n2]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

theorem isConstScalar_id {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (M : A.Modules) : IsConstScalar f (𝟙 M) (1 : k) := by
  intro U s
  simp [map_one, one_smul]

theorem eq_of_isConstScalar {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} {σ τ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) (hτ : IsConstScalar f τ c) : σ = τ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rw [hσ U s, hτ U s]

theorem eq_id_of_isConstScalar_one {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} {σ : M ⟶ M} (hσ : IsConstScalar f σ 1) : σ = 𝟙 M :=
  eq_of_isConstScalar f hσ (isConstScalar_id f M)

theorem isConstScalar_conj {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M N : A.Modules} (e : N ≅ M) {σ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) :
    IsConstScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [hσ U, Scheme.Modules.Hom.app_smul]
  congr 1
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end K1NonDeg16

open K1NonDeg16 in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0) (Q : L.AlgPoints hc k) (hQ : n • Q = 0) :
    (∀ P : L.AlgPoints hc k, n • P = 0 →
        IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) 1) ↔
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) := by
  classical
  constructor
  · intro H

    have h𝓜 : Scheme.Modules.IsInvertible
        ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛) :=
      Scheme.Modules.IsInvertible.pullback _ h𝓛
    have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) :=
      Scheme.Modules.IsInvertible.pullback _ h𝓛

    obtain ⟨hx0, β₀, -⟩ := H 0 (smul_zero _)

    have hinv : ∀ (P : L.AlgPoints hc k), n • P = 0 →
        ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
          (transportIso hx ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛)).symm ≪≫
            (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso β₀ ≪≫
              transportIso hx 𝓛 = β₀ := by
      intro P hP hx
      obtain ⟨hx', βP, hσ⟩ := H P hP

      have h1 := eq_id_of_isConstScalar_one f hσ
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h1
      have eΦ : (transportIso hx ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛)).inv ≫
          (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).map βP.hom ≫ (transportIso hx 𝓛).hom =
            βP.hom := by
        have := congrArg (fun γ => βP.hom ≫ γ) h1
        simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using this

      obtain ⟨c, hcu, -⟩ := AlgebraicGeometry.RiemannForm.existsUnique_isConstScalar k f hA _ hN (βP.inv ≫ β₀.hom)
      have hΨ : IsConstScalar f ((transportIso hx 𝓛).inv ≫
          (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).map (βP.inv ≫ β₀.hom) ≫
            (transportIso hx 𝓛).hom) c := by
        have h2 := AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map k f
          (translation f L (RelativeGroupLaw.AlgPoints.toPoint P)) (translation_over f L _) hcu
        have h3 := isConstScalar_conj f (transportIso hx 𝓛).symm h2
        simpa only [Iso.symm_hom, Iso.symm_inv, Category.assoc] using h3
      have eΨ := eq_of_isConstScalar f hΨ hcu

      apply Iso.ext
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      have hsplit : β₀.hom = βP.hom ≫ (βP.inv ≫ β₀.hom) := by simp
      conv_lhs => rw [hsplit]
      rw [Functor.map_comp, Category.assoc]
      rw [← Category.id_comp ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).map (βP.inv ≫ β₀.hom)),
        ← (transportIso hx 𝓛).hom_inv_id]
      simp only [Category.assoc]
      rw [reassoc_of% eΦ, eΨ]
      simp

    obtain ⟨α, -⟩ :=
      AlgebraicGeometry.RiemannForm.exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
        k f L hc hA _ 𝓛 h𝓜 h𝓛 g hdim n hn β₀ hinv
    exact ⟨α⟩
  · rintro ⟨α⟩ P hP
    have hx := AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc P n hP
    refine ⟨hx, (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso α, ?_⟩
    rw [transport_conj hx α]
    exact isConstScalar_id f _

end S_AlgebraicGeometry_RiemannForm_forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso (solution)
