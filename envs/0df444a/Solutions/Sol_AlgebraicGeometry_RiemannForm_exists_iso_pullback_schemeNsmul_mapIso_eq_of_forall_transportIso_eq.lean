-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/da1f755c-f84b-5f18-8320-41cd95667f15

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Theorems.Thm_AlgebraicGeometry_RiemannForm_map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType MvFormalGroup.instIsCommAddMv CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction CerednikDrinfeld.FormalODModule.isComm MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec AlgebraicGeometry.Scheme.nilpPoints_map_val LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk"
p2m_attr_erase "simp" "CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply CerednikDrinfeld.SpecialFormal.Rigidified.mk.injEq CerednikDrinfeld.FormalODModule.actRingHom_apply CerednikDrinfeld.SpecialFormalODModule.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.Hom.mk.injEq CerednikDrinfeld.FormalODModule.map_id CerednikDrinfeld.SpecialFormal.Series.map_id CerednikDrinfeld.SpecialFormal.Rigidified.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.twist_obj CerednikDrinfeld.SpecialFormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.map_varpi CerednikDrinfeld.FormalODModule.map_act CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.injEq CerednikDrinfeld.FormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.Hom.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.map_F CerednikDrinfeld.SpecialFormal.Rigidified.map_n CerednikDrinfeld.SpecialFormal.Rigidified.map_ρ CerednikDrinfeld.SpecialFormal.IsLawHom.toHom_toPowerSeries CerednikDrinfeld.SpecialFormal.Series.map_ringHom_id CerednikDrinfeld.FormalODModule.actEnd_toPowerSeries CerednikDrinfeld.SpecialFormal.Rigidified.map_X CerednikDrinfeld.FormalODModule.varpiEnd_toPowerSeries CerednikDrinfeld.FormalODModule.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg"
p2m_attr_erase "simp" "MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"
p2m_attr_erase "simp" "ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd GoodReductionJacobian.BareDeformation.mk.sizeOf_spec GoodReductionJacobian.BareDeformation.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace InvIsoDesc16

theorem descendOfKey {A : Scheme.{0}} (nn : A ⟶ A) [IsAffineHom nn] [Flat nn] [Surjective nn]
    (𝓜 𝓜' : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (β : (Scheme.Modules.pullback nn).obj 𝓜 ≅ (Scheme.Modules.pullback nn).obj 𝓜')
    (key : ∀ ⦃Y : Scheme.{0}⦄ (q : Y ⟶ A) ⦃i₁ i₂ : Unit⦄ (f₁ f₂ : Y ⟶ A)
      (hf₁ : f₁ ≫ (fun _ : Unit => nn) i₁ = q) (hf₂ : f₂ ≫ (fun _ : Unit => nn) i₂ = q),
      (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.map β.hom ≫
          ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj 𝓜').hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
        ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj 𝓜).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
          (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.map β.hom) :
    ∃ α : 𝓜 ≅ 𝓜', (Scheme.Modules.pullback nn).mapIso α = β := by
  have hbij := AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    nn 𝓜 𝓜' h𝓜 h𝓜'
  have hbij' := AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    nn 𝓜' 𝓜 h𝓜' h𝓜
  have hbij₁ := AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    nn 𝓜 𝓜 h𝓜 h𝓜
  have hbij₂ := AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    nn 𝓜' 𝓜' h𝓜' h𝓜'
  let E : (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj 𝓜 ≅ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj 𝓜' :=
    Pseudofunctor.DescentData.isoMk (fun _ => β) key
  obtain ⟨a, ha⟩ := hbij.2 E.hom
  obtain ⟨b, hb⟩ := hbij'.2 E.inv
  have hab : a ≫ b = 𝟙 _ := hbij₁.1 (a₁ := a ≫ b) (a₂ := 𝟙 _)
    (by rw [Functor.map_comp, ha, hb, E.hom_inv_id, CategoryTheory.Functor.map_id])
  have hba : b ≫ a = 𝟙 _ := hbij₂.1 (a₁ := b ≫ a) (a₂ := 𝟙 _)
    (by rw [Functor.map_comp, hb, ha, E.inv_hom_id, CategoryTheory.Functor.map_id])
  refine ⟨⟨a, b, hab, hba⟩, ?_⟩
  apply Iso.ext
  have := congrArg (fun Φ => Pseudofunctor.DescentData.Hom.hom Φ ()) ha
  exact this

end InvIsoDesc16

open InvIsoDesc16 in
open TopologicalSpace in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 𝓜' : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (β : (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓜 ≅ (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓜')
    (hβ : ∀ (P : L.AlgPoints hc k), n • P = 0 →
      ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
        (transportIso hx 𝓜).symm ≪≫
          (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso β ≪≫
            transportIso hx 𝓜' = β) :
    ∃ α : 𝓜 ≅ 𝓜', (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso α = β := by
  classical
  have hunit : IsUnit (n : k) := isUnit_iff_ne_zero.2 hn
  obtain ⟨hfin, hflat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit L hA (fun t x y => hc t x y) n hunit
  haveI := hfin
  haveI := hflat
  haveI : Smooth f := hA.smooth
  let s₀ : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
  have hfib : f.base ⁻¹' {s₀} = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    show f.base a = s₀
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace ↥A := ⟨by rw [← hfib]; exact (hA.connectedFibres s₀).isPreconnected⟩
  haveI : Nonempty ↥A := by
    obtain ⟨a, -⟩ := (hA.connectedFibres s₀).nonempty
    exact ⟨a⟩
  haveI : IsIntegral A := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
  haveI : Surjective (L.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field L hc n
  have HSQ : ∀ (P : L.AlgPoints hc k), n • P = 0 →
      ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
        (transportIso hx 𝓜).inv ≫ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).map β.hom =
          β.hom ≫ (transportIso hx 𝓜').inv := by
    intro P hP hx
    have e := congrArg Iso.hom (hβ P hP hx)
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at e
    rw [Iso.eq_comp_inv, Category.assoc]
    exact e
  exact descendOfKey (L.schemeNsmul n) 𝓜 𝓜' h𝓜 h𝓜' β
    (AlgebraicGeometry.RiemannForm.map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq k f L hc hA 𝓜 𝓜' g hdim n hn β.hom HSQ)

end S_AlgebraicGeometry_RiemannForm_exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq (solution)
