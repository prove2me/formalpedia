-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_widthOne_covering_equiv_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/da2a2fc0-a860-5017-9e1f-0294700b1428

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u v

p2m_open "AlgebraicCurve~genus IsLocalRing"

noncomputable section

namespace WidthOneEquivT

section PlaceCongr

variable {K S T : Type*} [Field K] [Field S] [Field T] [Algebra K S] [Algebra K T]
variable (e : S ≃+* T) (he : ∀ a : K, e (algebraMap K S a) = algebraMap K T a)

theorem mem_congrRingEquiv_iff (v : Place K S) (x : S) :
    e x ∈ (Place.congrRingEquiv e he v).toValuationSubring ↔ x ∈ v.toValuationSubring := by
  rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  show e.symm (e x) ∈ _ ↔ _
  rw [e.symm_apply_apply]

theorem congrResidueAlgEquiv_residue (v : Place K S) (x : v.toValuationSubring) :
    Place.congrResidueAlgEquiv e he v (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (Place.comapSymmRingEquiv e v.toValuationSubring x) := by
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem isRational_congrRingEquiv_iff (v : Place K S) :
    (Place.congrRingEquiv e he v).IsRational ↔ v.IsRational := by
  unfold Place.IsRational
  have hcomm : (algebraMap K (Place.congrRingEquiv e he v).ResidueField) =
      (Place.congrResidueAlgEquiv e he v).toAlgHom.toRingHom.comp (algebraMap K v.ResidueField) := by
    ext a
    simp
  rw [hcomm, RingHom.coe_comp]
  constructor
  · intro h
    exact (Function.Surjective.of_comp_iff' (Place.congrResidueAlgEquiv e he v).bijective _).mp h
  · intro h
    exact (Place.congrResidueAlgEquiv e he v).surjective.comp h

end PlaceCongr

section ChartCongr

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {S T : Type*} [Field S] [Field T] [Algebra (ResidueField A) S] [Algebra (ResidueField A) T]
variable (e : S ≃+* T) (he : ∀ a : ResidueField A, e (algebraMap (ResidueField A) S a) = algebraMap (ResidueField A) T a)

def chartCongr (C : ComponentChart A F S) : ComponentChart A F T where
  integers := C.integers
  residue := e.toRingHom.comp C.residue
  dom := C.dom
  nodes := C.nodes.map (Place.congrEquiv e he).toEmbedding
  placeMap := fun P => Place.congrRingEquiv e he (C.placeMap P)
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := e.surjective.comp C.residue_surjective
  ker_residue := by rw [RingHom.ker_equiv_comp]; exact C.ker_residue
  residue_algebraMap := fun a => by
    show e (C.residue _) = _
    rw [C.residue_algebraMap, he]
  exists_smul_mem := fun f hf => by
    obtain ⟨c, h, hne⟩ := C.exists_smul_mem f hf
    exact ⟨c, h, (map_ne_zero_iff _ e.injective).mpr hne⟩
  placeMap_not_mem_nodes := fun P hP h => by
    rw [Finset.mem_map] at h
    obtain ⟨x, hx, hxe⟩ := h
    have : x = C.placeMap P := (Place.congrEquiv e he).injective hxe
    exact C.placeMap_not_mem_nodes P hP (this ▸ hx)
  pointwise := fun P hP hrat f hf hfib => by
    obtain ⟨hm, h, heq⟩ := C.pointwise P hP hrat f hf
      (fun w hw hpw => hfib w hw (congrArg (Place.congrRingEquiv e he) hpw))
    refine ⟨(mem_congrRingEquiv_iff e he _ _).mpr hm, h, ?_⟩
    have := congrArg (Place.congrResidueAlgEquiv e he (C.placeMap P)) heq
    rw [AlgEquiv.commutes, congrResidueAlgEquiv_residue] at this
    exact this
  mapDomain_placeMap := fun f hf D hD hD0 Q' hQ' => by
    obtain ⟨Q, rfl⟩ := (Place.congrEquiv e he).surjective Q'
    have hQ : Q ∉ C.nodes := fun h => hQ' (Finset.mem_map_of_mem _ h)
    have hf0 : C.residue f ≠ 0 := fun h0 => hf (by show e (C.residue f) = 0; rw [h0, map_zero])
    have hcomp : (fun P => Place.congrRingEquiv e he (C.placeMap P)) =
        (Place.congrEquiv e he) ∘ C.placeMap := rfl
    rw [hcomp, Finsupp.mapDomain_comp, Finsupp.mapDomain_apply (Place.congrEquiv e he).injective,
      C.mapDomain_placeMap f hf0 D hD hD0 Q hQ]
    exact (Place.ord_congrRingEquiv e he Q (C.residue f)).symm

@[scoped simp] theorem chartCongr_integers (C : ComponentChart A F S) : (chartCongr e he C).integers = C.integers := rfl
@[scoped simp] theorem chartCongr_dom (C : ComponentChart A F S) : (chartCongr e he C).dom = C.dom := rfl
theorem chartCongr_residue (C : ComponentChart A F S) (x : C.integers) :
    (chartCongr e he C).residue x = e (C.residue x) := rfl
theorem chartCongr_placeMap (C : ComponentChart A F S) (P : Place L F) :
    (chartCongr e he C).placeMap P = Place.congrRingEquiv e he (C.placeMap P) := rfl
theorem mem_chartCongr_nodes (C : ComponentChart A F S) (x' : Place (ResidueField A) T) :
    x' ∈ (chartCongr e he C).nodes ↔ ∃ x ∈ C.nodes, Place.congrRingEquiv e he x = x' := by
  show x' ∈ C.nodes.map _ ↔ _
  rw [Finset.mem_map]
  rfl
theorem congr_mem_chartCongr_nodes (C : ComponentChart A F S) (x : Place (ResidueField A) S) :
    Place.congrRingEquiv e he x ∈ (chartCongr e he C).nodes ↔ x ∈ C.nodes := by
  rw [mem_chartCongr_nodes]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← (Place.congrEquiv e he).injective hxy]
  · exact fun h => ⟨x, h, rfl⟩

theorem isAttached_chartCongr {An : Annulus A F} {C : ComponentChart A F S} {x : Place (ResidueField A) S}
    (h : An.IsAttached C x) : An.IsAttached (chartCongr e he C) (Place.congrRingEquiv e he x) := by
  obtain ⟨hx, hz, hord, hslope⟩ := h
  refine ⟨(congr_mem_chartCongr_nodes e he C x).mpr hx, hz, ?_, ?_⟩
  · rw [chartCongr_residue, Place.ord_congrRingEquiv]; exact hord
  · intro f hf hne hzero P hP
    simp only [chartCongr_residue, EmbeddingLike.map_ne_zero_iff] at hne
    rw [chartCongr_residue, Place.ord_congrRingEquiv]
    exact hslope f hf hne hzero P hP

theorem discFibres_chartCongr (C : ComponentChart A F S)
    (hdisc : ∀ Q : Place (ResidueField A) S, Q ∉ C.nodes →
      ∃ (T' : F) (hT : T' ∈ C.integers), C.residue ⟨T', hT⟩ ≠ 0 ∧ Q.ord (C.residue ⟨T', hT⟩) = 1 ∧
        (∀ P ∈ C.dom, C.placeMap P = Q → T' ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T' ∈ A, (⟨P.evalAt T', h⟩ : A) ∈ maximalIdeal A) ∧
        ∀ c : A, c ∈ maximalIdeal A →
          ∃! P : Place L F, P ∈ C.dom ∧ C.placeMap P = Q ∧ P.evalAt T' = c) :
    ∀ Q : Place (ResidueField A) T, Q ∉ (chartCongr e he C).nodes →
      ∃ (T' : F) (hT : T' ∈ (chartCongr e he C).integers),
        (chartCongr e he C).residue ⟨T', hT⟩ ≠ 0 ∧ Q.ord ((chartCongr e he C).residue ⟨T', hT⟩) = 1 ∧
        (∀ P ∈ (chartCongr e he C).dom, (chartCongr e he C).placeMap P = Q → T' ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T' ∈ A, (⟨P.evalAt T', h⟩ : A) ∈ maximalIdeal A) ∧
        ∀ c : A, c ∈ maximalIdeal A →
          ∃! P : Place L F, P ∈ (chartCongr e he C).dom ∧ (chartCongr e he C).placeMap P = Q ∧
            P.evalAt T' = c := by
  intro Q' hQ'
  obtain ⟨Q, rfl⟩ := (Place.congrEquiv e he).surjective Q'
  have hQ : Q ∉ C.nodes := fun h => hQ' ((congr_mem_chartCongr_nodes e he C Q).mpr h)
  obtain ⟨T', hT, hne, hord, hfib, huniq⟩ := hdisc Q hQ
  have hinj : ∀ P, (chartCongr e he C).placeMap P = Place.congrEquiv e he Q ↔ C.placeMap P = Q := fun P =>
    (Place.congrEquiv e he).injective.eq_iff
  refine ⟨T', hT, ?_, ?_, ?_, ?_⟩
  · rw [chartCongr_residue]; exact (map_ne_zero_iff _ e.injective).mpr hne
  · rw [chartCongr_residue, Place.congrEquiv_apply, Place.ord_congrRingEquiv]; exact hord
  · intro P hP hPQ
    exact hfib P hP ((hinj P).mp hPQ)
  · intro c hc
    simp_rw [hinj]
    exact huniq c hc

end ChartCongr

section ULiftCurve

universe w
variable (K X : Type*) [Field K] [Field X] [Algebra K X]

def upEquiv : X ≃+* ULift.{w} X := (ULift.ringEquiv : ULift.{w} X ≃+* X).symm

theorem upEquiv_comm (a : K) : upEquiv X (algebraMap K X a) = algebraMap K (ULift.{w} X) a := rfl

theorem isCurveOver_ulift [h : IsCurveOver K X] : IsCurveOver K (ULift.{w} X) := by
  have hprin : HasPrincipalDivisors K (ULift.{w} X) := by
    refine ⟨fun f' hf' => ?_⟩
    have hf : (upEquiv X).symm f' ≠ 0 := by simpa using hf'
    obtain ⟨D, hD, hdeg⟩ := h.toHasPrincipalDivisors.exists_divisor _ hf
    refine ⟨Divisor.congr (upEquiv X) (upEquiv_comm K X) D, fun v' => ?_, by rw [Divisor.degree_congr]; exact hdeg⟩
    obtain ⟨v, rfl⟩ := (Place.congrEquiv (upEquiv X) (upEquiv_comm K X)).surjective v'
    rw [Place.congrEquiv_apply, Divisor.congr_apply_place_congr, hD v]
    conv_rhs => rw [← (upEquiv X : X ≃+* ULift.{w} X).apply_symm_apply f']
    exact (Place.ord_congrRingEquiv (upEquiv X) (upEquiv_comm K X) v _).symm
  have hfin : ∀ v' : Place K (ULift.{w} X), Module.Finite K v'.ResidueField := by
    intro v'
    obtain ⟨v, rfl⟩ := (Place.congrEquiv (upEquiv X) (upEquiv_comm K X)).surjective v'
    haveI := h.finiteResidue v
    exact Module.Finite.equiv (Place.congrResidueAlgEquiv (upEquiv X) (upEquiv_comm K X) v).toLinearEquiv
  have hrank : Module.finrank (ULift.{w} X) (Ω[ULift.{w} X⁄K]) = 1 := by
    haveI : Algebra.FormallyEtale X (ULift.{w} X) :=
      Algebra.FormallyEtale.of_equiv (ULift.algEquiv : ULift.{w} X ≃ₐ[X] X).symm
    haveI := h.kaehler_free_rank_one.1
    have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K X (ULift.{w} X)).finrank_eq
    rw [Module.finrank_baseChange, h.kaehler_free_rank_one.2] at h1
    exact h1.symm
  exact { toHasPrincipalDivisors := hprin, finiteResidue := hfin,
          kaehler_free_rank_one := ⟨Module.Free.of_divisionRing _ _, hrank⟩ }

theorem essFiniteType_ulift [Algebra.EssFiniteType K X] : Algebra.EssFiniteType K (ULift.{w} X) :=
  (Algebra.EssFiniteType.iff_of_algEquiv (ULift.algEquiv : ULift.{w} X ≃ₐ[K] X).symm).mp inferInstance

theorem isRational_ulift (hrat : ∀ Q : Place K X, Q.IsRational) (Q : Place K (ULift.{w} X)) : Q.IsRational := by
  obtain ⟨v, rfl⟩ := (Place.congrEquiv (upEquiv X) (upEquiv_comm K X)).surjective Q
  exact (isRational_congrRingEquiv_iff (upEquiv X) (upEquiv_comm K X) v).mpr (hrat v)

end ULiftCurve

section RatFuncFacts

variable (K : Type*) [Field K]

theorem essFiniteType_ratFunc : Algebra.EssFiniteType K (RatFunc K) := by
  haveI : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
  exact Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)

theorem X_mem_placeOfPoint_zero :
    (RatFunc.X : RatFunc K) ∈ (RationalFunctionField.placeOfPoint K 0).toValuationSubring := by
  rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum, ← RatFunc.algebraMap_X]
  exact RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K _ _

end RatFuncFacts

section Vertex

variable {L : Type u} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
variable {n m : ℕ} (Fbar : Fin n → Type v) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (w : Fin m → ℕ)

def FbarV : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)) → Type (max u v)
  | Sum.inl i => ULift.{u, v} (Fbar i)
  | Sum.inr _ => ULift.{v, u} (RatFunc (ResidueField A))

scoped instance instFieldFbarV : (x : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))) → Field (FbarV A Fbar w x)
  | Sum.inl i => inferInstanceAs (Field (ULift.{u, v} (Fbar i)))
  | Sum.inr _ => inferInstanceAs (Field (ULift.{v, u} (RatFunc (ResidueField A))))

scoped instance instAlgebraFbarV : (x : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))) → Algebra (ResidueField A) (FbarV A Fbar w x)
  | Sum.inl i => inferInstanceAs (Algebra (ResidueField A) (ULift.{u, v} (Fbar i)))
  | Sum.inr _ => inferInstanceAs (Algebra (ResidueField A) (ULift.{v, u} (RatFunc (ResidueField A))))

def eInl (i : Fin n) : Fbar i ≃+* FbarV A Fbar w (Sum.inl i) := upEquiv (Fbar i)

theorem eInl_comm (i : Fin n) (a : ResidueField A) :
    eInl A Fbar w i (algebraMap (ResidueField A) (Fbar i) a) = algebraMap (ResidueField A) (FbarV A Fbar w (Sum.inl i)) a :=
  rfl

def eInr (v' : Σ e : Fin m, Fin (w e - 1)) : RatFunc (ResidueField A) ≃+* FbarV A Fbar w (Sum.inr v') :=
  upEquiv (RatFunc (ResidueField A))

theorem eInr_comm (v' : Σ e : Fin m, Fin (w e - 1)) (a : ResidueField A) :
    eInr A Fbar w v' (algebraMap (ResidueField A) (RatFunc (ResidueField A)) a) =
      algebraMap (ResidueField A) (FbarV A Fbar w (Sum.inr v')) a :=
  rfl

def plS (i : Fin n) (x : Place (ResidueField A) (Fbar i)) : Place (ResidueField A) (FbarV A Fbar w (Sum.inl i)) :=
  Place.congrRingEquiv (eInl A Fbar w i) (eInl_comm A Fbar w i) x

def plR (v' : Σ e : Fin m, Fin (w e - 1)) (x : Place (ResidueField A) (RatFunc (ResidueField A))) :
    Place (ResidueField A) (FbarV A Fbar w (Sum.inr v')) :=
  Place.congrRingEquiv (eInr A Fbar w v') (eInr_comm A Fbar w v') x

theorem plS_injective (i : Fin n) : Function.Injective (plS A Fbar w i) :=
  (Place.congrEquiv (eInl A Fbar w i) (eInl_comm A Fbar w i)).injective

theorem plR_injective (v' : Σ e : Fin m, Fin (w e - 1)) : Function.Injective (plR A Fbar w v') :=
  (Place.congrEquiv (eInr A Fbar w v') (eInr_comm A Fbar w v')).injective

variable (C : ∀ i, ComponentChart A F (Fbar i))
variable (Cc : (Σ e : Fin m, Fin (w e - 1)) → ComponentChart A F (RatFunc (ResidueField A)))

def CV : (x : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))) → ComponentChart A F (FbarV A Fbar w x)
  | Sum.inl i => chartCongr (eInl A Fbar w i) (eInl_comm A Fbar w i) (C i)
  | Sum.inr v' => chartCongr (eInr A Fbar w v') (eInr_comm A Fbar w v') (Cc v')

theorem CV_inl (i : Fin n) : CV A Fbar w C Cc (Sum.inl i) = chartCongr (eInl A Fbar w i) (eInl_comm A Fbar w i) (C i) := rfl
theorem CV_inr (v' : Σ e : Fin m, Fin (w e - 1)) :
    CV A Fbar w C Cc (Sum.inr v') = chartCongr (eInr A Fbar w v') (eInr_comm A Fbar w v') (Cc v') := rfl

variable (src tgt : Fin m → Fin n)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))
variable (Qinf : Place (ResidueField A) (RatFunc (ResidueField A)))

def sNode (ε : Σ e : Fin m, Fin (w e)) : Σ x : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)), Place (ResidueField A) (FbarV A Fbar w x) :=
  if _h0 : ε.2.1 = 0 then ⟨Sum.inl (src ε.1), plS A Fbar w (src ε.1) (xs ε.1)⟩
  else ⟨Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
    plR A Fbar w _ (RationalFunctionField.placeOfPoint (ResidueField A) 0)⟩

def tNode (ε : Σ e : Fin m, Fin (w e)) : Σ x : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)), Place (ResidueField A) (FbarV A Fbar w x) :=
  if _h1 : ε.2.1 + 1 = w ε.1 then ⟨Sum.inl (tgt ε.1), plS A Fbar w (tgt ε.1) (xt ε.1)⟩
  else ⟨Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩, plR A Fbar w _ Qinf⟩

theorem sNode_fst (ε : Σ e : Fin m, Fin (w e)) :
    (sNode A Fbar w src xs ε).1 =
      (if _h0 : ε.2.1 = 0 then Sum.inl (src ε.1) else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩) := by
  unfold sNode; split_ifs <;> rfl

theorem tNode_fst (ε : Σ e : Fin m, Fin (w e)) :
    (tNode A Fbar w tgt xt Qinf ε).1 =
      (if _h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1) else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩) := by
  unfold tNode; split_ifs <;> rfl

theorem sNode_of_eq_zero (ε : Σ e : Fin m, Fin (w e)) (h0 : ε.2.1 = 0) :
    sNode A Fbar w src xs ε = ⟨Sum.inl (src ε.1), plS A Fbar w (src ε.1) (xs ε.1)⟩ := dif_pos h0

theorem sNode_of_ne_zero (ε : Σ e : Fin m, Fin (w e)) (h0 : ε.2.1 ≠ 0) :
    sNode A Fbar w src xs ε = ⟨Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
      plR A Fbar w _ (RationalFunctionField.placeOfPoint (ResidueField A) 0)⟩ := dif_neg h0

theorem tNode_of_eq (ε : Σ e : Fin m, Fin (w e)) (h1 : ε.2.1 + 1 = w ε.1) :
    tNode A Fbar w tgt xt Qinf ε = ⟨Sum.inl (tgt ε.1), plS A Fbar w (tgt ε.1) (xt ε.1)⟩ := dif_pos h1

theorem tNode_of_ne (ε : Σ e : Fin m, Fin (w e)) (h1 : ¬ ε.2.1 + 1 = w ε.1) :
    tNode A Fbar w tgt xt Qinf ε = ⟨Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩, plR A Fbar w _ Qinf⟩ := dif_neg h1

theorem elim_eq_inl {E : (Σ e : Fin m, Fin (w e)) ⊕ (Σ e : Fin m, Fin (w e))} {i : Fin n}
    {p : Place (ResidueField A) (FbarV A Fbar w (Sum.inl i))}
    (h : Sum.elim (sNode A Fbar w src xs) (tNode A Fbar w tgt xt Qinf) E = ⟨Sum.inl i, p⟩) :
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j))) (fun e => ⟨tgt e, xt e⟩)
        (Sum.map Sigma.fst Sigma.fst E) =
      ⟨i, (Place.congrEquiv (eInl A Fbar w i) (eInl_comm A Fbar w i)).symm p⟩ ∧
    Sum.elim (fun ε : (Σ e : Fin m, Fin (w e)) => ε.2.1 = 0) (fun ε => ε.2.1 + 1 = w ε.1) E := by
  rcases E with ε | ε <;> simp only [Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr] at h ⊢
  · by_cases h0 : ε.2.1 = 0
    · rw [sNode_of_eq_zero A Fbar w src xs ε h0] at h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      cases h1
      refine ⟨?_, h0⟩
      have h3 := eq_of_heq h2
      subst h3
      congr 1
    · rw [sNode_of_ne_zero A Fbar w src xs ε h0] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
  · by_cases h1 : ε.2.1 + 1 = w ε.1
    · rw [tNode_of_eq A Fbar w tgt xt Qinf ε h1] at h
      obtain ⟨h1', h2⟩ := Sigma.mk.inj_iff.mp h
      cases h1'
      refine ⟨?_, h1⟩
      have h3 := eq_of_heq h2
      subst h3
      congr 1
    · rw [tNode_of_ne A Fbar w tgt xt Qinf ε h1] at h
      exact absurd (congrArg Sigma.fst h) (by simp)

theorem elim_eq_inr {E : (Σ e : Fin m, Fin (w e)) ⊕ (Σ e : Fin m, Fin (w e))} {v' : Σ e : Fin m, Fin (w e - 1)}
    {p : Place (ResidueField A) (FbarV A Fbar w (Sum.inr v'))}
    (h : Sum.elim (sNode A Fbar w src xs) (tNode A Fbar w tgt xt Qinf) E = ⟨Sum.inr v', p⟩) :
    (E = Sum.inl ⟨v'.1, ⟨v'.2.1 + 1, by have := v'.2.2; omega⟩⟩ ∧
        p = plR A Fbar w v' (RationalFunctionField.placeOfPoint (ResidueField A) 0)) ∨
      (E = Sum.inr ⟨v'.1, ⟨v'.2.1, by have := v'.2.2; omega⟩⟩ ∧ p = plR A Fbar w v' Qinf) := by
  rcases E with ⟨e, ⟨d, hd⟩⟩ | ⟨e, ⟨d, hd⟩⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · by_cases h0 : d = 0
    · rw [sNode_of_eq_zero A Fbar w src xs _ h0] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · rw [sNode_of_ne_zero A Fbar w src xs _ h0] at h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      have h1' := Sum.inr.inj h1
      subst h1'
      refine Or.inl ⟨?_, (eq_of_heq h2).symm⟩
      simp only [Sum.inl.injEq]
      refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
      simp only
      omega
  · by_cases h1 : d + 1 = w e
    · rw [tNode_of_eq A Fbar w tgt xt Qinf _ h1] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · rw [tNode_of_ne A Fbar w tgt xt Qinf _ h1] at h
      obtain ⟨h1', h2⟩ := Sigma.mk.inj_iff.mp h
      have h1'' := Sum.inr.inj h1'
      subst h1''
      exact Or.inr ⟨rfl, (eq_of_heq h2).symm⟩

theorem nodes_existsV (hw1 : ∀ e, 1 ≤ w e)
    (hnodes1 : ∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩)
    (hCcnodes : ∀ v', ∀ Q, Q ∈ (Cc v').nodes →
      Q = RationalFunctionField.placeOfPoint (ResidueField A) 0 ∨ Q = Qinf) :
    ∀ x, ∀ p ∈ (CV A Fbar w C Cc x).nodes,
      ∃ ε, sNode A Fbar w src xs ε = ⟨x, p⟩ ∨ tNode A Fbar w tgt xt Qinf ε = ⟨x, p⟩
  | Sum.inl i, p, hp => by
    obtain ⟨q, hq, rfl⟩ := (mem_chartCongr_nodes _ _ _ _).mp hp
    obtain ⟨e, h | h⟩ := hnodes1 i q hq
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      subst h1
      have h3 := eq_of_heq h2
      subst h3
      refine ⟨⟨e, ⟨0, hw1 e⟩⟩, Or.inl ?_⟩
      rw [sNode_of_eq_zero A Fbar w src xs _ rfl]
      rfl
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      subst h1
      have h3 := eq_of_heq h2
      subst h3
      refine ⟨⟨e, ⟨w e - 1, by have := hw1 e; omega⟩⟩, Or.inr ?_⟩
      rw [tNode_of_eq A Fbar w tgt xt Qinf _ (by have := hw1 e; simp only; omega)]
      rfl
  | Sum.inr ⟨e, ⟨j, hj⟩⟩, p, hp => by
    obtain ⟨q, hq, rfl⟩ := (mem_chartCongr_nodes _ _ _ _).mp hp
    rcases hCcnodes _ q hq with hq0 | hq0 <;> subst q
    · refine ⟨⟨e, ⟨j + 1, by omega⟩⟩, Or.inl ?_⟩
      rw [sNode_of_ne_zero A Fbar w src xs _ (by simp)]
      rfl
    · refine ⟨⟨e, ⟨j, by omega⟩⟩, Or.inr ?_⟩
      rw [tNode_of_ne A Fbar w tgt xt Qinf _ (by simp only; omega)]
      rfl

theorem nodes_uniqueV
    (hnodes2 : ∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E')
    (h0inf : RationalFunctionField.placeOfPoint (ResidueField A) 0 ≠ Qinf) :
    ∀ x, ∀ p ∈ (CV A Fbar w C Cc x).nodes,
      ∀ E E' : (Σ e : Fin m, Fin (w e)) ⊕ (Σ e : Fin m, Fin (w e)),
        Sum.elim (sNode A Fbar w src xs) (tNode A Fbar w tgt xt Qinf) E = ⟨x, p⟩ →
        Sum.elim (sNode A Fbar w src xs) (tNode A Fbar w tgt xt Qinf) E' = ⟨x, p⟩ → E = E'
  | Sum.inl i, p, hp, E, E', hE, hE' => by
    obtain ⟨hA, hd⟩ := elim_eq_inl A Fbar w src tgt xs xt Qinf hE
    obtain ⟨hA', hd'⟩ := elim_eq_inl A Fbar w src tgt xs xt Qinf hE'
    have hq : (Place.congrEquiv (eInl A Fbar w i) (eInl_comm A Fbar w i)).symm p ∈ (C i).nodes := by
      obtain ⟨q, hq, rfl⟩ := (mem_chartCongr_nodes _ _ _ _).mp hp
      rwa [← Place.congrEquiv_apply, Equiv.symm_apply_apply]
    have hEE := hnodes2 i _ hq _ _ hA hA'
    rcases E with ⟨e, ⟨d, hdd⟩⟩ | ⟨e, ⟨d, hdd⟩⟩ <;> rcases E' with ⟨e', ⟨d', hdd'⟩⟩ | ⟨e', ⟨d', hdd'⟩⟩ <;>
      simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq] at hEE hd hd' ⊢
    · subst hEE; subst hd; subst hd'; rfl
    · subst hEE
      have : d = d' := by omega
      subst this
      rfl
  | Sum.inr v', p, hp, E, E', hE, hE' => by
    rcases elim_eq_inr A Fbar w src tgt xs xt Qinf hE with ⟨rfl, hp1⟩ | ⟨rfl, hp1⟩ <;>
      rcases elim_eq_inr A Fbar w src tgt xs xt Qinf hE' with ⟨rfl, hp2⟩ | ⟨rfl, hp2⟩
    · rfl
    · exact absurd (plR_injective A Fbar w v' (hp1.symm.trans hp2)) h0inf
    · exact absurd (plR_injective A Fbar w v' (hp2.symm.trans hp1)) h0inf
    · rfl

end Vertex

section VertexFacts

variable {L : Type u} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
variable {n m : ℕ} (Fbar : Fin n → Type v) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (w : Fin m → ℕ)
variable (C : ∀ i, ComponentChart A F (Fbar i))
variable (Cc : (Σ e : Fin m, Fin (w e - 1)) → ComponentChart A F (RatFunc (ResidueField A)))
variable (src tgt : Fin m → Fin n)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))
variable (Qinf : Place (ResidueField A) (RatFunc (ResidueField A)))
variable (B B' : (Σ e : Fin m, Fin (w e)) → Annulus A F)

theorem attS
    (hatt1 : ∀ e (h0 : 0 < w e), (B ⟨e, ⟨0, h0⟩⟩).IsAttached (C (src e)) (xs e))
    (hatt3 : ∀ e (d : Fin (w e)) (hd : 0 < d.1),
      (B ⟨e, d⟩).IsAttached (Cc ⟨e, ⟨d.1 - 1, by have := d.2; omega⟩⟩)
        (RationalFunctionField.placeOfPoint (ResidueField A) 0)) :
    ∀ ε, (B ε).IsAttached (CV A Fbar w C Cc (sNode A Fbar w src xs ε).1) (sNode A Fbar w src xs ε).2 := by
  rintro ⟨e, ⟨d, hd⟩⟩
  by_cases h0 : d = 0
  · rw [sNode_of_eq_zero A Fbar w src xs _ h0]
    subst h0
    exact isAttached_chartCongr _ _ (hatt1 e hd)
  · rw [sNode_of_ne_zero A Fbar w src xs _ h0]
    exact isAttached_chartCongr _ _ (hatt3 e ⟨d, hd⟩ (Nat.pos_of_ne_zero h0))

theorem attT
    (hatt2 : ∀ e (d : Fin (w e)), d.1 + 1 = w e → (B' ⟨e, d⟩).IsAttached (C (tgt e)) (xt e))
    (hatt4 : ∀ e (d : Fin (w e)) (hd : d.1 + 1 < w e), (B' ⟨e, d⟩).IsAttached (Cc ⟨e, ⟨d.1, by omega⟩⟩) Qinf) :
    ∀ ε, (B' ε).IsAttached (CV A Fbar w C Cc (tNode A Fbar w tgt xt Qinf ε).1) (tNode A Fbar w tgt xt Qinf ε).2 := by
  rintro ⟨e, ⟨d, hd⟩⟩
  by_cases h1 : d + 1 = w e
  · rw [tNode_of_eq A Fbar w tgt xt Qinf _ h1]
    exact isAttached_chartCongr _ _ (hatt2 e ⟨d, hd⟩ h1)
  · rw [tNode_of_ne A Fbar w tgt xt Qinf _ h1]
    exact isAttached_chartCongr _ _ (hatt4 e ⟨d, hd⟩ (by simp only; omega))

theorem ratV (hratBar : ∀ i, ∀ Q : Place (ResidueField A) (Fbar i), Q.IsRational)
    (hratK : ∀ Q : Place (ResidueField A) (RatFunc (ResidueField A)), Q.IsRational) :
    ∀ x, ∀ Q : Place (ResidueField A) (FbarV A Fbar w x), Q.IsRational
  | Sum.inl i => isRational_ulift _ _ (hratBar i)
  | Sum.inr _ => isRational_ulift _ _ hratK

theorem ratDomV (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational) (hratCc : ∀ v', ∀ P ∈ (Cc v').dom, P.IsRational) :
    ∀ x, ∀ P ∈ (CV A Fbar w C Cc x).dom, P.IsRational
  | Sum.inl i => hratF i
  | Sum.inr v' => hratCc v'

theorem curveV [∀ i, IsCurveOver (ResidueField A) (Fbar i)] : ∀ x, IsCurveOver (ResidueField A) (FbarV A Fbar w x)
  | Sum.inl i => isCurveOver_ulift (ResidueField A) (Fbar i)
  | Sum.inr _ => by
    haveI := AlgebraicCurve.isCurveOver_ratFunc (ResidueField A)
    exact isCurveOver_ulift (ResidueField A) (RatFunc (ResidueField A))

theorem essV [∀ i, Algebra.EssFiniteType (ResidueField A) (Fbar i)] :
    ∀ x, Algebra.EssFiniteType (ResidueField A) (FbarV A Fbar w x)
  | Sum.inl i => essFiniteType_ulift (ResidueField A) (Fbar i)
  | Sum.inr _ => by
    haveI := essFiniteType_ratFunc (ResidueField A)
    exact essFiniteType_ulift (ResidueField A) (RatFunc (ResidueField A))

theorem genusV_inl (i : Fin n) :
    genusFF (ResidueField A) (FbarV A Fbar w (Sum.inl i)) = genusFF (ResidueField A) (Fbar i) :=
  AlgebraicCurve.genusFF_eq_of_algEquiv (ULift.algEquiv : ULift.{u, v} (Fbar i) ≃ₐ[ResidueField A] Fbar i)

theorem genusV_inr (v' : Σ e : Fin m, Fin (w e - 1)) :
    genusFF (ResidueField A) (FbarV A Fbar w (Sum.inr v')) = genusFF (ResidueField A) (RatFunc (ResidueField A)) :=
  AlgebraicCurve.genusFF_eq_of_algEquiv
    (ULift.algEquiv : ULift.{v, u} (RatFunc (ResidueField A)) ≃ₐ[ResidueField A] RatFunc (ResidueField A))

theorem discV
    (hdisc : ∀ i, ∀ Q : Place (ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ maximalIdeal A) ∧
        ∀ c : A, c ∈ maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hdiscC : ∀ v', ∀ Q : Place (ResidueField A) (RatFunc (ResidueField A)), Q ∉ (Cc v').nodes →
      ∃ (T : F) (hT : T ∈ (Cc v').integers), (Cc v').residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((Cc v').residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (Cc v').dom, (Cc v').placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ maximalIdeal A) ∧
        ∀ c : A, c ∈ maximalIdeal A →
          ∃! P : Place L F, P ∈ (Cc v').dom ∧ (Cc v').placeMap P = Q ∧ P.evalAt T = c) :
    ∀ x, ∀ Q : Place (ResidueField A) (FbarV A Fbar w x), Q ∉ (CV A Fbar w C Cc x).nodes →
      ∃ (T : F) (hT : T ∈ (CV A Fbar w C Cc x).integers),
        (CV A Fbar w C Cc x).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((CV A Fbar w C Cc x).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (CV A Fbar w C Cc x).dom, (CV A Fbar w C Cc x).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ maximalIdeal A) ∧
        ∀ c : A, c ∈ maximalIdeal A →
          ∃! P : Place L F, P ∈ (CV A Fbar w C Cc x).dom ∧ (CV A Fbar w C Cc x).placeMap P = Q ∧
            P.evalAt T = c
  | Sum.inl i => discFibres_chartCongr _ _ (C i) (hdisc i)
  | Sum.inr v' => discFibres_chartCongr _ _ (Cc v') (hdiscC v')

end VertexFacts

end WidthOneEquivT
p2m_reactivate "P2MW.S_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne.WidthOneEquivT"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne.WidthOneEquivT"

open WidthOneEquivT in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type v) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
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
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    ∃ (n' m' : ℕ) (eV : V ≃ Fin n') (eE : (Σ e : Fin m, Fin (w e)) ≃ Fin m')
      (Fbar' : Fin n' → Type (max u v)) (instF : ∀ i, Field (Fbar' i))
      (instA : ∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar' i))
      (C' : ∀ i, ComponentChart A F (Fbar' i)) (An₁ An₁' : Fin m' → Annulus A F) (src' tgt' : Fin m' → Fin n')
      (xs' : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar' (src' e)))
      (xt' : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar' (tgt' e))),

      (∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar' i), Q.IsRational) ∧
      (∀ i, ∀ P ∈ (C' i).dom, P.IsRational) ∧
      (∀ e, (An₁' e).dom = (An₁ e).dom ∧ (An₁' e).modulus = (An₁ e).modulus ∧
      ((An₁ e).modulus : L) ≠ 0 ∧
      (An₁' e).param * (An₁ e).param = algebraMap L F ((An₁ e).modulus : L)) ∧
      (∀ e, ∃ u : Aˣ, (An₁ e).modulus = u * π ^ 1) ∧
      (∀ e, (An₁ e).IsAttached (C' (src' e)) (xs' e) ∧ (An₁' e).IsAttached (C' (tgt' e)) (xt' e)) ∧
      ((∀ i, ∀ x ∈ (C' i).nodes, ∃ e,
        (⟨src' e, xs' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)) = ⟨i, x⟩ ∨
        (⟨tgt' e, xt' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C' i).nodes, ∀ E E' : Fin m' ⊕ Fin m',
        Sum.elim (fun e => (⟨src' e, xs' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)))
          (fun e => ⟨tgt' e, xt' e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src' e, xs' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)))
          (fun e => ⟨tgt' e, xt' e⟩) E' = ⟨i, x⟩ → E = E')) ∧
      (∀ P : Place L F,
      (∃ i, P ∈ (C' i).dom ∧ (∀ j, P ∈ (C' j).dom → j = i) ∧ ∀ e, P ∉ (An₁ e).dom) ∨
      (∃ e, P ∈ (An₁ e).dom ∧ (∀ e', P ∈ (An₁ e').dom → e' = e) ∧ ∀ i, P ∉ (C' i).dom)) ∧
      (∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar' i), Q ∉ (C' i).nodes →
      ∃ (T : F) (hT : T ∈ (C' i).integers), (C' i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C' i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C' i).dom, (C' i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C' i).dom ∧ (C' i).placeMap P = Q ∧ P.evalAt T = c) ∧
      (genusFF L F + n' = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar' i)) + m' + 1) ∧
      (∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar' i)) ∧
      (∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar' i)) ∧

      (∀ i : Fin n, (C' (eV (Sum.inl i))).dom = (C i).dom ∧ (C' (eV (Sum.inl i))).integers = (C i).integers) ∧
      (∀ v : (Σ e : Fin m, Fin (w e - 1)), (C' (eV (Sum.inr v))).dom =
        {P | P ∈ (An v.1).dom ∧ ∃ (u : Aˣ) (h : P.evalAt (An v.1).param ∈ A),
          (⟨P.evalAt (An v.1).param, h⟩ : A) = u * π ^ (v.2.1 + 1)}) ∧
      (∀ ε : (Σ e : Fin m, Fin (w e)), (An₁ (eE ε)).dom =
        {P | P ∈ (An ε.1).dom ∧
          A.valuation (((π : A) : L) ^ (ε.2.1 + 1)) < A.valuation (P.evalAt (An ε.1).param) ∧
          A.valuation (P.evalAt (An ε.1).param) < A.valuation (((π : A) : L) ^ ε.2.1)} ∧
        (An₁ (eE ε)).param = (algebraMap L F (((π : A) : L) ^ ε.2.1))⁻¹ * (An ε.1).param) ∧
      (∀ ε : (Σ e : Fin m, Fin (w e)), src' (eE ε) = eV (ends ε).1 ∧ tgt' (eE ε) = eV (ends ε).2) := by
  intro V ends
  obtain ⟨Cc, Qinf, B, B', hX, hCcdom, hCcnodes, -, -, hBdom, hBparam, hBpair, -, hBw, hatt1, hatt2, hatt3, hatt4,
      hcov, hdiscC, hratK, hratCc, hgen⟩ :=
    AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne A π hπ hπ0 hrk F
      n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus

  have hw1 : ∀ e, 1 ≤ w e := by
    intro e
    obtain ⟨u, hu⟩ := hw e
    by_contra h
    have h0 : w e = 0 := by omega
    rw [h0, pow_zero, mul_one] at hu
    have hunit : IsUnit (An e).modulus := by rw [hu]; exact u.isUnit
    exact (IsLocalRing.mem_maximalIdeal _).mp (An e).modulus_mem hunit

  have h0inf : RationalFunctionField.placeOfPoint (IsLocalRing.ResidueField A) 0 ≠ Qinf := fun h =>
    hX (h ▸ X_mem_placeOfPoint_zero (IsLocalRing.ResidueField A))
  have hCcnodes' : ∀ v', ∀ Q, Q ∈ (Cc v').nodes →
      Q = RationalFunctionField.placeOfPoint (IsLocalRing.ResidueField A) 0 ∨ Q = Qinf := by
    intro v' Q hQ
    classical
    rw [hCcnodes v', Finset.mem_insert, Finset.mem_singleton] at hQ
    exact hQ

  let eV : (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))) ≃ Fin (Fintype.card (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)))) :=
    Fintype.equivFin _
  let eE : (Σ e : Fin m, Fin (w e)) ≃ Fin (Fintype.card (Σ e : Fin m, Fin (w e))) := Fintype.equivFin _
  let Ψ : (Σ j : Fin (Fintype.card (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)))),
      Place (IsLocalRing.ResidueField A) (FbarV A Fbar w (eV.symm j))) ≃
      (Σ x : Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)), Place (IsLocalRing.ResidueField A) (FbarV A Fbar w x)) :=
    Equiv.sigmaCongrLeft (β := fun x => Place (IsLocalRing.ResidueField A) (FbarV A Fbar w x)) eV.symm
  let sN := sNode A Fbar w src xs
  let tN := tNode A Fbar w tgt xt Qinf
  refine ⟨Fintype.card (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))), Fintype.card (Σ e : Fin m, Fin (w e)), eV, eE,
    fun j => FbarV A Fbar w (eV.symm j), fun j => inferInstance, fun j => inferInstance,
    fun j => CV A Fbar w C Cc (eV.symm j), fun e' => B (eE.symm e'), fun e' => B' (eE.symm e'),
    fun e' => (Ψ.symm (sN (eE.symm e'))).1, fun e' => (Ψ.symm (tN (eE.symm e'))).1,
    fun e' => (Ψ.symm (sN (eE.symm e'))).2, fun e' => (Ψ.symm (tN (eE.symm e'))).2,
    fun j => ratV A Fbar w hratBar hratK (eV.symm j),
    fun j => ratDomV A Fbar w C Cc hratF hratCc (eV.symm j),
    fun e' => hBpair _, fun e' => hBw _, ?_, ⟨?_, ?_⟩, ?_,
    fun j => discV A Fbar w C Cc hdisc hdiscC (eV.symm j), ?_,
    fun j => curveV A Fbar w (eV.symm j), fun j => essV A Fbar w (eV.symm j), ?_, ?_, ?_, ?_⟩
  ·
    intro e'
    constructor
    · have h := attS A Fbar w C Cc src xs B hatt1 hatt3 (eE.symm e')
      rw [← Ψ.apply_symm_apply (sNode A Fbar w src xs (eE.symm e'))] at h
      exact h
    · have h := attT A Fbar w C Cc tgt xt Qinf B' hatt2 hatt4 (eE.symm e')
      rw [← Ψ.apply_symm_apply (tNode A Fbar w tgt xt Qinf (eE.symm e'))] at h
      exact h
  ·
    intro j x' hx'
    obtain ⟨ε, hε⟩ := nodes_existsV A Fbar w C Cc src tgt xs xt Qinf hw1 hnodes.1 hCcnodes' (eV.symm j) x' hx'
    refine ⟨eE ε, ?_⟩
    have hj : Ψ.symm ⟨eV.symm j, x'⟩ = ⟨j, x'⟩ := Ψ.symm_apply_eq.mpr rfl
    have e1 : (⟨(Ψ.symm (sN (eE.symm (eE ε)))).1, (Ψ.symm (sN (eE.symm (eE ε)))).2⟩ :
        Σ j, Place (IsLocalRing.ResidueField A) (FbarV A Fbar w (eV.symm j))) = Ψ.symm (sN ε) := by
      rw [Equiv.symm_apply_apply]
    have e2 : (⟨(Ψ.symm (tN (eE.symm (eE ε)))).1, (Ψ.symm (tN (eE.symm (eE ε)))).2⟩ :
        Σ j, Place (IsLocalRing.ResidueField A) (FbarV A Fbar w (eV.symm j))) = Ψ.symm (tN ε) := by
      rw [Equiv.symm_apply_apply]
    rcases hε with h | h
    · exact Or.inl (e1.trans ((congrArg Ψ.symm h).trans hj))
    · exact Or.inr (e2.trans ((congrArg Ψ.symm h).trans hj))
  ·
    intro j x' hx' E₁ E₂ h₁ h₂
    obtain ⟨E₁, rfl⟩ := (Equiv.sumCongr eE eE).surjective E₁
    obtain ⟨E₂, rfl⟩ := (Equiv.sumCongr eE eE).surjective E₂
    have key : ∀ E₀ : (Σ e : Fin m, Fin (w e)) ⊕ (Σ e : Fin m, Fin (w e)),
        Sum.elim (fun e' => (⟨(Ψ.symm (sN (eE.symm e'))).1, (Ψ.symm (sN (eE.symm e'))).2⟩ :
            Σ j, Place (IsLocalRing.ResidueField A) (FbarV A Fbar w (eV.symm j))))
          (fun e' => ⟨(Ψ.symm (tN (eE.symm e'))).1, (Ψ.symm (tN (eE.symm e'))).2⟩) (Equiv.sumCongr eE eE E₀) =
        Ψ.symm (Sum.elim sN tN E₀) := by
      rintro (ε | ε) <;> simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr] <;>
        rw [Equiv.symm_apply_apply]
    have hj : Ψ.symm ⟨eV.symm j, x'⟩ = ⟨j, x'⟩ := Ψ.symm_apply_eq.mpr rfl
    have h₁' : Sum.elim sN tN E₁ = ⟨eV.symm j, x'⟩ :=
      Ψ.symm.injective (((key E₁).symm.trans h₁).trans hj.symm)
    have h₂' : Sum.elim sN tN E₂ = ⟨eV.symm j, x'⟩ :=
      Ψ.symm.injective (((key E₂).symm.trans h₂).trans hj.symm)
    rw [nodes_uniqueV A Fbar w C Cc src tgt xs xt Qinf hnodes.2 h0inf (eV.symm j) x' hx' E₁ E₂ h₁' h₂']
  ·
    intro P
    rcases hcov P with ⟨i, hPi, huniq, hnotCc, hnotB⟩ | ⟨v', hPv, huniq, hnotC, hnotB⟩ | ⟨ε, hPε, huniq, hnotC, hnotCc⟩
    · refine Or.inl ⟨eV (Sum.inl i), ?_, ?_, fun e' => hnotB _⟩
      · show P ∈ (CV A Fbar w C Cc (eV.symm (eV (Sum.inl i)))).dom
        rw [Equiv.symm_apply_apply]
        exact hPi
      · intro j hj
        obtain ⟨y, rfl⟩ := eV.surjective j
        have hj' : P ∈ (CV A Fbar w C Cc y).dom := by
          have h2 : P ∈ (CV A Fbar w C Cc (eV.symm (eV y))).dom := hj
          rw [Equiv.symm_apply_apply] at h2
          exact h2
        rcases y with i' | v'
        · rw [huniq i' hj']
        · exact absurd hj' (hnotCc v')
    · refine Or.inl ⟨eV (Sum.inr v'), ?_, ?_, fun e' => hnotB _⟩
      · show P ∈ (CV A Fbar w C Cc (eV.symm (eV (Sum.inr v')))).dom
        rw [Equiv.symm_apply_apply]
        exact hPv
      · intro j hj
        obtain ⟨y, rfl⟩ := eV.surjective j
        have hj' : P ∈ (CV A Fbar w C Cc y).dom := by
          have h2 : P ∈ (CV A Fbar w C Cc (eV.symm (eV y))).dom := hj
          rw [Equiv.symm_apply_apply] at h2
          exact h2
        rcases y with i' | v''
        · exact absurd hj' (hnotC i')
        · rw [huniq v'' hj']
    · refine Or.inr ⟨eE ε, ?_, ?_, ?_⟩
      · show P ∈ (B (eE.symm (eE ε))).dom
        rw [Equiv.symm_apply_apply]
        exact hPε
      · intro e' he'
        obtain ⟨ε', rfl⟩ := eE.surjective e'
        have he'' : P ∈ (B ε').dom := by
          have h2 : P ∈ (B (eE.symm (eE ε'))).dom := he'
          rw [Equiv.symm_apply_apply] at h2
          exact h2
        rw [huniq ε' he'']
      · intro j
        obtain ⟨y, rfl⟩ := eV.surjective j
        show P ∉ (CV A Fbar w C Cc (eV.symm (eV y))).dom
        rw [Equiv.symm_apply_apply]
        rcases y with i' | v'
        · exact hnotC i'
        · exact hnotCc v'
  ·
    have hcardV : Fintype.card (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))) = n + ∑ e, (w e - 1) := by
      simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    have hcardE : Fintype.card (Σ e : Fin m, Fin (w e)) = ∑ e, w e := by
      simp only [Fintype.card_sigma, Fintype.card_fin]
    have hsum : (∑ j, genusFF (IsLocalRing.ResidueField A) (FbarV A Fbar w (eV.symm j))) =
        (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) +
          ∑ v' : (Σ e : Fin m, Fin (w e - 1)),
            genusFF (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) := by
      rw [Fintype.sum_equiv eV.symm (fun j => genusFF (IsLocalRing.ResidueField A) (FbarV A Fbar w (eV.symm j)))
        (fun x => genusFF (IsLocalRing.ResidueField A) (FbarV A Fbar w x)) (fun _ => rfl), Fintype.sum_sum_type]
      congr 1
      · exact Finset.sum_congr rfl (fun i _ => genusV_inl A Fbar w i)
      · exact Finset.sum_congr rfl (fun v' _ => genusV_inr A Fbar w v')
    rw [hsum, hcardV, hcardE]
    omega
  ·
    intro i
    show (CV A Fbar w C Cc (eV.symm (eV (Sum.inl i)))).dom = (C i).dom ∧
      (CV A Fbar w C Cc (eV.symm (eV (Sum.inl i)))).integers = (C i).integers
    rw [Equiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  ·
    intro v'
    show (CV A Fbar w C Cc (eV.symm (eV (Sum.inr v')))).dom = _
    rw [Equiv.symm_apply_apply]
    exact hCcdom v'
  ·
    intro ε
    show (B (eE.symm (eE ε))).dom = _ ∧ (B (eE.symm (eE ε))).param = _
    rw [Equiv.symm_apply_apply]
    exact ⟨hBdom ε, hBparam ε⟩
  ·
    intro ε
    show (Ψ.symm (sN (eE.symm (eE ε)))).1 = eV (ends ε).1 ∧ (Ψ.symm (tN (eE.symm (eE ε)))).1 = eV (ends ε).2
    rw [Equiv.symm_apply_apply]
    exact ⟨congrArg eV (sNode_fst A Fbar w src xs ε), congrArg eV (tNode_fst A Fbar w tgt xt Qinf ε)⟩

end S_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne (solution)
