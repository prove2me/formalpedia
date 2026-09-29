-- Prove2me | solution 1 for AlgebraicCurve.exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5ff329e2-bf53-50c8-a0c0-d64fa799340e

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
import Theorems.Thm_AlgebraicCurve_exists_residue_prod_zpow_eq_one_of_forall_mapDomain_placeMap_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one_of_semistableCovering_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
import Theorems.Thm_Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero
import Theorems.Thm_Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

namespace RepAsm

open IsLocalRing

section Tate
variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

theorem eq_zero_of_pow_smul_eq_zero (k : ℕ) (y : TateModule p M)
    (h : ((p : ℤ_[p]) ^ k) • y = 0) : y = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h1 : ((((p : ℤ_[p]) ^ k) • y : TateModule p M) : ℕ → M) (n + k) = 0 := by
    rw [h]; rfl
  rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply, TateModule.compat_pow] at h1
  rw [h1]; rfl

theorem eq_zero_of_smul_eq_zero {a : ℤ_[p]} (ha : a ≠ 0) (y : TateModule p M)
    (h : a • y = 0) : y = 0 := by
  rw [PadicInt.unitCoeff_spec ha, mul_smul] at h
  have h2 : ((p : ℤ_[p]) ^ a.valuation) • y = 0 := by
    have := congrArg (fun z => (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • z) h
    rwa [smul_zero, ← mul_smul, Units.inv_mul, one_smul] at this
  exact eq_zero_of_pow_smul_eq_zero _ y h2

theorem eq_of_one_tmul_eq (y y' : TateModule p M)
    (h : ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y') :
    y = y' := by
  have h' : (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1) y =
      (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1) y' := h
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ_[p]) h'
  have hc0 : (c : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have h3 : (c : ℤ_[p]) • (y - y') = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact hc
  exact sub_eq_zero.mp (eq_zero_of_smul_eq_zero hc0 _ h3)

end Tate

section ValRing
variable {L : Type} [Field L] (A : ValuationSubring L)

private theorem _root_.RepAsm.mem_of_pow_mem {r : L} {n : ℕ} (hn : n ≠ 0) (h : r ^ n ∈ A) : r ∈ A := by
  rw [← A.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  by_contra h'
  exact absurd h (not_le.mpr (one_lt_pow₀ (not_le.mp h') hn))

p2m_export "RepAsm" "mem_of_pow_mem"

theorem exists_unit_of_pow_eq_coe {y : L} {n : ℕ} (hn : n ≠ 0) (u : Aˣ) (h : y ^ n = ((u : A) : L)) :
    ∃ u' : Aˣ, ((u' : A) : L) = y := by
  have hyA : y ∈ A := mem_of_pow_mem A hn (by rw [h]; exact (u : A).2)
  have hpow : (⟨y, hyA⟩ : A) ^ n = (u : A) := Subtype.ext (by simpa using h)
  have hu : IsUnit ((⟨y, hyA⟩ : A) ^ n) := by rw [hpow]; exact u.isUnit
  exact ⟨((isUnit_pow_iff hn).mp hu).unit, rfl⟩

theorem exists_unit_mul_pow_of_pow_eq {π' z : L} {q j : ℕ} (hq : q ≠ 0) (hπ'0 : π' ≠ 0)
    (hπ'A : π' ∈ A) (v : Aˣ) (h : z ^ q = ((v : A) : L) * (π' ^ q) ^ j) :
    ∃ (u : Aˣ) (hz : z ∈ A), (⟨z, hz⟩ : A) = u * ⟨π', hπ'A⟩ ^ j := by
  have hpj : (π' : L) ^ j ≠ 0 := pow_ne_zero _ hπ'0
  have hy : (z / π' ^ j) ^ q = ((v : A) : L) := by
    rw [div_pow, ← pow_mul, mul_comm j q, pow_mul, h, mul_div_assoc, div_self (pow_ne_zero _ (pow_ne_zero _ hπ'0)),
      mul_one]
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_coe A hq v hy
  have hzA : z ∈ A := by
    have : z = ((u : A) : L) * π' ^ j := by rw [hu, div_mul_cancel₀ _ hpj]
    rw [this]; exact mul_mem (u : A).2 (pow_mem hπ'A j)
  refine ⟨u, hzA, Subtype.ext ?_⟩
  show z = ((u : A) : L) * π' ^ j
  rw [hu, div_mul_cancel₀ _ hpj]

theorem eq_one_of_pow_eq_one_of_residue_eq_one {q : ℕ} (hq : IsUnit ((q : ℕ) : ResidueField A))
    {ω : A} (hω : ω ^ q = 1) (hres : residue A ω = 1) : ω = 1 := by
  have h1 : (∑ i ∈ Finset.range q, ω ^ i) * (ω - 1) = 0 := by rw [geom_sum_mul, hω, sub_self]
  have h2 : IsUnit (∑ i ∈ Finset.range q, ω ^ i) := by
    by_contra hnu
    have hmem : (∑ i ∈ Finset.range q, ω ^ i) ∈ maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal]; exact hnu
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sum] at this
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    exact hq.ne_zero this
  have := (h2.mul_right_eq_zero).mp h1
  exact sub_eq_zero.mp this

theorem pow_dvd_of_residue_zpow_eq_one {ℓ : ℕ} [hp : Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : ResidueField A))
    {K : ℕ} (ζ : Aˣ) (hζ : ζ ^ (ℓ ^ K) = 1) (hprim : K ≠ 0 → ζ ^ (ℓ ^ (K - 1)) ≠ 1) (T : ℤ)
    (hT : (Units.map (residue A : A →* ResidueField A) ζ) ^ T = 1) : ((ℓ ^ K : ℕ) : ℤ) ∣ T := by
  set ζb := Units.map (residue A : A →* ResidueField A) ζ with hζb
  have hord_dvd : orderOf ζb ∣ ℓ ^ K := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hζb, ← map_pow, hζ, map_one]
  obtain ⟨j, hjK, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hord_dvd
  have hjK' : j = K := by
    by_contra hne
    have hjlt : j < K := lt_of_le_of_ne hjK hne
    have hK0 : K ≠ 0 := by omega
    apply hprim hK0

    have hpow1 : ζb ^ (ℓ ^ (K - 1)) = 1 := by
      have : ζb ^ (ℓ ^ j) = 1 := by rw [← hj]; exact pow_orderOf_eq_one ζb
      have hle : j ≤ K - 1 := by omega
      obtain ⟨c, hc⟩ := pow_dvd_pow ℓ hle
      rw [hc, pow_mul, this, one_pow]
    have hres : residue A ((ζ ^ (ℓ ^ (K - 1)) : Aˣ) : A) = 1 := by
      have := congrArg (fun u : (ResidueField A)ˣ => (u : ResidueField A)) hpow1
      simpa [hζb, ← map_pow] using this
    have hω : (((ζ ^ (ℓ ^ (K - 1)) : Aˣ) : A)) ^ ℓ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hK0), hζ,
        Units.val_one]
    have := eq_one_of_pow_eq_one_of_residue_eq_one A hℓ hω hres
    exact Units.ext this
  subst hjK'
  rw [← hj]
  exact orderOf_dvd_iff_zpow_eq_one.mpr hT

end ValRing

section Transport
variable {K F : Type} [Field K] [Field F] [Algebra K F]
open scoped Pointwise

theorem mem_smul_iff' (g : SemilinearAut K F) (v : Place K F) (f : F) :
    g • f ∈ (g • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

theorem residue_smul (g : SemilinearAut K F) (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hf' : g • f ∈ (g • v).toValuationSubring) :
    IsLocalRing.residue (g • v).toValuationSubring ⟨g • f, hf'⟩
      = SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) := by
  have h1 : (⟨g • f, hf'⟩ : (g • v).toValuationSubring) =
      SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hf⟩ := Subtype.ext rfl
  rw [h1]
  show _ = IsLocalRing.ResidueField.mapEquiv (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring) _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem evalAt_smul (g : SemilinearAut K F) (v : Place K F) (hv : v.IsRational) (f : F) :
    (g • v).evalAt (g • f) = SemilinearAut.baseAut g (v.evalAt f) := by
  by_cases hf : f ∈ v.toValuationSubring
  · have hf' : g • f ∈ (g • v).toValuationSubring := (mem_smul_iff' g v f).mpr hf
    rw [(g • v).evalAt_of_mem hf', residue_smul g v hf hf', ← v.algebraMap_evalAt hv hf,
      SemilinearAut.smulResidueRingEquiv_algebraMap, Place.residueInv_algebraMap]
  · have hf' : g • f ∉ (g • v).toValuationSubring := fun h => hf ((mem_smul_iff' g v f).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hf, dif_neg hf', map_zero]

end Transport

section Finsupp
variable {α : Type} [DecidableEq α]

theorem prod_zpow_sub {G : Type} [CommGroupWithZero G] (f g : α →₀ ℤ) (h : α → G)
    (hf : ∀ a ∈ f.support, h a ≠ 0) (hg : ∀ a ∈ g.support, h a ≠ 0) :
    (f - g).prod (fun a k => h a ^ k) = f.prod (fun a k => h a ^ k) / g.prod (fun a k => h a ^ k) := by
  classical
  set s := f.support ∪ g.support with hs
  have hne : ∀ a ∈ s, h a ≠ 0 := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hf a ha
    · exact hg a ha
  rw [Finsupp.prod_of_support_subset (f - g) (Finsupp.support_sub) (fun a k => h a ^ k) (fun _ _ => zpow_zero _),
    Finsupp.prod_of_support_subset f Finset.subset_union_left (fun a k => h a ^ k) (fun _ _ => zpow_zero _),
    Finsupp.prod_of_support_subset g Finset.subset_union_right (fun a k => h a ^ k) (fun _ _ => zpow_zero _),
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Finsupp.sub_apply, zpow_sub₀ (hne a ha)]

omit [DecidableEq α] in
theorem prod_zpow_congr {G : Type} [CommGroupWithZero G] (f : α →₀ ℤ) (h h' : α → G)
    (hh : ∀ a ∈ f.support, h a = h' a) :
    f.prod (fun a k => h a ^ k) = f.prod (fun a k => h' a ^ k) :=
  Finset.prod_congr rfl fun a ha => by simp only [hh a ha]

end Finsupp

end RepAsm

namespace RepAsm
open IsLocalRing

theorem prod_zpow_eq_zpow_sum {ι G : Type} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem prod_zpow_src_eq_prod_zpow_tgt {G : Type} [CommGroup G] {n m : ℕ} (src tgt : Fin m → Fin n)
    (ε : Fin m → ℤ)
    (hε : ∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0))
    (A : Fin n → G) : ∏ e, A (src e) ^ ε e = ∏ e, A (tgt e) ^ ε e := by
  classical
  have key : ∀ (r : Fin m → Fin n), ∏ e, A (r e) ^ ε e = ∏ i, A i ^ (∑ e, if r e = i then ε e else 0) := by
    intro r
    have : ∀ e, A (r e) ^ ε e = ∏ i, A i ^ (if r e = i then ε e else 0) := by
      intro e
      rw [Finset.prod_eq_single (r e)]
      · simp
      · intro i _ hi
        rw [if_neg (Ne.symm hi), zpow_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [this]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact prod_zpow_eq_zpow_sum (A i) _ _
  rw [key src, key tgt]
  exact Finset.prod_congr rfl fun i _ => by rw [hε i]

theorem prod_zpow_eq_zpow_sum₀ {ι G : Type} [CommGroupWithZero G] (a : G) (ha : a ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

theorem zpow_injective_of_lt_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (c : Γˣ) (hc : (c : Γ) < 1)
    {a b : ℤ} (h : c ^ a = c ^ b) : a = b := by
  have hc1 : c < 1 := by rwa [← Units.val_lt_val, Units.val_one]
  have hc' : 1 < c⁻¹ := one_lt_inv'.mpr hc1
  have h' : c⁻¹ ^ a = c⁻¹ ^ b := by rw [inv_zpow, inv_zpow, h]
  exact (zpow_right_strictMono hc').injective h'

section Restr
variable {K F : Type} [Field K] [Field F] [Algebra K F]
open Classical

noncomputable def restr (E : Divisor K F) (U : Set (Place K F)) : Divisor K F := E.filter (· ∈ U)

theorem restr_apply_of_mem {E : Divisor K F} {U : Set (Place K F)} {P : Place K F} (h : P ∈ U) :
    restr E U P = E P := Finsupp.filter_apply_pos (· ∈ U) E h

theorem restr_apply_of_not_mem {E : Divisor K F} {U : Set (Place K F)} {P : Place K F} (h : P ∉ U) :
    restr E U P = 0 := Finsupp.filter_apply_neg (· ∈ U) E h

theorem mem_of_mem_support_restr {E : Divisor K F} {U : Set (Place K F)} {P : Place K F}
    (h : P ∈ (restr E U).support) : P ∈ U ∧ P ∈ E.support := by
  unfold restr at h
  rw [Finsupp.support_filter, Finset.mem_filter] at h
  exact ⟨h.2, h.1⟩

theorem restr_sub (E E' : Divisor K F) (U : Set (Place K F)) : restr (E - E') U = restr E U - restr E' U :=
  Finsupp.filter_sub _ E E'

theorem restr_zsmul (c : ℤ) (E : Divisor K F) (U : Set (Place K F)) : restr (c • E) U = c • restr E U :=
  Finsupp.filter_smul

theorem restr_aut_smul (g : SemilinearAut K F) (E : Divisor K F) (U : Set (Place K F))
    (hU : ∀ P, P ∈ U ↔ g⁻¹ • P ∈ U) : restr (g • E) U = g • restr E U := by
  ext P
  rw [SemilinearAut.divisor_smul_apply]
  by_cases hP : P ∈ U
  · rw [restr_apply_of_mem hP, restr_apply_of_mem ((hU P).mp hP), SemilinearAut.divisor_smul_apply]
  · rw [restr_apply_of_not_mem hP, restr_apply_of_not_mem (fun h => hP ((hU P).mpr h))]

theorem eq_sum_restr_add_sum_restr {n m : ℕ} (U : Fin n → Set (Place K F)) (V : Fin m → Set (Place K F))
    (hcover : ∀ P : Place K F,
      (∃ i, P ∈ U i ∧ (∀ j, P ∈ U j → j = i) ∧ ∀ e, P ∉ V e) ∨
      (∃ e, P ∈ V e ∧ (∀ e', P ∈ V e' → e' = e) ∧ ∀ i, P ∉ U i))
    (E : Divisor K F) : E = (∑ i, restr E (U i)) + ∑ e, restr E (V e) := by
  ext P
  rw [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  rcases hcover P with ⟨i, hi, huniq, hno⟩ | ⟨e, he, huniq, hno⟩
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hj => restr_apply_of_not_mem (fun h => hj (huniq j h))),
      restr_apply_of_mem hi, Finset.sum_eq_zero (fun e _ => restr_apply_of_not_mem (hno e)), add_zero]
  · rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)
        (fun e' _ he' => restr_apply_of_not_mem (fun h => he' (huniq e' h))),
      restr_apply_of_mem he, Finset.sum_eq_zero (fun i _ => restr_apply_of_not_mem (hno i)), zero_add]

theorem mapDomain_congr_support {β : Type} (f g : Place K F → β) (E : Divisor K F)
    (h : ∀ P ∈ E.support, f P = g P) : Finsupp.mapDomain f E = Finsupp.mapDomain g E := by
  unfold Finsupp.mapDomain Finsupp.sum
  exact Finset.sum_congr rfl fun P hP => by simp only [h P hP]

theorem pic0_mk_eq_mk_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ ((D : Divisor K F) - E) ∈ Divisor.principal (K := K) (F := F) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub]

theorem pic0_mk_zsmul (c : ℤ) (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk (c • D) = c • Pic0.mk D :=
  QuotientAddGroup.mk_zsmul _ _ c

end Restr

end RepAsm

set_option maxHeartbeats 1600000 in
open RepAsm in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
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
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ k : ℕ, ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0  := by
  intro v x hvx k
  classical
  have hp : Fact ℓ.Prime := inferInstance

  have hxinv : ∀ s ∈ S, ∀ j : ℕ, s • TateModule.proj ℓ (Pic0 L F) j x = TateModule.proj ℓ (Pic0 L F) j x := by
    intro s hs j
    have h0 : (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)
        (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp v.2 s) hs)
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hvx, ModularCurve.rationalGaloisRep_tmul] at h0
    have h2 := eq_of_one_tmul_eq _ _ h0
    have h3 := congrArg (fun z : TateModule ℓ (Pic0 L F) => (z : ℕ → Pic0 L F) j) h2
    simpa only [TateModule.rep_apply, TateModule.proj_apply] using h3

  have hwpos : ∀ e, 0 < w e := by
    intro e
    by_contra h0
    have hw0 : w e = 0 := by omega
    obtain ⟨u, hu⟩ := hw e
    rw [hw0, pow_zero, mul_one] at hu
    have hm := (An e).modulus_mem
    rw [hu, IsLocalRing.mem_maximalIdeal] at hm
    exact hm u.isUnit

  obtain ⟨N, hN⟩ := Fin.exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
    n m src tgt w hwpos ℓ hp.out.one_lt
  have hℓK0 : ℓ ^ (k + N) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hℓKpos : 0 < ℓ ^ (k + N) := Nat.pos_of_ne_zero hℓK0

  obtain ⟨π'L, hπ'⟩ : ∃ r : L, r ^ (ℓ ^ (k + N)) = (π : L) := IsAlgClosed.exists_pow_nat_eq (π : L) hℓKpos
  have hπL0 : ((π : A) : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hπ'0 : π'L ≠ 0 := by
    intro h; rw [h, zero_pow hℓK0] at hπ'; exact hπL0 hπ'.symm
  have hπ'A : π'L ∈ A := mem_of_pow_mem A hℓK0 (by rw [hπ']; exact π.2)
  set π' : A := ⟨π'L, hπ'A⟩ with hπ'def
  have hπ'pow : π' ^ (ℓ ^ (k + N)) = π := Subtype.ext hπ'
  have hπ'm : π' ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem _ (by rw [hπ'pow]; exact hπ)
  have hπ'ne : π' ≠ 0 := fun h => hπ'0 (congrArg Subtype.val h)
  have hw' : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π' ^ (ℓ ^ (k + N) * w e) := fun e => by
    obtain ⟨u, hu⟩ := hw e
    exact ⟨u, by rw [pow_mul, hπ'pow]; exact hu⟩

  obtain ⟨D₀, hD₀, hD₀c, hsupp⟩ := AlgebraicCurve.exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
    A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus ℓ (k + N) M D (TateModule.proj ℓ (Pic0 L F) (k + N) x) (TateModule.torsionBy_proj (k + N) x)

  have hlat : ∀ (e : Fin m) (P : Place L F), ∃ j : ℕ, P ∈ D₀.support → P ∈ (An e).dom →
      ∃ (u : Aˣ) (h : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, h⟩ : A) = u * π' ^ j := by
    intro e P
    by_cases hP : P ∈ D₀.support ∧ P ∈ (An e).dom
    · rcases hsupp P hP.1 with ⟨i, hPi⟩ | ⟨e', hPe', u, j, hu⟩
      · exfalso
        rcases hcover P with ⟨i', -, -, hno⟩ | ⟨e'', -, -, hno⟩
        · exact hno e hP.2
        · exact hno i hPi
      · have hee : e' = e := by
          rcases hcover P with ⟨i', -, -, hno⟩ | ⟨e'', -, huniq, -⟩
          · exact absurd hP.2 (hno e)
          · exact (huniq e' hPe').trans (huniq e hP.2).symm
        subst hee
        obtain ⟨u', hz, hu'⟩ := exists_unit_mul_pow_of_pow_eq A (z := P.evalAt (An e').param) (j := j) hℓK0 hπ'0 hπ'A u
          (by rw [hπ']; exact hu)
        exact ⟨j, fun _ _ => ⟨u', hz, hu'⟩⟩
    · exact ⟨0, fun h1 h2 => absurd (And.intro h1 h2) hP⟩
  choose J hJ using hlat

  obtain ⟨s₀, hs₀S, r₀, hr₀, hmove⟩ := hSℓ
  obtain ⟨hA₀, hfixπ, hres₀, hC₀, hAn₀, hpar₀, -, -, hpm₀⟩ := hS s₀ hs₀S

  have hAn_iff : ∀ e P, P ∈ (An e).dom ↔ s₀⁻¹ • P ∈ (An e).dom := by
    intro e P
    constructor
    · intro hP
      rcases hcover (s₀⁻¹ • P) with ⟨i, hi, -, -⟩ | ⟨e', he', -, -⟩
      · have : P ∈ (C i).dom := by simpa using hC₀ i _ hi
        rcases hcover P with ⟨_, -, -, hno⟩ | ⟨_, -, -, hno⟩
        · exact absurd hP (hno e)
        · exact absurd this (hno i)
      · have hP' : P ∈ (An e').dom := by simpa using hAn₀ e' _ he'
        rcases hcover P with ⟨_, -, -, hno⟩ | ⟨e'', -, huniq, -⟩
        · exact absurd hP (hno e)
        · rwa [(huniq e' hP').trans (huniq e hP).symm] at he'
    · intro h; simpa using hAn₀ e _ h
  have hC_iff : ∀ i P, P ∈ (C i).dom ↔ s₀⁻¹ • P ∈ (C i).dom := by
    intro i P
    constructor
    · intro hP
      rcases hcover (s₀⁻¹ • P) with ⟨i', hi', -, -⟩ | ⟨e, he, -, -⟩
      · have hP' : P ∈ (C i').dom := by simpa using hC₀ i' _ hi'
        rcases hcover P with ⟨i'', -, huniq, -⟩ | ⟨_, -, -, hno⟩
        · rwa [(huniq i' hP').trans (huniq i hP).symm] at hi'
        · exact absurd hP (hno i)
      · have : P ∈ (An e).dom := by simpa using hAn₀ e _ he
        rcases hcover P with ⟨_, -, -, hno⟩ | ⟨_, -, -, hno⟩
        · exact absurd this (hno e)
        · exact absurd hP (hno i)
    · intro h; simpa using hC₀ i _ h

  have hzs : ∀ e, ∀ P ∈ (An e).dom,
      (s₀ • P).evalAt (An e).param = SemilinearAut.baseAut s₀ (P.evalAt (An e).param) := by
    intro e P hP
    conv_lhs => rw [← hpar₀ e]
    exact evalAt_smul s₀ P ((An e).mem_dom P hP).1 _

  have hσπ'pow : (SemilinearAut.baseAut s₀ π'L) ^ (ℓ ^ (k + N)) = (π : L) := by
    rw [← map_pow, hπ', hfixπ]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Aˣ, ((ζ : A) : L) = SemilinearAut.baseAut s₀ π'L / π'L :=
    exists_unit_of_pow_eq_coe A hℓK0 1 (by rw [div_pow, hσπ'pow, hπ', div_self hπL0]; simp)
  have hσπ' : SemilinearAut.baseAut s₀ π'L = ((ζ : A) : L) * π'L := by rw [hζ, div_mul_cancel₀ _ hπ'0]
  have hζpow : ζ ^ (ℓ ^ (k + N)) = 1 := by
    apply Units.ext; apply Subtype.ext
    show (((ζ ^ (ℓ ^ (k + N)) : Aˣ) : A) : L) = (((1 : Aˣ) : A) : L)
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, hζ, div_pow, hσπ'pow, hπ', div_self hπL0]; simp

  have hη : ∀ u : Aˣ, ∃ η : Aˣ, Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) η = 1 ∧
      SemilinearAut.baseAut s₀ ((u : A) : L) = ((η : A) : L) * ((u : A) : L) := by
    intro u
    have hmem : SemilinearAut.baseAut s₀ ((u : A) : L) ∈ A := (hA₀ _).mp (u : A).2
    have hres : IsLocalRing.residue A ⟨_, hmem⟩ = IsLocalRing.residue A (u : A) := hres₀ (u : A) hmem
    have hunit : IsUnit (⟨_, hmem⟩ : A) := by
      by_contra hnu
      have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      rw [hres, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at h0
      exact h0 u.isUnit
    refine ⟨hunit.unit * u⁻¹, ?_, ?_⟩
    · have hmu : Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) hunit.unit =
          Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) u := by
        apply Units.ext
        simp only [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]
        exact hres
      rw [map_mul, map_inv, hmu, mul_inv_cancel]
    · rw [← MulMemClass.coe_mul, ← Units.val_mul, inv_mul_cancel_right, IsUnit.unit_spec]
  have hprim : k + N ≠ 0 → ζ ^ (ℓ ^ (k + N - 1)) ≠ 1 := by
    intro hK0 heq
    apply hmove
    have hKsucc : ℓ ^ (k + N - 1) * ℓ = ℓ ^ (k + N) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hK0)]
    have hρℓ : (π'L ^ (ℓ ^ (k + N - 1))) ^ ℓ = (π : L) := by rw [← pow_mul, hKsucc, hπ']
    have hρ0 : π'L ^ (ℓ ^ (k + N - 1)) ≠ 0 := pow_ne_zero _ hπ'0
    have hζ1 : ((ζ : A) : L) ^ (ℓ ^ (k + N - 1)) = 1 := by
      have := congrArg (fun u : Aˣ => ((u : A) : L)) heq
      simpa [Units.val_pow_eq_pow_val] using this
    have hσρ : SemilinearAut.baseAut s₀ (π'L ^ (ℓ ^ (k + N - 1))) = π'L ^ (ℓ ^ (k + N - 1)) := by
      rw [map_pow, hσπ', mul_pow, hζ1, one_mul]
    have hξpow : (r₀ / π'L ^ (ℓ ^ (k + N - 1))) ^ ℓ = 1 := by rw [div_pow, hr₀, hρℓ, div_self hπL0]
    obtain ⟨ξ, hξ⟩ : ∃ ξ : Aˣ, ((ξ : A) : L) = r₀ / π'L ^ (ℓ ^ (k + N - 1)) :=
      exists_unit_of_pow_eq_coe A hp.out.ne_zero 1 (by rw [hξpow]; simp)
    obtain ⟨η, hη1, hηξ⟩ := hη ξ
    have hηpow : η ^ ℓ = 1 := by
      apply Units.ext; apply Subtype.ext
      show (((η ^ ℓ : Aˣ) : A) : L) = (((1 : Aˣ) : A) : L)
      have h1 : (SemilinearAut.baseAut s₀ ((ξ : A) : L)) ^ ℓ = 1 := by rw [← map_pow, hξ, hξpow, map_one]
      rw [hηξ, mul_pow, hξ, hξpow, mul_one] at h1
      simpa [Units.val_pow_eq_pow_val] using h1
    have hη1' : η = 1 := by
      apply Units.ext
      apply eq_one_of_pow_eq_one_of_residue_eq_one A hℓ (ω := (η : A))
      · rw [← Units.val_pow_eq_pow_val, hηpow, Units.val_one]
      · have := congrArg (fun u : (IsLocalRing.ResidueField A)ˣ => (u : IsLocalRing.ResidueField A)) hη1
        simpa [Units.coe_map] using this
    have hσξ : SemilinearAut.baseAut s₀ (r₀ / π'L ^ (ℓ ^ (k + N - 1))) = r₀ / π'L ^ (ℓ ^ (k + N - 1)) := by
      rw [← hξ, hηξ, hη1']; simp
    calc SemilinearAut.baseAut s₀ r₀
        = SemilinearAut.baseAut s₀ (r₀ / π'L ^ (ℓ ^ (k + N - 1)) * π'L ^ (ℓ ^ (k + N - 1))) := by
          rw [div_mul_cancel₀ _ hρ0]
      _ = r₀ / π'L ^ (ℓ ^ (k + N - 1)) * π'L ^ (ℓ ^ (k + N - 1)) := by rw [map_mul, hσξ, hσρ]
      _ = r₀ := div_mul_cancel₀ _ hρ0
  set ζb : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) ζ
    with hζbdef

  have hroot : ∀ (e : Fin m) (P : Place L F), ∃ c : Aˣ, P ∈ D₀.support → P ∈ (An e).dom →
      Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) c = ζb ^ (J e P) ∧
      SemilinearAut.baseAut s₀ (P.evalAt (An e).param) = ((c : A) : L) * P.evalAt (An e).param := by
    intro e P
    by_cases hP : P ∈ D₀.support ∧ P ∈ (An e).dom
    · obtain ⟨u, hzA, hu⟩ := hJ e P hP.1 hP.2
      obtain ⟨η, hη1, hηu⟩ := hη u
      refine ⟨η * ζ ^ (J e P), fun _ _ => ⟨?_, ?_⟩⟩
      · rw [map_mul, map_pow, hη1, one_mul]
      · have hz : P.evalAt (An e).param = ((u : A) : L) * π'L ^ (J e P) := by
          have := congrArg (fun a : A => (a : L)) hu
          simpa using this
        rw [hz, map_mul, map_pow, hηu, hσπ']
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
        ring
    · exact ⟨1, fun h1 h2 => absurd (And.intro h1 h2) hP⟩
  choose cOf hcOf using hroot

  have hsD₀ : s₀ • D₀ ∈ Divisor.degZero (K := L) (F := F) := SemilinearAut.smul_mem_degZero s₀ hD₀
  have hEprin : s₀ • D₀ - D₀ ∈ Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk ⟨s₀ • D₀, hsD₀⟩ = Pic0.mk ⟨D₀, hD₀⟩ := by
      have : (⟨s₀ • D₀, hsD₀⟩ : Divisor.degZero (K := L) (F := F)) = SemilinearAut.degZeroSMulHom s₀ ⟨D₀, hD₀⟩ :=
        Subtype.ext (by rw [SemilinearAut.coe_degZeroSMulHom])
      rw [this, ← SemilinearAut.pic0_smul_mk, hD₀c, hxinv s₀ hs₀S]
    exact (pic0_mk_eq_mk_iff _ _).mp h1
  obtain ⟨f, hf0, hfE⟩ := hEprin

  have hzne : ∀ e, ∀ P ∈ (An e).dom, P.evalAt (An e).param ≠ 0 := fun e P hP => ((An e).mem_dom P hP).2.2.2.1
  have hsuppX : ∀ e P, P ∈ (restr D₀ (An e).dom).support → P ∈ (An e).dom ∧ P ∈ D₀.support :=
    fun e P hP => mem_of_mem_support_restr hP
  have hsuppS : ∀ e P, P ∈ (s₀ • restr D₀ (An e).dom).support → P ∈ (An e).dom := by
    intro e P hP
    rw [Finsupp.mem_support_iff, SemilinearAut.divisor_smul_apply] at hP
    exact (hAn_iff e P).mpr (mem_of_mem_support_restr (Finsupp.mem_support_iff.mpr hP)).1
  have hNN : ∀ e, restr (s₀ • D₀ - D₀) (An e).dom = s₀ • restr D₀ (An e).dom - restr D₀ (An e).dom := by
    intro e; rw [restr_sub, restr_aut_smul s₀ D₀ _ (hAn_iff e)]
  have hCC : ∀ i, restr (s₀ • D₀ - D₀) (C i).dom = s₀ • restr D₀ (C i).dom - restr D₀ (C i).dom := by
    intro i; rw [restr_sub, restr_aut_smul s₀ D₀ _ (hC_iff i)]

  have hvπ'0 : A.valuation π'L ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ'0
  have hvπ'lt : A.valuation π'L < 1 := (ValuationSubring.valuation_lt_one_iff A π').mp hπ'm
  have hzval : ∀ e, ∀ P ∈ (restr D₀ (An e).dom).support,
      A.valuation (P.evalAt (An e).param) = A.valuation π'L ^ (J e P) := by
    intro e P hP
    obtain ⟨u, hzA, hu⟩ := hJ e P (hsuppX e P hP).2 (hsuppX e P hP).1
    have hz : P.evalAt (An e).param = ((u : A) : L) * π'L ^ (J e P) := by
      have := congrArg (fun a : A => (a : L)) hu
      simpa using this
    rw [hz, map_mul, map_pow, A.valuation_unit, one_mul]
  have hmodval : ∀ e, A.valuation ((An e).modulus : L) = A.valuation π'L ^ (ℓ ^ (k + N) * w e) := by
    intro e
    obtain ⟨u, hu⟩ := hw' e
    have : ((An e).modulus : L) = ((u : A) : L) * π'L ^ (ℓ ^ (k + N) * w e) := by
      have := congrArg (fun a : A => (a : L)) hu
      simpa using this
    rw [this, map_mul, map_pow, A.valuation_unit, one_mul]
  obtain ⟨τ, hτdef⟩ : ∃ τ : Fin m → ℤ, ∀ e, τ e = (restr D₀ (An e).dom).sum (fun P k => k * (J e P : ℤ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Mass, hMdef⟩ : ∃ M : Fin m → ℤ, ∀ e, M e = (restr D₀ (An e).dom).sum (fun _ k => k) := ⟨_, fun _ => rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : Fin n → ℤ, ∀ i, d i = Divisor.degree (restr D₀ (C i).dom) := ⟨_, fun _ => rfl⟩
  have hproddepth : ∀ (c' : ℤ) (e : Fin m),
      ((restr (c' • D₀) (An e).dom).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
        A.valuation π'L ^ (c' * τ e) := by
    intro c' e
    rw [restr_zsmul, Finsupp.prod_of_support_subset _ Finsupp.support_smul _ (fun _ _ => zpow_zero _), hτdef,
      Finsupp.sum, Finset.mul_sum, ← prod_zpow_eq_zpow_sum₀ _ hvπ'0]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, hzval e P hP, ← zpow_natCast, ← zpow_mul]
    congr 1; ring
  have hmass : ∀ (c' : ℤ) (e : Fin m), ((restr (c' • D₀) (An e).dom).sum fun _ k => k) = c' * Mass e := by
    intro c' e
    rw [restr_zsmul, Finsupp.sum_smul_index' (fun _ => rfl), hMdef, Finsupp.mul_sum]
    simp only [smul_eq_mul]
  have hdegq : ∀ (c' : ℤ) (i : Fin n), Divisor.degree (restr (c' • D₀) (C i).dom) = c' * d i := by
    intro c' i; rw [restr_zsmul, map_zsmul, smul_eq_mul, hddef]

  let υ : Aˣ →* L := (A.subtype.toMonoidHom).comp (Units.coeHom A)
  have hυ : ∀ c : Aˣ, υ c = ((c : A) : L) := fun _ => rfl
  let W : Fin m → Aˣ := fun e => (restr D₀ (An e).dom).prod fun P k => cOf e P ^ k

  have hC2 := AlgebraicCurve.exists_residue_prod_zpow_eq_one_of_forall_mapDomain_placeMap_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one_of_semistableCovering_of_discFibres_of_rankOne
    A π' hπ'm hπ'ne hrk F n m Fbar hratBar C hratF An An' src tgt xs xt (fun e => ℓ ^ (k + N) * w e) hpair hw' hatt hnodes hcover hdisc hgenus
    f hf0 (fun i => restr (s₀ • D₀ - D₀) (C i).dom)
    (fun i P hP => (mem_of_mem_support_restr hP).1)
    (fun i P hP => by rw [restr_apply_of_mem hP]; exact hfE P)
    (fun i => by
      beta_reduce
      have hh : ∀ E : Divisor L F, Finsupp.mapDomain (C i).placeMap E =
          Finsupp.mapDomain.addMonoidHom (C i).placeMap E := fun _ => rfl
      rw [hCC, hh, map_sub, ← hh, ← hh, SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp,
        mapDomain_congr_support ((C i).placeMap ∘ (s₀ • ·)) (C i).placeMap _
          (fun P hP => hpm₀ i P (mem_of_mem_support_restr hP).1), sub_self])
    (fun e => restr (s₀ • D₀ - D₀) (An e).dom)
    (fun e P hP => (mem_of_mem_support_restr hP).1)
    (fun e P hP => by rw [restr_apply_of_mem hP]; exact hfE P)
    (fun e => by
      beta_reduce
      rw [hNN, Finsupp.sum_sub_index (fun _ _ _ => rfl), SemilinearAut.divisor_smul_def,
        Finsupp.sum_mapDomain_index_inj (MulAction.injective s₀), sub_self])
    (fun e => by
      beta_reduce
      rw [hNN, prod_zpow_sub _ _ _ (fun P hP => (Valuation.ne_zero_iff _).mpr (hzne e P (hsuppS e P hP)))
        (fun P hP => (Valuation.ne_zero_iff _).mpr (hzne e P (hsuppX e P hP).1)),
        SemilinearAut.divisor_smul_def, Finsupp.prod_mapDomain_index_inj (MulAction.injective s₀)]
      have hcongr : ((restr D₀ (An e).dom).prod fun P k => A.valuation ((s₀ • P).evalAt (An e).param) ^ k) =
          (restr D₀ (An e).dom).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k :=
        Finsupp.prod_congr fun P hP => by
          rw [hzs e P (hsuppX e P hP).1, (hcOf e P (hsuppX e P hP).2 (hsuppX e P hP).1).2, map_mul,
            A.valuation_unit, one_mul]
      rw [hcongr, div_self]
      exact Finsupp.prod_ne_zero_iff.mpr fun P hP =>
        zpow_ne_zero _ ((Valuation.ne_zero_iff _).mpr (hzne e P (hsuppX e P hP).1)))
  have hτ : ∀ ε : Fin m → ℤ,
      (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
      (∑ e, ε e * τ e) ≡ 0 [ZMOD ((ℓ : ℤ) ^ (k + N))] := by
    intro ε hε
    obtain ⟨hmem, hres⟩ := hC2 ε hε
    have hU : ∀ e, ((restr (s₀ • D₀ - D₀) (An e).dom).prod fun P k => (P.evalAt (An e).param) ^ k) = υ (W e) := by
      intro e
      rw [hNN, prod_zpow_sub _ _ _ (fun P hP => hzne e P (hsuppS e P hP)) (fun P hP => hzne e P (hsuppX e P hP).1),
        SemilinearAut.divisor_smul_def, Finsupp.prod_mapDomain_index_inj (MulAction.injective s₀)]
      have hcongr : ((restr D₀ (An e).dom).prod fun P k => ((s₀ • P).evalAt (An e).param) ^ k) =
          (restr D₀ (An e).dom).prod fun P k => (υ (cOf e P)) ^ k * (P.evalAt (An e).param) ^ k :=
        Finsupp.prod_congr fun P hP => by
          rw [hzs e P (hsuppX e P hP).1, (hcOf e P (hsuppX e P hP).2 (hsuppX e P hP).1).2, hυ, mul_zpow]
      have hne : ((restr D₀ (An e).dom).prod fun P k => (P.evalAt (An e).param) ^ k) ≠ 0 :=
        Finsupp.prod_ne_zero_iff.mpr fun P hP => zpow_ne_zero _ (hzne e P (hsuppX e P hP).1)
      rw [hcongr, Finsupp.prod_mul, mul_div_cancel_right₀ _ hne]
      show _ = υ ((restr D₀ (An e).dom).prod fun P k => cOf e P ^ k)
      rw [map_finsuppProd]
      exact Finsupp.prod_congr fun P _ => (map_zpow υ _ _).symm
    have hbig : (∏ e, ((restr (s₀ • D₀ - D₀) (An e).dom).prod fun P k => (P.evalAt (An e).param) ^ k) ^ ε e) =
        υ (∏ e, W e ^ ε e) := by
      rw [map_prod]; exact Finset.prod_congr rfl fun e _ => by rw [hU, map_zpow]
    have hWres : IsLocalRing.residue A ((∏ e, W e ^ ε e : Aˣ) : A) = 1 := by
      have : (⟨_, hmem⟩ : A) = ((∏ e, W e ^ ε e : Aˣ) : A) := Subtype.ext hbig
      rw [← this]; exact hres
    have hWb : ∀ e, Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (W e) = ζb ^ τ e := by
      intro e
      show Units.map _ ((restr D₀ (An e).dom).prod fun P k => cOf e P ^ k) = _
      rw [map_finsuppProd, hτdef e]
      simp only [Finsupp.prod, Finsupp.sum]
      rw [← prod_zpow_eq_zpow_sum]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [map_zpow, (hcOf e P (hsuppX e P hP).2 (hsuppX e P hP).1).1, ← zpow_natCast, ← zpow_mul, mul_comm]
    have hζT : ζb ^ (∑ e, τ e * ε e) = 1 := by
      rw [← prod_zpow_eq_zpow_sum]
      have : (∏ e, ζb ^ (τ e * ε e)) =
          Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (∏ e, W e ^ ε e) := by
        rw [map_prod]; exact Finset.prod_congr rfl fun e _ => by rw [map_zpow, hWb, ← zpow_mul]
      rw [this]; apply Units.ext; rw [Units.coe_map, MonoidHom.coe_coe, hWres, Units.val_one]
    have hdvd := pow_dvd_of_residue_zpow_eq_one A hℓ ζ hζpow hprim _ hζT
    rw [Int.modEq_zero_iff_dvd]
    have hcomm : (∑ e, ε e * τ e) = ∑ e, τ e * ε e := Finset.sum_congr rfl fun e _ => mul_comm _ _
    rw [hcomm]
    exact_mod_cast hdvd

  obtain ⟨φ, hφ⟩ := Fin.exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero n m src tgt
    ((ℓ : ℤ) ^ (k + N)) τ hτ

  have hqprin : ((ℓ ^ (k + N) : ℕ) : ℤ) • D₀ ∈ Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk (((ℓ ^ (k + N) : ℕ) : ℤ) • ⟨D₀, hD₀⟩) = Pic0.mk 0 := by
      rw [pic0_mk_zsmul, hD₀c, TateModule.torsionBy_proj, Pic0.mk_zero]
    have h2 := (pic0_mk_eq_mk_iff _ _).mp h1
    simpa using h2
  obtain ⟨g, hg0, hgE⟩ := hqprin
  obtain ⟨σ', a', ha', hV', hE'⟩ := AlgebraicCurve.exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
    A π' hπ'm hπ'ne hrk F n m Fbar hratBar C hratF An An' src tgt xs xt (fun e => ℓ ^ (k + N) * w e) hpair hw' hatt hnodes hcover hdisc hgenus
    g hg0 (fun i => restr (((ℓ ^ (k + N) : ℕ) : ℤ) • D₀) (C i).dom)
    (fun i P hP => (mem_of_mem_support_restr hP).1)
    (fun i P hP => by rw [restr_apply_of_mem hP]; exact hgE P)
    (fun e => restr (((ℓ ^ (k + N) : ℕ) : ℤ) • D₀) (An e).dom)
    (fun e P hP => (mem_of_mem_support_restr hP).1)
    (fun e P hP => by rw [restr_apply_of_mem hP]; exact hgE P)

  have hV'' : ∀ i : Fin n, (ℓ : ℤ) ^ (k + N) * d i + (∑ e, if src e = i then σ' e else 0) +
      (∑ e, if tgt e = i then (ℓ : ℤ) ^ (k + N) * Mass e - σ' e else 0) = 0 := by
    intro i
    have h := hV' i
    simp only [hdegq, hmass] at h
    push_cast at h
    exact h
  have hE'' : ∀ ε : Fin m → ℤ,
      (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
      (∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * τ e)) =
        ∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * Mass e - σ' e)) := by
    intro ε hε
    let cu : (A.ValueGroup)ˣ := Units.mk0 _ hvπ'0
    have ha'0 : ∀ i, A.valuation (a' i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).mpr (ha' i)
    let au : Fin n → (A.ValueGroup)ˣ := fun i => Units.mk0 _ (ha'0 i)
    have hedge : ∀ e, au (src e) * cu ^ ((ℓ : ℤ) ^ (k + N) * τ e) =
        au (tgt e) * cu ^ ((ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * Mass e - σ' e)) := by
      intro e
      have h := hE' e
      rw [hproddepth, hmass, hmodval, ← zpow_natCast, ← zpow_mul] at h
      push_cast at h
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
      exact h
    have hprod := congrArg (fun f : Fin m → (A.ValueGroup)ˣ => ∏ e, (f e) ^ ε e) (funext hedge)
    simp only [mul_zpow, Finset.prod_mul_distrib, ← zpow_mul] at hprod
    rw [prod_zpow_src_eq_prod_zpow_tgt src tgt ε hε au, prod_zpow_eq_zpow_sum, prod_zpow_eq_zpow_sum] at hprod
    have hinj := zpow_injective_of_lt_one cu hvπ'lt (mul_left_cancel hprod)
    have hc1 : ∀ X : Fin m → ℤ, (∑ e, ε e * X e) = ∑ e, X e * ε e := fun X => Finset.sum_congr rfl fun e _ => mul_comm _ _
    rw [hc1 (fun e => (ℓ : ℤ) ^ (k + N) * τ e), hc1 (fun e => (ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * Mass e - σ' e))]
    exact hinj

  obtain ⟨σ, α, hV, hE⟩ := hN k d Mass τ φ σ' hφ hV'' hE''

  obtain ⟨Di', hdom', hdeg', hprin'⟩ := AlgebraicCurve.exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
    A π' hπ'm hπ'ne hrk F n m Fbar hratBar C hratF An An' src tgt xs xt (fun e => ℓ ^ (k + N) * w e) hpair hw' hatt hnodes hcover hdisc hgenus
    (fun i => restr (((ℓ ^ N : ℕ) : ℤ) • D₀) (C i).dom)
    (fun i P hP => (mem_of_mem_support_restr hP).1)
    (fun e => restr (((ℓ ^ N : ℕ) : ℤ) • D₀) (An e).dom)
    (fun e P hP => (mem_of_mem_support_restr hP).1)
    (by
      intro e P hP
      obtain ⟨hPe, hPD⟩ := mem_of_mem_support_restr hP
      obtain ⟨u, h, hu⟩ := hJ e P (Finsupp.support_smul hPD) hPe
      exact ⟨J e P, u, h, hu⟩)
    σ (fun i => π'L ^ α i) (fun i => zpow_ne_zero _ hπ'0)
    (by
      intro i
      simp only [hdegq, hmass]
      push_cast
      exact hV i)
    (by
      intro e
      rw [hproddepth, hmass, hmodval, map_zpow₀, map_zpow₀, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hvπ'0,
        ← zpow_add₀ hvπ'0]
      congr 1
      have := hE e
      push_cast
      linarith)

  have hsum : (((ℓ ^ N : ℕ) : ℤ) • D₀) = (∑ i, restr (((ℓ ^ N : ℕ) : ℤ) • D₀) (C i).dom) +
      ∑ e, restr (((ℓ ^ N : ℕ) : ℤ) • D₀) (An e).dom :=
    eq_sum_restr_add_sum_restr (fun i => (C i).dom) (fun e => (An e).dom) hcover _
  have hdeg0 : (∑ i, Di' i) ∈ Divisor.degZero (K := L) (F := F) := by
    rw [Divisor.mem_degZero, map_sum]
    exact Finset.sum_eq_zero fun i _ => hdeg' i
  refine ⟨∑ i, Di' i, hdeg0, Di', ?_, rfl, hdom', hdeg'⟩
  have hlD₀ : (((ℓ ^ N : ℕ) : ℤ) • D₀) ∈ Divisor.degZero (K := L) (F := F) := AddSubgroup.zsmul_mem _ hD₀ _
  have h1 : Pic0.mk ⟨∑ i, Di' i, hdeg0⟩ = Pic0.mk ⟨((ℓ ^ N : ℕ) : ℤ) • D₀, hlD₀⟩ := by
    rw [pic0_mk_eq_mk_iff]
    have := Divisor.principal.neg_mem hprin'
    rw [← hsum] at this
    simpa using this
  rw [h1]
  have h2 : (⟨((ℓ ^ N : ℕ) : ℤ) • D₀, hlD₀⟩ : Divisor.degZero (K := L) (F := F)) = ((ℓ ^ N : ℕ) : ℤ) • ⟨D₀, hD₀⟩ := rfl
  rw [h2, pic0_mk_zsmul, hD₀c, TateModule.proj_apply, TateModule.proj_apply]
  exact TateModule.compat_pow x k N

end S_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
