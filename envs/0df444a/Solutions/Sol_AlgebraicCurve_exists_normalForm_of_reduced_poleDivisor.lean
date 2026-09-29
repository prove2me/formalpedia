-- Prove2me | solution 1 for AlgebraicCurve.exists_normalForm_of_reduced_poleDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f4a36c14-1bda-5bb3-9cd3-4b385ebb196a

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_normalForm_of_reduced_poleDivisor
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_normalForm_of_reduced_poleDivisor.AlgebraicCurve Polynomial"

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.heightOneSpectrum_asIdeal Place.adicValuation Place.ord_zero Place.ord_one Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace genusFF LSpace ell mem_lSpace_iff_ord lSpace_mono IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue isCurveOver_of_isAlgClosed_of_transcendental exists_separating_transcendental_of_perfectField ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental"
namespace NormalFormRR
p2m_open "AlgebraicCurve"

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem exists_compl_within {V W : Submodule K F} (h : V ≤ W) :
    ∃ U : Submodule K F, U ≤ W ∧ V ⊔ U = W ∧ V ⊓ U = ⊥ := by
  obtain ⟨Q, hQ⟩ := (V.comap W.subtype).exists_isCompl
  refine ⟨Q.map W.subtype, Submodule.map_subtype_le W Q, ?_, ?_⟩
  · apply le_antisymm (sup_le h (Submodule.map_subtype_le W Q))
    intro w hw
    have htop : (⟨w, hw⟩ : W) ∈ (V.comap W.subtype) ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
    have : w = (a : F) + (b : F) := by
      have := congrArg Subtype.val hab; simpa using this.symm
    rw [this]
    exact Submodule.add_mem_sup ha ⟨b, hb, rfl⟩
  · rw [eq_bot_iff]
    rintro y ⟨hyV, ⟨b, hb, rfl⟩⟩
    have hbV : b ∈ V.comap W.subtype := hyV
    have : b ∈ (V.comap W.subtype) ⊓ Q := ⟨hbV, hb⟩
    rw [hQ.inf_eq_bot, Submodule.mem_bot] at this
    rw [this]; simp

theorem finrank_compl_within {V W U : Submodule K F} [FiniteDimensional K W]
    (hsup : V ⊔ U = W) (hinf : V ⊓ U = ⊥) :
    Module.finrank K U = Module.finrank K W - Module.finrank K V := by
  have hV : V ≤ W := hsup ▸ le_sup_left
  have hU : U ≤ W := hsup ▸ le_sup_right
  haveI : FiniteDimensional K V := Submodule.finiteDimensional_of_le hV
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  have h := Submodule.finrank_sup_add_finrank_inf_eq V U
  rw [hsup, hinf, finrank_bot, add_zero] at h
  omega

theorem ord_pos_iff (v : Place K F) {f : F} (hf : f ≠ 0) : 0 < v.ord f ↔ v.adicValuation f < 1 := by
  rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem mem_toValuationSubring_iff_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  constructor
  · intro h
    exact ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf
  · intro h
    by_contra hmem
    have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
    have hnu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
      intro hu
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      apply hmem
      have hwF : (f⁻¹ : F) * (w : F) = 1 := by
        have := congrArg (fun z : v.toValuationSubring => (z : F)) hw
        simpa using this
      have hwf : (w : F) = f := by
        have h2 := congrArg (fun z => f * z) hwF
        simp only [← mul_assoc, mul_inv_cancel₀ hf, one_mul, mul_one] at h2
        exact h2
      rw [← hwf]
      exact w.2
    have hmax : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hlt : v.adicValuation f⁻¹ < 1 := by
      rw [← Place.heightOneSpectrum_asIdeal] at hmax
      have := (v.heightOneSpectrum.valuation_lt_one_iff_mem (K := F) ⟨f⁻¹, hinv⟩).mpr hmax
      simpa [Place.adicValuation] using this
    have := (ord_pos_iff v (inv_ne_zero hf)).mpr hlt
    rw [v.ord_inv] at this
    omega

theorem mem_maximalIdeal_iff_ord_pos (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ 0 < v.ord f := by
  rw [← Place.heightOneSpectrum_asIdeal, ← v.heightOneSpectrum.valuation_lt_one_iff_mem (K := F),
    ord_pos_iff v hf0]
  rfl

noncomputable def rev (d : ℕ) (q : K[X]) : K[X] :=
  ∑ n ∈ Finset.range (d + 1), Polynomial.C (q.coeff n) * Polynomial.X ^ (d - n)

theorem pow_mul_aeval_eq_aeval_rev {d : ℕ} {q : K[X]} (hq : q.natDegree ≤ d) {t w : F}
    (hwt : w * t = 1) : w ^ d * Polynomial.aeval t q = Polynomial.aeval w (rev d q) := by
  have hq' : Polynomial.aeval t q = ∑ n ∈ Finset.range (d + 1), algebraMap K F (q.coeff n) * t ^ n := by
    conv_lhs => rw [Polynomial.as_sum_range' q (d + 1) (Nat.lt_succ_of_le hq)]
    simp [Polynomial.aeval_monomial]
  rw [hq', Finset.mul_sum]
  simp only [rev, map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnd : n ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hpow : w ^ d = w ^ (d - n) * w ^ n := by rw [← pow_add, Nat.sub_add_cancel hnd]
  rw [hpow]
  have hwt' : w ^ n * t ^ n = 1 := by rw [← mul_pow, hwt, one_pow]
  calc w ^ (d - n) * w ^ n * ((algebraMap K F) (q.coeff n) * t ^ n)
      = (algebraMap K F) (q.coeff n) * w ^ (d - n) * (w ^ n * t ^ n) := by ring
    _ = (algebraMap K F) (q.coeff n) * w ^ (d - n) := by rw [hwt', mul_one]

theorem rev_coeff_zero (d : ℕ) (q : K[X]) : (rev d q).coeff 0 = q.coeff d := by
  simp only [rev, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single d]
  · simp
  · intro n hn hnd
    have : n ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [if_neg (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h

theorem hom_aeval_of_map_eq_zero {O : Type*} [CommRing O] [Algebra K O] (φ : O →+* K)
    (hφ : ∀ c : K, φ (algebraMap K O c) = c) {w : O} (hw : φ w = 0) (q : K[X]) :
    φ (Polynomial.aeval w q) = q.coeff 0 := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hw]
  have : φ.comp (algebraMap K O) = RingHom.id K := RingHom.ext hφ
  rw [this, Polynomial.eval₂_id, Polynomial.coeff_zero_eq_eval_zero]

section Eval

variable [IsAlgClosed K] [IsCurveOver K F]

theorem algebraMap_residueField_bijective (v : Place K F) :
    Function.Bijective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def ev (v : Place K F) : v.toValuationSubring →+* K :=
  ((RingEquiv.ofBijective (algebraMap K v.ResidueField) (algebraMap_residueField_bijective v)).symm :
      v.ResidueField →+* K).comp (IsLocalRing.residue v.toValuationSubring)

theorem algebraMap_ev (v : Place K F) (f : v.toValuationSubring) :
    algebraMap K v.ResidueField (ev v f) = IsLocalRing.residue v.toValuationSubring f := by
  show algebraMap K v.ResidueField ((RingEquiv.ofBijective (algebraMap K v.ResidueField)
    (algebraMap_residueField_bijective v)).symm (IsLocalRing.residue v.toValuationSubring f)) = _
  exact (RingEquiv.ofBijective (algebraMap K v.ResidueField)
    (algebraMap_residueField_bijective v)).apply_symm_apply _

theorem ev_eq_zero_iff (v : Place K F) (f : v.toValuationSubring) :
    ev v f = 0 ↔ f ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff, ← algebraMap_ev]
  constructor
  · intro h; rw [h, map_zero]
  · intro h
    exact (algebraMap K v.ResidueField).injective (by rw [h, map_zero])

theorem ev_algebraMap (v : Place K F) (c : K) :
    ev v ⟨algebraMap K F c, v.algebraMap_mem' c⟩ = c := by
  apply (algebraMap K v.ResidueField).injective
  rw [algebraMap_ev]
  rfl

end Eval

end AlgebraicCurve.NormalFormRR

set_option maxHeartbeats 6400000 in
open AlgebraicCurve.NormalFormRR in
theorem solution
    (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (P : Fin (2 * genusFF K F + 1) → Place K F)
    (hP : Function.Injective P) (hx : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hdegF : Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F = 2 * genusFF K F + 1)
    (hpole : ∀ j, (P j).ord x = -1)
    (hfin : ∀ v : Place K F, v ∉ Set.range P → 0 ≤ v.ord x) :
    ∃ (D : Divisor K F) (e : Fin (2 * genusFF K F + 1) → F)
      (d : Fin (2 * genusFF K F + 1) → ℕ)
      (q : Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → K[X])
      (τ : Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → K),
      (∀ v : Place K F, D v = max 0 (-v.ord x)) ∧
      e 0 = 1 ∧ d 0 = 0 ∧ (∀ i, i ≠ 0 → d i = 1 ∨ d i = 2) ∧ (∑ i, d i = 3 * genusFF K F) ∧
      (∀ (k : ℕ) (f : F), f ∈ riemannRochSpace (k • D) ↔
        ∃ c : Fin (2 * genusFF K F + 1) → K[X],
          (∀ i, c i ∈ Polynomial.degreeLT K (k + 1 - d i)) ∧
          f = ∑ i, Polynomial.aeval x (c i) * e i) ∧
      (∀ c : Fin (2 * genusFF K F + 1) → K[X], ∑ i, Polynomial.aeval x (c i) * e i = 0 → c = 0) ∧
      (∀ z : F, ∃ r : K[X], r ≠ 0 ∧ ∃ k : ℕ, Polynomial.aeval x r * z ∈ riemannRochSpace (k • D)) ∧
      (∀ i j, e i * e j = ∑ k, Polynomial.aeval x (q i j k) * e k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (q i j k).natDegree ≤ d i + d j - d k) ∧
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      (∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, (q i i' k).coeff (d i + d i' - d k) * τ j k) := by
  classical
  haveI := hfd
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = genusFF K F := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * genusFF K F + 1 := ⟨_, rfl⟩

  obtain ⟨t, ht, hfint, hsept⟩ := exists_separating_transcendental_of_perfectField hx hfd
  have hRR : ∀ E : Divisor K F, 2 * (g : ℤ) - 1 ≤ E.degree → (ell E : ℤ) = E.degree + 1 - g := by
    intro E hE
    rw [hg] at hE ⊢
    exact ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable K t ht hfint hsept E hE
  have hdeg1 : ∀ v : Place K F, (v.deg : ℤ) = 1 := fun v => by
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed v]; rfl
  let D : Divisor K F := ∑ j, Finsupp.single (P j) 1
  have hDapply : ∀ v, D v = ∑ j, (Finsupp.single (P j) (1 : ℤ)) v := fun v =>
    Finsupp.finsetSum_apply _ _ v
  have hDP : ∀ j, D (P j) = 1 := by
    intro j
    rw [hDapply, Finset.sum_eq_single j]
    · exact Finsupp.single_eq_same
    · intro i _ hij
      exact Finsupp.single_eq_of_ne (fun h => hij (hP h).symm)
    · intro h; exact absurd (Finset.mem_univ j) h
  have hDout : ∀ v, v ∉ Set.range P → D v = 0 := by
    intro v hv
    rw [hDapply]
    refine Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact hv ⟨j, rfl⟩
  have hD : ∀ v : Place K F, D v = max 0 (-v.ord x) := by
    intro v
    by_cases hv : v ∈ Set.range P
    · obtain ⟨j, rfl⟩ := hv
      rw [hDP, hpole]; rfl
    · rw [hDout v hv]
      have := hfin v hv
      rw [max_eq_left]; omega
  have hDnn : ∀ v, 0 ≤ D v := fun v => by rw [hD]; exact le_max_left _ _
  have hdegD : D.degree = m := by
    show Divisor.degree (∑ j, Finsupp.single (P j) 1) = m
    rw [map_sum]
    simp only [Divisor.degree_single, hdeg1, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [hm]
  have hx0 : x ≠ 0 := by
    intro h
    have := hpole 0
    rw [h, Place.ord_zero] at this
    exact absurd this (by norm_num)

  set L : ℕ → Submodule K F := fun k => LSpace (k • D) with hLdef
  have hmemL : ∀ (k : ℕ) (f : F), f ∈ L k ↔ f = 0 ∨ ∀ v, -((k : ℤ) * D v) ≤ v.ord f := by
    intro k f
    show f ∈ LSpace (k • D) ↔ _
    rw [mem_lSpace_iff_ord]
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
  have hmemL' : ∀ (k : ℕ) (f : F), f ≠ 0 →
      (f ∈ L k ↔ (∀ j, -(k : ℤ) ≤ (P j).ord f) ∧ ∀ v, v ∉ Set.range P → 0 ≤ v.ord f) := by
    intro k f hf
    rw [hmemL, or_iff_right hf]
    constructor
    · intro h
      refine ⟨fun j => by have := h (P j); rwa [hDP, mul_one] at this, fun v hv => ?_⟩
      have := h v; rwa [hDout v hv, mul_zero, neg_zero] at this
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ Set.range P
      · obtain ⟨j, rfl⟩ := hv; rw [hDP, mul_one]; exact h1 j
      · rw [hDout v hv, mul_zero, neg_zero]; exact h2 v hv
  have hLmono : ∀ k, L k ≤ L (k + 1) := fun k =>
    lSpace_mono fun v => by
      simp only [Finsupp.coe_smul, Pi.smul_apply]
      exact nsmul_le_nsmul_left (hDnn v) (Nat.le_succ k)
  have hLmono' : ∀ {j k}, j ≤ k → L j ≤ L k := by
    intro j k hjk
    induction hjk with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hLmono _)

  have hxmul : ∀ (k : ℕ) (f : F), f ∈ L k → x * f ∈ L (k + 1) := by
    intro k f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [mul_zero]; exact Submodule.zero_mem _
    obtain ⟨h1, h2⟩ := (hmemL' k f hf0).mp hf
    refine (hmemL' (k + 1) (x * f) (mul_ne_zero hx0 hf0)).mpr ⟨fun j => ?_, fun v hv => ?_⟩
    · rw [(P j).ord_mul hx0 hf0, hpole]; have := h1 j; push_cast; omega
    · rw [v.ord_mul hx0 hf0]; have := h2 v hv; have := hfin v hv; omega

  have hxdiv : ∀ (N k : ℕ) (f : F), f ∈ L N → x * f ∈ L (k + 1) → f ∈ L k := by
    intro N k f hfN hxf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Submodule.zero_mem _
    obtain ⟨-, h2⟩ := (hmemL' N f hf0).mp hfN
    obtain ⟨h1, -⟩ := (hmemL' (k + 1) (x * f) (mul_ne_zero hx0 hf0)).mp hxf
    refine (hmemL' k f hf0).mpr ⟨fun j => ?_, h2⟩
    have := h1 j
    rw [(P j).ord_mul hx0 hf0, hpole] at this
    push_cast at this; omega

  have h1L0 : (1 : F) ∈ L 0 := (hmemL 0 1).mpr (Or.inr fun v => by rw [Place.ord_one]; simp)
  have hxL1 : x ∈ L 1 := by
    refine (hmemL' 1 x hx0).mpr ⟨fun j => by rw [hpole]; norm_num, fun v hv => hfin v hv⟩
  have hxL0 : x ∉ L 0 := by
    intro h
    obtain ⟨h1, -⟩ := (hmemL' 0 x hx0).mp h
    have := h1 0
    rw [hpole] at this
    norm_num at this

  have hellL : ∀ k : ℕ, 1 ≤ k → (ell (k • D) : ℤ) = k * m + 1 - g := by
    intro k hk
    have hdegk : Divisor.degree (k • D) = k * m := by rw [map_nsmul, hdegD]; simp
    have hkm : (m : ℤ) ≤ k * m := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hk)
    rw [hRR (k • D) (by rw [hdegk]; push_cast [hm] at hkm ⊢; omega), hdegk]
  obtain ⟨hell0, -⟩ := exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD
  have hfinrankL : ∀ k : ℕ, 1 ≤ k → (Module.finrank K (L k) : ℤ) = k * m + 1 - g := hellL
  have hfinrankL0 : Module.finrank K (L 0) = 1 := by
    show ell ((0 : ℕ) • D) = 1
    rw [zero_smul]; exact hell0
  have hgm : (m : ℤ) = 2 * g + 1 := by simp [hm, hg]
  haveI hfinL : ∀ k, Module.Finite K (L k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Module.finite_of_finrank_eq_succ hfinrankL0
    · apply Module.finite_of_finrank_pos
      have : (0 : ℤ) < Module.finrank K (L k) := by rw [hfinrankL k hk]; nlinarith
      exact_mod_cast this

  have hL0 : ∀ f : F, f ∈ L 0 → ∃ c : K, f = algebraMap K F c := by
    intro f hf
    have hspan : Submodule.span K {(1 : F)} = L 0 := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact h1L0
      · rw [finrank_span_singleton one_ne_zero, hfinrankL0]
    have hf' : f ∈ Submodule.span K {(1 : F)} := by rw [hspan]; exact hf
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf'
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  have hconstL0 : ∀ c : K, algebraMap K F c ∈ L 0 := fun c => by
    have : algebraMap K F c = c • (1 : F) := by rw [Algebra.smul_def, mul_one]
    rw [this]; exact Submodule.smul_mem _ c h1L0

  have hli1x : LinearIndependent K ![(1 : F), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht0 : t = 0
    · subst ht0
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hxL0
      have : x = algebraMap K F (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff ((_root_.map_ne_zero _).mpr ht0)]
        linear_combination hst
      rw [this]; exact hconstL0 _
  set V₁ : Submodule K F := Submodule.span K (Set.range ![(1 : F), x]) with hV₁
  have hV₁fin : Module.finrank K V₁ = 2 := by
    rw [hV₁, finrank_span_eq_card hli1x]; rfl
  have hV₁le : V₁ ≤ L 1 := by
    rw [hV₁, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hLmono 0 h1L0
    · exact hxL1
  have hmemV₁ : ∀ f, f ∈ V₁ ↔ ∃ a b : K, f = algebraMap K F a + algebraMap K F b * x := by
    intro f
    rw [hV₁, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨c 0, c 1, ?_⟩
      simp [Fin.sum_univ_succ, Algebra.smul_def]
    · rintro ⟨a, b, rfl⟩
      refine ⟨![a, b], ?_⟩
      simp [Fin.sum_univ_succ, Algebra.smul_def]

  obtain ⟨U, hUle, hUsup, hUinf⟩ := exists_compl_within hV₁le
  haveI : Module.Finite K U := Submodule.finiteDimensional_of_le hUle
  have hUfin : Module.finrank K U = genusFF K F := by
    have h := finrank_compl_within (K := K) hUsup hUinf
    have h1 := hfinrankL 1 le_rfl
    rw [hV₁fin] at h
    have : (Module.finrank K U : ℤ) = Module.finrank K (L 1) - 2 := by
      have h2 : 2 ≤ Module.finrank K (L 1) := hV₁fin ▸ Submodule.finrank_mono hV₁le
      omega
    rw [h1, hgm] at this
    push_cast at this
    have : (Module.finrank K U : ℤ) = g := by linarith
    rw [hg] at this
    exact_mod_cast this
  let uB : Module.Basis (Fin (genusFF K F)) K U := Module.finBasisOfFinrankEq K U hUfin

  let μ : F →ₗ[K] F := LinearMap.mulLeft K x
  have hμ : ∀ f, μ f = x * f := fun _ => rfl
  have hμinj : Function.Injective μ := mul_right_injective₀ hx0
  have hmapfin : ∀ k, Module.finrank K ((L k).map μ) = Module.finrank K (L k) := fun k =>
    (Submodule.equivMapOfInjective μ hμinj (L k)).finrank_eq.symm
  have hmaple : ∀ k, (L k).map μ ≤ L (k + 1) := by
    rintro k _ ⟨f, hf, rfl⟩
    exact hxmul k f hf
  have hinfmap : ∀ k, L (k + 1) ⊓ (L (k + 1)).map μ = (L k).map μ := by
    intro k
    apply le_antisymm
    · rintro y ⟨hy1, ⟨f, hf, rfl⟩⟩
      exact ⟨f, hxdiv (k + 1) k f hf hy1, rfl⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact ⟨hxmul k f hf, ⟨f, hLmono k hf, rfl⟩⟩
  set V₂ : Submodule K F := L 1 ⊔ (L 1).map μ with hV₂
  have hV₂le : V₂ ≤ L 2 := sup_le (hLmono 1) (hmaple 1)
  have hV₂fin : (Module.finrank K V₂ : ℤ) = 2 * g + 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (L 1) ((L 1).map μ)
    rw [hinfmap 0, hmapfin, hmapfin] at h
    have h1 := hfinrankL 1 le_rfl
    rw [hgm] at h1
    push_cast at h1
    have h0 : (Module.finrank K (L 0) : ℤ) = 1 := by rw [hfinrankL0]; rfl
    have hZ : (Module.finrank K V₂ : ℤ) + Module.finrank K (L 0) =
        Module.finrank K (L 1) + Module.finrank K (L 1) := by exact_mod_cast h
    linarith

  obtain ⟨E, hEle, hEsup, hEinf⟩ := exists_compl_within hV₂le
  haveI : Module.Finite K E := Submodule.finiteDimensional_of_le hEle
  have hEfin : Module.finrank K E = genusFF K F := by
    have h := finrank_compl_within (K := K) hEsup hEinf
    have h2 := hfinrankL 2 (by norm_num)
    rw [hgm] at h2
    have hle : Module.finrank K V₂ ≤ Module.finrank K (L 2) := Submodule.finrank_mono hV₂le
    have : (Module.finrank K E : ℤ) = Module.finrank K (L 2) - Module.finrank K V₂ := by omega
    rw [h2, hV₂fin] at this
    push_cast at this
    have : (Module.finrank K E : ℤ) = g := by linarith
    rw [hg] at this
    exact_mod_cast this
  let eB : Module.Basis (Fin (genusFF K F)) K E := Module.finBasisOfFinrankEq K E hEfin

  have hlt2 : ∀ i : Fin (2 * genusFF K F), ¬((i : ℕ) < genusFF K F) → (i : ℕ) - genusFF K F < genusFF K F := by
    intro i hi; have := i.2; omega
  let e : Fin (2 * genusFF K F + 1) → F := fun i =>
    Fin.cases (1 : F)
      (fun i' : Fin (2 * genusFF K F) =>
        if h : (i' : ℕ) < genusFF K F then ((uB ⟨i', h⟩ : U) : F)
        else ((eB ⟨(i' : ℕ) - genusFF K F, hlt2 i' h⟩ : E) : F)) i
  let d : Fin (2 * genusFF K F + 1) → ℕ := fun i =>
    Fin.cases 0 (fun i' : Fin (2 * genusFF K F) => if (i' : ℕ) < genusFF K F then 1 else 2) i
  have he0 : e 0 = 1 := rfl
  have hd0 : d 0 = 0 := rfl
  have heS : ∀ i' : Fin (2 * genusFF K F), e i'.succ =
      (if h : (i' : ℕ) < genusFF K F then ((uB ⟨i', h⟩ : U) : F)
        else ((eB ⟨(i' : ℕ) - genusFF K F, hlt2 i' h⟩ : E) : F)) := fun _ => rfl
  have hdS : ∀ i' : Fin (2 * genusFF K F), d i'.succ = (if (i' : ℕ) < genusFF K F then 1 else 2) :=
    fun _ => rfl
  have hd12 : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2 := by
    intro i hi
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    rw [hdS]; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hdle : ∀ i, d i ≤ 2 := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hd0]; exact Nat.zero_le _
    · rcases hd12 i hi with h | h <;> omega
  have hdsum : ∑ i, d i = 3 * genusFF K F := by
    rw [Fin.sum_univ_succ, hd0, zero_add]
    simp only [hdS]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < genusFF K F then 1 else 2) (2 * genusFF K F),
      Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (genusFF K F)) (by omega : genusFF K F ≤ 2 * genusFF K F)]
    rw [Finset.sum_congr rfl (fun i (hi : i ∈ Finset.Ico 0 (genusFF K F)) => if_pos (Finset.mem_Ico.mp hi).2),
      Finset.sum_congr rfl (fun i (hi : i ∈ Finset.Ico (genusFF K F) (2 * genusFF K F)) =>
        if_neg (not_lt.mpr (Finset.mem_Ico.mp hi).1))]
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    omega

  have heL : ∀ i, e i ∈ L (d i) := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact h1L0
    · rw [heS, hdS]
      by_cases h : (i' : ℕ) < genusFF K F
      · rw [dif_pos h, if_pos h]; exact hUle (uB ⟨i', h⟩).2
      · rw [dif_neg h, if_neg h]; exact hEle (eB ⟨_, hlt2 i' h⟩).2

  have hpowL : ∀ (a j : ℕ) (f : F), f ∈ L j → x ^ a * f ∈ L (a + j) := by
    intro a j f hf
    induction a with
    | zero => rw [pow_zero, one_mul, zero_add]; exact hf
    | succ a ih =>
      rw [pow_succ, mul_comm (x ^ a) x, mul_assoc, show a + 1 + j = (a + j) + 1 by ring]
      exact hxmul _ _ ih
  have hmulL : ∀ (a b : ℕ) (f h : F), f ∈ L a → h ∈ L b → f * h ∈ L (a + b) := by
    intro a b f h hf hh
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [zero_mul]; exact Submodule.zero_mem _
    rcases eq_or_ne h 0 with rfl | hh0
    · rw [mul_zero]; exact Submodule.zero_mem _
    obtain ⟨hf1, hf2⟩ := (hmemL' a f hf0).mp hf
    obtain ⟨hh1, hh2⟩ := (hmemL' b h hh0).mp hh
    refine (hmemL' (a + b) (f * h) (mul_ne_zero hf0 hh0)).mpr ⟨fun j => ?_, fun v hv => ?_⟩
    · rw [(P j).ord_mul hf0 hh0]; have := hf1 j; have := hh1 j; push_cast; omega
    · rw [v.ord_mul hf0 hh0]; have := hf2 v hv; have := hh2 v hv; omega

  let fam : (k : ℕ) → (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)) → F :=
    fun k σ => x ^ (σ.2 : ℕ) * e σ.1
  have hfam : ∀ k σ, fam k σ = x ^ (σ.2 : ℕ) * e σ.1 := fun _ _ => rfl
  let S : ℕ → Submodule K F := fun k => Submodule.span K (Set.range (fam k))
  have hfammem : ∀ k σ, fam k σ ∈ S k := fun k σ => Submodule.subset_span ⟨σ, rfl⟩
  have hmonS : ∀ (k a : ℕ) (i : Fin (2 * genusFF K F + 1)), a + d i ≤ k → x ^ a * e i ∈ S k := by
    intro k a i h
    exact hfammem k ⟨i, ⟨a, by omega⟩⟩
  have hfamL : ∀ k σ, fam k σ ∈ L k := by
    rintro k ⟨i, a⟩
    have ha : (a : ℕ) + d i ≤ k := by have := a.2; omega
    exact hLmono' ha (hpowL a (d i) (e i) (heL i))
  have hSL : ∀ k, S k ≤ L k := fun k => Submodule.span_le.mpr (by rintro _ ⟨σ, rfl⟩; exact hfamL k σ)
  have hmemS : ∀ k f, f ∈ S k ↔ ∃ α : (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)) → K,
      ∑ σ, α σ • fam k σ = f := fun k f => Submodule.mem_span_range_iff_exists_fun K
  have hxS : ∀ k f, f ∈ S k → x * f ∈ S (k + 1) := by
    intro k f hf
    obtain ⟨α, rfl⟩ := (hmemS k f).mp hf
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [mul_smul_comm]
    refine Submodule.smul_mem _ _ ?_
    rw [hfam, ← mul_assoc, ← pow_succ']
    exact hmonS (k + 1) _ _ (by have := σ.2.2; omega)
  have hSmono : ∀ k, S k ≤ S (k + 1) := by
    intro k
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨σ, rfl⟩
    exact hmonS (k + 1) _ _ (by have := σ.2.2; omega)

  have hLS0 : L 0 ≤ S 0 := by
    intro f hf
    obtain ⟨c, rfl⟩ := hL0 f hf
    have : algebraMap K F c = c • (x ^ 0 * e 0) := by rw [he0, pow_zero, mul_one, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hmonS 0 0 0 (by rw [hd0]))
  have hUS1 : U ≤ S 1 := by
    intro u hu
    have hrepr := uB.sum_repr ⟨u, hu⟩
    have : u = ∑ l, (uB.repr ⟨u, hu⟩ l) • ((uB l : U) : F) := by
      have h := congrArg (fun z : U => (z : F)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h.symm
    rw [this]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    have hl : ((⟨l, by omega⟩ : Fin (2 * genusFF K F)) : ℕ) < genusFF K F := l.2
    have heq : ((uB l : U) : F) = x ^ 0 * e (Fin.succ ⟨l, by omega⟩) := by
      rw [heS, dif_pos hl, pow_zero, one_mul]
    rw [heq]
    exact hmonS 1 0 _ (by rw [hdS, if_pos hl])
  have hLS1 : L 1 ≤ S 1 := by
    rw [← hUsup]
    refine sup_le ?_ hUS1
    intro f hf
    obtain ⟨a, b, rfl⟩ := (hmemV₁ f).mp hf
    refine Submodule.add_mem _ ?_ ?_
    · have : algebraMap K F a = a • (x ^ 0 * e 0) := by rw [he0, pow_zero, mul_one, Algebra.smul_def, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ (hmonS 1 0 0 (by simp [hd0]))
    · have : algebraMap K F b * x = b • (x ^ 1 * e 0) := by rw [he0, pow_one, mul_one, Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ (hmonS 1 1 0 (by simp [hd0]))
  have hES2 : E ≤ S 2 := by
    intro u hu
    have hrepr := eB.sum_repr ⟨u, hu⟩
    have : u = ∑ l, (eB.repr ⟨u, hu⟩ l) • ((eB l : E) : F) := by
      have h := congrArg (fun z : E => (z : F)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h.symm
    rw [this]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    have hl : ¬(((⟨genusFF K F + l, by omega⟩ : Fin (2 * genusFF K F)) : ℕ) < genusFF K F) := by
      simp
    have heq : ((eB l : E) : F) = x ^ 0 * e (Fin.succ ⟨genusFF K F + l, by omega⟩) := by
      rw [heS, dif_neg hl, pow_zero, one_mul]
      congr 2
      · exact Fin.ext (by simp)
    rw [heq]
    exact hmonS 2 0 _ (by rw [hdS, if_neg hl])
  have hLS2 : L 2 ≤ S 2 := by
    rw [← hEsup]
    refine sup_le ?_ hES2
    refine sup_le ((hLS1.trans (hSmono 1))) ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hxS 1 f (hLS1 hf)

  have hT : ∀ k', 1 ≤ k' → L (k' + 1) ⊔ (L (k' + 1)).map μ = L (k' + 1 + 1) := by
    intro k' hk'
    apply Submodule.eq_of_le_of_finrank_eq (sup_le (hLmono _) (hmaple _))
    have h := Submodule.finrank_sup_add_finrank_inf_eq (L (k' + 1)) ((L (k' + 1)).map μ)
    rw [hinfmap k', hmapfin, hmapfin] at h
    have h1 := hfinrankL (k' + 1) (by omega)
    have h2 := hfinrankL k' hk'
    have h3 := hfinrankL (k' + 1 + 1) (by omega)
    push_cast at h1 h2 h3
    zify at h
    rw [h1, h2] at h
    have key : (Module.finrank K ↥(L (k' + 1) ⊔ (L (k' + 1)).map μ) : ℤ) =
        Module.finrank K (L (k' + 1 + 1)) := by
      rw [h3]; linarith
    exact_mod_cast key
  have hstep : ∀ k, 2 ≤ k → L k ≤ S k → L (k + 1) ≤ S (k + 1) := by
    intro k hk hind
    have hk1 : k - 1 + 1 = k := by omega
    have hTk : L k ⊔ (L k).map μ = L (k + 1) := by
      have := hT (k - 1) (by omega)
      rwa [hk1] at this
    rw [← hTk]
    refine sup_le (hind.trans (hSmono k)) ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hxS k f (hind hf)
  have hLS : ∀ k, L k ≤ S k := by
    intro k
    induction k with
    | zero => exact hLS0
    | succ k ih =>
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · exact hLS1
        · exact hLS2
      · exact hstep k hk ih
  have hLeqS : ∀ k, L k = S k := fun k => le_antisymm (hLS k) (hSL k)

  have hcard : ∀ k, 1 ≤ k →
      (Fintype.card (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)) : ℤ) = k * m + 1 - g := by
    intro k hk
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have : (∑ i : Fin (2 * genusFF K F + 1), ((k + 1 - d i : ℕ) : ℤ)) =
        ∑ i : Fin (2 * genusFF K F + 1), ((k : ℤ) + 1 - d i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hdle i; omega
    push_cast
    rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hds : (∑ i : Fin (2 * genusFF K F + 1), (d i : ℤ)) = 3 * g := by
      rw [hg]; exact_mod_cast hdsum
    rw [hds, hgm]
    push_cast
    rw [← hg]
    ring
  have hli : ∀ k, 1 ≤ k → LinearIndependent K (fam k) := by
    intro k hk
    let famL : (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)) → L k := fun σ => ⟨fam k σ, hfamL k σ⟩
    have htop : ⊤ ≤ Submodule.span K (Set.range famL) := by
      rintro ⟨y, hy⟩ -
      have hyS : y ∈ S k := hLS k hy
      have hrange : Set.range (fam k) = (L k).subtype '' Set.range famL := by
        ext z; constructor
        · rintro ⟨σ, rfl⟩; exact ⟨famL σ, ⟨σ, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩; exact ⟨σ, rfl⟩
      have : S k = (Submodule.span K (Set.range famL)).map (L k).subtype := by
        show Submodule.span K (Set.range (fam k)) = _
        rw [hrange, Submodule.span_image]
      rw [this] at hyS
      obtain ⟨z, hz, hzy⟩ := hyS
      have : z = ⟨y, hy⟩ := Subtype.ext hzy
      rw [← this]; exact hz
    have hcardk : Fintype.card (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)) =
        Module.finrank K (L k) := by
      have := hcard k hk
      rw [← hfinrankL k hk] at this
      exact_mod_cast this
    have hliL : LinearIndependent K famL := linearIndependent_of_top_le_span_of_card_eq_finrank htop hcardk
    exact hliL.map' (L k).subtype (Submodule.ker_subtype _)

  have haevalsum : ∀ (k : ℕ) (i : Fin (2 * genusFF K F + 1)) (c : K[X]), c.natDegree < k + 1 - d i →
      Polynomial.aeval x c * e i = ∑ a : Fin (k + 1 - d i), c.coeff a • fam k ⟨i, a⟩ := by
    intro k i c hc
    conv_lhs => rw [Polynomial.as_sum_range' c (k + 1 - d i) hc]
    rw [map_sum, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun a => Polynomial.aeval x (monomial a (c.coeff a)) * e i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.aeval_monomial, hfam, Algebra.smul_def, mul_assoc]
  have hsigma : ∀ (k : ℕ) (β : (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)) → F),
      ∑ i, ∑ a : Fin (k + 1 - d i), β ⟨i, a⟩ = ∑ σ, β σ := by
    intro k β
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

  have hind : ∀ c : Fin (2 * genusFF K F + 1) → K[X], ∑ i, Polynomial.aeval x (c i) * e i = 0 → c = 0 := by
    intro c hc
    set k : ℕ := 2 + ∑ i, (c i).natDegree with hk
    have hck : ∀ i, (c i).natDegree < k + 1 - d i := by
      intro i
      have h1 : (c i).natDegree ≤ ∑ i, (c i).natDegree :=
        Finset.single_le_sum (f := fun i => (c i).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have := hdle i; omega
    have hsum : ∑ σ : (Σ i : Fin (2 * genusFF K F + 1), Fin (k + 1 - d i)), (c σ.1).coeff σ.2 • fam k σ = 0 := by
      rw [← hc, ← hsigma k (fun σ => (c σ.1).coeff σ.2 • fam k σ)]
      exact Finset.sum_congr rfl fun i _ => (haevalsum k i (c i) (hck i)).symm
    have hzero := Fintype.linearIndependent_iff.mp (hli k (by omega)) _ hsum
    funext i
    ext a
    rw [Pi.zero_apply, Polynomial.coeff_zero]
    by_cases ha : a < k + 1 - d i
    · exact hzero ⟨i, ⟨a, ha⟩⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hck i; omega)

  have hL : ∀ (k : ℕ) (f : F), f ∈ L k ↔
      ∃ c : Fin (2 * genusFF K F + 1) → K[X],
        (∀ i, c i ∈ Polynomial.degreeLT K (k + 1 - d i)) ∧ f = ∑ i, Polynomial.aeval x (c i) * e i := by
    intro k f
    constructor
    · intro hf
      obtain ⟨α, rfl⟩ := (hmemS k f).mp (hLS k hf)
      refine ⟨fun i => ∑ a : Fin (k + 1 - d i), Polynomial.monomial (a : ℕ) (α ⟨i, a⟩), fun i => ?_, ?_⟩
      · refine Submodule.sum_mem _ fun a _ => Polynomial.mem_degreeLT.mpr ?_
        exact (Polynomial.degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr a.2)
      · rw [← hsigma k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Polynomial.aeval_monomial, hfam, Algebra.smul_def, mul_assoc]
    · rintro ⟨c, hc, rfl⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases h0 : c i = 0
      · rw [h0, map_zero, zero_mul]; exact Submodule.zero_mem _
      have hci : (c i).natDegree < k + 1 - d i := by
        have := Polynomial.mem_degreeLT.mp (hc i)
        rw [Polynomial.degree_eq_natDegree h0] at this
        exact_mod_cast this
      rw [haevalsum k i (c i) hci]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hfamL k ⟨i, a⟩)

  have hq : ∀ i j, ∃ c : Fin (2 * genusFF K F + 1) → K[X],
      (∀ k, c k ∈ Polynomial.degreeLT K (d i + d j + 1 - d k)) ∧
        e i * e j = ∑ k, Polynomial.aeval x (c k) * e k :=
    fun i j => (hL (d i + d j) (e i * e j)).mp (hmulL _ _ _ _ (heL i) (heL j))
  choose q hqdeg hmulE using hq
  have hdegq : ∀ i j k, (q i j k).natDegree ≤ d i + d j - d k := by
    intro i j k
    by_cases h0 : q i j k = 0
    · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le _
    · have h1 : (q i j k).natDegree < d i + d j + 1 - d k := by
        have := Polynomial.mem_degreeLT.mp (hqdeg i j k)
        rw [Polynomial.degree_eq_natDegree h0] at this
        exact_mod_cast this
      omega

  have hxconst : ∀ a : K, x - algebraMap K F a ≠ 0 := by
    intro a h
    apply hxL0
    rw [sub_eq_zero.mp h]; exact hconstL0 a
  have hxmem : ∀ v : Place K F, v ∉ Set.range P → x ∈ v.toValuationSubring := fun v hv =>
    (mem_toValuationSubring_iff_ord v hx0).mpr (hfin v hv)
  have hxa : ∀ v : Place K F, ∃ a : K, v ∉ Set.range P → 0 < v.ord (x - algebraMap K F a) := by
    intro v
    by_cases hv : v ∈ Set.range P
    · exact ⟨0, fun h => absurd hv h⟩
    refine ⟨ev v ⟨x, hxmem v hv⟩, fun _ => ?_⟩
    have hmem : x - algebraMap K F (ev v ⟨x, hxmem v hv⟩) ∈ v.toValuationSubring :=
      v.toValuationSubring.sub_mem (hxmem v hv) (v.algebraMap_mem' _)
    rw [← mem_maximalIdeal_iff_ord_pos v (hxconst _) hmem, ← ev_eq_zero_iff]
    have : (⟨x - algebraMap K F (ev v ⟨x, hxmem v hv⟩), hmem⟩ : v.toValuationSubring) =
        ⟨x, hxmem v hv⟩ - ⟨algebraMap K F (ev v ⟨x, hxmem v hv⟩), v.algebraMap_mem' _⟩ := rfl
    rw [this, map_sub, ev_algebraMap, sub_self]
  choose a ha using hxa

  have hpolyL : ∀ r : K[X], Polynomial.aeval x r ∈ L r.natDegree := by
    intro r
    refine (hL r.natDegree _).mpr ⟨fun i => if i = 0 then r else 0, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs with hi
      · subst hi
        rw [hd0, Nat.sub_zero]
        exact Polynomial.mem_degreeLT.mpr (lt_of_le_of_lt (Polynomial.degree_le_natDegree)
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)))
      · exact Submodule.zero_mem _
    · rw [Fin.sum_univ_succ]
      simp [he0]
  have hfrac : ∀ z : F, ∃ r : K[X], r ≠ 0 ∧ ∃ k : ℕ, Polynomial.aeval x r * z ∈ L k := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨1, one_ne_zero, 0, by rw [mul_zero]; exact Submodule.zero_mem _⟩
    obtain ⟨Dz, hDz, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz
    let B : Finset (Place K F) := Dz.support.filter fun v => v ∉ Set.range P
    let n : Place K F → ℕ := fun v => (-Dz v).toNat
    let r : K[X] := ∏ w ∈ B, (X - C (a w)) ^ n w
    have hr0 : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
    have hρ : Polynomial.aeval x r = ∏ w ∈ B, (x - algebraMap K F (a w)) ^ n w := by
      simp only [r, map_prod, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    set ρ : F := Polynomial.aeval x r with hρdef
    have hρ0 : ρ ≠ 0 := by
      rw [hρ]; exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hxconst _)
    have hρL := hpolyL r
    obtain ⟨hρP, hρout⟩ := (hmemL' r.natDegree ρ hρ0).mp hρL
    let T : ℕ := ∑ j, n (P j)
    refine ⟨r, hr0, r.natDegree + T, ?_⟩
    refine (hmemL' (r.natDegree + T) (ρ * z) (mul_ne_zero hρ0 hz)).mpr ⟨fun j => ?_, fun v hv => ?_⟩
    · rw [(P j).ord_mul hρ0 hz, ← hDz]
      have h1 := hρP j
      have h2 : -(n (P j) : ℤ) ≤ Dz (P j) := by
        show -(((-Dz (P j)).toNat : ℕ) : ℤ) ≤ Dz (P j)
        have := Int.self_le_toNat (-Dz (P j)); omega
      have h3 : n (P j) ≤ T := Finset.single_le_sum (f := fun j => n (P j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      push_cast; omega
    · rw [v.ord_mul hρ0 hz, ← hDz]
      have h1 := hρout v hv
      by_cases hDv : 0 ≤ Dz v
      · omega
      push Not at hDv
      have hvB : v ∈ B := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), hv⟩
      have hsplit : ρ = (x - algebraMap K F (a v)) ^ n v *
          ∏ w ∈ B.erase v, (x - algebraMap K F (a w)) ^ n w := by
        rw [hρ, Finset.mul_prod_erase B (fun w => (x - algebraMap K F (a w)) ^ n w) hvB]
      have hrest0 : ∏ w ∈ B.erase v, (x - algebraMap K F (a w)) ^ n w ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hxconst _)
      have hrestmem : ∏ w ∈ B.erase v, (x - algebraMap K F (a w)) ^ n w ∈ v.toValuationSubring :=
        prod_mem fun w _ => pow_mem (v.toValuationSubring.sub_mem (hxmem v hv) (v.algebraMap_mem' _)) _
      have hrest : 0 ≤ v.ord (∏ w ∈ B.erase v, (x - algebraMap K F (a w)) ^ n w) :=
        (mem_toValuationSubring_iff_ord v hrest0).mp hrestmem
      have hpow : v.ord ((x - algebraMap K F (a v)) ^ n v) = n v * v.ord (x - algebraMap K F (a v)) := by
        rw [← zpow_natCast, v.ord_zpow]
      have hnv : (n v : ℤ) = -Dz v := by
        show (((-Dz v).toNat : ℕ) : ℤ) = -Dz v
        rw [Int.toNat_of_nonneg (by omega)]
      have hordρ : v.ord ρ = n v * v.ord (x - algebraMap K F (a v)) +
          v.ord (∏ w ∈ B.erase v, (x - algebraMap K F (a w)) ^ n w) := by
        rw [hsplit, v.ord_mul (pow_ne_zero _ (hxconst _)) hrest0, hpow]
      have hav := ha v hv
      rw [hordρ, hnv]
      nlinarith

  set w : F := x⁻¹ with hwdef
  have hw0 : w ≠ 0 := inv_ne_zero hx0
  have hwx : w * x = 1 := inv_mul_cancel₀ hx0
  have hordw : ∀ j, (P j).ord w = 1 := fun j => by rw [hwdef, (P j).ord_inv, hpole]; rfl
  have hwmem : ∀ j, w ∈ (P j).toValuationSubring := fun j =>
    (mem_toValuationSubring_iff_ord _ hw0).mpr (by rw [hordw]; exact zero_le_one)
  have hevw : ∀ j, ev (P j) ⟨w, hwmem j⟩ = 0 := fun j =>
    (ev_eq_zero_iff _ _).mpr ((mem_maximalIdeal_iff_ord_pos _ hw0 _).mpr (by rw [hordw]; exact one_pos))
  have he0' : ∀ i, e i ≠ 0 := by
    intro i h
    have := hind (Pi.single i 1) (by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, map_one, one_mul, h]
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi)
    have := congrFun this i
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this
  have hordE : ∀ j i, -(d i : ℤ) ≤ (P j).ord (e i) := by
    intro j i
    have := ((hmemL' (d i) (e i) (he0' i)).mp (heL i)).1 j
    exact_mod_cast this
  let r : Fin (2 * genusFF K F + 1) → F := fun i => w ^ d i * e i
  have hr : ∀ i, r i = w ^ d i * e i := fun _ => rfl
  have hr0 : ∀ i, r i ≠ 0 := fun i => mul_ne_zero (pow_ne_zero _ hw0) (he0' i)
  have hrmem : ∀ j i, r i ∈ (P j).toValuationSubring := by
    intro j i
    refine (mem_toValuationSubring_iff_ord _ (hr0 i)).mpr ?_
    rw [hr, (P j).ord_mul (pow_ne_zero _ hw0) (he0' i), ← zpow_natCast, (P j).ord_zpow, hordw, mul_one]
    have := hordE j i; omega
  let τ : Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → K := fun j i => ev (P j) ⟨r i, hrmem j i⟩
  have hτ : ∀ j i, τ j i = ev (P j) ⟨r i, hrmem j i⟩ := fun _ _ => rfl
  have hτ0 : ∀ j, τ j 0 = 1 := by
    intro j
    rw [hτ]
    have : (⟨r 0, hrmem j 0⟩ : (P j).toValuationSubring) = 1 := Subtype.ext (by
      show w ^ d 0 * e 0 = 1; rw [hd0, he0, pow_zero, one_mul])
    rw [this, map_one]

  have hτmul : ∀ j i i', i ≠ 0 → i' ≠ 0 →
      τ j i * τ j i' = ∑ k, (q i i' k).coeff (d i + d i' - d k) * τ j k := by
    intro j i i' hi hi'
    have hdk : ∀ k, d k ≤ d i + d i' := by
      intro k
      rcases hd12 i hi with h1 | h1 <;> rcases hd12 i' hi' with h2 | h2 <;> have := hdle k <;> omega

    let β : Fin (2 * genusFF K F + 1) → (P j).toValuationSubring := fun k =>
      Polynomial.aeval (⟨w, hwmem j⟩ : (P j).toValuationSubring) (rev (d i + d i' - d k) (q i i' k))
    have hβ : ∀ k, ((β k : (P j).toValuationSubring) : F) =
        w ^ (d i + d i' - d k) * Polynomial.aeval x (q i i' k) := by
      intro k
      rw [pow_mul_aeval_eq_aeval_rev (hdegq i i' k) hwx]
      show algebraMap (P j).toValuationSubring F (Polynomial.aeval (⟨w, hwmem j⟩ : (P j).toValuationSubring) _) = _
      rw [← Polynomial.aeval_algebraMap_apply]
      rfl
    have hevβ : ∀ k, ev (P j) (β k) = (q i i' k).coeff (d i + d i' - d k) := by
      intro k
      rw [hom_aeval_of_map_eq_zero (ev (P j)) (fun c => ev_algebraMap (P j) c) (hevw j), rev_coeff_zero]

    have hprod : (⟨r i, hrmem j i⟩ : (P j).toValuationSubring) * ⟨r i', hrmem j i'⟩ =
        ∑ k, β k * ⟨r k, hrmem j k⟩ := by
      apply Subtype.ext
      push_cast
      simp only [hβ, hr]
      have : w ^ d i * e i * (w ^ d i' * e i') = w ^ (d i + d i') * (e i * e i') := by ring
      rw [this, hmulE i i', Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsplit : w ^ (d i + d i') = w ^ (d i + d i' - d k) * w ^ d k := by
        rw [← pow_add, Nat.sub_add_cancel (hdk k)]
      rw [hsplit]; ring
    have := congrArg (ev (P j)) hprod
    rw [map_mul, map_sum] at this
    simp only [map_mul, hevβ] at this
    rw [hτ, hτ, this]

  have hτdet : IsUnit (Matrix.det (Matrix.of τ)) := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

    set f : F := ∑ i, algebraMap K F (c i) * r i with hfdef
    have hfO : ∀ j, ∃ hf : f ∈ (P j).toValuationSubring, ev (P j) ⟨f, hf⟩ = 0 := by
      intro j
      let fO : (P j).toValuationSubring := ∑ i, algebraMap K (P j).toValuationSubring (c i) * ⟨r i, hrmem j i⟩
      have hfO : (fO : F) = f := by
        simp only [fO]; push_cast; rfl
      refine ⟨hfO ▸ fO.2, ?_⟩
      have : (⟨f, hfO ▸ fO.2⟩ : (P j).toValuationSubring) = fO := Subtype.ext hfO.symm
      rw [this, map_sum]
      have hj := congrFun hc j
      rw [Pi.zero_apply, Matrix.mulVec, dotProduct] at hj
      rw [← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Matrix.of_apply, hτ, mul_comm]
      congr 1
      exact ev_algebraMap (P j) (c i)

    set h : F := x ^ 2 * f with hhdef
    have hhsum : h = ∑ i, Polynomial.aeval x (Polynomial.C (c i) * Polynomial.X ^ (2 - d i)) * e i := by
      rw [hhdef, hfdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hr]
      have : x ^ 2 * w ^ d i = x ^ (2 - d i) := by
        rw [hwdef, inv_pow]
        exact (pow_sub₀ x hx0 (hdle i)).symm
      calc x ^ 2 * (algebraMap K F (c i) * (w ^ d i * e i))
          = algebraMap K F (c i) * (x ^ 2 * w ^ d i) * e i := by ring
        _ = algebraMap K F (c i) * x ^ (2 - d i) * e i := by rw [this]
    have hhL2 : h ∈ L 2 := by
      rw [hhsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hLmono' (by have := hdle i; omega) (hpowL (2 - d i) (d i) (e i) (heL i)))
    have hhL1 : h ∈ L 1 := by
      rcases eq_or_ne f 0 with hf0 | hf0
      · rw [hhdef, hf0, mul_zero]; exact Submodule.zero_mem _
      have hh0 : h ≠ 0 := mul_ne_zero (pow_ne_zero _ hx0) hf0
      obtain ⟨-, hout⟩ := (hmemL' 2 h hh0).mp hhL2
      refine (hmemL' 1 h hh0).mpr ⟨fun j => ?_, hout⟩
      obtain ⟨hfmem, hev⟩ := hfO j
      have hpos : 0 < (P j).ord f :=
        (mem_maximalIdeal_iff_ord_pos _ hf0 hfmem).mp ((ev_eq_zero_iff _ _).mp hev)
      rw [hhdef, (P j).ord_mul (pow_ne_zero _ hx0) hf0, ← zpow_natCast, (P j).ord_zpow, hpole]
      push_cast; omega
    obtain ⟨b, hb, hhb⟩ := (hL 1 h).mp hhL1
    have heq := hind (fun i => b i - Polynomial.C (c i) * Polynomial.X ^ (2 - d i)) (by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      rw [← hhb, ← hhsum, sub_self])
    apply hc0
    funext i
    have hi := congrFun heq i
    simp only [Pi.zero_apply, sub_eq_zero] at hi
    have hcoeff := congrArg (fun p : K[X] => p.coeff (2 - d i)) hi
    simp only [Polynomial.coeff_C_mul_X_pow, if_true] at hcoeff
    rw [← hcoeff, Pi.zero_apply]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have := Polynomial.mem_degreeLT.mp (hb i)
    have h2 : (1 + 1 - d i : ℕ) = 2 - d i := by omega
    rw [h2] at this
    exact this
  exact ⟨D, e, d, q, τ, hD, he0, hd0, hd12, hdsum, hL, hind, hfrac, hmulE,
    fun i j k _ _ => hdegq i j k, hτdet, hτ0, hτmul⟩

end S_AlgebraicCurve_exists_normalForm_of_reduced_poleDivisor
end P2MW
export P2MW.S_AlgebraicCurve_exists_normalForm_of_reduced_poleDivisor (solution)
