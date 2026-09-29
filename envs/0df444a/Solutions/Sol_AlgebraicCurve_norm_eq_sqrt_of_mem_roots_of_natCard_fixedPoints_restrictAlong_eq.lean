-- Prove2me | solution 1 for AlgebraicCurve.norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6c394cfa-4f6b-5d42-9e2e-aab712c36b61

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_AlgebraicCurve_sum_divisors_mul_card_places_lt_of_even
import Theorems.Thm_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

namespace P2mRHRoots

open Finset Matrix

theorem norm_le_of_norm_sum_pow_le {ι : Type*} [Fintype ι] (α : ι → ℂ) {R : ℝ} (hR : 0 < R)
    (c : ℝ) (h : ∀ N : ℕ, 1 ≤ N → ‖∑ i, α i ^ N‖ ≤ c * R ^ N) (i₀ : ι) : ‖α i₀‖ ≤ R := by
  classical
  set s : Finset ℂ := Finset.univ.image α with hs_def
  set m : ℕ := s.card with hm_def
  set e : Fin m ≃ {x // x ∈ s} := s.equivFin.symm with he_def
  set β : Fin m → ℂ := fun j => ((e j : {x // x ∈ s}) : ℂ) with hβ_def
  have hβinj : Function.Injective β := by
    intro j j' hjj'
    exact e.injective (Subtype.ext hjj')
  set mult : Fin m → ℕ := fun j => (Finset.univ.filter fun i => α i = β j).card with hmult_def
  have hmult_pos : ∀ j, 0 < mult j := by
    intro j
    have hj : β j ∈ s := (e j).2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hpow : ∀ N : ℕ, ∑ i, α i ^ N = ∑ j, (mult j : ℂ) * β j ^ N := by
    intro N
    have h1 : ∑ i, α i ^ N =
        ∑ b ∈ s, ((Finset.univ.filter fun i => α i = b).card : ℂ) * b ^ N := by
      have := Finset.sum_comp (s := (Finset.univ : Finset ι)) (fun x : ℂ => x ^ N) α
      rw [this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [nsmul_eq_mul]
    rw [h1, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e (fun j => (mult j : ℂ) * β j ^ N)
      (fun x => ((Finset.univ.filter fun i => α i = (x : ℂ)).card : ℂ) * (x : ℂ) ^ N)
      (fun j => rfl)).symm
  set V : Matrix (Fin m) (Fin m) ℂ := Matrix.vandermonde β with hV_def
  have hV : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV_def]
    exact (Matrix.det_vandermonde_ne_zero_iff).mpr hβinj
  set u : ℕ → Fin m → ℂ := fun N j => (mult j : ℂ) * β j ^ N with hu_def
  set P : ℕ → Fin m → ℂ := fun N j => ∑ i, α i ^ (N + (j : ℕ)) with hP_def
  have huV : ∀ N, u N ᵥ* V = P N := by
    intro N
    ext j
    simp only [Matrix.vecMul, dotProduct, hV_def, Matrix.vandermonde_apply, hu_def, hP_def]
    rw [hpow]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hu : ∀ N, u N = P N ᵥ* V⁻¹ := by
    intro N
    rw [← huV, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hV, Matrix.vecMul_one]
  set K : Fin m → ℝ := fun j => ∑ l : Fin m, c * R ^ (l : ℕ) * ‖V⁻¹ l j‖ with hK_def
  have hbound : ∀ N : ℕ, 1 ≤ N → ∀ j, (mult j : ℝ) * ‖β j‖ ^ N ≤ K j * R ^ N := by
    intro N hN j
    have hnorm : ‖u N j‖ = (mult j : ℝ) * ‖β j‖ ^ N := by
      simp [hu_def, norm_pow]
    rw [← hnorm, hu N]
    simp only [Matrix.vecMul, dotProduct]
    calc ‖∑ l, P N l * V⁻¹ l j‖
        ≤ ∑ l, ‖P N l * V⁻¹ l j‖ := norm_sum_le _ _
      _ = ∑ l, ‖P N l‖ * ‖V⁻¹ l j‖ := by simp_rw [norm_mul]
      _ ≤ ∑ l : Fin m, (c * R ^ (N + (l : ℕ))) * ‖V⁻¹ l j‖ := by
          gcongr with l _
          exact h _ (by omega)
      _ = K j * R ^ N := by
          rw [hK_def, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  have hβle : ∀ j, ‖β j‖ ≤ R := by
    intro j
    by_contra hlt
    have hlt : R < ‖β j‖ := not_le.mp hlt
    have hratio : 1 < ‖β j‖ / R := by rwa [one_lt_div hR]
    have htend := tendsto_pow_atTop_atTop_of_one_lt hratio
    obtain ⟨N, hNK, hN1⟩ :=
      ((htend.eventually_gt_atTop (K j)).and (Filter.eventually_ge_atTop 1)).exists
    have hb := hbound N hN1 j
    have hmj : (1 : ℝ) ≤ mult j := by exact_mod_cast hmult_pos j
    have hpowle : ‖β j‖ ^ N ≤ K j * R ^ N := by
      have : ‖β j‖ ^ N ≤ (mult j : ℝ) * ‖β j‖ ^ N :=
        le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) hmj
      exact this.trans hb
    have : (‖β j‖ / R) ^ N ≤ K j := by
      rw [div_pow, div_le_iff₀ (pow_pos hR N)]
      exact hpowle
    exact absurd hNK (not_lt.mpr this)
  set x : {x // x ∈ s} := ⟨α i₀, Finset.mem_image_of_mem α (Finset.mem_univ i₀)⟩ with hx_def
  have : β (e.symm x) = α i₀ := by
    simp [hβ_def, hx_def]
  rw [← this]
  exact hβle _

theorem eq_of_prod_eq_pow {ι : Type*} [Fintype ι] (a : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ i, 0 ≤ a i) (hle : ∀ i, a i ≤ c) (hprod : ∏ i, a i = c ^ Fintype.card ι) (i₀ : ι) :
    a i₀ = c := by
  classical
  by_contra hne
  have hlt : a i₀ < c := lt_of_le_of_ne (hle i₀) hne
  have hpos : ∀ i, 0 < a i := by
    intro i
    rcases (h0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ i, a i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
      rw [this] at hprod
      exact (pow_pos hc _).ne' hprod.symm
  have : ∏ i, a i < ∏ _i : ι, c :=
    Finset.prod_lt_prod (fun i _ => hpos i) (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hlt⟩
  rw [Finset.prod_const, Finset.card_univ, hprod] at this
  exact lt_irrefl _ this

section Main

variable (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]

theorem norm_eq_sqrt
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (P : Polynomial ℤ) (hP : P.Monic) (hdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (h0 : P.coeff 0 = (Nat.card k : ℤ) ^ AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ = Real.sqrt (Nat.card k : ℝ) := by
  classical

  have hC : AlgebraicCurve.ConstantsAreBase k F₀ :=
    AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen φ hφ
  haveI : Algebra.EssFiniteType k F₀ := by
    obtain ⟨s, hs⟩ := hfg
    exact IntermediateField.fg_top_iff.mp ⟨s, hs⟩
  have hcount := AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
    k K F₀ F hfg hgen φ hφi hφ
  have hup := AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even k F₀ hC
  obtain ⟨m, hm, c, hlow⟩ := AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places k F₀ hC

  set q : ℕ := Nat.card k with hq_def
  set g₀ : ℕ := AlgebraicCurve.genusFF k F₀ with hg₀
  set g : ℕ := AlgebraicCurve.genusFF K F with hg
  set B : ℕ → ℕ := fun r =>
    ∑ d ∈ Nat.divisors r, d * Nat.card {v : AlgebraicCurve.Place k F₀ | v.deg = d} with hB_def
  set Pc : Polynomial ℂ := P.map (Int.castRingHom ℂ) with hPc
  set Rt : Multiset ℂ := Pc.roots with hRt
  have hq1 : 1 < q := Finite.one_lt_card
  set R : ℝ := Real.sqrt (q : ℝ) with hR_def
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast (zero_lt_one.trans hq1))

  set α : Rt.ToType → ℂ := fun x => x.1 with hα
  have hsumα : ∀ f : ℂ → ℂ, ∑ x, f (α x) = (Rt.map f).sum := by
    intro f
    rw [Finset.sum_eq_multiset_sum]
    conv_rhs => rw [← Multiset.map_univ_coe Rt]
    rw [Multiset.map_map]
    rfl

  have hS : ∀ r : ℕ, 1 ≤ r → ((B r : ℕ) : ℂ) = (q : ℂ) ^ r + 1 - ∑ x, α x ^ r := by
    intro r hr
    have h1 := (hcount r hr).2
    have h2 := hfix r hr
    rw [hsumα (fun z => z ^ r), ← h2, h1]

  set r₀ : ℕ := (g₀ + 1) ^ 4 with hr₀_def
  have hr₀ : (g₀ + 1) ^ 4 < q ^ r₀ := Nat.lt_pow_self hq1
  set Ms : ℕ := 2 * m * r₀ with hM_def
  have hr₀pos : 0 < r₀ := by positivity
  have hMpos : 0 < Ms := by positivity
  set C : ℝ := max (2 * (g₀ : ℝ) + 1) c with hC_def
  have key : ∀ N : ℕ, 1 ≤ N → ‖∑ x, (α x ^ Ms) ^ N‖ ≤ C * (R ^ Ms) ^ N := by
    intro N hN
    have hr0 : 0 < Ms * N := Nat.mul_pos hMpos hN
    have hreven : Even (Ms * N) := ⟨m * r₀ * N, by rw [hM_def]; ring⟩
    have hmr : m ∣ Ms * N := ⟨2 * r₀ * N, by rw [hM_def]; ring⟩
    have hr₀r : r₀ ≤ Ms * N := by
      calc r₀ = 1 * 1 * r₀ * 1 := by ring
        _ ≤ 2 * m * r₀ * N := by gcongr <;> omega
    have hqr : (g₀ + 1) ^ 4 < q ^ (Ms * N) :=
      hr₀.trans_le (Nat.pow_le_pow_right hq1.le hr₀r)
    have h1 : ((B (Ms * N) : ℕ) : ℝ) < (q : ℝ) ^ (Ms * N) + 1 + (2 * (g₀ : ℝ) + 1) * R ^ (Ms * N) :=
      hup (Ms * N) hreven hqr
    have h2 : (q : ℝ) ^ (Ms * N) + 1 - c * R ^ (Ms * N) ≤ ((B (Ms * N) : ℕ) : ℝ) :=
      hlow (Ms * N) hr0 hmr
    have h3 : ((B (Ms * N) : ℕ) : ℂ) = (q : ℂ) ^ (Ms * N) + 1 - ∑ x, α x ^ (Ms * N) :=
      hS (Ms * N) (Nat.one_le_of_lt hr0)
    have hsum : ∑ x, (α x ^ Ms) ^ N = (q : ℂ) ^ (Ms * N) + 1 - ((B (Ms * N) : ℕ) : ℂ) := by
      simp_rw [← pow_mul]
      rw [h3]
      ring
    have hcast : (q : ℂ) ^ (Ms * N) + 1 - ((B (Ms * N) : ℕ) : ℂ) =
        (((q : ℝ) ^ (Ms * N) + 1 - ((B (Ms * N) : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsum, hcast, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, abs_le]
    have hRr : 0 ≤ R ^ (Ms * N) := pow_nonneg hRpos.le _
    have hC1 : (2 * (g₀ : ℝ) + 1) * R ^ (Ms * N) ≤ C * R ^ (Ms * N) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hRr
    have hC2 : c * R ^ (Ms * N) ≤ C * R ^ (Ms * N) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hRr
    constructor <;> linarith

  have hle : ∀ x, ‖α x‖ ≤ R := by
    intro x
    have := norm_le_of_norm_sum_pow_le (fun x => α x ^ Ms) (pow_pos hRpos Ms) C key x
    rw [norm_pow] at this
    exact le_of_pow_le_pow_left₀ hMpos.ne' hRpos.le this

  have hPcm : Pc.Monic := hP.map _
  have hcardRt : Fintype.card Rt.ToType = 2 * g := by
    rw [Multiset.card_coe, hRt, IsAlgClosed.card_roots_eq_natDegree, hPc, hP.natDegree_map, hdeg]
  have hprodC : ∏ x, α x = Rt.prod := by
    rw [Finset.prod_eq_multiset_prod]
    conv_rhs => rw [← Multiset.map_univ_coe Rt]
  have hPcdeg : Pc.natDegree = 2 * g := by rw [hPc, hP.natDegree_map, hdeg]
  have hcoeff : Pc.coeff 0 = Rt.prod := by
    rw [(IsAlgClosed.splits Pc).coeff_zero_eq_prod_roots_of_monic hPcm, hPcdeg,
      Even.neg_one_pow ⟨g, by ring⟩, one_mul]
  have hcoeff' : Pc.coeff 0 = ((q : ℂ)) ^ g := by
    rw [hPc, Polynomial.coeff_map, h0]
    simp
  have hprod : ∏ x, ‖α x‖ = R ^ Fintype.card Rt.ToType := by
    rw [← norm_prod, hprodC, ← hcoeff, hcoeff', norm_pow, hcardRt, pow_mul, hR_def,
      Real.sq_sqrt (by positivity)]
    simp

  intro z hz
  have heq := eq_of_prod_eq_pow (fun x => ‖α x‖) hRpos (fun x => norm_nonneg _) hle hprod
  obtain ⟨x, hx⟩ : ∃ x : Rt.ToType, α x = z := by
    have : z ∈ (Finset.univ.val.map fun x : Rt.ToType => x.1) := by
      rw [Multiset.map_univ_coe]; exact hz
    obtain ⟨x, -, hx⟩ := Multiset.mem_map.mp this
    exact ⟨x, hx⟩
  rw [← hx]
  exact heq x

end Main

end P2mRHRoots

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (P : Polynomial ℤ) (hP : P.Monic) (hdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (h0 : P.coeff 0 = (Nat.card k : ℤ) ^ AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ = Real.sqrt (Nat.card k : ℝ) :=
  P2mRHRoots.norm_eq_sqrt k K F₀ F hfg hgen φ hφi hφ P hP hdeg h0 hfix

end S_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
end P2MW
export P2MW.S_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq (solution)
