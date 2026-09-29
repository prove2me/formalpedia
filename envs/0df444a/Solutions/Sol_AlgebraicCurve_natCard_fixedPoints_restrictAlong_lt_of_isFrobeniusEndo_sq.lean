-- Prove2me | solution 1 for AlgebraicCurve.natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/56c281d4-8238-5525-8195-5ea7476e84f7

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_P2M_Dup_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.restrictAlong Place.ord_restrictAlong Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsFrobeniusEndo IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue genusFF FunctionFieldRiemannRoch LSpace ell mem_lSpace_iff mem_lSpace_iff_ord lSpace_mono one_mem_lSpace_zero ConstantsAreBase HasCanonicalDivisor canonicalDivisorOf genus constantsAreBase_of_deg_eq_one degree_canonicalDivisor_eq_of_riemannRoch functionFieldRiemannRoch_of_isAlgClosed_of_transcendental IsCurveOver.exists_separating_transcendental stichtenothGenusExists_of_isCurveOver weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists genus_eq_genusFF hasCanonicalDivisor_of_isCurveOver dCoordGenerates_of_isCurveOver ell_eq_zero_of_degree_neg finiteDimensional_lSpace"
p2m_open "AlgebraicCurve"

namespace BombieriUpper

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem mem_of_adicValuation_le_one {f : F} (h : v.adicValuation f ≤ 1) :
    f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact mem_of_ord_nonneg v hf (((v.adicValuation_le_one_iff).mp h).resolve_left hf)

theorem mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 :=
  ⟨v.adicValuation_le_one_of_mem, mem_of_adicValuation_le_one v⟩

theorem adicValuation_lt_one_iff_mem_maximalIdeal (a : v.toValuationSubring) :
    v.adicValuation (a : F) < 1 ↔ a ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff a]
  exact ⟨fun h => h.ne, fun h => lt_of_le_of_ne (v.adicValuation_le_one_of_mem a.2) h⟩

theorem adicValuation_algebraMap_eq_one {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := (IsUnit.mk0 c hc).map _
  have := (v.adicValuation_coe_eq_one_iff (algebraMap K v.toValuationSubring c)).mpr hu
  simpa using this

theorem algebraMap_eq_zero_of_adicValuation_lt_one {c : K}
    (h : v.adicValuation (algebraMap K F c) < 1) : c = 0 := by
  by_contra hc
  exact h.ne (adicValuation_algebraMap_eq_one v hc)

theorem adicValuation_pow_eq {f : F} (hf : f ≠ 0) (n : ℕ) :
    v.adicValuation (f ^ n) = exp (-((n : ℤ) * v.ord f)) := by
  rw [map_pow, v.adicValuation_eq_exp_neg_ord hf, ← exp_nsmul, nsmul_eq_mul, mul_neg]

theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem exists_algebraMap_sub_lt_one
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {y : F} (hy : y ∈ v.toValuationSubring) :
    ∃ c : K, v.adicValuation (y - algebraMap K F c) < 1 := by
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue v.toValuationSubring ⟨y, hy⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨y, hy⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero]
    rfl
  have := (adicValuation_lt_one_iff_mem_maximalIdeal v _).mpr hmem
  simpa using this

end SinglePlace

section Fixed

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  {φ : F →ₐ[K] F} (hφ : φ.toRingHom.IsIntegral)

theorem mem_restrictAlong_iff (w : Place K F) (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

variable {hφ}

theorem mem_iff_map_mem_of_fixed {P : Place K F}
    (hP : Function.IsFixedPt (Place.restrictAlong φ hφ) P) (f : F) :
    f ∈ P.toValuationSubring ↔ φ f ∈ P.toValuationSubring := by
  rw [← mem_restrictAlong_iff hφ P f]
  rw [show P.restrictAlong φ hφ = P from hP]

theorem ord_map_of_fixed {ℓ : ℕ} (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) {P : Place K F}
    (hP : Function.IsFixedPt (Place.restrictAlong φ hφ) P) (f : F) :
    P.ord (φ f) = ℓ * P.ord f := by
  have := Place.ord_restrictAlong φ hφ P f
  rw [h.ramificationIndexAlong_eq hℓ P] at this
  rw [this, show P.restrictAlong φ hφ = P from hP]

theorem adicValuation_map_of_fixed {ℓ : ℕ} (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    {P : Place K F} (hP : Function.IsFixedPt (Place.restrictAlong φ hφ) P) (f : F) :
    P.adicValuation (φ f) = P.adicValuation f ^ ℓ := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [hℓ]
  have hφf : φ f ≠ 0 := by simpa using hf
  rw [P.adicValuation_eq_exp_neg_ord hφf, ord_map_of_fixed h hℓ hP f, ← map_pow,
    adicValuation_pow_eq P hf ℓ]

theorem adicValuation_map_sub_self_lt_one {ℓ : ℕ} (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    {P : Place K F} (hP : Function.IsFixedPt (Place.restrictAlong φ hφ) P)
    (hsurj : Function.Surjective (algebraMap K P.ResidueField))
    {z : F} (hz : z ∈ P.toValuationSubring) :
    P.adicValuation (φ z - z) < 1 := by
  obtain ⟨c, hc⟩ := exists_algebraMap_sub_lt_one P hsurj hz
  have h1 : P.adicValuation (φ (z - algebraMap K F c)) < 1 := by
    rw [adicValuation_map_of_fixed h hℓ hP]
    exact pow_lt_one' hc hℓ
  have : φ z - z = φ (z - algebraMap K F c) - (z - algebraMap K F c) := by
    rw [map_sub, AlgHom.commutes]; ring
  rw [this]
  exact Valuation.map_sub_lt _ h1 hc

end Fixed

section CharP

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adicValuation_lt_exp_iff_le (v : Place K F) (f : F) (n : ℤ) :
    v.adicValuation f < exp n ↔ v.adicValuation f ≤ exp (n - 1) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [v.adicValuation_eq_exp_neg_ord hf, exp_lt_exp, exp_le_exp]
  omega

theorem coeff_eq_zero_of_adicValuation_sum_le (v : Place K F) {π : F}
    (hπ : v.adicValuation π = exp (-1)) :
    ∀ (n e : ℕ) (a : ℕ → K),
      v.adicValuation (∑ i ∈ Finset.range n, algebraMap K F (a i) * π ^ (i + e + 1)) ≤
          exp (-((n + e + 1 : ℕ) : ℤ)) →
        ∀ i < n, a i = 0 := by
  intro n
  induction n with
  | zero => intro e a _ i hi; omega
  | succ n ih =>
    intro e a hsum
    have hvπ : ∀ k : ℕ, v.adicValuation (π ^ k) = exp (-(k : ℤ)) := by
      intro k; rw [map_pow, hπ, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
    have hterm : ∀ (c : K) (k : ℕ),
        v.adicValuation (algebraMap K F c * π ^ k) ≤ exp (-(k : ℤ)) := by
      intro c k
      rw [map_mul, hvπ]
      exact mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)

    rw [Finset.sum_range_succ'] at hsum
    set T := ∑ i ∈ Finset.range n, algebraMap K F (a (i + 1)) * π ^ (i + 1 + e + 1) with hT
    have hTle : v.adicValuation T ≤ exp (-((e + 2 : ℕ) : ℤ)) := by
      apply Valuation.map_sum_le
      intro i _
      refine (hterm _ _).trans ?_
      rw [exp_le_exp]; push_cast; omega
    have htot : v.adicValuation (T + algebraMap K F (a 0) * π ^ (0 + e + 1)) ≤
        exp (-((e + 2 : ℕ) : ℤ)) := by
      refine hsum.trans ?_
      rw [exp_le_exp]; push_cast; omega
    have h0 : a 0 = 0 := by
      by_contra ha
      have hbot : v.adicValuation (algebraMap K F (a 0) * π ^ (0 + e + 1)) =
          exp (-((e + 1 : ℕ) : ℤ)) := by
        rw [map_mul, adicValuation_algebraMap_eq_one v ha, one_mul, hvπ]; push_cast; ring_nf
      have : v.adicValuation (algebraMap K F (a 0) * π ^ (0 + e + 1)) ≤
          exp (-((e + 2 : ℕ) : ℤ)) := by
        have := Valuation.map_sub v.adicValuation (T + algebraMap K F (a 0) * π ^ (0 + e + 1)) T
        rw [add_sub_cancel_left] at this
        exact this.trans (max_le htot hTle)
      rw [hbot, exp_le_exp] at this
      push_cast at this; omega

    have hT' : v.adicValuation
        (∑ i ∈ Finset.range n, algebraMap K F (a (i + 1)) * π ^ (i + (e + 1) + 1)) ≤
        exp (-((n + (e + 1) + 1 : ℕ) : ℤ)) := by
      have : T = ∑ i ∈ Finset.range n, algebraMap K F (a (i + 1)) * π ^ (i + (e + 1) + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show i + 1 + e + 1 = i + (e + 1) + 1 by ring]
      rw [← this]
      have h2 : T + algebraMap K F (a 0) * π ^ (0 + e + 1) = T := by rw [h0]; simp
      rw [h2] at hsum
      refine hsum.trans ?_
      rw [exp_le_exp]; push_cast; omega
    have := ih (e + 1) (fun i => a (i + 1)) hT'
    intro i hi
    rcases i with _ | i
    · exact h0
    · exact this i (by omega)

variable {φ : F →ₐ[K] F} {hφ : φ.toRingHom.IsIntegral}

theorem natCast_choose_eq_zero_of_fixed {ℓ : ℕ} (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    {P : Place K F} (hP : Function.IsFixedPt (Place.restrictAlong φ hφ) P)
    (hsurj : Function.Surjective (algebraMap K P.ResidueField))
    {j : ℕ} (hj0 : 0 < j) (hjℓ : j < ℓ) : ((ℓ.choose j : ℕ) : K) = 0 := by
  classical
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  set π : F := (π₀ : F) with hπdef
  have hπ : P.adicValuation π = exp (-1) := P.adicValuation_coe_irreducible hπ₀
  have hvπ : ∀ k : ℕ, P.adicValuation (π ^ k) = exp (-(k : ℤ)) := by
    intro k; rw [map_pow, hπ, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  obtain ⟨y, hy⟩ := h.pow_mem_range (π + 1)
  have hymem : y ∈ P.toValuationSubring := by
    rw [mem_iff_map_mem_of_fixed hP, hy]
    exact pow_mem (add_mem π₀.2 (one_mem _)) _
  obtain ⟨c, hc⟩ := exists_algebraMap_sub_lt_one P hsurj hymem

  have hc' : P.adicValuation (y - algebraMap K F c) ≤ exp (-1) := by
    have := (adicValuation_lt_exp_iff_le P _ 0).mp (by simpa using hc)
    simpa using this
  have hmain : P.adicValuation ((π + 1) ^ ℓ - algebraMap K F c) ≤ exp (-(ℓ : ℤ)) := by
    have := adicValuation_map_of_fixed h hℓ hP (y - algebraMap K F c)
    rw [map_sub, hy, AlgHom.commutes] at this
    rw [this, show exp (-(ℓ : ℤ)) = exp (-1) ^ ℓ by
      rw [← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]]
    exact pow_le_pow_left' hc' ℓ

  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := Nat.exists_eq_succ_of_ne_zero hℓ
  set a : ℕ → K := fun m => ((ℓ' + 1).choose (m + 1) : K) with ha
  set S : F := ∑ m ∈ Finset.range ℓ', algebraMap K F (a m) * π ^ (m + 0 + 1) with hS
  have hexp : (π + 1) ^ (ℓ' + 1) = 1 + S + π ^ (ℓ' + 1) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, pow_zero, Nat.choose_zero_right,
      Nat.sub_self, hS, ha, map_natCast, add_zero]
    have : ∀ m ∈ Finset.range ℓ',
        π ^ (m + 1) * (((ℓ' + 1).choose (m + 1) : ℕ) : F) =
          (((ℓ' + 1).choose (m + 1) : ℕ) : F) * π ^ (m + 1) := fun m _ => mul_comm _ _
    rw [Finset.sum_congr rfl this]
    ring
  have hSle : P.adicValuation S ≤ exp (-1) := by
    apply Valuation.map_sum_le
    intro m _
    rw [map_mul, hvπ]
    refine (mul_le_of_le_one_left' (P.adicValuation_algebraMap_le_one _)).trans ?_
    rw [exp_le_exp]; push_cast; omega
  have hπℓ : P.adicValuation (π ^ (ℓ' + 1)) = exp (-((ℓ' + 1 : ℕ) : ℤ)) := hvπ _
  have hSπ : P.adicValuation (S + π ^ (ℓ' + 1)) ≤ exp (-1) := by
    refine (Valuation.map_add _ _ _).trans (max_le hSle ?_)
    rw [hπℓ, exp_le_exp]; push_cast; omega

  have hc1 : c = 1 := by
    have hlt : P.adicValuation (algebraMap K F (1 - c)) < 1 := by
      have heq : algebraMap K F (1 - c) =
          ((π + 1) ^ (ℓ' + 1) - algebraMap K F c) - (S + π ^ (ℓ' + 1)) := by
        rw [hexp, map_sub, map_one]; ring
      rw [heq]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt hmain ?_
        rw [← exp_zero, exp_lt_exp]; omega
      · refine lt_of_le_of_lt hSπ ?_
        rw [← exp_zero, exp_lt_exp]; omega
    have := algebraMap_eq_zero_of_adicValuation_lt_one P hlt
    exact (sub_eq_zero.mp this).symm
  subst hc1

  have hSle' : P.adicValuation S ≤ exp (-((ℓ' + 0 + 1 : ℕ) : ℤ)) := by
    have heq : S = ((π + 1) ^ (ℓ' + 1) - algebraMap K F 1) - π ^ (ℓ' + 1) := by
      rw [hexp, map_one]; ring
    rw [heq]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · refine hmain.trans (le_of_eq ?_)
      congr 1
    · rw [hπℓ]
  have hall := coeff_eq_zero_of_adicValuation_sum_le P hπ ℓ' 0 a hSle'
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := Nat.exists_eq_succ_of_ne_zero hj0.ne'
  have := hall m (by omega)
  simpa [ha] using this

theorem choose_pow_mul_modEq (p a m : ℕ) [hp : Fact p.Prime] :
    (p ^ a * m).choose (p ^ a) ≡ m [MOD p] := by
  have := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := a) (a := m) (b := 1)
  simpa using this

theorem exists_charP_of_fixed {ℓ : ℕ} (h : IsFrobeniusEndo ℓ φ) (hℓ : 2 ≤ ℓ)
    {P : Place K F} (hP : Function.IsFixedPt (Place.restrictAlong φ hφ) P)
    (hsurj : Function.Surjective (algebraMap K P.ResidueField)) :
    ∃ p : ℕ, p.Prime ∧ CharP K p ∧ ∃ a : ℕ, ℓ = p ^ a := by
  have hℓ0 : ℓ ≠ 0 := by omega
  have hchoose := fun j (hj0 : 0 < j) (hjℓ : j < ℓ) =>
    natCast_choose_eq_zero_of_fixed h hℓ0 hP hsurj hj0 hjℓ
  have hℓK : ((ℓ : ℕ) : K) = 0 := by
    have := hchoose 1 one_pos (by omega)
    simpa using this
  set p := ringChar K with hpdef
  haveI hKp : CharP K p := ringChar.charP K
  have hpℓ : p ∣ ℓ := (CharP.cast_eq_zero_iff K p ℓ).mp hℓK
  have hp0 : p ≠ 0 := by
    rintro hp0; rw [hp0, zero_dvd_iff] at hpℓ; exact hℓ0 hpℓ
  have hp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hKp, ?_⟩
  obtain ⟨a, m, hm, hℓam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hℓ0 p hp.ne_one
  refine ⟨a, ?_⟩
  suffices m = 1 by rw [hℓam, this, mul_one]
  by_contra hm1
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hm2 : 2 ≤ m := by omega
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hlt : p ^ a < ℓ := by
    rw [hℓam]
    calc p ^ a = p ^ a * 1 := (mul_one _).symm
      _ < p ^ a * m := Nat.mul_lt_mul_of_pos_left (by omega) hpa
  have h0 := hchoose (p ^ a) hpa hlt
  rw [CharP.cast_eq_zero_iff K p] at h0
  have hmod := choose_pow_mul_modEq p a m
  rw [← hℓam] at hmod
  exact hm (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h0)))

end CharP

section LSingle

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_lSpace_single_iff (P₀ : Place K F) {k : ℤ} {f : F} :
    f ∈ LSpace (Finsupp.single P₀ k) ↔
      P₀.adicValuation f ≤ exp k ∧ ∀ w : Place K F, w ≠ P₀ → w.adicValuation f ≤ 1 := by
  rw [mem_lSpace_iff]
  constructor
  · intro h
    refine ⟨by simpa using h P₀, fun w hw => ?_⟩
    have := h w
    rwa [Finsupp.single_eq_of_ne hw, exp_zero] at this
  · rintro ⟨h0, h1⟩ w
    by_cases hw : w = P₀
    · subst hw; simpa using h0
    · rw [Finsupp.single_eq_of_ne hw, exp_zero]; exact h1 w hw

theorem mul_mem_lSpace_add {D₁ D₂ : Divisor K F} {f g : F} (hf : f ∈ LSpace D₁)
    (hg : g ∈ LSpace D₂) : f * g ∈ LSpace (D₁ + D₂) := by
  intro v
  rw [map_mul, Finsupp.add_apply, exp_add]
  exact mul_le_mul' (hf v) (hg v)

theorem pow_mem_lSpace_smul {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (n : ℕ) :
    f ^ n ∈ LSpace (n • D) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_lSpace_zero
  | succ n ih => rw [pow_succ, succ_nsmul]; exact mul_mem_lSpace_add ih hf

theorem single_le_single (P₀ : Place K F) {a b : ℤ} (hab : a ≤ b) :
    Finsupp.single P₀ a ≤ Finsupp.single P₀ b := by
  intro w
  by_cases hw : w = P₀
  · subst hw; simpa using hab
  · simp [Finsupp.single_eq_of_ne hw]

theorem smul_single_natCast (P₀ : Place K F) (n : ℕ) (k : ℤ) :
    n • Finsupp.single P₀ k = Finsupp.single P₀ ((n : ℤ) * k) := by
  rw [Finsupp.smul_single, nsmul_eq_mul]

theorem ord_le_zero_of_mem_lSpace_single (hC : ConstantsAreBase K F) (P₀ : Place K F) {k : ℤ}
    {u : F} (hu : u ∈ LSpace (Finsupp.single P₀ k)) (hu0 : u ≠ 0) : P₀.ord u ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hu' : u ∈ LSpace (0 : Divisor K F) := by
    intro w
    rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
    by_cases hw : w = P₀
    · subst hw
      rw [w.adicValuation_le_one_iff]; exact Or.inr hpos.le
    · exact ((mem_lSpace_single_iff P₀).mp hu).2 w hw
  rw [hC] at hu'
  obtain ⟨c, hc'⟩ := hu'
  rw [Algebra.linearMap_apply] at hc'
  subst hc'
  have hc : c ≠ 0 := by rintro rfl; simp at hu0
  have h1 : P₀.adicValuation (algebraMap K F c) = 1 :=
    adicValuation_algebraMap_eq_one P₀ hc
  rw [P₀.adicValuation_eq_exp_neg_ord hu0, ← exp_zero, exp_inj] at h1
  omega

theorem exists_adapted_span (hC : ConstantsAreBase K F) (P₀ : Place K F)
    (hsurj : Function.Surjective (algebraMap K P₀.ResidueField)) (k : ℕ) :
    ∃ s : Finset F,
      (∀ u ∈ s, u ≠ 0 ∧ u ∈ LSpace (Finsupp.single P₀ (k : ℤ)) ∧
        -(k : ℤ) ≤ P₀.ord u ∧ P₀.ord u ≤ 0) ∧
      Set.InjOn P₀.ord (s : Set F) ∧
      LSpace (Finsupp.single P₀ (k : ℤ)) ≤ Submodule.span K (s : Set F) := by
  classical
  induction k with
  | zero =>
    refine ⟨{1}, ?_, by simp [Set.InjOn], ?_⟩
    · intro u hu
      rw [Finset.mem_singleton] at hu; subst hu
      refine ⟨one_ne_zero, ?_, by simp [P₀.ord_one], by simp [P₀.ord_one]⟩
      rw [Nat.cast_zero, Finsupp.single_zero]; exact one_mem_lSpace_zero
    · intro f hf
      rw [Nat.cast_zero, Finsupp.single_zero, show LSpace (0 : Divisor K F) = _ from hC] at hf
      obtain ⟨c, rfl⟩ := hf
      rw [Finset.coe_singleton, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  | succ k ih =>
    obtain ⟨s, hs, hinj, hspan⟩ := ih
    have hmono : LSpace (Finsupp.single P₀ (k : ℤ)) ≤
        LSpace (Finsupp.single P₀ ((k + 1 : ℕ) : ℤ)) :=
      lSpace_mono (single_le_single P₀ (by push_cast; omega))
    by_cases hex : ∃ u, u ∈ LSpace (Finsupp.single P₀ ((k + 1 : ℕ) : ℤ)) ∧
        u ∉ LSpace (Finsupp.single P₀ (k : ℤ))
    · obtain ⟨u, hu1, hu0⟩ := hex
      have hune : u ≠ 0 := by rintro rfl; exact hu0 (Submodule.zero_mem _)

      have hval : P₀.adicValuation u = exp ((k : ℤ) + 1) := by
        have h1 := ((mem_lSpace_single_iff P₀).mp hu1).1
        have h2 : ¬ P₀.adicValuation u ≤ exp (k : ℤ) := fun h =>
          hu0 ((mem_lSpace_single_iff P₀).mpr ⟨h, ((mem_lSpace_single_iff P₀).mp hu1).2⟩)
        push Not at h2
        push_cast at h1
        rw [P₀.adicValuation_eq_exp_neg_ord hune] at h1 h2 ⊢
        rw [exp_le_exp] at h1
        rw [exp_lt_exp] at h2
        rw [exp_inj]
        omega
      have hord : P₀.ord u = -((k : ℤ) + 1) := by
        rw [P₀.adicValuation_eq_exp_neg_ord hune, exp_inj] at hval; omega
      have hnotin : u ∉ (s : Set F) := by
        intro hu; have := (hs u hu).2.2.1; omega
      refine ⟨insert u s, ?_, ?_, ?_⟩
      · intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact ⟨hune, hu1, by rw [hord]; push_cast; omega, by rw [hord]; omega⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hs w hw
          exact ⟨h1, hmono h2, by push_cast; omega, h4⟩
      · rw [Finset.coe_insert, Set.injOn_insert hnotin]
        refine ⟨hinj, ?_⟩
        rintro ⟨w, hw, hEq⟩
        have := (hs w hw).2.2.1
        omega
      · intro f hf

        set g := f * u⁻¹ with hg
        have hgmem : g ∈ P₀.toValuationSubring := by
          apply mem_of_adicValuation_le_one
          rw [hg, map_mul, map_inv₀, hval]
          have := ((mem_lSpace_single_iff P₀).mp hf).1
          push_cast at this
          calc P₀.adicValuation f * (exp ((k : ℤ) + 1))⁻¹
              ≤ exp ((k : ℤ) + 1) * (exp ((k : ℤ) + 1))⁻¹ := by gcongr
            _ = 1 := mul_inv_cancel₀ (exp_ne_zero)
        obtain ⟨c, hc⟩ := exists_algebraMap_sub_lt_one P₀ hsurj hgmem
        have hdecomp : f = c • u + (g - algebraMap K F c) * u := by
          rw [hg, Algebra.smul_def, sub_mul, inv_mul_cancel_right₀ hune]; ring
        have hrest : (g - algebraMap K F c) * u ∈ LSpace (Finsupp.single P₀ (k : ℤ)) := by
          rw [mem_lSpace_single_iff]
          constructor
          · have hlt : P₀.adicValuation ((g - algebraMap K F c) * u) < exp ((k : ℤ) + 1) := by
              rw [map_mul, hval]
              calc P₀.adicValuation (g - algebraMap K F c) * exp ((k : ℤ) + 1)
                  < 1 * exp ((k : ℤ) + 1) := mul_lt_mul_of_pos_right hc exp_pos
                _ = exp ((k : ℤ) + 1) := one_mul _
            have := (adicValuation_lt_exp_iff_le P₀ _ _).mp hlt
            simpa using this
          · intro w hw
            have hfw := ((mem_lSpace_single_iff P₀).mp hf).2 w hw
            have huw := ((mem_lSpace_single_iff P₀).mp hu1).2 w hw
            have : (g - algebraMap K F c) * u = f - algebraMap K F c * u := by
              rw [hg, sub_mul, inv_mul_cancel_right₀ hune]
            rw [this]
            refine (Valuation.map_sub _ _ _).trans (max_le hfw ?_)
            rw [map_mul]
            exact mul_le_one' (w.adicValuation_algebraMap_le_one c) huw
        rw [hdecomp, Finset.coe_insert]
        refine Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_insert _ _))) ?_
        exact Submodule.span_mono (Set.subset_insert _ _) (hspan (hrest))
    · push Not at hex
      refine ⟨s, fun u hu => ?_, hinj, fun f hf => hspan (hex f hf)⟩
      obtain ⟨h1, h2, h3, h4⟩ := hs u hu
      exact ⟨h1, hmono h2, by push_cast; omega, h4⟩

theorem ell_le_card_of_span_le {D : Divisor K F} {s : Finset F}
    (h : LSpace D ≤ Submodule.span K (s : Set F)) : ell D ≤ s.card :=
  (Submodule.finrank_mono h).trans (finrank_span_finset_le_card (R := K) s)

end LSingle

section DistinctVal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem exists_adicValuation_sum_eq {ι : Type*} [DecidableEq ι] (f : ι → F) :
    ∀ (t : Finset ι), t.Nonempty → (∀ i ∈ t, f i ≠ 0) →
      Set.InjOn (fun i => v.adicValuation (f i)) (t : Set ι) →
      ∃ i ∈ t, v.adicValuation (∑ j ∈ t, f j) = v.adicValuation (f i) ∧
        ∀ j ∈ t, v.adicValuation (f j) ≤ v.adicValuation (f i) := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | @insert a t ha ih =>
    intro _ hne hinj
    by_cases ht : t.Nonempty
    · obtain ⟨i, hi, hsum, hmax⟩ := ih ht (fun j hj => hne j (Finset.mem_insert_of_mem hj))
        (hinj.mono (by simp))
      have hai : v.adicValuation (f a) ≠ v.adicValuation (f i) := by
        intro hEq
        have := hinj (Finset.mem_coe.mpr (Finset.mem_insert_self a t))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) hEq
        subst this; exact ha hi
      rw [Finset.sum_insert ha]
      rcases lt_or_gt_of_ne hai with hlt | hgt
      · refine ⟨i, Finset.mem_insert_of_mem hi, ?_, ?_⟩
        · rw [Valuation.map_add_eq_of_lt_right]
          · exact hsum
          · rw [hsum]; exact hlt
        · intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hlt.le
          · exact hmax j hj
      · refine ⟨a, Finset.mem_insert_self a t, ?_, ?_⟩
        · rw [Valuation.map_add_eq_of_lt_left]
          rw [hsum]; exact hgt
        · intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact le_rfl
          · exact (hmax j hj).trans hgt.le
    · rw [Finset.not_nonempty_iff_eq_empty] at ht
      subst ht
      exact ⟨a, Finset.mem_insert_self a _, by simp, by simp⟩

theorem sum_ne_zero_of_injOn {ι : Type*} [DecidableEq ι] (f : ι → F) {t : Finset ι}
    (ht : t.Nonempty) (hne : ∀ i ∈ t, f i ≠ 0)
    (hinj : Set.InjOn (fun i => v.adicValuation (f i)) (t : Set ι)) :
    ∑ j ∈ t, f j ≠ 0 := by
  obtain ⟨i, hi, hsum, -⟩ := exists_adicValuation_sum_eq v f t ht hne hinj
  intro h0
  rw [h0, map_zero] at hsum
  exact v.adicValuation_ne_zero (hne i hi) hsum.symm

end DistinctVal

section RR

open KaehlerDifferential IntermediateField

variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] [IsCurveOver K E]

theorem residue_surjective (v : Place K E) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem dimension_package (hfg : ∃ s : Finset E, IntermediateField.adjoin K (s : Set E) = ⊤)
    (P₀ : Place K E) :
    ConstantsAreBase K E ∧
    (∀ D : Divisor K E, FiniteDimensional K (LSpace D)) ∧
    (∀ k : ℕ, (k : ℤ) + 1 - genusFF K E ≤ ell (Finsupp.single P₀ (k : ℤ))) ∧
    (∀ k : ℕ, 2 * (genusFF K E : ℤ) - 2 < k →
      (ell (Finsupp.single P₀ (k : ℤ)) : ℤ) = k + 1 - genusFF K E) := by
  haveI : Algebra.EssFiniteType K E := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨t, htr, hfd, -⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := E)
  have hRR : FunctionFieldRiemannRoch K E :=
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental htr hfd
  haveI : HasCanonicalDivisor (K := K) (F := E) := hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place K E, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hdeg1 : P₀.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P₀
  have hC : ConstantsAreBase K E := constantsAreBase_of_deg_eq_one P₀ hdeg1
  have hgen : genus K E = genusFF K E := genus_eq_genusFF hRR
    (weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR
      (stichtenothGenusExists_of_isCurveOver hC)) hC
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[E⁄K])
  have hdegK := degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω
  haveI hL0 : FiniteDimensional K (LSpace (0 : Divisor K E)) := by
    rw [show LSpace (0 : Divisor K E) = _ from hC]; infer_instance
  have hfd : ∀ D : Divisor K E, FiniteDimensional K (LSpace D) := fun D =>
    finiteDimensional_lSpace D
  have hdegD : ∀ k : ℕ, Divisor.degree (Finsupp.single P₀ (k : ℤ)) = k := by
    intro k; rw [Divisor.degree_single, hdeg1]; simp
  have hRRk : ∀ k : ℕ, (ell (Finsupp.single P₀ (k : ℤ)) : ℤ) -
      ell (canonicalDivisorOf hω - Finsupp.single P₀ (k : ℤ)) = k + 1 - genusFF K E := by
    intro k
    have := hRR hω (Finsupp.single P₀ (k : ℤ))
    rw [hdegD, hgen] at this
    exact this
  refine ⟨hC, hfd, fun k => ?_, fun k hk => ?_⟩
  · have := hRRk k; omega
  · have h0 : ell (canonicalDivisorOf hω - Finsupp.single P₀ (k : ℤ)) = 0 := by
      apply ell_eq_zero_of_degree_neg
      rw [map_sub, hdegK, hdegD, hgen]; omega
    have := hRRk k
    rw [h0] at this
    simpa using this

end RR

section Root

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  {φ : F →ₐ[K] F} {hφ : φ.toRingHom.IsIntegral} {q : ℕ}

theorem ord_map_eq (h : IsFrobeniusEndo (q ^ 2) φ) (hq : q ≠ 0) (w : Place K F) (f : F) :
    w.ord (φ f) = (q : ℤ) ^ 2 * (w.restrictAlong φ hφ).ord f := by
  have := Place.ord_restrictAlong φ hφ w f
  rw [h.ramificationIndexAlong_eq (pow_ne_zero 2 hq) w] at this
  rw [this]; push_cast; ring

def root (h : IsFrobeniusEndo (q ^ 2) φ) (z : F) : F :=
  (h.mem_range_pow z).choose ^ q

theorem root_pow (h : IsFrobeniusEndo (q ^ 2) φ) (z : F) : (root h z) ^ q = φ z := by
  unfold root
  rw [← pow_mul, ← sq, ← (h.mem_range_pow z).choose_spec]

theorem root_eq_zero_iff (h : IsFrobeniusEndo (q ^ 2) φ) (hq : q ≠ 0) (z : F) :
    root h z = 0 ↔ z = 0 := by
  constructor
  · intro h0
    have := root_pow h z
    rw [h0, zero_pow hq] at this
    exact (map_eq_zero φ).mp this.symm
  · rintro rfl
    have := root_pow h (0 : F)
    rw [map_zero] at this
    exact (pow_eq_zero_iff hq).mp this

theorem ord_root (h : IsFrobeniusEndo (q ^ 2) φ) (hq : q ≠ 0) (w : Place K F) (z : F) :
    w.ord (root h z) = q * (w.restrictAlong φ hφ).ord z := by
  have h1 : w.ord ((root h z) ^ q) = w.ord (φ z) := by rw [root_pow]
  rw [ord_pow, ord_map_eq (hφ := hφ) h hq w z] at h1
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
  have : (q : ℤ) * w.ord (root h z) = q * (q * (w.restrictAlong φ hφ).ord z) := by
    rw [h1]; ring
  exact mul_left_cancel₀ hq' this

theorem root_mem_lSpace (h : IsFrobeniusEndo (q ^ 2) φ) (hq : q ≠ 0) {P₀ : Place K F}
    (hP₀ : Function.IsFixedPt (Place.restrictAlong φ hφ) P₀)
    (hinj : Function.Injective (Place.restrictAlong φ hφ)) {n : ℕ} {z : F}
    (hz : z ∈ LSpace (Finsupp.single P₀ (n : ℤ))) :
    root h z ∈ LSpace (Finsupp.single P₀ ((q * n : ℕ) : ℤ)) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [(root_eq_zero_iff h hq 0).mpr rfl]; exact zero_mem _
  have hr0 : root h z ≠ 0 := fun h0 => hz0 ((root_eq_zero_iff h hq z).mp h0)
  rw [mem_lSpace_iff_ord]
  right
  intro w
  rw [ord_root (hφ := hφ) h hq w z]
  have hzw := ((mem_lSpace_iff_ord).mp hz).resolve_left hz0 (w.restrictAlong φ hφ)
  by_cases hw : w.restrictAlong φ hφ = P₀
  · have hw' : w = P₀ := hinj (hw.trans hP₀.symm)
    subst hw'
    rw [hw, Finsupp.single_eq_same] at hzw
    rw [hw, Finsupp.single_eq_same]; push_cast; nlinarith
  · rw [Finsupp.single_eq_of_ne hw] at hzw
    have : (0 : ℤ) ≤ Finsupp.single P₀ (((q * n : ℕ)) : ℤ) w := by
      by_cases hw' : w = P₀
      · subst hw'; rw [Finsupp.single_eq_same]; positivity
      · rw [Finsupp.single_eq_of_ne hw']
    nlinarith

theorem sum_mul_root_pow (h : IsFrobeniusEndo (q ^ 2) φ) {p c : ℕ} [ExpChar F p]
    (hqc : q = p ^ c) {ι : Type*} (t : Finset ι) (a z : ι → F) :
    (∑ i ∈ t, a i * root h (z i)) ^ q = ∑ i ∈ t, (a i) ^ q * φ (z i) := by
  subst hqc
  rw [sum_pow_char_pow p c t]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, root_pow]

end Root

section Main

variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] [IsCurveOver K E]

theorem degree_eq_sum (D : Divisor K E) : Divisor.degree D = ∑ w ∈ D.support, D w := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [IsCurveOver.deg_eq_one_of_isAlgClosed w]

theorem main_bound
    (hfg : ∃ s : Finset E, IntermediateField.adjoin K (s : Set E) = ⊤)
    (q : ℕ) (hq : (genusFF K E + 1) ^ 2 < q)
    (ψ : E →ₐ[K] E) (hψi : ψ.toRingHom.IsIntegral)
    (hψ : IsFrobeniusEndo (q ^ 2) ψ) :
    (Function.fixedPoints (Place.restrictAlong ψ hψi)).Finite ∧
      Nat.card (Function.fixedPoints (Place.restrictAlong ψ hψi)) <
        q ^ 2 + 1 + (2 * genusFF K E + 1) * q := by
  classical

  have hq1 : 1 < q := lt_of_le_of_lt (Nat.one_le_pow _ _ (Nat.succ_pos _)) hq
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hq0 : m + 1 ≠ 0 := by omega
  have hQ0 : (m + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hgm : (genusFF K E + 1) ^ 2 < m + 1 := hq

  rcases (Function.fixedPoints (Place.restrictAlong ψ hψi)).eq_empty_or_nonempty with
    hempty | ⟨P₀, hP₀⟩
  · refine ⟨hempty ▸ Set.finite_empty, ?_⟩
    rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]; positivity
  have hP₀' : Function.IsFixedPt (Place.restrictAlong ψ hψi) P₀ :=
    Function.mem_fixedPoints.mp hP₀
  have hsurj : ∀ v : Place K E, Function.Surjective (algebraMap K v.ResidueField) :=
    fun v => residue_surjective v
  have hinjΦ : Function.Injective (Place.restrictAlong ψ hψi) :=
    hψ.restrictAlong_injective hQ0 hψi

  obtain ⟨p, hp, hKp, a, ha⟩ :=
    exists_charP_of_fixed hψ (le_trans hq1 (Nat.le_self_pow two_ne_zero _)) hP₀' (hsurj P₀)
  haveI : Fact p.Prime := ⟨hp⟩
  have hqdvd : m + 1 ∣ p ^ a := by rw [← ha]; exact dvd_pow_self _ two_ne_zero
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp hqdvd
  haveI : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p

  obtain ⟨hC, hfd, hlow, hexact⟩ := dimension_package hfg P₀
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = m + 1 + 2 * genusFF K E := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, N₁ = (m + 1) * m + n := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = m + (m + 1) * n := ⟨_, rfl⟩

  obtain ⟨s, hs, hsinj, hspan⟩ := exists_adapted_span hC P₀ (hsurj P₀) m
  have hcard : (m : ℤ) + 1 - genusFF K E ≤ s.card :=
    (hlow m).trans (by exact_mod_cast ell_le_card_of_span_le hspan)

  haveI hVfd : FiniteDimensional K (LSpace (Finsupp.single P₀ (n : ℤ))) := hfd _
  haveI hWfd : FiniteDimensional K (LSpace (Finsupp.single P₀ (N₁ : ℤ))) := hfd _
  have hV : (n : ℤ) + 1 - genusFF K E ≤ ell (Finsupp.single P₀ (n : ℤ)) := hlow n
  have hW : (ell (Finsupp.single P₀ (N₁ : ℤ)) : ℤ) = N₁ + 1 - genusFF K E :=
    hexact N₁ (by rw [hN₁, hn]; push_cast; nlinarith)

  have hdivW : (m + 1) • Finsupp.single P₀ (m : ℤ) + Finsupp.single P₀ (n : ℤ) =
      Finsupp.single P₀ (N₁ : ℤ) := by
    rw [smul_single_natCast, ← Finsupp.single_add]
    congr 1; rw [hN₁]; push_cast; ring
  have hdivr : Finsupp.single P₀ (m : ℤ) + Finsupp.single P₀ ((((m + 1) * n : ℕ)) : ℤ) =
      Finsupp.single P₀ (r : ℤ) := by
    rw [← Finsupp.single_add]
    congr 1; rw [hr]; push_cast; ring

  let lam : (↥s → LSpace (Finsupp.single P₀ (n : ℤ))) →ₗ[K] E :=
    { toFun := fun y => ∑ u : ↥s, ((u : E) ^ (m + 1)) * ((y u : _) : E)
      map_add' := fun y y' => by
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c y => by
        simp [Finset.smul_sum] }
  have hlam_apply : ∀ y, lam y = ∑ u : ↥s, ((u : E) ^ (m + 1)) * ((y u : _) : E) :=
    fun y => rfl
  have hlam_mem : ∀ y, lam y ∈ LSpace (Finsupp.single P₀ (N₁ : ℤ)) := by
    intro y
    rw [hlam_apply]
    refine Submodule.sum_mem _ fun u _ => ?_
    have h1 := pow_mem_lSpace_smul (hs u u.2).2.1 (m + 1)
    have h2 := mul_mem_lSpace_add h1 (y u).2
    rwa [hdivW] at h2
  let lamW := LinearMap.codRestrict (LSpace (Finsupp.single P₀ (N₁ : ℤ))) lam hlam_mem
  have hdim : Module.finrank K (LSpace (Finsupp.single P₀ (N₁ : ℤ))) <
      Module.finrank K (↥s → LSpace (Finsupp.single P₀ (n : ℤ))) := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    have key : (ell (Finsupp.single P₀ (N₁ : ℤ)) : ℤ) <
        s.card * ell (Finsupp.single P₀ (n : ℤ)) := by
      have h1 : ((m : ℤ) + 1 - genusFF K E) * (n + 1 - genusFF K E) ≤
          (s.card : ℤ) * ell (Finsupp.single P₀ (n : ℤ)) :=
        mul_le_mul hcard hV (by rw [hn]; push_cast; linarith) (by positivity)
      have hgm' : ((genusFF K E : ℤ) + 1) ^ 2 < m + 1 := by exact_mod_cast hgm
      rw [hW]
      rw [hn] at h1; rw [hN₁, hn]; push_cast at h1 ⊢
      nlinarith
    exact_mod_cast key
  obtain ⟨y, hy_mem, hy_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := lamW) hdim)
  have hy0 : lam y = 0 := by
    have := LinearMap.mem_ker.mp hy_mem
    simpa [lamW] using congrArg Subtype.val this

  set x : E := ∑ u : ↥s, (u : E) * root hψ ((y u : _) : E) with hx

  have hxq : x ^ (m + 1) = ∑ u : ↥s, (u : E) ^ (m + 1) * ψ ((y u : _) : E) :=
    sum_mul_root_pow hψ hc Finset.univ _ _

  have hxL : x ∈ LSpace (Finsupp.single P₀ (r : ℤ)) := by
    rw [hx]
    refine Submodule.sum_mem _ fun u _ => ?_
    have h1 := (hs u u.2).2.1
    have h2 := root_mem_lSpace (hφ := hψi) hψ hq0 hP₀' hinjΦ (y u).2
    have := mul_mem_lSpace_add h1 h2
    rwa [hdivr] at this

  have hy_ex : ∃ u : ↥s, ((y u : _) : E) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hy_ne
    funext u
    exact Subtype.ext (by simpa using hall u)
  have hroot0 : ∀ z : E, root hψ z = 0 ↔ z = 0 := root_eq_zero_iff hψ hq0
  have hx0 : x ≠ 0 := by
    have hxt : x = ∑ u ∈ Finset.univ.filter (fun u : ↥s => ((y u : _) : E) ≠ 0),
        (u : E) * root hψ ((y u : _) : E) := by
      rw [hx]; symm
      apply Finset.sum_filter_of_ne
      intro u _ hne h0
      apply hne
      rw [(hroot0 _).mpr h0, mul_zero]
    rw [hxt]
    obtain ⟨u₀, hu₀⟩ := hy_ex
    apply sum_ne_zero_of_injOn P₀ (fun u : ↥s => (u : E) * root hψ ((y u : _) : E))
      ⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₀⟩⟩
    · intro u hu
      have hyu : ((y u : _) : E) ≠ 0 := (Finset.mem_filter.mp hu).2
      exact mul_ne_zero (hs u u.2).1 (fun h0 => hyu ((hroot0 _).mp h0))
    · intro u₁ hu₁ u₂ hu₂ heq
      have hy₁ : ((y u₁ : _) : E) ≠ 0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hu₁)).2
      have hy₂ : ((y u₂ : _) : E) ≠ 0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hu₂)).2
      have hr₁ : root hψ ((y u₁ : _) : E) ≠ 0 := fun h0 => hy₁ ((hroot0 _).mp h0)
      have hr₂ : root hψ ((y u₂ : _) : E) ≠ 0 := fun h0 => hy₂ ((hroot0 _).mp h0)
      obtain ⟨hu₁0, -, hb₁, hb₁'⟩ := hs u₁ u₁.2
      obtain ⟨hu₂0, -, hb₂, hb₂'⟩ := hs u₂ u₂.2
      simp only at heq
      rw [P₀.adicValuation_eq_exp_neg_ord (mul_ne_zero hu₁0 hr₁),
        P₀.adicValuation_eq_exp_neg_ord (mul_ne_zero hu₂0 hr₂), exp_inj, neg_inj,
        P₀.ord_mul hu₁0 hr₁, P₀.ord_mul hu₂0 hr₂, ord_root (hφ := hψi) hψ hq0,
        ord_root (hφ := hψi) hψ hq0, hP₀'] at heq
      have hord : P₀.ord (u₁ : E) = P₀.ord (u₂ : E) := by
        rcases lt_trichotomy (P₀.ord ((y u₁ : _) : E)) (P₀.ord ((y u₂ : _) : E)) with
          hAB | hAB | hAB
        · exfalso
          have := mul_le_mul_of_nonneg_left (show P₀.ord ((y u₁ : _) : E) + 1 ≤
            P₀.ord ((y u₂ : _) : E) by omega) (show (0 : ℤ) ≤ (m + 1 : ℕ) by positivity)
          push_cast at this heq
          nlinarith
        · rw [hAB] at heq; push_cast at heq; linarith
        · exfalso
          have := mul_le_mul_of_nonneg_left (show P₀.ord ((y u₂ : _) : E) + 1 ≤
            P₀.ord ((y u₁ : _) : E) by omega) (show (0 : ℤ) ≤ (m + 1 : ℕ) by positivity)
          push_cast at this heq
          nlinarith
      exact Subtype.ext (hsinj u₁.2 u₂.2 hord)

  have hfixlt : ∀ P : Place K E, Function.IsFixedPt (Place.restrictAlong ψ hψi) P →
      P ≠ P₀ → P.adicValuation x < 1 := by
    intro P hP hne
    have hval_le : ∀ {k : ℤ} {f : E}, f ∈ LSpace (Finsupp.single P₀ k) →
        P.adicValuation f ≤ 1 := fun hf => ((mem_lSpace_single_iff P₀).mp hf).2 P hne
    have hxq_val : P.adicValuation (x ^ (m + 1)) < 1 := by
      have hrew : x ^ (m + 1) =
          ∑ u : ↥s, (u : E) ^ (m + 1) * (ψ ((y u : _) : E) - ((y u : _) : E)) := by
        rw [hxq, ← sub_zero (∑ u : ↥s, (u : E) ^ (m + 1) * ψ ((y u : _) : E)), ← hy0,
          hlam_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [hrew]
      apply P.adicValuation.map_sum_lt one_ne_zero
      intro u _
      rw [map_mul, map_pow]
      calc P.adicValuation (u : E) ^ (m + 1) * P.adicValuation (ψ ((y u : _) : E) - (y u : _))
          ≤ P.adicValuation (ψ ((y u : _) : E) - (y u : _)) :=
            mul_le_of_le_one_left' (pow_le_one' (hval_le (hs u u.2).2.1) _)
        _ < 1 := adicValuation_map_sub_self_lt_one hψ hQ0 hP (hsurj P)
            (mem_of_adicValuation_le_one P (hval_le (y u).2))
    rw [map_pow] at hxq_val
    by_contra hge
    push Not at hge
    exact absurd (lt_of_le_of_lt (one_le_pow_of_one_le' hge _) hxq_val) (lt_irrefl _)

  obtain ⟨D, hD, hD0⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx0
  set Z : Finset (Place K E) := D.support.filter (fun w => 0 < D w) with hZ
  have hsub : Function.fixedPoints (Place.restrictAlong ψ hψi) ⊆
      ((insert P₀ Z : Finset (Place K E)) : Set (Place K E)) := by
    intro P hP
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    by_cases hne : P = P₀
    · exact Or.inl hne
    right
    rw [hZ, Finset.mem_filter, Finsupp.mem_support_iff, hD P]
    have hlt := hfixlt P (Function.mem_fixedPoints.mp hP) hne
    rw [P.adicValuation_eq_exp_neg_ord hx0, ← exp_zero, exp_lt_exp] at hlt
    exact ⟨by omega, by omega⟩
  have hZcard : (Z.card : ℤ) ≤ r := by
    have h1 : Z.card • (1 : ℤ) ≤ ∑ w ∈ Z, D w :=
      Finset.card_nsmul_le_sum Z (fun w => D w) 1 fun w hw => by
        have := (Finset.mem_filter.mp hw).2; show (1 : ℤ) ≤ D w; omega
    have h2 := Finset.sum_filter_add_sum_filter_not D.support (fun w => 0 < D w) (fun w => D w)
    have h3 : ∑ w ∈ D.support, D w = 0 := by rw [← degree_eq_sum]; exact hD0
    have h4 : -(r : ℤ) ≤ ∑ w ∈ D.support.filter (fun w => ¬ 0 < D w), D w := by
      have hsub' : D.support.filter (fun w => ¬ 0 < D w) ⊆ {P₀} := by
        intro w hw
        rw [Finset.mem_filter, Finsupp.mem_support_iff, hD w] at hw
        rw [Finset.mem_singleton]
        by_contra hne
        have hle := ((mem_lSpace_single_iff P₀).mp hxL).2 w hne
        rcases (w.adicValuation_le_one_iff).mp hle with h0 | h0
        · exact hx0 h0
        · omega
      rcases Finset.subset_singleton_iff.mp hsub' with h | h
      · rw [h, Finset.sum_empty]; omega
      · rw [h, Finset.sum_singleton, hD P₀]
        have := ((mem_lSpace_iff_ord).mp hxL).resolve_left hx0 P₀
        rwa [Finsupp.single_eq_same] at this
    rw [nsmul_one] at h1
    rw [← hZ] at h2
    linarith
  have hfin : (Function.fixedPoints (Place.restrictAlong ψ hψi)).Finite :=
    (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  rw [Nat.card_coe_set_eq]
  have hle : (Function.fixedPoints (Place.restrictAlong ψ hψi)).ncard ≤ (insert P₀ Z).card := by
    rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have hins := Finset.card_insert_le P₀ Z
  have hr' : r + 1 = (m + 1) ^ 2 + (2 * genusFF K E + 1) * (m + 1) := by
    rw [hr, hn]; ring
  omega

end Main

end BombieriUpper

end AlgebraicCurve

end

theorem solution
    (K E : Type*) [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
    [AlgebraicCurve.IsCurveOver K E]
    (hfg : ∃ s : Finset E, IntermediateField.adjoin K (s : Set E) = ⊤)
    (q : ℕ) (hq : (AlgebraicCurve.genusFF K E + 1) ^ 2 < q)
    (ψ : E →ₐ[K] E) (hψi : ψ.toRingHom.IsIntegral)
    (hψ : AlgebraicCurve.IsFrobeniusEndo (q ^ 2) ψ) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong ψ hψi)).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong ψ hψi)) <
        q ^ 2 + 1 + (2 * AlgebraicCurve.genusFF K E + 1) * q :=
  AlgebraicCurve.BombieriUpper.main_bound hfg q hq ψ hψi hψ

end S_AlgebraicCurve_natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
end P2MW
export P2MW.S_AlgebraicCurve_natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq (solution)
