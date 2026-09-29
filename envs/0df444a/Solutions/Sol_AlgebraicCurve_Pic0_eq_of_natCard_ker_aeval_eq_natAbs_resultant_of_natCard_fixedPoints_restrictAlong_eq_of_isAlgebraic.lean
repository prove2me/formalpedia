-- Prove2me | solution 1 for AlgebraicCurve.Pic0.eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b8e00567-8665-5899-b4c4-35c1dddf976a

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_Multiset_filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq
import Theorems.Thm_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
import Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_Polynomial_eq_of_forall_sum_roots_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

namespace P2mIdentAlg

open Polynomial

theorem resultant_X_pow_sub_one_eq_prod (P : ℤ[X]) (hP : P.Monic) (heven : Even P.natDegree)
    (n : ℕ) :
    (((X ^ n - 1 : ℤ[X]).resultant P : ℤ) : ℂ) =
      ((P.map (Int.castRingHom ℂ)).roots.map (fun z => 1 - z ^ n)).prod := by
  set G : ℤ[X] := X ^ n - 1 with hG
  set Pc : ℂ[X] := P.map (Int.castRingHom ℂ) with hPc
  have hGdeg : G.natDegree = n := by
    rw [hG, ← C_1, natDegree_X_pow_sub_C]
  have hGc : G.map (Int.castRingHom ℂ) = X ^ n - 1 := by
    rw [hG, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
  have hGcdeg : (X ^ n - 1 : ℂ[X]).natDegree = n := by
    rw [← C_1, natDegree_X_pow_sub_C]
  have hPcm : Pc.Monic := hP.map _
  have hPcdeg : Pc.natDegree = P.natDegree := hP.natDegree_map _
  have h1 : (((G.resultant P : ℤ)) : ℂ) = (X ^ n - 1 : ℂ[X]).resultant Pc n P.natDegree := by
    show (Int.castRingHom ℂ) (G.resultant P G.natDegree P.natDegree) = _
    rw [← resultant_map_map, hGc, hGdeg]
  have h2 : (X ^ n - 1 : ℂ[X]).resultant Pc n P.natDegree =
      Pc.resultant (X ^ n - 1) Pc.natDegree n := by
    rw [resultant_comm, hPcdeg, Even.neg_one_pow (heven.mul_left n), one_mul]
  have h3 : Pc.resultant (X ^ n - 1) Pc.natDegree n = (Pc.roots.map (fun z => z ^ n - 1)).prod := by
    rw [resultant_eq_prod_eval Pc (X ^ n - 1) n hGcdeg.le (IsAlgClosed.splits Pc), hPcm.leadingCoeff,
      one_pow, one_mul]
    simp
  have h4 : (Pc.roots.map (fun z => z ^ n - 1)).prod = (Pc.roots.map (fun z => 1 - z ^ n)).prod := by
    have hcard : Multiset.card Pc.roots = P.natDegree := by
      rw [IsAlgClosed.card_roots_eq_natDegree, hPcdeg]
    have : Pc.roots.map (fun z => z ^ n - 1) = (Pc.roots.map (fun z => 1 - z ^ n)).map Neg.neg := by
      rw [Multiset.map_map]; congr 1; funext z; simp
    rw [this, Multiset.prod_map_neg, Multiset.card_map, hcard, Even.neg_one_pow heven, one_mul]
  rw [h1, h2, h3, h4]

theorem int_poly_eq_of_natAbs_resultant_eq (P Q : ℤ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hdeg : P.natDegree = Q.natDegree) (heven : Even Q.natDegree)
    (c : ℝ) (hc : 1 < c) (hQr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ = c)
    (h : ∀ n : ℕ, 0 < n →
      ((X ^ n - 1 : ℤ[X]).resultant P).natAbs = ((X ^ n - 1 : ℤ[X]).resultant Q).natAbs) :
    P = Q := by
  classical
  set Ls := (P.map (Int.castRingHom ℂ)).roots with hL
  set Ws := (Q.map (Int.castRingHom ℂ)).roots with hW
  have hevenP : Even P.natDegree := hdeg ▸ heven
  have hsq : ∀ n : ℕ, 0 < n →
      ((2 • Ls).map fun z => 1 - z ^ n).prod = ((2 • Ws).map fun z => 1 - z ^ n).prod := by
    intro n hn
    rw [Multiset.map_nsmul, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.prod_nsmul,
      ← resultant_X_pow_sub_one_eq_prod P hP hevenP n, ← resultant_X_pow_sub_one_eq_prod Q hQ heven n]
    rcases Int.natAbs_eq_natAbs_iff.mp (h n hn) with h1 | h1
    · rw [h1]
    · rw [h1]; push_cast; ring
  have hω2 : ∀ z ∈ 2 • Ws, ‖z‖ = c := fun z hz => hQr z (Multiset.mem_of_mem_nsmul hz)
  have hrig := Multiset.filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq (2 • Ls) (2 • Ws) c hc hω2 hsq
  rw [Multiset.filter_nsmul] at hrig
  have hfilt : Ls.filter (fun z => z ≠ 0) = Ws := by
    ext z
    have := congr_arg (Multiset.count z) hrig
    rw [Multiset.count_nsmul, Multiset.count_nsmul] at this
    omega
  have hcardL : Multiset.card Ls = P.natDegree := by
    rw [hL, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map]
  have hcardW : Multiset.card Ws = Q.natDegree := by
    rw [hW, IsAlgClosed.card_roots_eq_natDegree, hQ.natDegree_map]
  have hLW : Ls = Ws := by
    rw [← hfilt]
    symm
    apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
    rw [hfilt, hcardW, hcardL, hdeg]
  have key : P.map (Int.castRingHom ℂ) = Q.map (Int.castRingHom ℂ) := by
    rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hP.map (Int.castRingHom ℂ)),
      (IsAlgClosed.splits _).eq_prod_roots_of_monic (hQ.map (Int.castRingHom ℂ)), ← hL, ← hW, hLW]
  exact Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective key

variable (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]

theorem dfr_polynomial_eq_classNumberPolynomial
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (Pπ : ℤ[X]) (hπm : Pπ.Monic) (hπdeg : Pπ.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hπ : ∀ G : ℤ[X], G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        (G.resultant Pπ ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant Pπ).natAbs) ∧
        (G.resultant Pπ = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (P : ℤ[X]) (hPm : P.Monic) (hPdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hP0 : P.coeff 0 = (Nat.card k : ℤ) ^ AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum))
    (hkerP : ∀ n : ℕ, 0 < n →
      (Function.fixedPoints (⇑T)^[n]).Finite ∧
      ((X ^ n - 1 : ℤ[X]).resultant P = Nat.card (Function.fixedPoints (⇑T)^[n]))) :
    Pπ = P := by
  classical
  have hRH := AlgebraicCurve.norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
    k K F₀ F hfg hgen φ hφi hφ P hPm hPdeg hP0 hfix
  have hq1 : (1 : ℝ) < Real.sqrt (Nat.card k : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card k))

  have kerEquiv : ∀ n : ℕ,
      ((Polynomial.aeval (R := ℤ) T.toIntLinearMap (X ^ n - 1 : ℤ[X])).toAddMonoidHom.ker) ≃
        (Function.fixedPoints (⇑T)^[n]) := fun n =>
    Equiv.subtypeEquivRight fun x => by
      show x ∈ (Polynomial.aeval (R := ℤ) T.toIntLinearMap (X ^ n - 1 : ℤ[X])).toAddMonoidHom.ker ↔
        x ∈ Function.fixedPoints (⇑T)^[n]
      rw [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub, Polynomial.aeval_one,
        map_pow, Polynomial.aeval_X, LinearMap.sub_apply, Module.End.one_apply,
        Module.End.pow_apply, sub_eq_zero, Function.mem_fixedPoints, Function.IsFixedPt]
      rfl
  refine int_poly_eq_of_natAbs_resultant_eq Pπ P hπm hPm (hπdeg.trans hPdeg.symm)
    (hPdeg ▸ ⟨_, two_mul _⟩) _ hq1 hRH fun n hn => ?_
  have hGm : (X ^ n - 1 : ℤ[X]).Monic := by
    rw [← C_1]; exact Polynomial.monic_X_pow_sub_C _ hn.ne'
  have hG0 : ((((X ^ n - 1 : ℤ[X]).coeff 0 : ℤ)) : K) ≠ 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega), Polynomial.coeff_one_zero,
      zero_sub, Int.cast_neg, Int.cast_one]
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨h1, h2⟩ := hπ (X ^ n - 1) hGm hG0
  obtain ⟨hfin, hresP⟩ := hkerP n hn
  have hres : (X ^ n - 1 : ℤ[X]).resultant Pπ ≠ 0 := by
    intro h0
    haveI : Finite (Function.fixedPoints (⇑T)^[n]) := hfin.to_subtype
    exact h2 h0 (Finite.of_equiv _ (kerEquiv n).symm)
  rw [← h1 hres, Nat.card_congr (kerEquiv n), hresP, Int.natAbs_natCast]

theorem main
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (Pπ : ℤ[X]) (hπm : Pπ.Monic) (hπdeg : Pπ.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hπ : ∀ G : ℤ[X], G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        (G.resultant Pπ ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant Pπ).natAbs) ∧
        (G.resultant Pπ = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (P : ℤ[X]) (hPm : P.Monic) (hPdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    Pπ = P := by

  have hC : AlgebraicCurve.ConstantsAreBase k F₀ :=
    AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen φ hφ

  obtain ⟨PS, hSm, hSdeg, hS0, hSfix, hSker⟩ :=
    AlgebraicCurve.Pic0.exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
      k K F₀ F hfg hC hgen halg φ hφi hφ T hT

  have h1 : Pπ = PS :=
    dfr_polynomial_eq_classNumberPolynomial k K F₀ F hfg hgen φ hφi hφ T Pπ hπm hπdeg hπ PS hSm hSdeg
      hS0 (fun n hn => (hSfix n hn).2) (fun n hn => ⟨(hSker n hn).1, (hSker n hn).2.2.1⟩)

  have h2 : P.map (Int.castRingHom ℂ) = PS.map (Int.castRingHom ℂ) := by
    refine Polynomial.eq_of_forall_sum_roots_pow_eq _ _ (hPm.map _) (hSm.map _) (IsAlgClosed.splits _)
      (IsAlgClosed.splits _) (by rw [hPm.natDegree_map, hSm.natDegree_map, hPdeg, hSdeg]) ?_
    intro n hn
    have e1 := hfix n hn
    have e2 := (hSfix n hn).2
    rw [e1] at e2

    have := congr_arg (fun z : ℂ => (Nat.card k : ℂ) ^ n + 1 - z) e2
    simpa using this
  rw [h1]
  exact (Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective h2).symm

end P2mIdentAlg

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (Pπ : Polynomial ℤ) (hπm : Pπ.Monic) (hπdeg : Pπ.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hπ : ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        (G.resultant Pπ ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant Pπ).natAbs) ∧
        (G.resultant Pπ = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (P : Polynomial ℤ) (hPm : P.Monic) (hPdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    Pπ = P :=
  P2mIdentAlg.main k K F₀ F hfg hgen halg φ hφi hφ T hT Pπ hπm hπdeg hπ P hPm hPdeg hfix

end S_AlgebraicCurve_Pic0_eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic (solution)
