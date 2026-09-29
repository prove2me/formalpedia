-- Prove2me | solution 1 for AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/edddf270-e07d-564f-8f1c-04f0b69d06c4

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Theorems.Thm_AutomorphicForm_norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal
import Theorems.Thm_AutomorphicForm_SatakeCombination_mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "localIntegralSet localCentralizer localCentralizerBorel IsOrbitalIntegral SatakeCombination.slotDeg SatakeCombination.slotWord SatakeCombination.slotCoeff norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal SatakeCombination.mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg"
namespace LocalCoeffTAux
p2m_open "AutomorphicForm"

open LaurentPolynomial

theorem mul_T_apply (Q : ℂ[T;T⁻¹]) (a m : ℤ) : (Q * T a : ℂ[T;T⁻¹]).coeff m = Q.coeff (m - a) := by
  simp only [T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem one_apply' (m : ℤ) : (1 : ℂ[T;T⁻¹]).coeff m = if (0 : ℤ) = m then 1 else 0 := by
  rw [← T_zero, T_apply]

theorem add_apply' (P Q : ℂ[T;T⁻¹]) (m : ℤ) : (P + Q).coeff m = P.coeff m + Q.coeff m := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem pow_succ_apply (a : ℤ) (k : ℕ) (m : ℤ) :
    ((T a + T (-a)) ^ (k + 1) : ℂ[T;T⁻¹]).coeff m =
      ((T a + T (-a)) ^ k : ℂ[T;T⁻¹]).coeff (m - a) + ((T a + T (-a)) ^ k : ℂ[T;T⁻¹]).coeff (m + a) := by
  rw [pow_succ, mul_add, add_apply', mul_T_apply, mul_T_apply, sub_neg_eq_add]

theorem two_dvd_of_apply_ne_zero (k : ℕ) (n : ℤ)
    (h : ((T 1 + T (-1)) ^ k : ℂ[T;T⁻¹]).coeff n ≠ 0) : 2 ∣ (k : ℤ) - n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, one_apply'] at h
    by_cases h0 : (0 : ℤ) = n
    · subst h0; simp
    · exact absurd (if_neg h0) h
  | succ k ih =>
    rw [pow_succ_apply 1] at h
    by_cases h1 : ((T 1 + T (-1)) ^ k : ℂ[T;T⁻¹]).coeff (n - 1) = 0
    · rw [h1, zero_add] at h
      have e : ((k + 1 : ℕ) : ℤ) - n = ((k : ℤ) - (n + 1)) + 2 := by push_cast; ring
      rw [e]
      exact dvd_add (ih _ h) (dvd_refl 2)
    · have e : ((k + 1 : ℕ) : ℤ) - n = (k : ℤ) - (n - 1) := by push_cast; ring
      rw [e]
      exact ih _ h1

theorem valued_coe_eq_exp_neg_one_of_irreducible
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hint : Valuation.Integers (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))
      (v.adicCompletionIntegers K) := Valuation.valuationSubring.integers _
  have hϖK : (ϖ : v.adicCompletion K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hlt : Valued.v (ϖ : v.adicCompletion K) < 1 := hint.valuation_irreducible_lt_one hϖ
  have hne : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖK
  obtain ⟨π₀, hπ₀⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-1 : ℤ))
  have hπ₀le : Valued.v π₀ ≤ 1 := by
    rw [hπ₀, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set p : v.adicCompletionIntegers K := ⟨π₀, hπ₀le⟩ with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h' : π₀ = 0 := congrArg Subtype.val h
    rw [h', map_zero] at hπ₀
    exact WithZero.exp_ne_zero hπ₀.symm
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hval : WithZero.exp (-1 : ℤ) = Valued.v (ϖ : v.adicCompletion K) ^ n := by
    have e1 : π₀ = ((w : v.adicCompletionIntegers K) : v.adicCompletion K) *
        (ϖ : v.adicCompletion K) ^ n := by
      have := congrArg (fun q : v.adicCompletionIntegers K => (q : v.adicCompletion K)) hw
      simpa using this
    have hw1 : Valued.v ((w : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := hint.valuation_unit w
    rw [← hπ₀, e1, map_mul, map_pow, hw1, one_mul]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ϖ : v.adicCompletion K) = WithZero.exp m :=
    ⟨WithZero.log (Valued.v (ϖ : v.adicCompletion K)), (WithZero.exp_log hne).symm⟩
  rw [hm] at hval hlt ⊢
  rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hval
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_inj]
  have hdvd : (n : ℤ) ∣ 1 := dvd_neg.mp ⟨m, hval⟩
  have hn1 : n = 1 := Nat.dvd_one.mp (by exact_mod_cast hdvd)
  subst hn1
  simpa using hval.symm

theorem norm_coe_eq_inv_absNorm_of_irreducible
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    ‖(ϖ : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_coe_eq_exp_neg_one_of_irreducible K v ϖ hϖ,
    show WithZero.exp (-1 : ℤ) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    zpow_neg, zpow_one]
  push_cast
  rfl

end AutomorphicForm.LocalCoeffTAux

open AutomorphicForm.LocalCoeffTAux in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (k j : ℕ)
    (hf : 0 < AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (Nw : ℕ) (hNw : Ideal.absNorm (ws v).1.asIdeal = Nw)
    (hNwf : Nw = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s x : ℂ) (hζ : ζ ≠ 0) (hs : s ^ 2 = ζ)
    (hx : x ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ)

    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))

    (u : v.adicCompletion K) (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℤ)
    (hud : ‖u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ d)

    (t : ℤ → GL (Fin 2) (v.adicCompletion K))
    (ht : ∀ e : ℤ, (t e : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖ : v.adicCompletion K) ^ e * u, (ϖ : v.adicCompletion K) ^ e])
    (τ : ∀ e : ℤ, @Measure (AutomorphicForm.localCentralizer K v (t e)) (AutomorphicForm.localCentralizerBorel K v (t e)))
    (hτ : ∀ e : ℤ, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (t e)) (τ e))
    (hτ1 : ∀ e : ℤ, τ e (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I : (Fin 2 →₀ ℕ) → ℤ → ℂ)
    (hI : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, ∀ e : ℤ,
      AutomorphicForm.IsOrbitalIntegral K v (t e) (τ e)
        (fun y : GL (Fin 2) (v.adicCompletion K) =>
          ∑ ι : Fin (r 0) → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun i => rT (ι i)).prod * z ^ (r 1))⁻¹ * y)) (I r e)) :
    (∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
        Summable fun e : ℤ => ‖x ^ e * I r e‖) ∧
    ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
        AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * ∑' e : ℤ, x ^ e * I r e =
      ((‖u - 1‖ : ℝ) : ℂ)⁻¹ *
        (if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ d then
          ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ k * ζ ^ j *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff
                (d / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
            (((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ (-(d / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ))))
        else 0) := by
  classical

  have hϖK : (ϖ : v.adicCompletion K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hnϖ : ‖(ϖ : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ :=
    norm_coe_eq_inv_absNorm_of_irreducible K v ϖ hϖ
  have hNvn : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hNvn
  have hc0 : ((‖u - 1‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (sub_ne_zero.mpr hu1)
  have hfz : (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  have hdiff : ∀ e : ℤ, ((‖(ϖ : v.adicCompletion K) ^ e * u - (ϖ : v.adicCompletion K) ^ e‖ : ℝ) : ℂ) = ((‖u - 1‖ : ℝ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ e)⁻¹ := by
    intro e
    have e1 : (ϖ : v.adicCompletion K) ^ e * u - (ϖ : v.adicCompletion K) ^ e = (ϖ : v.adicCompletion K) ^ e * (u - 1) := by ring
    rw [e1, norm_mul, norm_zpow, hnϖ, inv_zpow]
    push_cast
    ring

  have hmac : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, ∀ e : ℤ,
      ((‖u - 1‖ : ℝ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ e)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) * I r e =
        (if e + d + e = ((r 0 : ℕ) : ℤ) + 2 * ((r 1 : ℕ) : ℤ) then
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ (r 0) : LaurentPolynomial ℂ).coeff (e + d - e) else 0) := by
    intro r hr e
    have hab : (ϖ : v.adicCompletion K) ^ e * u ≠ (ϖ : v.adicCompletion K) ^ e := fun h =>
      hu1 (mul_left_cancel₀ (zpow_ne_zero e hϖK) (h.trans (mul_one _).symm))
    have ha : ‖(ϖ : v.adicCompletion K) ^ e * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ (e + d) := by
      rw [norm_mul, norm_zpow, hud, ← zpow_add₀ (norm_ne_zero_iff.mpr hϖK)]
    have hb : ‖(ϖ : v.adicCompletion K) ^ e‖ = ‖(ϖ : v.adicCompletion K)‖ ^ e := norm_zpow _ _
    have h :=
      AutomorphicForm.norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal
        K v ϖ hϖ hϖ0 n rT hrT z hz (r 0) (r 1) ((ϖ : v.adicCompletion K) ^ e * u) ((ϖ : v.adicCompletion K) ^ e)
        hab (e + d) e ha hb (t e) (ht e) (τ e) (hτ e) (hτ1 e) (I r e) (hI r hr e)
    rwa [hdiff e] at h

  have hzero : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, ∀ e : ℤ,
      ¬ (e + d + e = ((r 0 : ℕ) : ℤ) + 2 * ((r 1 : ℕ) : ℤ)) → I r e = 0 := by
    intro r hr e hne
    have h := hmac r hr e
    rw [if_neg hne] at h
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero hc0 (inv_ne_zero (zpow_ne_zero e hq0))) (pow_ne_zero _ hq0))

  have hsum : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, Summable fun e : ℤ => ‖x ^ e * I r e‖ := by
    intro r hr
    apply summable_of_ne_finset_zero (s := {(((r 0 : ℕ) : ℤ) + 2 * ((r 1 : ℕ) : ℤ) - d) / 2})
    intro e he
    rw [Finset.mem_singleton] at he
    rw [hzero r hr e (fun h => he (by omega)), mul_zero, norm_zero]
  refine ⟨hsum, ?_⟩

  have hterm : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, ∀ e : ℤ,
      AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * (x ^ e * I r e) =
        ((‖u - 1‖ : ℝ) : ℂ)⁻¹ * ((x * (Ideal.absNorm v.asIdeal : ℂ)) ^ e *
          (AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r / (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) *
            (if e + d + e = ((r 0 : ℕ) : ℤ) + 2 * ((r 1 : ℕ) : ℤ) then
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ (r 0) : LaurentPolynomial ℂ).coeff (e + d - e) else 0))) := by
    intro r hr e
    have h := hmac r hr e
    rw [← h, mul_zpow]
    have e1 : ((‖u - 1‖ : ℝ) : ℂ)⁻¹ * ((‖u - 1‖ : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hc0
    have e2 : ((Ideal.absNorm v.asIdeal : ℂ) ^ e)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ e = 1 := inv_mul_cancel₀ (zpow_ne_zero e hq0)
    have e3 : ((Ideal.absNorm v.asIdeal : ℂ) ^ (r 1))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) = 1 := inv_mul_cancel₀ (pow_ne_zero _ hq0)
    calc AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * (x ^ e * I r e)
        = AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * (x ^ e * I r e) * (((‖u - 1‖ : ℝ) : ℂ)⁻¹ * ((‖u - 1‖ : ℝ) : ℂ)) * (((Ideal.absNorm v.asIdeal : ℂ) ^ e)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ e) *
            (((Ideal.absNorm v.asIdeal : ℂ) ^ (r 1))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1)) := by rw [e1, e2, e3]; ring
      _ = _ := by rw [div_eq_mul_inv]; ring

  have hinner : ∀ e : ℤ, ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * (x ^ e * I r e) =
      ((‖u - 1‖ : ℝ) : ℂ)⁻¹ *
        (if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ e ∧ e + d + e = (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * ((k : ℤ) + 2 * (j : ℤ)) then
          ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ k * ζ ^ j *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff
                ((e + d - e) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
            ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ (-((e + d - e) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)))
        else 0) := by
    intro e
    rw [Finset.sum_congr rfl (fun r hr => hterm r hr e), ← Finset.mul_sum, ← Finset.mul_sum,
      AutomorphicForm.SatakeCombination.mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg
        K L ws v k j hf Nw hNw hNwf ζ s x hζ hs hx (e + d) e]

  have hsum' : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, Summable fun e : ℤ => AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * (x ^ e * I r e) :=
    fun r hr => (hsum r hr).of_norm.mul_left _
  rw [Finset.sum_congr rfl (fun r _ => (tsum_mul_left).symm), ← Summable.tsum_finsetSum hsum',
    tsum_congr hinner]
  simp only [add_sub_cancel_left]
  rw [tsum_mul_left]
  congr 1
  generalize hW : (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * ((k : ℤ) + 2 * (j : ℤ)) = W
  rw [tsum_eq_single ((W - d) / 2) (fun e he => if_neg (fun hP => he (by obtain ⟨_, h2⟩ := hP; omega)))]
  by_cases hd : (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ d
  · rw [if_pos hd]
    by_cases hP : (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ (W - d) / 2 ∧ (W - d) / 2 + d + (W - d) / 2 = W
    · rw [if_pos hP]
    · rw [if_neg hP]
      obtain ⟨n', hn'⟩ := hd
      have hdn : d / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) = n' := by rw [hn', Int.mul_ediv_cancel_left _ hfz]
      rw [hdn]
      suffices hL : ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff n' = 0 by
        rw [hL, mul_zero, zero_mul]
      by_contra hL
      obtain ⟨a, ha⟩ := two_dvd_of_apply_ne_zero k n' hL
      apply hP
      have he1 : (W - d) / 2 = (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * (a + j) := by
        have h2 : W - d = 2 * ((AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * (a + j)) := by
          rw [← hW, hn']; linear_combination (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * ha
        rw [h2, Int.mul_ediv_cancel_left _ two_ne_zero]
      refine ⟨he1 ▸ dvd_mul_right _ _, ?_⟩
      rw [he1, ← hW, hn']
      linear_combination (-(AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) * ha
  · rw [if_neg hd, if_neg]
    rintro ⟨⟨b, hb⟩, h2⟩
    exact hd ⟨(k : ℤ) + 2 * j - 2 * b, by linear_combination h2 - 2 * hb - hW⟩

end S_AutomorphicForm_sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
end P2MW
export P2MW.S_AutomorphicForm_sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow (solution)
