-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/47ed0356-e98b-56a3-81c8-c09942c140e0

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Theorems.Thm_NumberField_denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
import Theorems.Thm_AutomorphicForm_exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
set_option Elab.async false
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

noncomputable section

section Lattice
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem sup'_infinitePlace_eq_norm_mixedEmbedding (ξ : K) :
    Finset.univ.sup' Finset.univ_nonempty (fun w : InfinitePlace K => w ξ)
      = ‖NumberField.mixedEmbedding K ξ‖ := by
  rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
  simp only [NumberField.mixedEmbedding.normAtPlace_apply]

private theorem exists_pos_le_sup_infinitePlace (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ f : ℝ, 0 < f ∧ ∀ ξ : K, ξ ∈ (I : FractionalIdeal (𝓞 K)⁰ K) → ξ ≠ 0 →
      f ≤ Finset.univ.sup' Finset.univ_nonempty (fun w : InfinitePlace K => w ξ) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_singleton_iff.1
    (isOpen_discrete ({0} : Set (NumberField.mixedEmbedding.idealLattice K I)))
  refine ⟨ε, hε, fun ξ hξ hξ0 => ?_⟩
  rw [sup'_infinitePlace_eq_norm_mixedEmbedding]
  by_contra hlt
  rw [not_le] at hlt
  have hmem : NumberField.mixedEmbedding K ξ ∈ NumberField.mixedEmbedding.idealLattice K I :=
    (NumberField.mixedEmbedding.mem_idealLattice K I).2 ⟨ξ, hξ, rfl⟩
  have h0 : (⟨NumberField.mixedEmbedding K ξ, hmem⟩ : NumberField.mixedEmbedding.idealLattice K I) = 0 := by
    apply hball
    rw [Subtype.dist_eq, Submodule.coe_zero, dist_zero_right]
    exact hlt
  exact hξ0 ((map_eq_zero (NumberField.mixedEmbedding K)).1 (congrArg Subtype.val h0))

private theorem exists_forall_summable_sup_infinitePlace_rpow_neg (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Summable fun ξ : {ξ : K // ξ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)} =>
        (Finset.univ.sup' Finset.univ_nonempty (fun w : InfinitePlace K => w (ξ : K))) ^ (-(N : ℝ)) := by
  refine ⟨Module.finrank ℤ (NumberField.mixedEmbedding.idealLattice K I) + 1, fun N hN => ?_⟩
  have hsum := ZLattice.summable_norm_rpow (NumberField.mixedEmbedding.idealLattice K I) (-(N : ℝ)) (by
    have h : (Module.finrank ℤ (NumberField.mixedEmbedding.idealLattice K I) : ℝ) + 1 ≤ N := by
      exact_mod_cast hN
    linarith)
  let φ : {ξ : K // ξ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)} → NumberField.mixedEmbedding.idealLattice K I :=
    fun ξ => ⟨NumberField.mixedEmbedding K ξ.1, (NumberField.mixedEmbedding.mem_idealLattice K I).2 ⟨ξ.1, ξ.2, rfl⟩⟩
  have hφ : Function.Injective φ := fun ξ η h =>
    Subtype.ext (NumberField.mixedEmbedding_injective K (congrArg Subtype.val h))
  refine (hsum.comp_injective hφ).congr fun ξ => ?_
  simp only [Function.comp_def, φ, Submodule.coe_norm, sup'_infinitePlace_eq_norm_mixedEmbedding]

private theorem exists_pos_le_prod_infinitePlace_pow_mult (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ ξ : K, ξ ∈ (I : FractionalIdeal (𝓞 K)⁰ K) → ξ ≠ 0 →
      ν ≤ ∏ w : InfinitePlace K, w ξ ^ w.mult := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I : FractionalIdeal (𝓞 K)⁰ K)
  have haK : (algebraMap (𝓞 K) K a) ≠ 0 := by
    simpa using (RingOfIntegers.coe_eq_zero_iff.not.2 ha)
  have haI : aI ≠ ⊥ := by
    rintro rfl
    have h0 : (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [hI, FractionalIdeal.coeIdeal_bot, mul_zero]
    exact Units.ne_zero I h0
  have hnormA : Algebra.norm ℚ (algebraMap (𝓞 K) K a) ≠ 0 := Algebra.norm_ne_zero_iff.2 haK
  have hNaI : (0 : ℝ) < Ideal.absNorm aI := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 haI)
  refine ⟨(Ideal.absNorm aI : ℝ) / |(Algebra.norm ℚ (algebraMap (𝓞 K) K a) : ℝ)|,
    div_pos hNaI (abs_pos.2 (by exact_mod_cast hnormA)), fun ξ hξ hξ0 => ?_⟩
  rw [InfinitePlace.prod_eq_abs_norm]
  rw [hI, FractionalIdeal.mem_singleton_mul] at hξ
  obtain ⟨y, hy, rfl⟩ := hξ
  obtain ⟨y', hy'I, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hy'0 : y' ≠ 0 := by
    rintro rfl
    simp at hξ0
  have hdvd : (Ideal.absNorm aI : ℤ) ∣ Algebra.norm ℤ y' := Ideal.absNorm_dvd_norm_of_mem hy'I
  have hny' : Algebra.norm ℤ y' ≠ 0 := by
    intro h0
    have h1 : (Algebra.norm ℤ y' : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 K) K y') := Algebra.coe_norm_int y'
    rw [h0, Int.cast_zero] at h1
    exact Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (RingOfIntegers.coe_injective)).2 hy'0 :
      algebraMap (𝓞 K) K y' ≠ 0) h1.symm
  have hle : (Ideal.absNorm aI : ℤ) ≤ |Algebra.norm ℤ y'| :=
    Int.le_of_dvd (abs_pos.2 hny') ((dvd_abs _ _).2 hdvd)
  have hleR : (Ideal.absNorm aI : ℝ) ≤ |(Algebra.norm ℚ (algebraMap (𝓞 K) K y') : ℝ)| := by
    rw [← Algebra.coe_norm_int y']
    exact_mod_cast hle
  rw [map_mul, Algebra.norm_inv, abs_mul, abs_inv]
  push_cast
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hleR (inv_nonneg.2 (abs_nonneg _))

end Lattice

open Finset in
private theorem exists_argmax_weighted_core {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ι → ℕ) (s a : ι → ℝ) (s₀ ν : ℝ)
    (hs : ∀ i, s₀ ≤ s i) (hs₀ : 0 ≤ s₀) (ha : ∀ i, 0 ≤ a i)
    (hν : ν ≤ ∏ i, a i ^ n i) :
    ∃ i, (∀ j, s₀ * a j ≤ s i * a i) ∧ (∏ j, s j ^ n j) * ν ≤ (s i * a i) ^ (∑ j, n j) := by
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun j => s j * a j) univ_nonempty
  refine ⟨i, fun j => ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (hs j) (ha j)).trans (hi j (mem_univ j))
  · have hsa : ∀ j, 0 ≤ s j * a j := fun j => mul_nonneg (hs₀.trans (hs j)) (ha j)
    calc (∏ j, s j ^ n j) * ν
        ≤ (∏ j, s j ^ n j) * ∏ j, a j ^ n j :=
          mul_le_mul_of_nonneg_left hν (prod_nonneg fun j _ => pow_nonneg (hs₀.trans (hs j)) _)
      _ = ∏ j, (s j * a j) ^ n j := by
          rw [← prod_mul_distrib]; exact prod_congr rfl fun j _ => (mul_pow _ _ _).symm
      _ ≤ ∏ j, (s i * a i) ^ n j :=
          prod_le_prod (fun j _ => pow_nonneg (hsa j) _)
            (fun j _ => pow_le_pow_left₀ (hsa j) (hi j (mem_univ j)) _)
      _ = (s i * a i) ^ (∑ j, n j) := prod_pow_eq_pow_sum _ _ _

private theorem exists_direction_of_infinitePlace (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) :
    ∃ v : mixedEmbedding.mixedSpace K,
      (∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) ≠ 1) ∧
      normAtPlace w v = 1 ∧ ∀ w' : InfinitePlace K, w' ≠ w → normAtPlace w' v = 0 := by
  classical

  obtain ⟨e, he_mul, he_ne, hnorm_w, hnorm_ne⟩ : ∃ e : mixedEmbedding.mixedSpace K, e * e = e ∧ e ≠ 0 ∧
      normAtPlace w e = 1 ∧ ∀ w' : InfinitePlace K, w' ≠ w → normAtPlace w' e = 0 := by
    by_cases hw : w.IsReal
    · refine ⟨(Pi.single ⟨w, hw⟩ (1 : ℝ), 0), ?_, ?_, ?_, fun w' hw' => ?_⟩
      · ext i <;> simp [Pi.single_apply]
      · intro h
        have := congrArg (fun x : mixedEmbedding.mixedSpace K => x.1 ⟨w, hw⟩) h
        simp at this
      · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]; simp
      · by_cases hw'r : w'.IsReal
        · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw'r]
          have : (⟨w', hw'r⟩ : {v : InfinitePlace K // v.IsReal}) ≠ ⟨w, hw⟩ := fun h => hw' (congrArg Subtype.val h)
          simp [Pi.single_apply, this]
        · rw [mixedEmbedding.normAtPlace_apply_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw'r)]; simp
    · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
      refine ⟨(0, Pi.single ⟨w, hwc⟩ (1 : ℂ)), ?_, ?_, ?_, fun w' hw' => ?_⟩
      · ext i <;> simp [Pi.single_apply]
      · intro h
        have := congrArg (fun x : mixedEmbedding.mixedSpace K => x.2 ⟨w, hwc⟩) h
        simp at this
      · rw [mixedEmbedding.normAtPlace_apply_of_isComplex hwc]; simp
      · by_cases hw'r : w'.IsReal
        · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw'r]; simp
        · have hw'c := InfinitePlace.not_isReal_iff_isComplex.1 hw'r
          rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw'c]
          have : (⟨w', hw'c⟩ : {v : InfinitePlace K // v.IsComplex}) ≠ ⟨w, hwc⟩ :=
            fun h => hw' (congrArg Subtype.val h)
          simp [Pi.single_apply, this]

  have htrace : Algebra.trace ℝ (mixedEmbedding.mixedSpace K) e ≠ 0 := by
    rw [Algebra.trace_apply]
    set L := Algebra.lmul ℝ (mixedEmbedding.mixedSpace K) e with hL
    have hidem : IsIdempotentElem L := by
      show L * L = L
      refine LinearMap.ext fun y => ?_
      rw [Module.End.mul_apply]
      show e * (e * y) = e * y
      rw [← mul_assoc, he_mul]
    have hproj := (LinearMap.isProj_range_iff_isIdempotentElem L).2 hidem
    rw [hproj.trace]
    have hrange : LinearMap.range L ≠ ⊥ := by
      intro hbot
      have hmem : e ∈ LinearMap.range L := ⟨1, mul_one e⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact he_ne hmem
    exact_mod_cast mt Submodule.finrank_eq_zero.1 hrange
  refine ⟨e, ⟨1 / (2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace K) e), ?_⟩, hnorm_w, hnorm_ne⟩
  set τ : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace K) e with hτ
  have hval : 1 / (2 * τ) * τ = (1 / 2 : ℝ) := by
    field_simp
  have harg : (2 * Real.pi * (1 / 2 : ℝ)) = Real.pi := by ring
  rw [NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace, RingEquiv.apply_symm_apply,
    map_smul, smul_eq_mul, ← hτ, hval, Real.fourierChar_apply, harg, Complex.exp_pi_mul_I]
  norm_num

private theorem inv_mul_unipotentGL2_mul_globalPoints_diagOne (K : Type) [Field K] [NumberField K] (α : K)
    (hα : α ≠ 0) (x : AdeleRing (𝓞 K) K) :
    (globalPoints (𝓞 K) K (diagOne (Units.mk0 α hα)))⁻¹ * unipotentGL2 x
        * globalPoints (𝓞 K) K (diagOne (Units.mk0 α hα))
      = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) α⁻¹ * x) := by
  have hαα : algebraMap K (AdeleRing (𝓞 K) K) α⁻¹ * algebraMap K (AdeleRing (𝓞 K) K) α = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hα, map_one]
  rw [← map_inv, ← map_inv]
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, globalPoints_apply, diagOne_coe_apply,
    unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Units.val_inv_eq_inv_val, hαα, mul_assoc]

private theorem inv_globalPoints_diagOne_mul_unipotentGL2_mul (K : Type) [Field K] [NumberField K] (α : K)
    (hα : α ≠ 0) (x : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K) :
    (globalPoints (𝓞 K) K (diagOne (Units.mk0 α hα)))⁻¹ * (unipotentGL2 x * h)
      = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) α⁻¹ * x)
          * ((globalPoints (𝓞 K) K (diagOne (Units.mk0 α hα)))⁻¹ * h) := by
  rw [← inv_mul_unipotentGL2_mul_globalPoints_diagOne K α hα x]
  simp only [mul_assoc, mul_inv_cancel_left]

private theorem unipotentGL2_algebraMap_mul_of_components (K : Type) [Field K] [NumberField K] (a : K)
    (v : mixedEmbedding.mixedSpace K) (t : ℝ) (x : AdeleRing (𝓞 K) K)
    (hx₁ : Prod.fst x = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v)) (hx₂ : Prod.snd x = 0) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) a * x)
      = unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • (mixedEmbedding K a * v)), 0) := by
  congr 1
  refine Prod.ext ?_ ?_
  · show algebraMap K (InfiniteAdeleRing K) a * Prod.fst x
        = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • (mixedEmbedding K a * v))
    rw [hx₁, ← mul_smul_comm, map_mul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      RingEquiv.symm_apply_apply]
  · show algebraMap K (FiniteAdeleRing (𝓞 K) K) a * Prod.snd x = 0
    rw [hx₂, mul_zero]

private theorem unipotentGL2_arch_rat_eq (K : Type) [Field K] [NumberField K] (y : InfiniteAdeleRing K) (β : K) :
    unipotentGL2 (R := AdeleRing (𝓞 K) K) (y, algebraMap K (FiniteAdeleRing (𝓞 K) K) β)
      = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)
          * unipotentGL2 (R := AdeleRing (𝓞 K) K) (y - algebraMap K (InfiniteAdeleRing K) β, 0) := by
  rw [← unipotentGL2_add]
  congr 1
  refine Prod.ext ?_ ?_
  · show y = algebraMap K (InfiniteAdeleRing K) β + (y - algebraMap K (InfiniteAdeleRing K) β)
    exact (add_sub_cancel _ _).symm
  · show algebraMap K (FiniteAdeleRing (𝓞 K) K) β = algebraMap K (FiniteAdeleRing (𝓞 K) K) β + 0
    exact (add_zero _).symm

private theorem forall_norm_le_of_forall_arch (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (hrat : ∀ (β : K) (h : AdelicGL2 (𝓞 K) K), φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = φ h)
    (g : AdelicGL2 (𝓞 K) K) (B : ℝ)
    (harch : ∀ y : InfiniteAdeleRing K, ‖φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) (y, 0) * g)‖ ≤ B)
    (u : AdeleRing (𝓞 K) K) : ‖φ (unipotentGL2 u * g)‖ ≤ B := by
  have hcont : Continuous fun b : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K =>
      ‖φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) b * g)‖ :=
    (hφ.comp ((CuspidalSpectrum.continuous_unipotentGL2_adele K).mul continuous_const)).norm
  have hclosed : IsClosed {b : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K |
      ‖φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) b * g)‖ ≤ B} :=
    isClosed_le hcont continuous_const
  have hdense : DenseRange (Prod.map (id : InfiniteAdeleRing K → InfiniteAdeleRing K)
      (algebraMap K (FiniteAdeleRing (𝓞 K) K))) :=
    denseRange_id.prodMap (NumberField.denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext K).1
  refine hdense.induction_on u hclosed ?_
  rintro ⟨y, β⟩
  show ‖φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) (y, algebraMap K (FiniteAdeleRing (𝓞 K) K) β) * g)‖ ≤ B
  rw [unipotentGL2_arch_rat_eq, mul_assoc, hrat]
  exact harch _

private theorem sum_normAtPlace_mixedEmbedding_mul_div (K : Type) [Field K] [NumberField K] (a : K)
    (w : InfinitePlace K) (v : mixedEmbedding.mixedSpace K) (hw : normAtPlace w v = 1)
    (hv : ∀ w' : InfinitePlace K, w' ≠ w → normAtPlace w' v = 0) (s : InfinitePlace K → ℝ) :
    ∑ w' : InfinitePlace K, normAtPlace w' (mixedEmbedding K a * v) / s w' = w a / s w := by
  rw [Finset.sum_eq_single w (fun w' _ hw' => by simp [map_mul, hv w' hw']) (fun h => (h (Finset.mem_univ w)).elim)]
  simp [map_mul, normAtPlace_apply, hw]

private theorem exists_forall_norm_whittakerCoefficient_le_of_chain
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) (s₀ : ℝ) (hs₀ : 0 < s₀) (M : ℕ) (w : InfinitePlace K) :
    ∃ cw : ℝ, 0 < cw ∧
      ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f →
        (∀ (γ : GL (Fin 2) K) (h : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * h) = f h) →
        (∀ (h : AdelicGL2 (𝓞 K) K), ∀ u' ∈ finiteAdelicGL2Subgroup K,
          (∀ i j, ((glFin (𝓞 K) K u' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
            idealBall (𝓞 K) K N) →
          (∀ i j, ((((glFin (𝓞 K) K u')⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          f (h * u') = f h) →
        ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
          ∀ (s : InfinitePlace K → ℝ), (∀ w, s₀ ≤ s w) →
          ∀ Λ : ℝ,
            (∀ v : mixedEmbedding.mixedSpace K, ∃ xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ,
              xs 0 = f ∧
              (∀ j, Continuous (xs j)) ∧
              (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
                xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) ∧
              (∀ j (h : AdelicGL2 (𝓞 K) K),
                HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * h)) (xs (j + 1) h) 0) ∧
              (∀ (y : InfiniteAdeleRing K) (t : FiniteAdeleRing (𝓞 K) K),
                (∀ i j, ((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) :
                      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
                (∀ i j, ((((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g))⁻¹ :
                      GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
                      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
                ‖xs M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g)‖ ≤
                  Λ * (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / s w) ^ M)) →
            ∀ α : K, α ≠ 0 →
              ‖whittakerCoefficient K
                  (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                  (NumberField.StandardAddChar.stdAddChar K) f α g‖ ≤ cw * Λ * (w α * s w) ^ (-(M : ℝ)) := by
  obtain ⟨v, hv, hw1, hw0⟩ := exists_direction_of_infinitePlace K w
  obtain ⟨cw, hcw, hibp⟩ :=
    AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) M v hv
  refine ⟨cw, hcw, ?_⟩
  intro f hf hleft hlevel g hg s hs Λ hchain α hα
  obtain ⟨xs, hxs0, hxsc, hxsinv, hxsd, hxsb⟩ := hchain (mixedEmbedding K α⁻¹ * v)
  set Dα : AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K (diagOne (Units.mk0 α hα)) with hDα
  have hsw : 0 < s w := hs₀.trans_le (hs w)

  set B : ℝ := Λ * (w α⁻¹ / s w) ^ M with hB
  have hbound : ∀ u' : AdeleRing (𝓞 K) K, ‖xs M (unipotentGL2 u' * g)‖ ≤ B := by
    intro u'
    refine forall_norm_le_of_forall_arch K (xs M) (hxsc M) (fun β h => hxsinv M β h) g B (fun y => ?_) u'
    have hid : ∀ i j, ((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K) 0 * g) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N := by
      intro i j
      rw [unipotentGL2_zero, mul_one, inv_mul_cancel, map_one, Units.val_one, sub_self, Matrix.zero_apply]
      exact zero_mem_idealBall N
    have hid' : ∀ i j, ((((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K) 0 * g))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
        idealBall (𝓞 K) K N := by
      intro i j
      rw [unipotentGL2_zero, mul_one, inv_mul_cancel, map_one, inv_one, Units.val_one, sub_self, Matrix.zero_apply]
      exact zero_mem_idealBall N
    have hper := hxsb y 0 hid hid'
    rwa [sum_normAtPlace_mixedEmbedding_mul_div K α⁻¹ w v hw1 hw0 s] at hper

  have hkey := hibp (fun j h => xs j (Dα⁻¹ * h)) (Dα * g) B
    (fun j => (hxsc j).comp (continuous_const.mul continuous_id))
    (fun j β h => by
      beta_reduce
      rw [hDα, inv_globalPoints_diagOne_mul_unipotentGL2_mul K α hα, ← map_mul, hxsinv])
    (fun j u' => by
      beta_reduce
      refine (hxsd j (Dα⁻¹ * (unipotentGL2 u' * (Dα * g)))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [hDα, inv_globalPoints_diagOne_mul_unipotentGL2_mul K α hα,
        unipotentGL2_algebraMap_mul_of_components K α⁻¹ v t _ rfl rfl])
    (fun u' => by
      beta_reduce
      rw [hDα, inv_globalPoints_diagOne_mul_unipotentGL2_mul K α hα, inv_mul_cancel_left]
      exact hbound _)
  have hys0 : (fun h => f (Dα⁻¹ * h)) = f := by
    funext h
    rw [hDα, ← map_inv, hleft]
  simp only [hxs0] at hkey
  rw [hys0] at hkey
  rw [AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul K _ _ _ _
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) f hleft α hα g]
  refine hkey.trans (le_of_eq ?_)
  rw [hB, map_inv₀, Real.rpow_neg (mul_nonneg (apply_nonneg w α) hsw.le), Real.rpow_natCast, ← inv_pow, mul_inv,
    div_eq_mul_inv]
  ring

end

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) (s₀ : ℝ) (hs₀ : 0 < s₀) (M'' : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧
      ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f →
        (∀ (γ : GL (Fin 2) K) (h : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * h) = f h) →
        (∀ (h : AdelicGL2 (𝓞 K) K), ∀ u' ∈ finiteAdelicGL2Subgroup K,
          (∀ i j, ((glFin (𝓞 K) K u' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
            idealBall (𝓞 K) K N) →
          (∀ i j, ((((glFin (𝓞 K) K u')⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          f (h * u') = f h) →
        ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
          @constantTerm _
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
            (fun x => unipotentGL2 x) f g = 0 →
          ∀ (s : InfinitePlace K → ℝ), (∀ w, s₀ ≤ s w) →
          ∀ Λ : ℝ,
            (∀ v : mixedEmbedding.mixedSpace K, ∃ xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ,
              xs 0 = f ∧
              (∀ j, Continuous (xs j)) ∧
              (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
                xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) ∧
              (∀ j (h : AdelicGL2 (𝓞 K) K),
                HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * h)) (xs (j + 1) h) 0) ∧
              (∀ (y : InfiniteAdeleRing K) (t : FiniteAdeleRing (𝓞 K) K),
                (∀ i j, ((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) :
                      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
                (∀ i j, ((((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g))⁻¹ :
                      GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
                      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
                ‖xs M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g)‖ ≤
                  Λ * (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / s w) ^ M)) →
            ‖f g‖ ≤ C * Λ * (∏ w : InfinitePlace K, s w ^ w.mult) ^ (-(M'' : ℝ) / Module.finrank ℚ K) := by
  classical
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hsupp :=
    AutomorphicForm.exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
      K c u d₁ d₂ T N hN
  obtain ⟨I, hI⟩ := hsupp
  have hfloor := exists_pos_le_prod_infinitePlace_pow_mult I
  obtain ⟨ν, hν, hνle⟩ := hfloor
  have hsummable := exists_forall_summable_sup_infinitePlace_rpow_neg I
  obtain ⟨N₀, hN₀⟩ := hsummable
  have hsumm := hN₀ N₀ le_rfl
  set S : Set K := {ξ | ξ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)} with hS
  set b : K → ℝ := fun ξ => (Finset.univ.sup' Finset.univ_nonempty fun w : InfinitePlace K => w ξ) ^ (-(N₀ : ℝ))
    with hb
  have hbS : Summable (S.indicator b) := summable_subtype_iff_indicator.1 hsumm
  have hsup_nn : ∀ ξ : K, 0 ≤ Finset.univ.sup' Finset.univ_nonempty fun w : InfinitePlace K => w ξ := fun ξ =>
    Finset.le_sup'_of_le (fun w : InfinitePlace K => w ξ) (Finset.mem_univ w₀) (apply_nonneg w₀ ξ)
  have hb_nn : ∀ ξ : K, 0 ≤ b ξ := fun ξ => by
    rw [hb]
    exact Real.rpow_nonneg (hsup_nn ξ) _
  have hbS_nn : ∀ ξ, 0 ≤ S.indicator b ξ := fun ξ => Set.indicator_nonneg (fun ξ _ => hb_nn ξ) ξ
  choose cw hcwpos hcw using fun w : InfinitePlace K =>
    exists_forall_norm_whittakerCoefficient_le_of_chain K c u d₁ d₂ T N hN s₀ hs₀ (M'' + N₀) w
  set cmax : ℝ := ∑ w : InfinitePlace K, cw w with hcmax
  have hcw_le : ∀ w, cw w ≤ cmax := fun w =>
    Finset.single_le_sum (fun w _ => (hcwpos w).le) (Finset.mem_univ w)
  have hcmax_nn : 0 ≤ cmax := (hcwpos w₀).le.trans (hcw_le w₀)
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  set A : ℝ := cmax * ν ^ (-(M'' : ℝ) / Module.finrank ℚ K) * s₀ ^ (-(N₀ : ℝ)) with hA
  have hA_nn : 0 ≤ A := by positivity
  have htsum_nn : 0 ≤ ∑' ξ : K, S.indicator b ξ := tsum_nonneg hbS_nn
  refine ⟨M'' + N₀, A * ∑' ξ : K, S.indicator b ξ + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg hA_nn htsum_nn) one_pos, ?_⟩
  intro f hf hleft hlevel g hg hct s hs Λ hchain
  set P := productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K) with hP
  set W : K → ℂ := fun α => whittakerCoefficient K P (NumberField.StandardAddChar.stdAddChar K) f α g with hW
  have hs_pos : ∀ w, 0 < s w := fun w => hs₀.trans_le (hs w)
  have hprod_pos : 0 < ∏ w : InfinitePlace K, s w ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (hs_pos w) _
  set Pw : ℝ := (∏ w : InfinitePlace K, s w ^ w.mult) ^ (-(M'' : ℝ) / Module.finrank ℚ K) with hPw
  have hPw_pos : 0 < Pw := Real.rpow_pos_of_pos hprod_pos _

  have hΛ : 0 ≤ Λ := by
    have h1 := hcw w₀ f hf hleft hlevel g hg s hs Λ hchain 1 one_ne_zero
    have hx : 0 < (w₀ (1 : K) * s w₀) ^ (-((M'' + N₀ : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by rw [map_one, one_mul]; exact hs_pos w₀) _
    by_contra hneg
    push Not at hneg
    have : cw w₀ * Λ * (w₀ (1 : K) * s w₀) ^ (-((M'' + N₀ : ℕ) : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hcwpos w₀) hneg) hx
    exact absurd (h1.trans_lt this) (not_lt.2 (norm_nonneg _))

  have hterm : ∀ α : K, ‖W α‖ ≤ (A * Λ * Pw) * S.indicator b α := by
    intro α
    by_cases hαS : α ∈ S
    · by_cases hα0 : α = 0
      · subst hα0
        have h0 : W 0 = 0 := by
          simp only [hW, whittakerCoefficient_zero_eq_constantTerm]
          exact hct
        rw [h0, norm_zero]
        exact mul_nonneg (by positivity) (hbS_nn 0)
      · rw [Set.indicator_of_mem hαS]

        obtain ⟨i, hi_all, hi_pow⟩ := exists_argmax_weighted_core (fun w : InfinitePlace K => w.mult) s
          (fun w => w α) s₀ ν hs hs₀.le (fun w => apply_nonneg w α) (hνle α hαS hα0)
        have hX_pos : 0 < s i * i α := mul_pos (hs_pos i) (InfinitePlace.pos_iff.2 hα0)
        have hsup_nn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty fun w : InfinitePlace K => w α :=
          Finset.le_sup'_of_le _ (Finset.mem_univ i) (apply_nonneg i α)
        have hsup_le : s₀ * Finset.univ.sup' Finset.univ_nonempty (fun w : InfinitePlace K => w α) ≤ s i * i α := by
          rw [mul_comm s₀, ← le_div_iff₀ hs₀, Finset.sup'_le_iff]
          intro w _
          rw [le_div_iff₀ hs₀, mul_comm]
          exact hi_all w
        have h1 := hcw i f hf hleft hlevel g hg s hs Λ hchain α hα0

        have hsplit : (i α * s i) ^ (-((M'' + N₀ : ℕ) : ℝ)) =
            (s i * i α) ^ (-(M'' : ℝ)) * (s i * i α) ^ (-(N₀ : ℝ)) := by
          rw [mul_comm (i α), ← Real.rpow_add hX_pos]
          push_cast
          ring_nf

        have hfirst : (s i * i α) ^ (-(M'' : ℝ)) ≤ Pw * ν ^ (-(M'' : ℝ) / Module.finrank ℚ K) := by
          have hsum : (∑ w : InfinitePlace K, w.mult) = Module.finrank ℚ K := InfinitePlace.sum_mult_eq
          rw [hsum] at hi_pow
          have hXn : (s i * i α) ^ (-(M'' : ℝ)) =
              ((s i * i α) ^ (Module.finrank ℚ K : ℕ)) ^ (-(M'' : ℝ) / Module.finrank ℚ K) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le, mul_div_cancel₀ _ hn.ne']
          rw [hXn, hPw, ← Real.mul_rpow hprod_pos.le hν.le]
          exact Real.rpow_le_rpow_of_nonpos (mul_pos hprod_pos hν) hi_pow
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (Nat.cast_nonneg _)) hn.le)

        have hsecond : (s i * i α) ^ (-(N₀ : ℝ)) ≤ s₀ ^ (-(N₀ : ℝ)) * b α := by
          have hpos : 0 < s₀ * Finset.univ.sup' Finset.univ_nonempty fun w : InfinitePlace K => w α :=
            mul_pos hs₀ (lt_of_lt_of_le (InfinitePlace.pos_iff.2 hα0) (Finset.le_sup' (fun w : InfinitePlace K => w α)
              (Finset.mem_univ i)))
          rw [hb, ← Real.mul_rpow hs₀.le hsup_nn]
          exact Real.rpow_le_rpow_of_nonpos hpos hsup_le (neg_nonpos.2 (Nat.cast_nonneg _))
        calc ‖W α‖ ≤ cw i * Λ * (i α * s i) ^ (-((M'' + N₀ : ℕ) : ℝ)) := h1
          _ = cw i * Λ * ((s i * i α) ^ (-(M'' : ℝ)) * (s i * i α) ^ (-(N₀ : ℝ))) := by rw [hsplit]
          _ ≤ cmax * Λ * ((Pw * ν ^ (-(M'' : ℝ) / Module.finrank ℚ K)) * (s₀ ^ (-(N₀ : ℝ)) * b α)) := by
            gcongr
            · exact hcw_le i
          _ = (A * Λ * Pw) * b α := by
            rw [hA]
            ring
    · rw [Set.indicator_of_notMem hαS, mul_zero]
      have h0 : W α = 0 := hI f hlevel g hg α hαS
      rw [h0, norm_zero]

  have hWsum : Summable W := Summable.of_norm_bounded (hbS.mul_left (A * Λ * Pw)) hterm
  have hexp : HasSum W (f g) :=
    AutomorphicForm.hasSum_whittakerCoefficient K _ _ _ (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) f g
      (hf.comp ((AutomorphicForm.CuspidalSpectrum.continuous_unipotentGL2_adele K).mul continuous_const)) hWsum
  have hbound : ‖f g‖ ≤ (A * Λ * Pw) * ∑' ξ : K, S.indicator b ξ := by
    rw [← hexp.tsum_eq]
    have hB : HasSum (fun ξ => (A * Λ * Pw) * S.indicator b ξ) ((A * Λ * Pw) * ∑' ξ : K, S.indicator b ξ) :=
      hbS.hasSum.mul_left _
    exact tsum_of_norm_bounded hB hterm
  refine hbound.trans ?_
  calc (A * Λ * Pw) * ∑' ξ : K, S.indicator b ξ = (A * ∑' ξ : K, S.indicator b ξ) * Λ * Pw := by ring
    _ ≤ (A * ∑' ξ : K, S.indicator b ξ + 1) * Λ * Pw := by
      gcongr
      exact le_add_of_nonneg_right zero_le_one

end S_AutomorphicForm_exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall (solution)
