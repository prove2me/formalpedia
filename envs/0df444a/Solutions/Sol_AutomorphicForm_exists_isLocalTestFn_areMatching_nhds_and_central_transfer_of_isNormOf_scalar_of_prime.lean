-- Prove2me | solution 1 for AutomorphicForm.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c09c8322-38ae-5011-9d25-1b6d0f3e0fcc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem scalar_mul_comm (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = x * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (c : v.adicCompletion K) (fun r => Commute.all _ r)
    (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).eq

private theorem inv_mul_scalar_mul (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem isOrbitalIntegral_scalar_exists_eq_mul (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
      (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ)
    (h : IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv I) :
    ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
      IsSectionFn K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv w ∧
        I = fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * ∫ x, (w x : ℂ) ∂(localHaar K v) := by
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨w, hw, ?_⟩
  simp only [inv_mul_scalar_mul]
  exact integral_const_mul _ _

namespace ScalarTransfer

private theorem isOrbitalIntegral_scalar_eq_zero_of_apply_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) : I = 0 := by
  obtain ⟨w, -, hw⟩ := isOrbitalIntegral_scalar_exists_eq_mul c τ f I hI
  rw [hw, hf, zero_mul]

end ScalarTransfer

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem mem_localCentralizer_scalar (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    x ∈ localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [localCentralizer, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact scalar_mul_comm c x

private noncomputable def scalarCentralizerEquiv (c : (v.adicCompletion K)ˣ) :
    localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ* GL (Fin 2) (v.adicCompletion K) where
  toFun t := (t : GL (Fin 2) (v.adicCompletion K))
  invFun x := ⟨x, mem_localCentralizer_scalar c x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

private theorem exists_integral_sectionFn_scalar_eq (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
      (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ) :
    ∃ r : ℝ, ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≠ 0 →
      ∀ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
        IsSectionFn K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f w → ∫ x, w x ∂(localHaar K v) = r := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  haveI := isHaarMeasure_localHaar K v
  letI := localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  haveI : BorelSpace (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := ⟨rfl⟩
  haveI := hτ
  set ν : Measure (GL (Fin 2) (v.adicCompletion K)) :=
    τ.map (Subtype.val : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) → _) with hν_def
  haveI : ν.IsHaarMeasure := by
    have h := ContinuousMulEquiv.isHaarMeasure_map τ (scalarCentralizerEquiv (K := K) (v := v) c)
    exact h
  set r : NNReal := (localHaar K v).haarScalarFactor ν with hr
  refine ⟨(r : ℝ), fun f hf w hw => ?_⟩
  obtain ⟨-, hwm, hwc, hsec⟩ := hw

  have hK : IsCompact (tsupport w) := hwc
  have hres : (localHaar K v).restrict (tsupport w) = (r • ν).restrict (tsupport w) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Measure.smul_apply]
    have hcl : IsCompact (closure (s ∩ tsupport w)) :=
      hK.of_isClosed_subset isClosed_closure
        (closure_minimal Set.inter_subset_right (isClosed_tsupport w))
    exact Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (localHaar K v) ν hcl
  have hout : ∀ x, x ∉ tsupport w → w x = 0 := fun x hx => by
    by_contra h
    exact hx (subset_tsupport w (Function.mem_support.mpr h))

  have h1 : ∫ x, w x ∂(localHaar K v) = ∫ x, w x ∂(r • ν) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, hres,
      setIntegral_eq_integral_of_forall_compl_eq_zero hout]

  have h2 : ∫ x, w x ∂ν = 1 := by
    have hsec1 := hsec 1 (by simpa using hf)
    rw [hν_def, integral_map continuous_subtype_val.measurable.aemeasurable hwm.aestronglyMeasurable]
    simpa using hsec1
  rw [h1, integral_smul_nnreal_measure, h2, NNReal.smul_def, smul_eq_mul, mul_one]

namespace ScalarTransfer

private theorem isOrbitalIntegral_scalar_eq_of_apply_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (f g : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfg : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = g (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
    (I J : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I)
    (hJ : AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ g J) : I = J := by
  letI := localGLBorel K v
  obtain ⟨w, hw, hIw⟩ := isOrbitalIntegral_scalar_exists_eq_mul c τ f I hI
  obtain ⟨w', hw', hJw⟩ := isOrbitalIntegral_scalar_exists_eq_mul c τ g J hJ
  by_cases hf0 : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0
  · rw [hIw, hJw, ← hfg, hf0, zero_mul, zero_mul]
  · have hg0 : g (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≠ 0 := hfg ▸ hf0
    obtain ⟨r, hr⟩ := exists_integral_sectionFn_scalar_eq c τ hτ
    rw [hIw, hJw, hfg, integral_complex_ofReal, integral_complex_ofReal, hr f hf0 w hw, hr g hg0 w' hw']

end ScalarTransfer

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem mul_mem_localIntegralSet {g h : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hh.2 i k) (hg.2 k j)

private theorem inv_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) : g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  refine ⟨hg.2, fun i j => ?_⟩
  rw [inv_inv]
  exact hg.1 i j

private theorem preimage_mul_right_localIntegralSet {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ localIntegralSet K v) : (· * k) ⁻¹' localIntegralSet K v = localIntegralSet K v := by
  ext g
  simp only [Set.mem_preimage]
  constructor
  · intro hgk
    have := mul_mem_localIntegralSet hgk (inv_mem_localIntegralSet hk)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this
  · intro hg
    exact mul_mem_localIntegralSet hg hk

private theorem isCompact_preimage_mul_right_localIntegralSet (x : GL (Fin 2) (v.adicCompletion K)) :
    IsCompact ((· * x) ⁻¹' localIntegralSet K v) := by
  have h : (· * x) ⁻¹' localIntegralSet K v = (· * x⁻¹) '' localIntegralSet K v := by
    rw [Set.image_mul_right, inv_inv]
  rw [h]
  exact (isCompact_localIntegralSet K v).image (continuous_mul_const _)

private noncomputable def modFun (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) (x : GL (Fin 2) (v.adicCompletion K)) : NNReal := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := hν
  exact (ν.map (· * x)).haarScalarFactor ν

private theorem measure_preimage_mul_right_eq (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) (x : GL (Fin 2) (v.adicCompletion K))
    {s : Set (GL (Fin 2) (v.adicCompletion K))} (hs : @MeasurableSet _ (localGLBorel K v) s)
    (hsc : IsCompact (closure s)) :
    ν ((· * x) ⁻¹' s) = modFun ν hν x • ν s := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  haveI := hν
  have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (ν.map (· * x)) ν hsc
  rw [Measure.map_apply (continuous_mul_const x).measurable hs] at h
  exact h

private theorem measure_localIntegralSet_ne_zero
    (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) : ν (localIntegralSet K v) ≠ 0 := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := hν
  exact ((isOpen_localIntegralSet K v).measure_pos ν ⟨1, one_mem_localIntegralSet K v⟩).ne'

private theorem measure_localIntegralSet_ne_top
    (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) : ν (localIntegralSet K v) ≠ ⊤ := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := hν
  exact (isCompact_localIntegralSet K v).measure_lt_top.ne

private theorem measure_preimage_mul_right_localIntegralSet_eq
    (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) (x : GL (Fin 2) (v.adicCompletion K)) :
    ν ((· * x) ⁻¹' localIntegralSet K v) = (modFun ν hν x : ENNReal) * ν (localIntegralSet K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  rw [measure_preimage_mul_right_eq ν hν x (isOpen_localIntegralSet K v).measurableSet
    ((isCompact_localIntegralSet K v).closure_of_subset subset_rfl), ENNReal.smul_def, smul_eq_mul]

private theorem modFun_mul (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) (x y : GL (Fin 2) (v.adicCompletion K)) :
    modFun ν hν (x * y) = modFun ν hν x * modFun ν hν y := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  have hset : (· * (x * y)) ⁻¹' localIntegralSet K v = (· * x) ⁻¹' ((· * y) ⁻¹' localIntegralSet K v) := by
    ext g
    simp only [Set.mem_preimage, mul_assoc]
  have hmeas : MeasurableSet ((· * y) ⁻¹' localIntegralSet K v) :=
    (isOpen_localIntegralSet K v).measurableSet.preimage (continuous_mul_const y).measurable
  have hcpt : IsCompact (closure ((· * y) ⁻¹' localIntegralSet K v)) :=
    (isCompact_preimage_mul_right_localIntegralSet y).closure_of_subset subset_rfl
  have h1 := measure_preimage_mul_right_localIntegralSet_eq ν hν (x * y)
  rw [hset, measure_preimage_mul_right_eq ν hν x hmeas hcpt,
    measure_preimage_mul_right_localIntegralSet_eq ν hν y, ENNReal.smul_def, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul] at h1
  exact (ENNReal.coe_inj.mp
    ((ENNReal.mul_left_inj (measure_localIntegralSet_ne_zero ν hν) (measure_localIntegralSet_ne_top ν hν)).mp h1)).symm

private theorem modFun_eq_one_of_mem (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ localIntegralSet K v) : modFun ν hν k = 1 := by
  letI := localGLBorel K v
  have h := measure_preimage_mul_right_localIntegralSet_eq ν hν k
  rw [preimage_mul_right_localIntegralSet hk] at h
  have h' : ((1 : NNReal) : ENNReal) * ν (localIntegralSet K v) =
      (modFun ν hν k : ENNReal) * ν (localIntegralSet K v) := by
    rw [ENNReal.coe_one, one_mul]
    exact h
  exact (ENNReal.coe_inj.mp
    ((ENNReal.mul_left_inj (measure_localIntegralSet_ne_zero ν hν) (measure_localIntegralSet_ne_top ν hν)).mp h')).symm

private theorem modFun_eq_one_of_comm (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) {z : GL (Fin 2) (v.adicCompletion K)}
    (hz : ∀ g : GL (Fin 2) (v.adicCompletion K), g * z = z * g) : modFun ν hν z = 1 := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := hν
  have h := measure_preimage_mul_right_localIntegralSet_eq ν hν z
  have hset : (· * z) ⁻¹' localIntegralSet K v = (fun g => z * g) ⁻¹' localIntegralSet K v := by
    ext g
    simp only [Set.mem_preimage, hz]
  rw [hset, measure_preimage_mul ν z (localIntegralSet K v)] at h
  have h' : ((1 : NNReal) : ENNReal) * ν (localIntegralSet K v) =
      (modFun ν hν z : ENNReal) * ν (localIntegralSet K v) := by
    rw [ENNReal.coe_one, one_mul]
    exact h
  exact (ENNReal.coe_inj.mp
    ((ENNReal.mul_left_inj (measure_localIntegralSet_ne_zero ν hν) (measure_localIntegralSet_ne_top ν hν)).mp h')).symm

private theorem modFun_conj (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν) (d t : GL (Fin 2) (v.adicCompletion K)) :
    modFun ν hν (d * t * d⁻¹) = modFun ν hν t := by
  have h1 : modFun ν hν 1 = 1 := modFun_eq_one_of_mem ν hν (one_mem_localIntegralSet K v)
  rw [modFun_mul ν hν, modFun_mul ν hν, mul_comm (modFun ν hν d), mul_assoc, ← modFun_mul ν hν, mul_inv_cancel, h1,
    mul_one]

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem nnreal_eq_one_of_mul_self_eq_one {a : NNReal} (h : a * a = 1) : a = 1 := by
  have h' : (a : ℝ) * a = 1 := by exact_mod_cast h
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact NNReal.coe_injective (by simpa using h1)
  · exact absurd h1 (by linarith [a.coe_nonneg])

private noncomputable def diagGL (a b : v.adicCompletion K) (ha : a ≠ 0) (hb : b ≠ 0) :
    GL (Fin 2) (v.adicCompletion K) where
  val := Matrix.diagonal ![a, b]
  inv := Matrix.diagonal ![a⁻¹, b⁻¹]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha, hb]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha, hb]

private noncomputable def centralGL (c : v.adicCompletion K) (hc : c ≠ 0) : GL (Fin 2) (v.adicCompletion K) where
  val := Matrix.scalar (Fin 2) c
  inv := Matrix.scalar (Fin 2) c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

private noncomputable def upperGL (c : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) where
  val := !![1, c; 0, 1]
  inv := !![1, -c; 0, 1]
  val_inv := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
  inv_val := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp

private noncomputable def lowerGL (c : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) where
  val := !![1, 0; c, 1]
  inv := !![1, 0; -c, 1]
  val_inv := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
  inv_val := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp

private noncomputable def weylGL : GL (Fin 2) (v.adicCompletion K) where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
  inv_val := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp

private theorem diagGL_val (a b : v.adicCompletion K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((diagGL a b ha hb : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem diagGL_inv_val (a b : v.adicCompletion K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (((diagGL a b ha hb)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![a⁻¹, 0; 0, b⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem centralGL_val (c : v.adicCompletion K) (hc : c ≠ 0) :
    ((centralGL c hc : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![c, 0; 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem weylGL_mem : (weylGL : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    first | exact zero_mem _ | exact one_mem _

private theorem centralGL_comm (c : v.adicCompletion K) (hc : c ≠ 0) (g : GL (Fin 2) (v.adicCompletion K)) :
    g * centralGL c hc = centralGL c hc * g := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute c (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).eq.symm

private theorem diagGL_mul_diagGL_eq_centralGL (x : v.adicCompletion K) (hx : x ≠ 0) :
    diagGL x 1 hx one_ne_zero * diagGL 1 x one_ne_zero hx = centralGL x hx := by
  apply Units.ext
  rw [Units.val_mul, diagGL_val, diagGL_val, centralGL_val, Matrix.mul_fin_two]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]

private theorem weylGL_conj_diagGL (x : v.adicCompletion K) (hx : x ≠ 0) :
    weylGL * diagGL x 1 hx one_ne_zero * weylGL⁻¹ = diagGL 1 x one_ne_zero hx := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagGL_val, diagGL_val]
  show !![0, 1; 1, 0] * !![x, 0; 0, 1] * !![0, 1; 1, 0] = !![1, 0; 0, x]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]

private theorem diagGL_conj_upperGL (a c : v.adicCompletion K) (ha : a ≠ 0) :
    diagGL a 1 ha one_ne_zero * upperGL c * (diagGL a 1 ha one_ne_zero)⁻¹ = upperGL (a * c) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagGL_val, diagGL_inv_val]
  show !![a, 0; 0, 1] * !![1, c; 0, 1] * !![a⁻¹, 0; 0, 1⁻¹] = !![1, a * c; 0, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, inv_one, mul_inv_cancel₀ ha]

private theorem diagGL_conj_lowerGL (a c : v.adicCompletion K) (ha : a ≠ 0) :
    diagGL 1 a one_ne_zero ha * lowerGL c * (diagGL 1 a one_ne_zero ha)⁻¹ = lowerGL (a * c) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagGL_val, diagGL_inv_val]
  show !![1, 0; 0, a] * !![1, 0; c, 1] * !![1⁻¹, 0; 0, a⁻¹] = !![1, 0; a * c, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, inv_one, mul_inv_cancel₀ ha]

private theorem upperGL_mul_upperGL (c : v.adicCompletion K) : upperGL c * upperGL c = upperGL (c + c) := by
  apply Units.ext
  rw [Units.val_mul]
  show !![1, c; 0, 1] * !![1, c; 0, 1] = !![1, c + c; 0, 1]
  rw [Matrix.mul_fin_two]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]

private theorem lowerGL_mul_lowerGL (c : v.adicCompletion K) : lowerGL c * lowerGL c = lowerGL (c + c) := by
  apply Units.ext
  rw [Units.val_mul]
  show !![1, 0; c, 1] * !![1, 0; c, 1] = !![1, 0; c + c, 1]
  rw [Matrix.mul_fin_two]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]

private theorem upperGL_zero : (upperGL 0 : GL (Fin 2) (v.adicCompletion K)) = 1 := by
  apply Units.ext
  show (!![1, (0 : v.adicCompletion K); 0, 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1
  rw [Matrix.one_fin_two]

private theorem lowerGL_zero : (lowerGL 0 : GL (Fin 2) (v.adicCompletion K)) = 1 := by
  apply Units.ext
  show (!![1, 0; (0 : v.adicCompletion K), 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1
  rw [Matrix.one_fin_two]

private theorem diagGL_eq_centralGL_mul_diagGL (a b : v.adicCompletion K) (ha : a ≠ 0) (hb : b ≠ 0) :
    diagGL a b ha hb = centralGL b hb * diagGL (a * b⁻¹) 1 (mul_ne_zero ha (inv_ne_zero hb)) one_ne_zero := by
  apply Units.ext
  rw [Units.val_mul, diagGL_val, diagGL_val, centralGL_val, Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add]
  rw [mul_comm a, mul_inv_cancel_left₀ hb]

section modular

variable (ν : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
  (hν : @Measure.IsHaarMeasure _ _ _ (localGLBorel K v) ν)

include hν

private theorem modFun_ne_zero (g : GL (Fin 2) (v.adicCompletion K)) : modFun ν hν g ≠ 0 := by
  intro h
  have h1 := modFun_mul ν hν g g⁻¹
  rw [mul_inv_cancel, modFun_eq_one_of_mem ν hν (one_mem_localIntegralSet K v), h, zero_mul] at h1
  exact one_ne_zero h1

private theorem modFun_centralGL (c : v.adicCompletion K) (hc : c ≠ 0) : modFun ν hν (centralGL c hc) = 1 :=
  modFun_eq_one_of_comm ν hν (centralGL_comm c hc)

private theorem modFun_diagGL_one (x : v.adicCompletion K) (hx : x ≠ 0) :
    modFun ν hν (diagGL x 1 hx one_ne_zero) = 1 := by
  apply nnreal_eq_one_of_mul_self_eq_one
  have h2 : modFun ν hν (diagGL 1 x one_ne_zero hx) = modFun ν hν (diagGL x 1 hx one_ne_zero) := by
    rw [← weylGL_conj_diagGL x hx, modFun_conj ν hν]
  have h3 := modFun_mul ν hν (diagGL x 1 hx one_ne_zero) (diagGL 1 x one_ne_zero hx)
  rw [diagGL_mul_diagGL_eq_centralGL, modFun_centralGL ν hν, h2] at h3
  exact h3.symm

private theorem modFun_diagGL (a b : v.adicCompletion K) (ha : a ≠ 0) (hb : b ≠ 0) :
    modFun ν hν (diagGL a b ha hb) = 1 := by
  rw [diagGL_eq_centralGL_mul_diagGL, modFun_mul ν hν, modFun_centralGL ν hν, modFun_diagGL_one ν hν, mul_one]

private theorem modFun_upperGL (c : v.adicCompletion K) : modFun ν hν (upperGL c) = 1 := by
  by_cases hc : c = 0
  · rw [hc, upperGL_zero]
    exact modFun_eq_one_of_mem ν hν (one_mem_localIntegralSet K v)
  have hsq : modFun ν hν (upperGL c) * modFun ν hν (upperGL c) = modFun ν hν (upperGL (c + c)) := by
    rw [← modFun_mul ν hν, upperGL_mul_upperGL]
  by_cases h2 : c + c = 0
  · rw [h2, upperGL_zero, modFun_eq_one_of_mem ν hν (one_mem_localIntegralSet K v)] at hsq
    exact nnreal_eq_one_of_mul_self_eq_one hsq
  · have hconj : modFun ν hν (upperGL (c + c)) = modFun ν hν (upperGL c) := by
      have ha : (c + c) / c ≠ 0 := div_ne_zero h2 hc
      have := diagGL_conj_upperGL ((c + c) / c) c ha
      rw [div_mul_cancel₀ _ hc] at this
      rw [← this, modFun_conj ν hν]
    rw [hconj] at hsq
    exact mul_left_cancel₀ (modFun_ne_zero ν hν _) (by rw [hsq, mul_one])

private theorem modFun_lowerGL (c : v.adicCompletion K) : modFun ν hν (lowerGL c) = 1 := by
  by_cases hc : c = 0
  · rw [hc, lowerGL_zero]
    exact modFun_eq_one_of_mem ν hν (one_mem_localIntegralSet K v)
  have hsq : modFun ν hν (lowerGL c) * modFun ν hν (lowerGL c) = modFun ν hν (lowerGL (c + c)) := by
    rw [← modFun_mul ν hν, lowerGL_mul_lowerGL]
  by_cases h2 : c + c = 0
  · rw [h2, lowerGL_zero, modFun_eq_one_of_mem ν hν (one_mem_localIntegralSet K v)] at hsq
    exact nnreal_eq_one_of_mul_self_eq_one hsq
  · have hconj : modFun ν hν (lowerGL (c + c)) = modFun ν hν (lowerGL c) := by
      have ha : (c + c) / c ≠ 0 := div_ne_zero h2 hc
      have := diagGL_conj_lowerGL ((c + c) / c) c ha
      rw [div_mul_cancel₀ _ hc] at this
      rw [← this, modFun_conj ν hν]
    rw [hconj] at hsq
    exact mul_left_cancel₀ (modFun_ne_zero ν hν _) (by rw [hsq, mul_one])

private theorem modFun_eq_one (g : GL (Fin 2) (v.adicCompletion K)) : modFun ν hν g = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have key : ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), M.det ≠ 0 →
      ∀ h : M.det ≠ 0, modFun ν hν (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) = 1 := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun N => ∀ h : N.det ≠ 0, modFun ν hν (Matrix.GeneralLinearGroup.mkOfDetNeZero N h) = 1) M hM ?_ ?_ ?_
    · intro D hD h
      rw [Matrix.det_diagonal, Fin.prod_univ_two] at hD
      have h0 : D 0 ≠ 0 := left_ne_zero_of_mul hD
      have h1 : D 1 ≠ 0 := right_ne_zero_of_mul hD
      have heq : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) h = diagGL (D 0) (D 1) h0 h1 := by
        apply Units.ext
        show Matrix.diagonal D = Matrix.diagonal ![D 0, D 1]
        congr 1
        ext i
        fin_cases i <;> rfl
      rw [heq]
      exact modFun_diagGL ν hν _ _ h0 h1
    · intro t h
      obtain ⟨i, j, hij, c⟩ := t
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · have heq : Matrix.GeneralLinearGroup.mkOfDetNeZero _ h = upperGL c := by
          apply Units.ext
          show Matrix.TransvectionStruct.toMatrix ⟨0, 1, hij, c⟩ = !![1, c; 0, 1]
          rw [Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection]
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.single]
        rw [heq]
        exact modFun_upperGL ν hν c
      · have heq : Matrix.GeneralLinearGroup.mkOfDetNeZero _ h = lowerGL c := by
          apply Units.ext
          show Matrix.TransvectionStruct.toMatrix ⟨1, 0, hij, c⟩ = !![1, 0; c, 1]
          rw [Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection]
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.single]
        rw [heq]
        exact modFun_lowerGL ν hν c
      · exact absurd rfl hij
    · intro A B hA hB PA PB h
      have heq : Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) h =
          Matrix.GeneralLinearGroup.mkOfDetNeZero A hA * Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        apply Units.ext
        rfl
      rw [heq, modFun_mul ν hν, PA hA, PB hB, mul_one]
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) hdet = g := by
    apply Units.ext
    rfl
  rw [← hg]
  exact key _ hdet hdet

end modular

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem isSectionFn_scalar_normalizedIndicator (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
      (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) :
    IsSectionFn K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f
      (fun x => ((@Measure.map _ _ (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (localGLBorel K v) (scalarCentralizerEquiv c) τ) (localIntegralSet K v)).toReal⁻¹ *
        (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) x) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  letI := localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  haveI : BorelSpace (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := ⟨rfl⟩
  haveI := hτ
  set e := scalarCentralizerEquiv (K := K) (v := v) c
  set ν : Measure (GL (Fin 2) (v.adicCompletion K)) := τ.map e with hν_def
  haveI hν : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τ e
  have hK0 : MeasurableSet (localIntegralSet K v) := (isOpen_localIntegralSet K v).measurableSet
  have hne0 : ν (localIntegralSet K v) ≠ 0 := measure_localIntegralSet_ne_zero ν hν
  have hnetop : ν (localIntegralSet K v) ≠ ⊤ := measure_localIntegralSet_ne_top ν hν
  have hpos : (ν (localIntegralSet K v)).toReal ≠ 0 := (ENNReal.toReal_pos hne0 hnetop).ne'
  show IsSectionFn K v _ τ f
    (fun x => (ν (localIntegralSet K v)).toReal⁻¹ * (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) x)
  refine ⟨fun x => ?_, ?_, ?_, fun x _ => ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  · exact (measurable_const.indicator hK0).const_mul _
  · refine HasCompactSupport.intro (isCompact_localIntegralSet K v) fun x hx => ?_
    simp [Set.indicator_of_notMem hx]
  ·
    have hmap : ∫ t : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (ν (localIntegralSet K v)).toReal⁻¹ *
            (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) (↑t * x) ∂τ =
        ∫ g, (ν (localIntegralSet K v)).toReal⁻¹ *
            (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) (g * x) ∂ν := by
      have he : Measurable (e : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) →
          GL (Fin 2) (v.adicCompletion K)) := e.continuous.measurable
      rw [hν_def, integral_map he.aemeasurable]
      · rfl
      · exact (((measurable_const.indicator hK0).const_mul _).comp
          (continuous_mul_const x).measurable).aestronglyMeasurable
    have hind : ∀ g : GL (Fin 2) (v.adicCompletion K),
        (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) (g * x) =
          ((· * x) ⁻¹' localIntegralSet K v).indicator 1 g := by
      intro g
      rfl
    rw [hmap, integral_const_mul]
    simp_rw [hind]
    rw [integral_indicator_one (hK0.preimage (continuous_mul_const x).measurable), measureReal_def,
      measure_preimage_mul_right_localIntegralSet_eq ν hν x, modFun_eq_one ν hν x, ENNReal.coe_one, one_mul]
    exact inv_mul_cancel₀ hpos

namespace ScalarTransfer

private theorem exists_isOrbitalIntegral_scalar
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f) :
    ∃ J : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f J := by
  have _ := hf
  exact ⟨_, _, isSectionFn_scalar_normalizedIndicator c τ hτ f, rfl⟩

end ScalarTransfer

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

open TensorProduct

namespace CoupledPartner

section Commutativity

variable {R : Type} [CommRing R]

private theorem entries_comm_aux (p q r s a b c d a' b' c' d' : R) (hΔ : IsUnit ((p - s) ^ 2 + 4 * q * r))
    (ht1 : a * p + b * r = p * a + q * c) (ht2 : a * q + b * s = p * b + q * d)
    (ht3 : c * p + d * r = r * a + s * c) (hu1 : a' * p + b' * r = p * a' + q * c')
    (hu2 : a' * q + b' * s = p * b' + q * d') (hu3 : c' * p + d' * r = r * a' + s * c') :
    b * c' - b' * c = 0 ∧ b' * (a - d) - b * (a' - d') = 0 ∧ c * (a' - d') - c' * (a - d) = 0 := by

  have ht1' : b * r = q * c := by linear_combination ht1
  have ht2' : b * (p - s) = q * (a - d) := by linear_combination (-1 : R) * ht2
  have ht3' : c * (p - s) = r * (a - d) := by linear_combination ht3
  have hu1' : b' * r = q * c' := by linear_combination hu1
  have hu2' : b' * (p - s) = q * (a' - d') := by linear_combination (-1 : R) * hu2
  have hu3' : c' * (p - s) = r * (a' - d') := by linear_combination hu3

  have e1 : (p - s) * (b * c' - b' * c) = q * ((a - d) * c' - (a' - d') * c) := by
    linear_combination c' * ht2' - c * hu2'
  have e2 : (p - s) * ((a - d) * c' - (a' - d') * c) = 0 := by
    linear_combination (a - d) * hu3' - (a' - d') * ht3'
  have e3 : q * r * (b * c' - b' * c) = 0 := by
    linear_combination (q * c') * ht1' - (q * c) * hu1'
  have E1 : b * c' - b' * c = 0 :=
    (hΔ.mul_right_eq_zero).mp (by linear_combination (p - s) * e1 + q * e2 + 4 * e3)
  have f1 : (p - s) * (b' * (a - d) - b * (a' - d')) = 0 := by
    linear_combination (a - d) * hu2' - (a' - d') * ht2'
  have f2 : q * (b' * (a - d) - b * (a' - d')) = 0 := by
    linear_combination (-b') * ht2' + b * hu2'
  have E2 : b' * (a - d) - b * (a' - d') = 0 :=
    (hΔ.mul_right_eq_zero).mp (by linear_combination (p - s) * f1 + 4 * r * f2)
  have g1 : (p - s) * (c * (a' - d') - c' * (a - d)) = 0 := by
    linear_combination (a' - d') * ht3' - (a - d) * hu3'
  have g2 : r * (c * (a' - d') - c' * (a - d)) = 0 := by
    linear_combination (-c) * hu3' + c' * ht3'
  have E3 : c * (a' - d') - c' * (a - d) = 0 :=
    (hΔ.mul_right_eq_zero).mp (by linear_combination (p - s) * g1 + 4 * q * g2)
  exact ⟨E1, E2, E3⟩

private theorem mul_comm_of_commute_of_isUnit_discr (g t u : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (Matrix.trace g ^ 2 - 4 * Matrix.det g)) (ht : t * g = g * t) (hu : u * g = g * u) :
    t * u = u * t := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hg
  have h := fun i j => congrFun (congrFun ht i) j
  have h' := fun i j => congrFun (congrFun hu i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h h'
  have hΔ : IsUnit ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) := by
    convert hg using 1
    all_goals try rfl
    ring
  obtain ⟨E1, E2, E3⟩ := entries_comm_aux (g 0 0) (g 0 1) (g 1 0) (g 1 1) (t 0 0) (t 0 1) (t 1 0) (t 1 1)
    (u 0 0) (u 0 1) (u 1 0) (u 1 1) hΔ (h 0 0) (h 0 1) (h 1 0) (h' 0 0) (h' 0 1) (h' 1 0)
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination E1
  · linear_combination E2
  · linear_combination E3
  · linear_combination (-1 : R) * E1

end Commutativity

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

private theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ (Algebra.TensorProduct.includeRight a) = Algebra.TensorProduct.includeRight a := by
  simp [sigmaTensor, Algebra.TensorProduct.includeRight_apply]

private theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  apply Units.ext
  ext i j
  simp only [sigmaGL, toTensorGL, Matrix.GeneralLinearGroup.map_apply]
  exact sigmaTensor_includeRight K L A σ _

private theorem sigmaGL_iterate_apply (n : ℕ) (t : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((⇑(sigmaGL K L A σ))^[n] t : GL (Fin 2) (L ⊗[K] A)) i j = (⇑(sigmaTensor K L A σ))^[n] (t i j) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    simp only [sigmaGL, Matrix.GeneralLinearGroup.map_apply]

private theorem sigmaTensor_iterate (n : ℕ) (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] x = Algebra.TensorProduct.map (σ ^ n).toAlgHom (AlgHom.id K A) x := by
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    exact (congrArg (fun f : L ⊗[K] A →ₐ[K] L ⊗[K] A => f x) Algebra.TensorProduct.map_id).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
      (Algebra.TensorProduct.map (σ ^ n).toAlgHom (AlgHom.id K A) x) = _
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    congr 2
    ext y
    simp [pow_succ']

private theorem sigmaTensor_iterate_finrank [FiniteDimensional K L] [IsGalois K L] (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[Module.finrank K L] x = x := by
  rw [sigmaTensor_iterate, ← IsGalois.card_aut_eq_finrank K L, pow_card_eq_one']
  have h : Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) = AlgHom.id K (L ⊗[K] A) :=
    Algebra.TensorProduct.ext' fun l a => by simp
  exact congrArg (fun f : L ⊗[K] A →ₐ[K] L ⊗[K] A => f x) h

private theorem sigmaGL_iterate_finrank [FiniteDimensional K L] [IsGalois K L] (t : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t := by
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate_finrank]

private theorem mul_eq_of_mem_twistedCentralizer {δ t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) : t * δ = δ * sigmaGL K L A σ t := by
  have h : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  calc t * δ = t * δ * (sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ t := (inv_mul_cancel_right _ _).symm
    _ = δ * sigmaGL K L A σ t := by rw [h]

private def partialNorm (δ : GL (Fin 2) (L ⊗[K] A)) (k : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range k).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

private theorem partialNorm_succ (δ : GL (Fin 2) (L ⊗[K] A)) (k : ℕ) :
    partialNorm K L A σ δ (k + 1) = partialNorm K L A σ δ k * (⇑(sigmaGL K L A σ))^[k] δ := by
  simp only [partialNorm, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]

private theorem normString_eq_partialNorm (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = partialNorm K L A σ δ (Module.finrank K L) := rfl

private theorem mul_partialNorm {δ t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ twistedCentralizer K L A σ δ)
    (k : ℕ) : t * partialNorm K L A σ δ k = partialNorm K L A σ δ k * (⇑(sigmaGL K L A σ))^[k] t := by
  induction k with
  | zero => simp [partialNorm]
  | succ k ih =>
    rw [partialNorm_succ, ← mul_assoc, ih, mul_assoc, ← iterate_map_mul,
      mul_eq_of_mem_twistedCentralizer K L A σ ht, iterate_map_mul, ← mul_assoc, ← Function.iterate_succ_apply]

private theorem commute_normString [FiniteDimensional K L] [IsGalois K L] {δ t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) : t * normString K L A σ δ = normString K L A σ δ * t := by
  rw [normString_eq_partialNorm, mul_partialNorm K L A σ ht, sigmaGL_iterate_finrank]

private theorem partialNorm_conj (δ y : GL (Fin 2) (L ⊗[K] A)) (k : ℕ) :
    partialNorm K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) k =
      y⁻¹ * partialNorm K L A σ δ k * (⇑(sigmaGL K L A σ))^[k] y := by
  induction k with
  | zero => simp [partialNorm]
  | succ k ih =>
    rw [partialNorm_succ, partialNorm_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv,
      ← Function.iterate_succ_apply]
    group

private theorem normString_conj [FiniteDimensional K L] [IsGalois K L] (δ y : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) = y⁻¹ * normString K L A σ δ * y := by
  rw [normString_eq_partialNorm, normString_eq_partialNorm, partialNorm_conj, sigmaGL_iterate_finrank]

private theorem sigmaGL_normString [FiniteDimensional K L] [IsGalois K L] (δ : GL (Fin 2) (L ⊗[K] A)) :
    δ * sigmaGL K L A σ (normString K L A σ δ) = normString K L A σ δ * δ := by
  have h1 : ∀ k, δ * sigmaGL K L A σ (partialNorm K L A σ δ k) = partialNorm K L A σ δ (k + 1) := by
    intro k
    induction k with
    | zero => simp [partialNorm]
    | succ k ih =>
      rw [partialNorm_succ K L A σ δ (k + 1), partialNorm_succ, map_mul, ← mul_assoc, ih, partialNorm_succ,
        ← Function.iterate_succ_apply' (⇑(sigmaGL K L A σ))]
  rw [normString_eq_partialNorm, h1, partialNorm_succ, sigmaGL_iterate_finrank]

private theorem isRegularSemisimple_toTensorGL {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ) :
    IsRegularSemisimple (toTensorGL K L A γ) := by
  unfold IsRegularSemisimple at hγ ⊢
  set f : A →+* L ⊗[K] A := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom
  have h : ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      f.mapMatrix (γ : Matrix (Fin 2) (Fin 2) A) := rfl
  have htr : Matrix.trace (f.mapMatrix (γ : Matrix (Fin 2) (Fin 2) A)) =
      f (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A)) := (AddMonoidHom.map_trace f _).symm
  rw [h, ← RingHom.map_det, htr]
  have h4 : f (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A)) ^ 2 - 4 * f (Matrix.det (γ : Matrix (Fin 2) (Fin 2) A)) =
      f (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) A)) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [h4]
  exact hγ.map f

private theorem commute_toTensorGL_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {s : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    {u : GL (Fin 2) (L ⊗[K] A)} (hu : u * toTensorGL K L A γ = toTensorGL K L A γ * u) :
    toTensorGL K L A s * u = u * toTensorGL K L A s := by
  have hsγ : s * γ = γ * s := ((Subgroup.mem_centralizer_iff.mp hs) γ (Set.mem_singleton γ)).symm
  apply Units.ext
  have h1 : (toTensorGL K L A s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * toTensorGL K L A γ =
      (toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * toTensorGL K L A s := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hsγ]
  have h2 : (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * toTensorGL K L A γ =
      (toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * u := by
    rw [← Units.val_mul, ← Units.val_mul, hu]
  rw [Units.val_mul, Units.val_mul]
  exact mul_comm_of_commute_of_isUnit_discr _ _ _ (isRegularSemisimple_toTensorGL K L A hγ) h1 h2

private theorem commute_of_commute_toTensorGL {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {t u : GL (Fin 2) (L ⊗[K] A)} (ht : t * toTensorGL K L A γ = toTensorGL K L A γ * t)
    (hu : u * toTensorGL K L A γ = toTensorGL K L A γ * u) : t * u = u * t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine mul_comm_of_commute_of_isUnit_discr _ _ _ (isRegularSemisimple_toTensorGL K L A hγ) ?_ ?_
  · rw [← Units.val_mul, ← Units.val_mul, ht]
  · rw [← Units.val_mul, ← Units.val_mul, hu]

end Twist

section Fixed

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

private def galTensor (τ : L ≃ₐ[K] L) : L ⊗[K] A →ₐ[K] L ⊗[K] A :=
  Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A)

private theorem galTensor_tmul (τ : L ≃ₐ[K] L) (l : L) (a : A) : galTensor K L A τ (l ⊗ₜ a) = τ l ⊗ₜ[K] a := by
  simp [galTensor]

private theorem galTensor_mul (τ₁ τ₂ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    galTensor K L A (τ₁ * τ₂) x = galTensor K L A τ₁ (galTensor K L A τ₂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => simp only [galTensor_tmul, AlgEquiv.mul_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

private theorem galTensor_one (x : L ⊗[K] A) : galTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => simp only [galTensor_tmul, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, hx, hy]

private theorem sigmaTensor_eq_galTensor (x : L ⊗[K] A) : sigmaTensor K L A σ x = galTensor K L A σ x := rfl

private theorem galTensor_eq_of_sigmaTensor_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {x : L ⊗[K] A} (hx : sigmaTensor K L A σ x = x) (τ : L ≃ₐ[K] L) : galTensor K L A τ x = x := by
  rw [sigmaTensor_eq_galTensor] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
  have hinv : galTensor K L A σ⁻¹ x = x := by
    have h := congrArg (galTensor K L A σ⁻¹) hx
    rw [← galTensor_mul, inv_mul_cancel, galTensor_one] at h
    exact h.symm
  refine zpow_induction_left (P := fun τ => galTensor K L A τ x = x) (galTensor_one K L A x)
    (fun a ha => ?_) (fun a ha => ?_) k
  · show galTensor K L A (σ * a) x = x
    rw [galTensor_mul, ha, hx]
  · show galTensor K L A (σ⁻¹ * a) x = x
    rw [galTensor_mul, ha, hinv]

private theorem exists_includeRight_of_forall_galTensor_eq [FiniteDimensional K L] [IsGalois K L] [CharZero K]
    (x : L ⊗[K] A) (hx : ∀ τ : L ≃ₐ[K] L, galTensor K L A τ x = x) :
    ∃ a : A, x = Algebra.TensorProduct.includeRight a := by
  have key : ∀ y : L ⊗[K] A, ∃ a : A,
      ∑ τ : L ≃ₐ[K] L, galTensor K L A τ y = Algebra.TensorProduct.includeRight a := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l a =>
      refine ⟨Algebra.trace K L l • a, ?_⟩
      simp only [galTensor_tmul]
      rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.TensorProduct.includeRight_apply]
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨a₁, h₁⟩ := h₁
      obtain ⟨a₂, h₂⟩ := h₂
      refine ⟨a₁ + a₂, ?_⟩
      rw [map_add, ← h₁, ← h₂, ← Finset.sum_add_distrib]
      simp only [map_add]
  obtain ⟨a, ha⟩ := key x
  have hsum : ∑ τ : L ≃ₐ[K] L, galTensor K L A τ x = (Fintype.card (L ≃ₐ[K] L) : K) • x := by
    simp only [hx, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hc : (Fintype.card (L ≃ₐ[K] L) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card (L ≃ₐ[K] L) : K)⁻¹ • a, ?_⟩
  rw [map_smul, ← ha, hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem includeRight_injective [FiniteDimensional K L] [CharZero K] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  set φ : L →ₗ[K] K := (Module.finrank K L : K)⁻¹ • (Algebra.trace K L) with hφdef
  have hℓ : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hφ : φ 1 = 1 := by
    rw [hφdef, LinearMap.smul_apply, ← map_one (algebraMap K L), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one,
      smul_eq_mul, inv_mul_cancel₀ hℓ]
  set r : L ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id with hr
  have hret : ∀ a : A, r (Algebra.TensorProduct.includeRight a) = a := by
    intro a
    rw [hr, Algebra.TensorProduct.includeRight_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, hφ, LinearMap.id_apply, one_smul]
  intro a b hab
  rw [← hret a, ← hret b, hab]

private theorem toTensorGL_injective [FiniteDimensional K L] [CharZero K] :
    Function.Injective (toTensorGL K L A) := by
  intro s₁ s₂ h
  apply Units.ext
  have h' : (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.mapMatrix
      (s₁ : Matrix (Fin 2) (Fin 2) A) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.mapMatrix (s₂ : Matrix (Fin 2) (Fin 2) A) :=
    congrArg Units.val h
  exact Matrix.map_injective (includeRight_injective K L A) h'

private theorem exists_toTensorGL_of_sigmaGL_eq [FiniteDimensional K L] [IsGalois K L] [CharZero K]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t : GL (Fin 2) (L ⊗[K] A))
    (ht : sigmaGL K L A σ t = t) : ∃ s : GL (Fin 2) A, toTensorGL K L A s = t := by
  set f : A →+* L ⊗[K] A := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom with hf
  have hentry : ∀ (u : GL (Fin 2) (L ⊗[K] A)), sigmaGL K L A σ u = u →
      ∀ i j, ∃ a : A, (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = Algebra.TensorProduct.includeRight a := by
    intro u hu i j
    apply exists_includeRight_of_forall_galTensor_eq K L A
    apply galTensor_eq_of_sigmaTensor_eq K L A σ hgen
    have := congrArg (fun w : GL (Fin 2) (L ⊗[K] A) => (w : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hu
    simpa only [sigmaGL, Matrix.GeneralLinearGroup.map_apply] using this
  have hinv : sigmaGL K L A σ t⁻¹ = t⁻¹ := by rw [map_inv, ht]
  choose S hS using hentry t ht
  choose S' hS' using hentry t⁻¹ hinv
  have hM : f.mapMatrix (Matrix.of S) = (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hS]
    rfl
  have hM' : f.mapMatrix (Matrix.of S') = ((t⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hS']
    rfl
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    Matrix.map_injective (includeRight_injective K L A)
  have h1 : Matrix.of S * Matrix.of S' = 1 := by
    apply hinj
    rw [map_mul, map_one, hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Matrix.of S' * Matrix.of S = 1 := by
    apply hinj
    rw [map_mul, map_one, hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨Matrix.of S, Matrix.of S', h1, h2⟩, ?_⟩
  apply Units.ext
  exact hM

end Fixed

section Centralizer

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

private theorem mem_twistedCentralizer_iff [FiniteDimensional K L] [IsGalois K L] [CharZero K]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y) (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ twistedCentralizer K L A σ δ ↔
      ∃ s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), t = y * toTensorGL K L A s * y⁻¹ := by
  set δ₀ := y⁻¹ * δ * sigmaGL K L A σ y with hδ₀
  have hN : normString K L A σ δ₀ = toTensorGL K L A γ := by
    rw [hδ₀, normString_conj]
    exact hy.symm
  have hδ₀γ : δ₀ * toTensorGL K L A γ = toTensorGL K L A γ * δ₀ := by
    have h := sigmaGL_normString K L A σ δ₀
    rwa [hN, sigmaGL_toTensorGL] at h
  have hδ : δ = y * δ₀ * (sigmaGL K L A σ y)⁻¹ := by
    rw [hδ₀]
    group
  constructor
  · intro ht
    set s₀ := y⁻¹ * t * y with hs₀
    have hs₀γ : s₀ * toTensorGL K L A γ = toTensorGL K L A γ * s₀ := by
      have hN' := commute_normString K L A σ ht
      rw [hy, hs₀]
      calc y⁻¹ * t * y * (y⁻¹ * normString K L A σ δ * y)
          = y⁻¹ * (t * normString K L A σ δ) * y := by group
        _ = y⁻¹ * (normString K L A σ δ * t) * y := by rw [hN']
        _ = y⁻¹ * normString K L A σ δ * y * (y⁻¹ * t * y) := by group
    have hs₀δ₀ : s₀ * δ₀ = δ₀ * sigmaGL K L A σ s₀ := by
      have htδ := mul_eq_of_mem_twistedCentralizer K L A σ ht
      rw [hs₀, hδ₀, map_mul, map_mul, map_inv]
      calc y⁻¹ * t * y * (y⁻¹ * δ * sigmaGL K L A σ y)
          = y⁻¹ * (t * δ) * sigmaGL K L A σ y := by group
        _ = y⁻¹ * (δ * sigmaGL K L A σ t) * sigmaGL K L A σ y := by rw [htδ]
        _ = y⁻¹ * δ * sigmaGL K L A σ y *
            ((sigmaGL K L A σ y)⁻¹ * sigmaGL K L A σ t * sigmaGL K L A σ y) := by group
    have hcomm : s₀ * δ₀ = δ₀ * s₀ := commute_of_commute_toTensorGL K L A hγ hs₀γ hδ₀γ
    have hfix : sigmaGL K L A σ s₀ = s₀ := mul_left_cancel (hs₀δ₀.symm.trans hcomm)
    obtain ⟨s, hs⟩ := exists_toTensorGL_of_sigmaGL_eq K L A σ hgen s₀ hfix
    refine ⟨s, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      apply toTensorGL_injective K L A
      rw [map_mul, map_mul, hs, hs₀γ]
    · rw [hs, hs₀]
      group
  · rintro ⟨s, hs, rfl⟩
    have hc : toTensorGL K L A s * δ₀ = δ₀ * toTensorGL K L A s :=
      commute_toTensorGL_of_mem_centralizer K L A hγ hs hδ₀γ
    show y * toTensorGL K L A s * y⁻¹ * δ * (sigmaGL K L A σ (y * toTensorGL K L A s * y⁻¹))⁻¹ = δ
    rw [map_mul, map_mul, map_inv, sigmaGL_toTensorGL, hδ]
    calc y * toTensorGL K L A s * y⁻¹ * (y * δ₀ * (sigmaGL K L A σ y)⁻¹) *
          (sigmaGL K L A σ y * toTensorGL K L A s * (sigmaGL K L A σ y)⁻¹)⁻¹
        = y * (toTensorGL K L A s * δ₀) * (toTensorGL K L A s)⁻¹ * (sigmaGL K L A σ y)⁻¹ := by group
      _ = y * (δ₀ * toTensorGL K L A s) * (toTensorGL K L A s)⁻¹ * (sigmaGL K L A σ y)⁻¹ := by rw [hc]
      _ = y * δ₀ * (sigmaGL K L A σ y)⁻¹ := by group

end Centralizer

end CoupledPartner

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

open TensorProduct

namespace CoupledPartner

section Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (A : Type) [CommRing A]
  [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

private noncomputable def retr [CharZero K] : L ⊗[K] A →ₗ[A] A :=
  (Algebra.TensorProduct.rid K A A).toLinearMap ∘ₗ
    (LinearMap.baseChange A ((Module.finrank K L : K)⁻¹ • (Algebra.trace K L))) ∘ₗ
      (TensorProduct.RightActions.Module.TensorProduct.comm K A L).symm.toLinearMap

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem retr_includeRight [CharZero K] (a : A) :
    retr K L A (Algebra.TensorProduct.includeRight a) = a := by
  have hℓ : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hφ : ((Module.finrank K L : K)⁻¹ • (Algebra.trace K L)) 1 = 1 := by
    rw [LinearMap.smul_apply, ← map_one (algebraMap K L), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one,
      smul_eq_mul, inv_mul_cancel₀ hℓ]
  simp only [retr, Algebra.TensorProduct.includeRight_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul, LinearMap.baseChange_tmul, hφ,
    AlgEquiv.toLinearMap_apply, Algebra.TensorProduct.rid_tmul, one_smul]

private theorem continuous_retr [CharZero K] : Continuous (retr K L A) :=
  IsModuleTopology.continuous_of_linearMap (retr K L A)

private theorem continuous_includeRight :
    Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  haveI := IsModuleTopology.toContinuousAdd A (L ⊗[K] A)
  exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))

private theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  haveI := isTopologicalRing_tensor K L A
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map (continuous_includeRight K L A)
  · change Continuous fun g : GL (Fin 2) A =>
      (((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    have h2 : (fun g : GL (Fin 2) A =>
        (((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
        fun g => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map
          (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
      funext g
      rw [← map_inv]
      rfl
    rw [h2]
    exact Units.continuous_coe_inv.matrix_map (continuous_includeRight K L A)

end Topology

section Transport

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (A : Type) [CommRing A]
  [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

private noncomputable def cpxHom [IsGalois K L] [CharZero K] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ) {δ y : GL (Fin 2) (L ⊗[K] A)}
    (hy : IsNormConjugator K L A σ γ δ y) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →* twistedCentralizer K L A σ δ where
  toFun s := ⟨y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹,
    (mem_twistedCentralizer_iff K L A σ hgen hγ hy _).mpr ⟨s, s.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]
    group

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem cpxHom_apply [IsGalois K L] [CharZero K] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ) {δ y : GL (Fin 2) (L ⊗[K] A)}
    (hy : IsNormConjugator K L A σ γ δ y) (s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((cpxHom K L A σ hgen hγ hy s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := rfl

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem cpxHom_bijective [IsGalois K L] [CharZero K]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y) :
    Function.Bijective (cpxHom K L A σ hgen hγ hy) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply toTensorGL_injective K L A
    have h := congrArg (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))) hab
    simp only [cpxHom_apply] at h
    rwa [mul_right_cancel_iff, mul_left_cancel_iff] at h
  · intro t
    obtain ⟨s, hs, ht⟩ := (mem_twistedCentralizer_iff K L A σ hgen hγ hy t).mp t.2
    exact ⟨⟨s, hs⟩, Subtype.ext ht.symm⟩

private noncomputable def cpxEquiv [IsGalois K L] [CharZero K]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* twistedCentralizer K L A σ δ := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  refine { MulEquiv.ofBijective (cpxHom K L A σ hgen hγ hy) (cpxHom_bijective K L A σ hgen hγ hy) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  ·
    show Continuous fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      (⟨y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹,
        (mem_twistedCentralizer_iff K L A σ hgen hγ hy _).mpr ⟨s, s.2, rfl⟩⟩ : twistedCentralizer K L A σ δ)
    exact Continuous.subtype_mk
      ((continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul continuous_const) _
  ·
    set e := MulEquiv.ofBijective (cpxHom K L A σ hgen hγ hy) (cpxHom_bijective K L A σ hgen hγ hy) with he
    show Continuous e.symm
    have heapp : ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
        ((e s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
          y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := fun s => rfl
    have hinv : ∀ t : twistedCentralizer K L A σ δ,
        toTensorGL K L A ((e.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A) =
          y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y := by
      intro t
      have h := congrArg (fun u : twistedCentralizer K L A σ δ => (u : GL (Fin 2) (L ⊗[K] A))) (e.apply_symm_apply t)
      beta_reduce at h
      rw [heapp] at h
      rw [← h]
      group
    have hmat : ∀ t : twistedCentralizer K L A σ δ,
        (((e.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A) :
          Matrix (Fin 2) (Fin 2) A) =
          ((y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y : GL (Fin 2) (L ⊗[K] A)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (retr K L A) := by
      intro t
      rw [← hinv t]
      ext i j
      simp only [Matrix.map_apply]
      exact (retr_includeRight K L A _).symm
    have hmat' : ∀ t : twistedCentralizer K L A σ δ,
        ((((e.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) :
          Matrix (Fin 2) (Fin 2) A) =
          ((y⁻¹ * ((t : GL (Fin 2) (L ⊗[K] A))⁻¹) * y : GL (Fin 2) (L ⊗[K] A)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (retr K L A) := by
      intro t
      have h := hinv t
      have h' : toTensorGL K L A (((e.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A)⁻¹) =
          y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A))⁻¹ * y := by
        rw [map_inv, h]
        group
      rw [← h']
      ext i j
      simp only [Matrix.map_apply]
      exact (retr_includeRight K L A _).symm
    apply continuous_induced_rng.2
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · simp only [Function.comp_def, hmat]
      exact (Units.continuous_val.comp
        ((continuous_const.mul continuous_subtype_val).mul continuous_const)).matrix_map (continuous_retr K L A)
    · simp only [Function.comp_def, hmat']
      exact (Units.continuous_val.comp
        ((continuous_const.mul continuous_subtype_val.inv).mul continuous_const)).matrix_map (continuous_retr K L A)

private theorem cpxEquiv_apply [IsGalois K L] [CharZero K]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y)
    (s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((cpxEquiv K L A σ hgen hγ hy s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := rfl

private theorem exists_isHaarMeasure_coupled [IsGalois K L] [CharZero K]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ) :
    ∃ τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' ∧ Coupled K L A σ γ δ y τ τ' := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  letI := glBorelOf (L ⊗[K] A)
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI := hτ
  set e := cpxEquiv K L A σ hgen hγ hy with he
  refine ⟨Measure.map e τ, ContinuousMulEquiv.isHaarMeasure_map τ e, ?_⟩
  show Measure.map (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y)
      (Measure.map e τ) =
    Measure.map
      (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => toTensorGL K L A (t : GL (Fin 2) A)) τ
  have hg : Measurable fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hem : Measurable (e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → twistedCentralizer K L A σ δ) :=
    e.continuous.measurable
  rw [Measure.map_map hg hem]
  congr 1
  funext s
  simp only [Function.comp_apply, he, cpxEquiv_apply]
  group

end Transport

end CoupledPartner

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

open TopologicalSpace

namespace TwistedSection

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
private theorem sigmaTensor_tmul (x : L) (a : A) : sigmaTensor K L A σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor]

omit [IsTopologicalRing A] in
private theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  have hs : ∀ (a : A) (x : L) (b : A), a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
    intro a x b
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
  let f : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := fun x y => map_add (sigmaTensor K L A σ) x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [hs, sigmaTensor_tmul K L A σ, sigmaTensor_tmul K L A σ, hs]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  exact IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
private theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_map (continuous_sigmaTensor K L A σ),
    Units.continuous_coe_inv.matrix_map (continuous_sigmaTensor K L A σ)⟩

private theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensorGL K L A
  have h : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv) continuous_const

omit [TopologicalSpace A] [IsTopologicalRing A] in

private theorem mul_comm_of_mem_twistedCentralizer [IsGalois K L] {δ s t : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsRegularSemisimple (normString K L A σ δ)) (hs : s ∈ twistedCentralizer K L A σ δ)
    (ht : t ∈ twistedCentralizer K L A σ δ) : s * t = t * s := by
  have hs' := congrArg Units.val (CoupledPartner.commute_normString K L A σ hs)
  have ht' := congrArg Units.val (CoupledPartner.commute_normString K L A σ ht)
  rw [Units.val_mul, Units.val_mul] at hs' ht'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact CoupledPartner.mul_comm_of_commute_of_isUnit_discr _ _ _ ((isRegularSemisimple_iff _).1 hδ) hs' ht'

private theorem continuous_inv_mul_mul_sigmaGL (δ : GL (Fin 2) (L ⊗[K] A)) :
    Continuous fun x : GL (Fin 2) (L ⊗[K] A) => x⁻¹ * δ * sigmaGL K L A σ x := by
  haveI := isTopologicalRing_tensor K L A
  exact (continuous_inv.mul continuous_const).mul (continuous_sigmaGL K L A σ)

end Generic

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

omit [NumberField L] in
private theorem mul_mem_semiLocalIntegers {x y : L ⊗[K] v.adicCompletion K} (hx : x ∈ semiLocalIntegers K L v)
    (hy : y ∈ semiLocalIntegers K L v) : x * y ∈ semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, map_mul _ a b⟩

omit [NumberField L] in
private theorem add_mem_semiLocalIntegers {x y : L ⊗[K] v.adicCompletion K} (hx : x ∈ semiLocalIntegers K L v)
    (hy : y ∈ semiLocalIntegers K L v) : x + y ∈ semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add _ a b⟩

private def semiLocalIntegralSubgroup : Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := semiLocalIntegralSet K L v
  one_mem' := one_mem_semiLocalIntegralSet K L v
  mul_mem' := by
    intro a b ha hb
    have ha' := (mem_integralUnitsSet (g := a)).1 ha
    have hb' := (mem_integralUnitsSet (g := b)).1 hb
    refine (mem_integralUnitsSet (g := a * b)).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_semiLocalIntegers K L v (mul_mem_semiLocalIntegers K L v (ha'.1 i 0) (hb'.1 0 j))
        (mul_mem_semiLocalIntegers K L v (ha'.1 i 1) (hb'.1 1 j))
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_semiLocalIntegers K L v (mul_mem_semiLocalIntegers K L v (hb'.2 i 0) (ha'.2 0 j))
        (mul_mem_semiLocalIntegers K L v (hb'.2 i 1) (ha'.2 1 j))
  inv_mem' := by
    intro a ha
    have ha' := (mem_integralUnitsSet (g := a)).1 ha
    refine (mem_integralUnitsSet (g := a⁻¹)).2 ⟨ha'.2, ?_⟩
    rw [inv_inv]
    exact ha'.1

private theorem isCompact_semiLocalIntegralSubgroup :
    IsCompact (semiLocalIntegralSubgroup K L v : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
  isCompact_semiLocalIntegralSet K L v

private theorem isOpen_semiLocalIntegralSubgroup :
    IsOpen (semiLocalIntegralSubgroup K L v : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
  isOpen_semiLocalIntegralSet K L v

omit [NumberField L] in
private theorem borelSpace_twistedCentralizerBorel [FiniteDimensional K L]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    @BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) _
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) :=
  @BorelSpace.mk _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) rfl

private theorem exists_isLocallyConstant_forall_isTwistedSectionFnOn [IsGalois K L]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hC : IsCompact C) :
    ∃ w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
      HasCompactSupport w ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, Function.support φ ⊆ C →
        IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  obtain ⟨Ω, hΩ, hΩx⟩ :=
    exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul K L v σ δ hδ C hC
  obtain ⟨w, h0, hlc, hsupp, hint⟩ :=
    @MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one _ _ _ _
      (semiLocalIntegralSubgroup K L v) (isCompact_semiLocalIntegralSubgroup K L v)
      (isOpen_semiLocalIntegralSubgroup K L v) (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (isClosed_twistedCentralizer K L (v.adicCompletion K) σ δ)
      (fun s hs t ht => mul_comm_of_mem_twistedCentralizer K L (v.adicCompletion K) σ hδ hs ht)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) (borelSpace_twistedCentralizerBorel K L σ v δ)
      τ' hτ' Ω hΩ
  refine ⟨w, h0, hlc, hsupp, fun φ hφ => ⟨h0, ?_, hsupp, fun x hx => ?_⟩⟩
  · letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
    exact hlc.continuous.measurable
  · exact hint x (hΩx x (hφ (Function.mem_support.2 hx)))

private theorem integrable_conj_sigmaGL_mul_ofReal (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : IsLocallyConstant φ)
    {w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ} (hw : IsLocallyConstant w) (hws : HasCompactSupport w) :
    Integrable (fun x => φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ))
      (semiLocalHaar K L v) := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  have hc : Continuous fun x => φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) :=
    (hφ.continuous.comp (continuous_inv_mul_mul_sigmaGL K L (v.adicCompletion K) σ δ)).mul
      (Complex.continuous_ofReal.comp hw.continuous)
  have hs : HasCompactSupport fun x => φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) :=
    hws.mono fun x hx => Function.mem_support.2
      (Complex.ofReal_ne_zero.1 (right_ne_zero_of_mul (Function.mem_support.1 hx)))
  exact hc.integrable_of_hasCompactSupport hs

private theorem isTwistedOrbitalIntegralOn_eq_integral (hσn : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφm : Measurable[glBorelOf (L ⊗[K] v.adicCompletion K)] φ) (hφb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) {I' : ℂ}
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I')
    {w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ}
    (hw : IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w) :
    I' = ∫ x, φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) ∂(semiLocalHaar K L v) :=
  IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
    (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' φ hφm hφb hI' ⟨w, hw, rfl⟩

private theorem measurable_and_bounded_of_isSemiLocalTestFn (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : IsSemiLocalTestFn K L v φ) :
    Measurable[glBorelOf (L ⊗[K] v.adicCompletion K)] φ ∧ ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
  exact ⟨hφ.1.continuous.measurable, hφ.1.continuous.bounded_above_of_compact_support hφ.2⟩

private theorem isSemiLocalTestFn_add {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : IsSemiLocalTestFn K L v φ) (hψ : IsSemiLocalTestFn K L v ψ) : IsSemiLocalTestFn K L v (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

private theorem isTwistedOrbitalIntegralOn_add_eq_add [IsGalois K L] (hσn : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : IsSemiLocalTestFn K L v φ)
    (hψ : IsSemiLocalTestFn K L v ψ) (I₁ I₂ J : ℂ)
    (hI₁ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I₁)
    (hI₂ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' ψ I₂)
    (hJ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (φ + ψ) J) :
    J = I₁ + I₂ := by
  obtain ⟨w, -, hlc, hsupp, hsec⟩ := exists_isLocallyConstant_forall_isTwistedSectionFnOn K L σ v δ hδ τ' hτ'
    (tsupport φ ∪ tsupport ψ) (hφ.2.isCompact.union hψ.2.isCompact)
  have hwφ := hsec φ ((subset_tsupport φ).trans Set.subset_union_left)
  have hwψ := hsec ψ ((subset_tsupport ψ).trans Set.subset_union_right)
  have hwφψ : IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' (φ + ψ) w := by
    refine hsec (φ + ψ) fun x hx => ?_
    rw [Function.mem_support, Pi.add_apply] at hx
    by_cases hφx : φ x = 0
    · rw [hφx, zero_add] at hx
      exact Set.subset_union_right (subset_tsupport ψ hx)
    · exact Set.subset_union_left (subset_tsupport φ hφx)
  obtain ⟨hφm, hφb⟩ := measurable_and_bounded_of_isSemiLocalTestFn K L v φ hφ
  obtain ⟨hψm, hψb⟩ := measurable_and_bounded_of_isSemiLocalTestFn K L v ψ hψ
  obtain ⟨hφψm, hφψb⟩ := measurable_and_bounded_of_isSemiLocalTestFn K L v (φ + ψ) (isSemiLocalTestFn_add K L v hφ hψ)
  rw [isTwistedOrbitalIntegralOn_eq_integral K L σ v hσn δ hδ τ' hτ' φ hφm hφb hI₁ hwφ,
    isTwistedOrbitalIntegralOn_eq_integral K L σ v hσn δ hδ τ' hτ' ψ hψm hψb hI₂ hwψ,
    isTwistedOrbitalIntegralOn_eq_integral K L σ v hσn δ hδ τ' hτ' (φ + ψ) hφψm hφψb hJ hwφψ,
    ← integral_add (integrable_conj_sigmaGL_mul_ofReal K L σ v δ φ hφ.1 hlc hsupp)
      (integrable_conj_sigmaGL_mul_ofReal K L σ v δ ψ hψ.1 hlc hsupp)]
  congr 1
  funext x
  rw [Pi.add_apply, add_mul]

private theorem isSemiLocalTestFn_finset_sum {ι : Type} (s : Finset ι)
    (φ : ι → GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : ∀ j ∈ s, IsSemiLocalTestFn K L v (φ j)) :
    IsSemiLocalTestFn K L v (∑ j ∈ s, φ j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact isSemiLocalTestFn_zero K L v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSemiLocalTestFn_add K L v (hφ a (Finset.mem_insert_self a s))
      (ih fun j hj => hφ j (Finset.mem_insert_of_mem hj))

private theorem isTwistedOrbitalIntegralOn_finset_sum [IsGalois K L] (hσn : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    {ι : Type} (s : Finset ι) (φ : ι → GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ j ∈ s, IsSemiLocalTestFn K L v (φ j)) (I' : ι → ℂ)
    (hI' : ∀ j ∈ s, IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (φ j) (I' j))
    (J : ℂ) (hJ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (∑ j ∈ s, φ j) J) :
    J = ∑ j ∈ s, I' j := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty =>
    rw [Finset.sum_empty]
    rw [Finset.sum_empty] at hJ
    obtain ⟨hm, hb⟩ := measurable_and_bounded_of_isSemiLocalTestFn K L v _ (isSemiLocalTestFn_zero K L v)
    rw [isTwistedOrbitalIntegralOn_eq_integral K L σ v hσn δ hδ τ' hτ' _ hm hb hJ
      (isTwistedSectionFnOn_zero K L (v.adicCompletion K) σ δ τ')]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha] at hJ
    have hφa := hφ a (Finset.mem_insert_self a s)
    have hφs : ∀ j ∈ s, IsSemiLocalTestFn K L v (φ j) := fun j hj => hφ j (Finset.mem_insert_of_mem hj)
    have hsum := isSemiLocalTestFn_finset_sum K L v s φ hφs
    obtain ⟨w, -, -, -, hsec⟩ := exists_isLocallyConstant_forall_isTwistedSectionFnOn K L σ v δ hδ τ' hτ'
      (tsupport (∑ j ∈ s, φ j)) hsum.2.isCompact
    have hI₂ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (∑ j ∈ s, φ j)
        (∫ x, (∑ j ∈ s, φ j) (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ)
          ∂(semiLocalHaar K L v)) :=
      ⟨w, hsec _ (subset_tsupport _), rfl⟩
    rw [isTwistedOrbitalIntegralOn_add_eq_add K L σ v hσn δ hδ τ' hτ' (φ a) (∑ j ∈ s, φ j) hφa hsum _ _ J
      (hI' a (Finset.mem_insert_self a s)) hI₂ hJ,
      ih hφs (fun j hj => hI' j (Finset.mem_insert_of_mem hj)) _ hI₂]

end Local

end TwistedSection

end AutomorphicForm

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

open TopologicalSpace

namespace RegularOrbit

section Companion

variable {F : Type*} [Field F]

private def companion (t d : F) : Matrix (Fin 2) (Fin 2) F := !![0, -d; 1, t]

private theorem det_companion (t d : F) : (companion t d).det = d := by
  simp [companion]

private def cycMat (a : Matrix (Fin 2) (Fin 2) F) (e0 e1 : F) : Matrix (Fin 2) (Fin 2) F :=
  !![e0, a 0 0 * e0 + a 0 1 * e1; e1, a 1 0 * e0 + a 1 1 * e1]

private theorem mul_cycMat (a : Matrix (Fin 2) (Fin 2) F) (e0 e1 : F) :
    a * cycMat a e0 e1 = cycMat a e0 e1 * companion a.trace a.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, companion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

private theorem det_cycMat_e1 (a : Matrix (Fin 2) (Fin 2) F) : (cycMat a 1 0).det = a 1 0 := by
  simp [cycMat]

private theorem det_cycMat_e2 (a : Matrix (Fin 2) (Fin 2) F) : (cycMat a 0 1).det = -a 0 1 := by
  simp [cycMat]

private theorem det_cycMat_e12 (a : Matrix (Fin 2) (Fin 2) F) :
    (cycMat a 1 1).det = a 1 0 + a 1 1 - (a 0 0 + a 0 1) := by
  simp [cycMat]

private theorem det_cycMat_ne_zero_or (a : Matrix (Fin 2) (Fin 2) F) (ha : a.trace ^ 2 - 4 * a.det ≠ 0) :
    (cycMat a 1 0).det ≠ 0 ∨ (cycMat a 0 1).det ≠ 0 ∨ (cycMat a 1 1).det ≠ 0 := by
  rcases eq_or_ne (a 1 0) 0 with h10 | h10
  · rcases eq_or_ne (a 0 1) 0 with h01 | h01
    · right; right
      rw [det_cycMat_e12, h10, h01]
      intro h
      apply ha
      have h' : a 1 1 = a 0 0 := by linear_combination h
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, h10, h01, h']
      ring
    · right; left
      rw [det_cycMat_e2]
      exact neg_ne_zero.2 h01
  · left
    rw [det_cycMat_e1]
    exact h10

private theorem exists_det_cycMat_ne_zero (a : Matrix (Fin 2) (Fin 2) F) (ha : a.trace ^ 2 - 4 * a.det ≠ 0) :
    ∃ e0 e1 : F, (cycMat a e0 e1).det ≠ 0 := by
  rcases det_cycMat_ne_zero_or a ha with h | h | h
  · exact ⟨1, 0, h⟩
  · exact ⟨0, 1, h⟩
  · exact ⟨1, 1, h⟩

private theorem exists_shape_of_mul_companion_eq (t d : F) (x : Matrix (Fin 2) (Fin 2) F)
    (hx : x * companion t d = companion t d * x) :
    ∃ α β : F, x = !![α, -(d * β); β, α + t * β] := by
  refine ⟨x 0 0, x 1 0, ?_⟩
  have h00 := congrFun (congrFun hx 0) 0
  have h10 := congrFun (congrFun hx 1) 0
  simp [companion, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination h00
  · simp
  · simp
    linear_combination h10

private theorem shape_mul_comm (t d α β α' β' : F) :
    !![α, -(d * β); β, α + t * β] * !![α', -(d * β'); β', α' + t * β'] =
      !![α', -(d * β'); β', α' + t * β'] * !![α, -(d * β); β, α + t * β] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem mul_comm_of_mul_companion_eq (t d : F) (x y : Matrix (Fin 2) (Fin 2) F)
    (hx : x * companion t d = companion t d * x) (hy : y * companion t d = companion t d * y) :
    x * y = y * x := by
  obtain ⟨α, β, rfl⟩ := exists_shape_of_mul_companion_eq t d x hx
  obtain ⟨α', β', rfl⟩ := exists_shape_of_mul_companion_eq t d y hy
  exact shape_mul_comm t d α β α' β'

private theorem isUnit_companion_of_isUnit (t d : F) (hd : IsUnit d) : IsUnit (companion t d) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_companion]
  exact hd

private noncomputable def companionUnit (g : GL (Fin 2) F) : GL (Fin 2) F :=
  (isUnit_companion_of_isUnit (g : Matrix (Fin 2) (Fin 2) F).trace (g : Matrix (Fin 2) (Fin 2) F).det
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit g))).unit

private theorem coe_companionUnit (g : GL (Fin 2) F) :
    (companionUnit g : Matrix (Fin 2) (Fin 2) F) =
      companion (g : Matrix (Fin 2) (Fin 2) F).trace (g : Matrix (Fin 2) (Fin 2) F).det :=
  IsUnit.unit_spec _

private noncomputable def cycUnit
    (g : GL (Fin 2) F) (e0 e1 : F) (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    GL (Fin 2) F :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)).unit

private theorem coe_cycUnit
    (g : GL (Fin 2) F) (e0 e1 : F) (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    (cycUnit g e0 e1 h : Matrix (Fin 2) (Fin 2) F) = cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1 :=
  IsUnit.unit_spec _

private theorem mul_cycUnit
    (g : GL (Fin 2) F) (e0 e1 : F) (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    g * cycUnit g e0 e1 h = cycUnit g e0 e1 h * companionUnit g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_cycUnit, coe_companionUnit]
  exact mul_cycMat _ e0 e1

private theorem eq_cycUnit_mul_companionUnit (g : GL (Fin 2) F) (e0 e1 : F)
    (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    g = cycUnit g e0 e1 h * companionUnit g * (cycUnit g e0 e1 h)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact mul_cycUnit g e0 e1 h

private theorem disc_ne_zero_of_isRegularSemisimple (g : GL (Fin 2) F) (hg : IsRegularSemisimple g) :
    (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
  (isRegularSemisimple_iff_ne_zero g).1 hg

private theorem exists_conj_companionUnit (g : GL (Fin 2) F) (hg : IsRegularSemisimple g) :
    ∃ p : GL (Fin 2) F, g = p * companionUnit g * p⁻¹ := by
  obtain ⟨e0, e1, h⟩ := exists_det_cycMat_ne_zero _ (disc_ne_zero_of_isRegularSemisimple g hg)
  exact ⟨cycUnit g e0 e1 h, eq_cycUnit_mul_companionUnit g e0 e1 h⟩

private theorem trace_conj (g x : GL (Fin 2) F) :
    ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mul]

private theorem det_conj (g x : GL (Fin 2) F) :
    ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

private theorem exists_conj_of_trace_det (g h : GL (Fin 2) F) (hg : IsRegularSemisimple g)
    (htr : (h : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace)
    (hdet : (h : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det) :
    ∃ y : GL (Fin 2) F, y * g * y⁻¹ = h := by
  have hh : IsRegularSemisimple h := by
    rw [isRegularSemisimple_iff_ne_zero, htr, hdet]
    exact disc_ne_zero_of_isRegularSemisimple g hg
  have hc : companionUnit h = companionUnit g := by
    apply Units.ext
    rw [coe_companionUnit, coe_companionUnit, htr, hdet]
  obtain ⟨p, hp⟩ := exists_conj_companionUnit g hg
  obtain ⟨q, hq⟩ := exists_conj_companionUnit h hh
  refine ⟨q * p⁻¹, ?_⟩
  rw [hq, hc]
  conv_lhs => rw [hp]
  group

private theorem mul_comm_of_conj (p c : GL (Fin 2) F) (t d : F) (hc : (c : Matrix (Fin 2) (Fin 2) F) = companion t d)
    (x y : GL (Fin 2) F) (hx : x * (p * c * p⁻¹) = p * c * p⁻¹ * x) (hy : y * (p * c * p⁻¹) = p * c * p⁻¹ * y) :
    x * y = y * x := by
  have hx' : (p⁻¹ * x * p) * c = c * (p⁻¹ * x * p) := by
    calc (p⁻¹ * x * p) * c = p⁻¹ * (x * (p * c * p⁻¹)) * p := by group
      _ = p⁻¹ * (p * c * p⁻¹ * x) * p := by rw [hx]
      _ = c * (p⁻¹ * x * p) := by group
  have hy' : (p⁻¹ * y * p) * c = c * (p⁻¹ * y * p) := by
    calc (p⁻¹ * y * p) * c = p⁻¹ * (y * (p * c * p⁻¹)) * p := by group
      _ = p⁻¹ * (p * c * p⁻¹ * y) * p := by rw [hy]
      _ = c * (p⁻¹ * y * p) := by group
  have hxm : ((p⁻¹ * x * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * companion t d =
      companion t d * ((p⁻¹ * x * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hc, ← Units.val_mul, ← Units.val_mul, hx']
  have hym : ((p⁻¹ * y * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * companion t d =
      companion t d * ((p⁻¹ * y * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hc, ← Units.val_mul, ← Units.val_mul, hy']
  have hm := mul_comm_of_mul_companion_eq t d _ _ hxm hym
  have hu : (p⁻¹ * x * p) * (p⁻¹ * y * p) = (p⁻¹ * y * p) * (p⁻¹ * x * p) :=
    Units.ext (by simpa only [Units.val_mul] using hm)
  calc x * y = p * ((p⁻¹ * x * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
    _ = p * ((p⁻¹ * y * p) * (p⁻¹ * x * p)) * p⁻¹ := by rw [hu]
    _ = y * x := by group

private theorem centralizer_comm (g : GL (Fin 2) F) (hg : IsRegularSemisimple g) :
    ∀ a ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)),
      ∀ b ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)), a * b = b * a := by
  obtain ⟨p, hp⟩ := exists_conj_companionUnit g hg
  intro a ha b hb
  rw [Subgroup.mem_centralizer_iff] at ha hb
  have ha' : g * a = a * g := ha g (Set.mem_singleton g)
  have hb' : g * b = b * g := hb g (Set.mem_singleton g)
  rw [hp] at ha' hb'
  exact mul_comm_of_conj p (companionUnit g) _ _ (coe_companionUnit g) a b ha'.symm hb'.symm

end Companion

section Orbit

open Topology

variable {F : Type*} [Field F]

private def orbitSet (γ : GL (Fin 2) F) : Set (GL (Fin 2) F) :=
  {m | Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F)} ∩
    {m | Matrix.det (m : Matrix (Fin 2) (Fin 2) F) = Matrix.det (γ : Matrix (Fin 2) (Fin 2) F)}

private theorem mem_orbitSet_iff {γ m : GL (Fin 2) F} :
    m ∈ orbitSet γ ↔
      Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) ∧
        Matrix.det (m : Matrix (Fin 2) (Fin 2) F) = Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) :=
  Iff.rfl

private theorem self_mem_orbitSet (γ : GL (Fin 2) F) : γ ∈ orbitSet γ := ⟨rfl, rfl⟩

private theorem conj_mem_orbitSet {γ m : GL (Fin 2) F} (g : GL (Fin 2) F) (hm : m ∈ orbitSet γ) :
    g * m * g⁻¹ ∈ orbitSet γ := by
  obtain ⟨htr, hdet⟩ := hm
  have htr' : Matrix.trace ((g * m * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet' : Matrix.det ((g * m * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.det (m : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  exact ⟨htr'.trans htr, hdet'.trans hdet⟩

private scoped instance conjMulAction (γ : GL (Fin 2) F) : MulAction (GL (Fin 2) F) (orbitSet γ) where
  smul g m := ⟨g * m * g⁻¹, conj_mem_orbitSet g m.2⟩
  one_smul m := Subtype.ext (by
    show (1 : GL (Fin 2) F) * (m : GL (Fin 2) F) * 1⁻¹ = m
    rw [inv_one, mul_one, one_mul])
  mul_smul g h m := Subtype.ext (by
    show g * h * (m : GL (Fin 2) F) * (g * h)⁻¹ = g * (h * (m : GL (Fin 2) F) * h⁻¹) * g⁻¹
    simp only [mul_inv_rev, mul_assoc])

private theorem val_smul (γ g : GL (Fin 2) F) (m : orbitSet γ) :
    ((g • m : orbitSet γ) : GL (Fin 2) F) = g * m * g⁻¹ := rfl

private theorem isPretransitive_conj (γ : GL (Fin 2) F)
    (hconj : ∀ m ∈ orbitSet γ, ∃ y : GL (Fin 2) F, y * γ * y⁻¹ = m) :
    MulAction.IsPretransitive (GL (Fin 2) F) (orbitSet γ) :=
  ⟨fun a b => by
    obtain ⟨ya, hya⟩ := hconj a.1 a.2
    obtain ⟨yb, hyb⟩ := hconj b.1 b.2
    refine ⟨yb * ya⁻¹, Subtype.ext ?_⟩
    rw [val_smul, ← hya, ← hyb]
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]⟩

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_trace_val :
    Continuous fun m : GL (Fin 2) F => Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) :=
  (Units.continuous_val :
    Continuous fun m : GL (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F)).matrix_trace

private theorem continuous_det_val :
    Continuous fun m : GL (Fin 2) F => Matrix.det (m : Matrix (Fin 2) (Fin 2) F) :=
  (Units.continuous_val :
    Continuous fun m : GL (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F)).matrix_det

private theorem continuous_conj_val (γ : GL (Fin 2) F) :
    Continuous fun p : GL (Fin 2) F × orbitSet γ => ((p.1 • p.2 : orbitSet γ) : GL (Fin 2) F) := by
  show Continuous fun p : GL (Fin 2) F × orbitSet γ => p.1 * (p.2 : GL (Fin 2) F) * p.1⁻¹
  exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst.inv

private theorem continuousSMul_conj (γ : GL (Fin 2) F) : ContinuousSMul (GL (Fin 2) F) (orbitSet γ) :=
  ⟨continuous_induced_rng.2 (continuous_conj_val γ)⟩

variable [T2Space F]

private theorem isClosed_orbitSet (γ : GL (Fin 2) F) : IsClosed (orbitSet γ) :=
  (isClosed_eq continuous_trace_val continuous_const).inter
    (isClosed_eq continuous_det_val continuous_const)

private theorem exists_isCompact_centralizer_mul
    [LocallyCompactSpace (GL (Fin 2) F)] [SigmaCompactSpace (GL (Fin 2) F)]
    (γ : GL (Fin 2) F)
    (hconj : ∀ m ∈ orbitSet γ, ∃ y : GL (Fin 2) F, y * γ * y⁻¹ = m)
    (K₀ : Subgroup (GL (Fin 2) F)) (hK₀c : IsCompact (K₀ : Set (GL (Fin 2) F)))
    (hK₀o : IsOpen (K₀ : Set (GL (Fin 2) F)))
    (C : Set (GL (Fin 2) F)) (hC : IsCompact C) :
    ∃ Ω : Set (GL (Fin 2) F), IsCompact Ω ∧
      ∀ x : GL (Fin 2) F, x⁻¹ * γ * x ∈ C →
        ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) F)), ∃ d ∈ Ω, x = t * d := by
  haveI : ContinuousSMul (GL (Fin 2) F) (orbitSet γ) := continuousSMul_conj γ
  haveI : MulAction.IsPretransitive (GL (Fin 2) F) (orbitSet γ) := isPretransitive_conj γ hconj
  haveI : LocallyCompactSpace (orbitSet γ) := (isClosed_orbitSet γ).locallyCompactSpace
  obtain ⟨γX, hγXv⟩ : ∃ m : orbitSet γ, (m : GL (Fin 2) F) = γ := ⟨⟨γ, self_mem_orbitSet γ⟩, rfl⟩
  have hopen : IsOpenMap fun g : GL (Fin 2) F => g • γX := isOpenMap_smul_of_sigmaCompact γX
  have hCXc : IsCompact (Subtype.val ⁻¹' C : Set (orbitSet γ)) :=
    (isClosed_orbitSet γ).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hWo : ∀ g : GL (Fin 2) F, IsOpen ((fun g' : GL (Fin 2) F => g' • γX) ''
      ((fun k : GL (Fin 2) F => g * k) '' (K₀ : Set (GL (Fin 2) F)))) :=
    fun g => hopen _ (isOpenMap_mul_left g _ hK₀o)
  have hcov : (Subtype.val ⁻¹' C : Set (orbitSet γ)) ⊆ ⋃ g : GL (Fin 2) F,
      (fun g' : GL (Fin 2) F => g' • γX) ''
        ((fun k : GL (Fin 2) F => g * k) '' (K₀ : Set (GL (Fin 2) F))) := by
    intro m _
    obtain ⟨y, hy⟩ := hconj m.1 m.2
    refine Set.mem_iUnion.2 ⟨y, y * 1, ⟨1, K₀.one_mem, rfl⟩, Subtype.ext ?_⟩
    rw [val_smul, mul_one, hγXv]
    exact hy
  obtain ⟨s, hs⟩ := hCXc.elim_finite_subcover _ hWo hcov
  refine ⟨⋃ g ∈ s, (fun k : GL (Fin 2) F => k⁻¹ * g⁻¹) '' (K₀ : Set (GL (Fin 2) F)), ?_, ?_⟩
  · exact s.isCompact_biUnion fun g _ => hK₀c.image (continuous_inv.mul continuous_const)
  · intro x hx
    have hxm : x⁻¹ * γ * x ∈ orbitSet γ := by
      have h := conj_mem_orbitSet x⁻¹ (self_mem_orbitSet γ)
      rwa [inv_inv] at h
    have hmem : (⟨x⁻¹ * γ * x, hxm⟩ : orbitSet γ) ∈ (Subtype.val ⁻¹' C : Set (orbitSet γ)) := hx
    obtain ⟨g, hg, hW⟩ := Set.mem_iUnion₂.1 (hs hmem)
    obtain ⟨g', ⟨k, hk, hgk⟩, hk'⟩ := hW
    subst hgk
    have h1 : g * k * γ * (g * k)⁻¹ = x⁻¹ * γ * x := by
      have h0 := congrArg Subtype.val hk'
      simp only [val_smul, hγXv] at h0
      exact h0
    have h2 : g * k * γ = x⁻¹ * γ * x * (g * k) := mul_inv_eq_iff_eq_mul.mp h1
    have h3 : x * (g * k) * γ = γ * (x * (g * k)) := by
      rw [mul_assoc, h2]
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    refine ⟨x * (g * k), ?_, k⁻¹ * g⁻¹, Set.mem_iUnion₂.2 ⟨g, hg, k, hk, rfl⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact h3.symm
    · simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Orbit

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def integralSubgroup : Subgroup (GL (Fin 2) (v.adicCompletion K)) where
  carrier := localIntegralSet K v
  one_mem' := one_mem_localIntegralSet K v
  mul_mem' := by
    intro a b ha hb
    have ha' := (mem_localIntegralSet K v (g := a)).1 ha
    have hb' := (mem_localIntegralSet K v (g := b)).1 hb
    refine (mem_localIntegralSet K v (g := a * b)).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (ha'.1 i k) (hb'.1 k j)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (hb'.2 i k) (ha'.2 k j)
  inv_mem' := by
    intro a ha
    have ha' := (mem_localIntegralSet K v (g := a)).1 ha
    refine (mem_localIntegralSet K v (g := a⁻¹)).2 ⟨ha'.2, ?_⟩
    rw [inv_inv]
    exact ha'.1

private theorem coe_integralSubgroup :
    (integralSubgroup K v : Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v :=
  rfl

private theorem isCompact_integralSubgroup :
    IsCompact (integralSubgroup K v : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_integralSubgroup]
  exact isCompact_localIntegralSet K v

private theorem isOpen_integralSubgroup : IsOpen (integralSubgroup K v : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_integralSubgroup]
  exact isOpen_localIntegralSet K v

private theorem isClosed_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed (localCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have h : (localCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) = {x | γ * x = x * γ} := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem borelSpace_localCentralizerBorel (γ : GL (Fin 2) (v.adicCompletion K)) :
    @BorelSpace (localCentralizer K v γ) _ (localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (localCentralizerBorel K v γ) rfl

private theorem measurable_of_isLocallyConstant {w : GL (Fin 2) (v.adicCompletion K) → ℝ}
    (hw : IsLocallyConstant w) : @Measurable (GL (Fin 2) (v.adicCompletion K)) ℝ (localGLBorel K v) _ w := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  exact hw.continuous.measurable

private theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem sigmaCompactSpace_localGL : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion K)) := by
  haveI := locallyCompactSpace_localGL K v
  haveI := secondCountableTopology_localGL K v
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

private theorem exists_isCompact_localCentralizer_mul (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsRegularSemisimple γ) (C : Set (GL (Fin 2) (v.adicCompletion K))) (hC : IsCompact C) :
    ∃ Ω : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact Ω ∧
      ∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * γ * x ∈ C →
        ∃ t ∈ localCentralizer K v γ, ∃ d ∈ Ω, x = t * d := by
  haveI := locallyCompactSpace_localGL K v
  haveI := sigmaCompactSpace_localGL K v
  exact exists_isCompact_centralizer_mul γ (fun m hm => exists_conj_of_trace_det γ m hγ hm.1 hm.2)
    (integralSubgroup K v) (isCompact_integralSubgroup K v) (isOpen_integralSubgroup K v) C hC

private theorem exists_isLocallyConstant_forall_isSectionFn (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsRegularSemisimple γ) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (C : Set (GL (Fin 2) (v.adicCompletion K))) (hC : IsCompact C) :
    ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧ HasCompactSupport w ∧
      ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, Function.support f ⊆ C → IsSectionFn K v γ τ f w := by
  obtain ⟨D, hD, hDx⟩ := exists_isCompact_localCentralizer_mul K v γ hγ C hC
  obtain ⟨w, h0, hlc, hsupp, hint⟩ :=
    @MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one _ _ _ _
      (integralSubgroup K v) (isCompact_integralSubgroup K v) (isOpen_integralSubgroup K v)
      (localCentralizer K v γ) (isClosed_localCentralizer K v γ) (centralizer_comm γ hγ)
      (localCentralizerBorel K v γ) (borelSpace_localCentralizerBorel K v γ) τ hτ D hD
  refine ⟨w, h0, hlc, hsupp, fun f hf => ⟨h0, measurable_of_isLocallyConstant K v hlc, hsupp, fun x hx => ?_⟩⟩
  exact hint x (hDx x (hf (Function.mem_support.2 hx)))

end Local

end RegularOrbit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

open TopologicalSpace

namespace ScalarTransfer

private theorem isLocalTestFn_sub
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f g : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hg : AutomorphicForm.IsLocalTestFn K v g) : AutomorphicForm.IsLocalTestFn K v (f - g) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  rw [sub_eq_add_neg]
  exact hf.2.add hg.2.neg

end ScalarTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

section Linearity

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem continuous_inv_mul_mul (γ : GL (Fin 2) (v.adicCompletion K)) :
    Continuous fun x : GL (Fin 2) (v.adicCompletion K) => x⁻¹ * γ * x :=
  (continuous_inv.mul continuous_const).mul continuous_id

private theorem integrable_conj_mul_ofReal (γ : GL (Fin 2) (v.adicCompletion K))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : IsLocallyConstant f) {w : GL (Fin 2) (v.adicCompletion K) → ℝ}
    (hw : IsLocallyConstant w) (hws : HasCompactSupport w) :
    Integrable (fun x => f (x⁻¹ * γ * x) * (w x : ℂ)) (localHaar K v) := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  haveI := isHaarMeasure_localHaar K v
  have hc : Continuous fun x => f (x⁻¹ * γ * x) * (w x : ℂ) :=
    (hf.continuous.comp (continuous_inv_mul_mul K v γ)).mul (Complex.continuous_ofReal.comp hw.continuous)
  have hs : HasCompactSupport fun x => f (x⁻¹ * γ * x) * (w x : ℂ) :=
    hws.mono fun x hx => Function.mem_support.2
      (Complex.ofReal_ne_zero.1 (right_ne_zero_of_mul (Function.mem_support.1 hx)))
  exact hc.integrable_of_hasCompactSupport hs

private theorem isOrbitalIntegral_eq_integral_of_isSectionFn (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsRegularSemisimple γ) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : IsLocalTestFn K v f) {I : ℂ} (hI : IsOrbitalIntegral K v γ τ f I)
    {w : GL (Fin 2) (v.adicCompletion K) → ℝ} (hw : IsSectionFn K v γ τ f w) :
    I = ∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v) := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  have hI' : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I :=
    (isOrbitalIntegralOn_localHaar_iff K v γ τ f I).mpr hI
  have hJ' : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f
      (∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)) :=
    (isOrbitalIntegralOn_localHaar_iff K v γ τ f _).mpr ⟨w, hw, rfl⟩
  exact IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
    (isHaarMeasure_localHaar K v) γ hγ τ hτ f hf.1.continuous.measurable
    (hf.1.continuous.bounded_above_of_compact_support hf.2) hI' hJ'

private theorem isOrbitalIntegral_sub_eq_sub (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (f g : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : IsLocalTestFn K v f) (hg : IsLocalTestFn K v g)
    (I J M : ℂ) (hI : IsOrbitalIntegral K v γ τ f I) (hJ : IsOrbitalIntegral K v γ τ g J)
    (hM : IsOrbitalIntegral K v γ τ (f - g) M) : M = I - J := by
  obtain ⟨w, -, hlc, hsupp, hsec⟩ := RegularOrbit.exists_isLocallyConstant_forall_isSectionFn K v γ hγ τ hτ
    (tsupport f ∪ tsupport g) (hf.2.isCompact.union hg.2.isCompact)
  have hwf : IsSectionFn K v γ τ f w := hsec f ((subset_tsupport f).trans Set.subset_union_left)
  have hwg : IsSectionFn K v γ τ g w := hsec g ((subset_tsupport g).trans Set.subset_union_right)
  have hwfg : IsSectionFn K v γ τ (f - g) w := by
    refine hsec (f - g) fun x hx => ?_
    rw [Function.mem_support, Pi.sub_apply] at hx
    by_cases hfx : f x = 0
    · rw [hfx, zero_sub, neg_ne_zero] at hx
      exact Set.subset_union_right (subset_tsupport g hx)
    · exact Set.subset_union_left (subset_tsupport f hfx)
  rw [isOrbitalIntegral_eq_integral_of_isSectionFn K v γ hγ τ hτ f hf hI hwf,
    isOrbitalIntegral_eq_integral_of_isSectionFn K v γ hγ τ hτ g hg hJ hwg,
    isOrbitalIntegral_eq_integral_of_isSectionFn K v γ hγ τ hτ (f - g)
      (ScalarTransfer.isLocalTestFn_sub K v f g hf hg) hM hwfg,
    ← integral_sub (integrable_conj_mul_ofReal K v γ f hf.1 hlc hsupp)
      (integrable_conj_mul_ofReal K v γ g hg.1 hlc hsupp)]
  congr 1
  funext x
  rw [Pi.sub_apply, sub_mul]

private theorem isOrbitalIntegral_sub_eq_zero_of_forall_eq (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsRegularSemisimple γ) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (f g : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : IsLocalTestFn K v f) (hg : IsLocalTestFn K v g)
    (hfg : ∀ I J : ℂ, IsOrbitalIntegral K v γ τ f I → IsOrbitalIntegral K v γ τ g J → I = J)
    (M : ℂ) (hM : IsOrbitalIntegral K v γ τ (f - g) M) : M = 0 := by
  obtain ⟨w, -, -, -, hsec⟩ := RegularOrbit.exists_isLocallyConstant_forall_isSectionFn K v γ hγ τ hτ
    (tsupport f ∪ tsupport g) (hf.2.isCompact.union hg.2.isCompact)
  have hI : IsOrbitalIntegral K v γ τ f (∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)) :=
    ⟨w, hsec f ((subset_tsupport f).trans Set.subset_union_left), rfl⟩
  have hJ : IsOrbitalIntegral K v γ τ g (∫ x, g (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)) :=
    ⟨w, hsec g ((subset_tsupport g).trans Set.subset_union_right), rfl⟩
  rw [isOrbitalIntegral_sub_eq_sub K v γ hγ τ hτ f g hf hg _ _ M hI hJ hM, hfg _ _ hI hJ, sub_self]

end Linearity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

namespace CentralTransfer

section Invariants

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

private noncomputable def normInvariants (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) :=
  (Matrix.trace (normString K L (v.adicCompletion K) σ g :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)),
    Matrix.det (normString K L (v.adicCompletion K) σ g :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))

private noncomputable def embInvariants (γ : GL (Fin 2) (v.adicCompletion K)) :
    (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) :=
  (Matrix.trace (toTensorGL K L (v.adicCompletion K) γ :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)),
    Matrix.det (toTensorGL K L (v.adicCompletion K) γ :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))

omit [NumberField L] in

private theorem pair_conj (a x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (Matrix.trace ((x⁻¹ * a * x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)),
      Matrix.det ((x⁻¹ * a * x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
    (Matrix.trace (a : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)),
      Matrix.det (a : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  simp only [Units.val_mul, Matrix.trace_units_conj', Matrix.det_units_conj']

omit [NumberField L] in

private theorem normInvariants_conj
    (hN : ∀ δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      normString K L (v.adicCompletion K) σ (y⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ y) =
        y⁻¹ * normString K L (v.adicCompletion K) σ δ * y)
    (δ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    normInvariants K L σ v (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
      normInvariants K L σ v δ := by
  unfold normInvariants
  rw [hN δ x]
  exact pair_conj K L v _ x

omit [NumberField L] in

private theorem normInvariants_eq_of_isNormConjugator
    {γ : GL (Fin 2) (v.adicCompletion K)} {δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hy : IsNormConjugator K L (v.adicCompletion K) σ γ δ y) :
    normInvariants K L σ v δ = embInvariants K L v γ := by
  have hy' : toTensorGL K L (v.adicCompletion K) γ =
      y⁻¹ * normString K L (v.adicCompletion K) σ δ * y := hy
  unfold normInvariants embInvariants
  rw [hy']
  exact (pair_conj K L v _ y).symm

omit [NumberField L] in

private theorem isRegularSemisimple_normString_iff_of_normInvariants_eq
    {g g' : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (h : normInvariants K L σ v g = normInvariants K L σ v g') :
    IsRegularSemisimple (normString K L (v.adicCompletion K) σ g) ↔
      IsRegularSemisimple (normString K L (v.adicCompletion K) σ g') := by
  unfold normInvariants at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  unfold IsRegularSemisimple
  rw [h1, h2]

private theorem continuous_normInvariants
    (hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ)) :
    Continuous (normInvariants K L σ v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hN : Continuous (normString K L (v.adicCompletion K) σ) := by
    have := continuous_list_prod (List.range (Module.finrank K L))
      (f := fun i : ℕ => (⇑(sigmaGL K L (v.adicCompletion K) σ))^[i]) (fun i _ => hσc.iterate i)
    exact this
  exact (Continuous.matrix_trace (Units.continuous_val.comp hN)).prodMk
    (Continuous.matrix_det (Units.continuous_val.comp hN))

private theorem continuous_embInvariants (hιc : Continuous (toTensorGL K L (v.adicCompletion K))) :
    Continuous (embInvariants K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (Continuous.matrix_trace (Units.continuous_val.comp hιc)).prodMk
    (Continuous.matrix_det (Units.continuous_val.comp hιc))

private theorem isTwistedOrbitalIntegralOn_congr (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : ∀ x, φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
      ψ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I) :
    IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' ψ I := by
  obtain ⟨w, ⟨hw0, hwm, hws, hwi⟩, hIw⟩ := hI
  refine ⟨w, ⟨hw0, hwm, hws, fun x hx => hwi x ?_⟩, ?_⟩
  · rwa [h x]
  · rw [hIw]
    congr 1
    funext x
    rw [h x]

private theorem isTwistedSectionFnOn_of_support (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ} {w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ}
    (h : ∀ x, ψ x ≠ 0 → φ x ≠ 0) (hw : IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w) :
    IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' ψ w := by
  obtain ⟨hw0, hwm, hws, hwi⟩ := hw
  exact ⟨hw0, hwm, hws, fun x hx => hwi x (h _ hx)⟩

end Invariants
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

section Scalar

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem inv_mul_scalar_mul (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have h : Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = x * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    apply Units.ext
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (c : v.adicCompletion K) (fun _ => Commute.all _ _)
      (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).eq
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem isOrbitalIntegral_scalar_eq (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
      (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    {r : ℝ}
    (hr : ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≠ 0 →
      ∀ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
        IsSectionFn K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f w → ∫ x, w x ∂(localHaar K v) = r)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) {I : ℂ}
    (hI : IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) :
    I = f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (r : ℂ) := by
  letI := localGLBorel K v
  obtain ⟨w, hw, hIw⟩ := hI
  have hconst : (fun x => f (x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x) * (w x : ℂ)) =
      fun x => f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (w x : ℂ) := by
    funext x
    rw [inv_mul_scalar_mul K v c x]
  rw [hIw, hconst, integral_const_mul, integral_complex_ofReal]
  by_cases hf : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0
  · rw [hf, zero_mul, zero_mul]
  · rw [hr f hf w hw]

end Scalar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

section Sums

variable {X : Type} [TopologicalSpace X]

private theorem isLocallyConstant_sum {ι : Type} [Fintype ι] (f : ι → X → ℂ)
    (hf : ∀ j, IsLocallyConstant (f j)) : IsLocallyConstant fun x => ∑ j, f j x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ j, ∀ᶠ y in nhds x, f j y = f j x :=
    fun j => (IsLocallyConstant.iff_eventually_eq (f j)).1 (hf j) x
  exact (Filter.eventually_all.2 h).mono fun y hy => Finset.sum_congr rfl fun j _ => hy j

end Sums
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

section Assembly

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

private def CentralClause (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  ∀ (c₁ : (v.adicCompletion K)ˣ) (δ₁ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
    IsNormConjugator K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ₁ y →
    ∀ (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁))
        (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁)))
      (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ₁)
        (twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁)),
      @Measure.IsHaarMeasure _ _ _
        (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁)) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁) τ' →
      Coupled K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ₁ y τ τ' →
      (∀ I I' : ℂ, IsTwistedOrbitalIntegral K L v σ δ₁ τ' φ I' →
        IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) τ f I → I' = I) ∧
      (∀ w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
        IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ₁ τ' φ w →
        Integrable (fun x => φ (x⁻¹ * δ₁ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ))
          (semiLocalHaar K L v))

private theorem exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_cover
    (hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ))
    (hιc : Continuous (toTensorGL K L (v.adicCompletion K)))
    (hN : ∀ δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      normString K L (v.adicCompletion K) σ (y⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ y) =
        y⁻¹ * normString K L (v.adicCompletion K) σ δ * y)
    (htsect : ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) →
      ∀ (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
        (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      ∀ (C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))), IsCompact C →
      ∃ w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
        HasCompactSupport w ∧
        ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, Function.support φ ⊆ C →
          IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w)
    (htsum : ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) →
      ∀ (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
        (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      ∀ {ι : Type} (s : Finset ι) (φ : ι → GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        (∀ j ∈ s, IsSemiLocalTestFn K L v (φ j)) → ∀ (I' : ι → ℂ),
        (∀ j ∈ s,
          IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (φ j) (I' j)) →
        ∀ J : ℂ,
          IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (∑ j ∈ s, φ j) J →
          J = ∑ j ∈ s, I' j)
    (hsect : ∀ (γ : GL (Fin 2) (v.adicCompletion K)), IsRegularSemisimple γ →
      ∀ (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)),
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
      ∀ (C : Set (GL (Fin 2) (v.adicCompletion K))), IsCompact C →
      ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
        HasCompactSupport w ∧
        ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, Function.support f ⊆ C → IsSectionFn K v γ τ f w)
    (hval : ∀ (γ : GL (Fin 2) (v.adicCompletion K)), IsRegularSemisimple γ →
      ∀ (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)),
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
      ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), IsLocalTestFn K v f →
      ∀ {I : ℂ}, IsOrbitalIntegral K v γ τ f I →
      ∀ {w : GL (Fin 2) (v.adicCompletion K) → ℝ}, IsSectionFn K v γ τ f w →
      I = ∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v))
    (hintg : ∀ (γ : GL (Fin 2) (v.adicCompletion K)) (f : GL (Fin 2) (v.adicCompletion K) → ℂ),
      IsLocallyConstant f →
      ∀ {w : GL (Fin 2) (v.adicCompletion K) → ℝ}, IsLocallyConstant w → HasCompactSupport w →
      Integrable (fun x => f (x⁻¹ * γ * x) * (w x : ℂ)) (localHaar K v))
    (c : (v.adicCompletion K)ˣ)
    (hscalar : ∀ (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      @Measure.IsHaarMeasure _ _ _
        (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
      ∃ r : ℝ, ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ,
        f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≠ 0 →
        ∀ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
          IsSectionFn K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f w →
            ∫ x, w x ∂(localHaar K v) = r)
    (hexists : ∀ (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      @Measure.IsHaarMeasure _ _ _
        (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
      ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v f →
      ∃ J : ℂ, IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f J)
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ₀))
    (hc : IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀)
    (hloc : ∀ (δ₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ¬ IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ₁) →
      ∃ U ∈ nhds δ₁, ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
        IsSemiLocalTestFn K L v φ → tsupport φ ⊆ U →
        ∃ f : GL (Fin 2) (v.adicCompletion K) → ℂ,
          IsLocalTestFn K v f ∧ AreMatchingLocal K L v σ φ f ∧ CentralClause K L σ v φ f)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv)
    (hcover : ∀ (P : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) → Prop),
      (∀ g, normInvariants K L σ v g = normInvariants K L σ v δ₀ → ∃ U ∈ nhds g, P U) →
      ∃ B : Set ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)), IsOpen B ∧
        normInvariants K L σ v δ₀ ∈ B ∧
        ∃ (n : ℕ) (U : Fin n → Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
          (φ : Fin n → GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
          (∀ j, P (U j)) ∧ (∀ j, IsSemiLocalTestFn K L v (φ j)) ∧ (∀ j, tsupport (φ j) ⊆ U j) ∧
          (∀ j x, φ j x ≠ 0 → φv x ≠ 0) ∧
          (∀ x, normInvariants K L σ v x ∈ B → φv x = ∑ j, φ j x)) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        (∀ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) →
          ∀ γ ∈ V, IsRegularSemisimple γ →
          ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
            IsNormConjugator K L (v.adicCompletion K) σ γ δ y →
          ∀ (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
            (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
              (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
            @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
            @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
            Coupled K L (v.adicCompletion K) σ γ δ y τ τ' →
            ∀ I I' : ℂ, IsTwistedOrbitalIntegral K L v σ δ τ' φv I' →
              IsOrbitalIntegral K v γ τ fv I → I' = I) ∧
        (∀ γ ∈ V, IsRegularSemisimple γ →
          (¬ ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ) →
          ∀ τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ),
            @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
            ∀ I : ℂ, IsOrbitalIntegral K v γ τ fv I → I = 0)) ∧
      (∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        IsNormConjugator K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y →
        ∀ (τ : @Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
            (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ₀)
            (twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀)),
          @Measure.IsHaarMeasure _ _ _
            (localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀) τ' →
          Coupled K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegral K L v σ δ₀ τ' φv I' →
            IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv I → I' = I) := by
  classical
  have _ := hσc
  have _ := hφv
  obtain ⟨y₀, hy₀⟩ := hc

  have hfibre : ∀ g, normInvariants K L σ v g = normInvariants K L σ v δ₀ →
      ∃ U ∈ nhds g, ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
        IsSemiLocalTestFn K L v φ → tsupport φ ⊆ U →
        ∃ f : GL (Fin 2) (v.adicCompletion K) → ℂ,
          IsLocalTestFn K v f ∧ AreMatchingLocal K L v σ φ f ∧ CentralClause K L σ v φ f :=
    fun g hg => hloc g fun h =>
      hδ₀ ((isRegularSemisimple_normString_iff_of_normInvariants_eq K L σ v hg).1 h)
  obtain ⟨B, hBo, hδ₀B, n, U, φ, hPU, hφ, hsub, hsupp, hsum⟩ := hcover _ hfibre
  choose f hf hmatch hcent using fun j => hPU j (φ j) (hφ j) (hsub j)

  have hC' : IsCompact (⋃ j, tsupport (f j)) := isCompact_iUnion fun j => (hf j).2
  have hfvsupp : Function.support (fun x => ∑ j, f j x) ⊆ ⋃ j, tsupport (f j) := by
    intro x hx
    have hx' : ∑ j, f j x ≠ 0 := hx
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    exact Set.mem_iUnion.2 ⟨j, subset_tsupport _ hj⟩
  have hfvlt : IsLocalTestFn K v fun x => ∑ j, f j x :=
    ⟨isLocallyConstant_sum f fun j => (hf j).1,
      hC'.of_isClosed_subset isClosed_closure
        (closure_minimal hfvsupp (isClosed_iUnion_of_finite fun j => isClosed_closure))⟩

  have huntw : ∀ (γ : GL (Fin 2) (v.adicCompletion K)), IsRegularSemisimple γ →
      ∀ (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)),
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
      ∀ I : ℂ, IsOrbitalIntegral K v γ τ (fun x => ∑ j, f j x) I →
      ∃ w₁ : GL (Fin 2) (v.adicCompletion K) → ℝ, (∀ j, IsSectionFn K v γ τ (f j) w₁) ∧
        I = ∑ j, ∫ x, f j (x⁻¹ * γ * x) * (w₁ x : ℂ) ∂(localHaar K v) := by
    intro γ hγ τ hτ I hI
    obtain ⟨w₁, -, hw₁lc, hw₁cs, hw₁⟩ := hsect γ hγ τ hτ _ hC'
    refine ⟨w₁, fun j => hw₁ (f j) ((subset_tsupport _).trans (Set.subset_iUnion (fun j => tsupport (f j)) j)), ?_⟩
    have h1 : (fun x => (∑ j, f j (x⁻¹ * γ * x)) * (w₁ x : ℂ)) =
        fun x => ∑ j, f j (x⁻¹ * γ * x) * (w₁ x : ℂ) := by
      funext x
      rw [Finset.sum_mul]
    calc I = ∫ x, (∑ j, f j (x⁻¹ * γ * x)) * (w₁ x : ℂ) ∂(localHaar K v) :=
          hval γ hγ τ hτ _ hfvlt hI (hw₁ _ hfvsupp)
      _ = ∑ j, ∫ x, f j (x⁻¹ * γ * x) * (w₁ x : ℂ) ∂(localHaar K v) := by
          rw [h1]
          exact integral_finsetSum Finset.univ fun j _ => hintg γ (f j) (hf j).1 hw₁lc hw₁cs

  have hemb : embInvariants K L v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = normInvariants K L σ v δ₀ :=
    (normInvariants_eq_of_isNormConjugator K L σ v hy₀).symm
  have hV : embInvariants K L v ⁻¹' B ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c) :=
    (continuous_embInvariants K L v hιc).continuousAt.preimage_mem_nhds
      (hBo.mem_nhds (by rw [hemb]; exact hδ₀B))
  refine ⟨fun x => ∑ j, f j x, hfvlt, ⟨embInvariants K L v ⁻¹' B, hV, ?_, ?_⟩, ?_⟩
  ·
    intro δ hδ γ hγV hγ y hy τ τ' hτ hτ' hcoup I I' hI' hI
    have hδB : normInvariants K L σ v δ ∈ B := by
      rw [normInvariants_eq_of_isNormConjugator K L σ v hy]
      exact hγV
    have hclass : ∀ x, φv (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
        (∑ j, φ j) (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) := by
      intro x
      rw [Finset.sum_apply]
      exact hsum _ (by rw [normInvariants_conj K L σ v hN]; exact hδB)
    have hI's : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
        (∑ j, φ j) I' :=
      isTwistedOrbitalIntegralOn_congr K L σ v δ τ' hclass hI'
    have hC : IsCompact (⋃ j, tsupport (φ j)) := isCompact_iUnion fun j => (hφ j).2
    obtain ⟨w₀, -, -, -, hw₀⟩ := htsect δ hδ τ' hτ' _ hC
    have hw₀j : ∀ j, IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' (φ j) w₀ :=
      fun j => hw₀ (φ j) ((subset_tsupport _).trans (Set.subset_iUnion (fun j => tsupport (φ j)) j))
    have hI'sum : I' = ∑ j,
        ∫ x, φ j (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w₀ x : ℂ) ∂(semiLocalHaar K L v) :=
      htsum δ hδ τ' hτ' Finset.univ φ (fun j _ => hφ j)
        (fun j => ∫ x, φ j (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w₀ x : ℂ) ∂(semiLocalHaar K L v))
        (fun j _ => ⟨w₀, hw₀j j, rfl⟩) I' hI's
    obtain ⟨w₁, hw₁, hIsum⟩ := huntw γ hγ τ hτ I hI
    rw [hI'sum, hIsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨hm1, -⟩ := hmatch j
    exact hm1 δ hδ γ hγ y hy τ τ' hτ hτ' hcoup _ _ ⟨w₀, hw₀j j, rfl⟩ ⟨w₁, hw₁ j, rfl⟩
  ·
    intro γ _ hγ hnot τ hτ I hI
    obtain ⟨w₁, hw₁, hIsum⟩ := huntw γ hγ τ hτ I hI
    rw [hIsum]
    refine Finset.sum_eq_zero fun j _ => ?_
    obtain ⟨-, hm2⟩ := hmatch j
    exact hm2 γ hγ hnot τ hτ _ ⟨w₁, hw₁ j, rfl⟩
  ·
    intro y hy τ τ' hτ hτ' hcoup I I' hI' hI
    obtain ⟨r, hr⟩ := hscalar τ hτ
    choose J hJ using fun j => hexists τ hτ (f j) (hf j)
    obtain ⟨w, hw, hI'w⟩ := hI'
    have hclass : ∀ x, φv (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) =
        ∑ j, φ j (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) :=
      fun x => hsum _ (by rw [normInvariants_conj K L σ v hN]; exact hδ₀B)
    have hwj : ∀ j, IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ₀ τ' (φ j) w :=
      fun j => isTwistedSectionFnOn_of_support K L σ v δ₀ τ' (hsupp j) hw
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun x => φ j (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ))
          (semiLocalHaar K L v) :=
      fun j _ => (hcent j c δ₀ y hy τ τ' hτ hτ' hcoup).2 w (hwj j)
    have hI'sum : I' = ∑ j,
        ∫ x, φ j (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) ∂(semiLocalHaar K L v) := by
      rw [hI'w]
      have h1 : (fun x => φv (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ)) =
          fun x => ∑ j, φ j (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) := by
        funext x
        rw [hclass x, Finset.sum_mul]
      rw [h1]
      exact integral_finsetSum Finset.univ hint
    have hpiece : ∀ j,
        ∫ x, φ j (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) ∂(semiLocalHaar K L v) =
          J j :=
      fun j => (hcent j c δ₀ y hy τ τ' hτ hτ' hcoup).1 (J j)
        (∫ x, φ j (x⁻¹ * δ₀ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ) ∂(semiLocalHaar K L v))
        ⟨w, hwj j, rfl⟩ (hJ j)
    have hJ' : ∀ j, J j = f j (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (r : ℂ) :=
      fun j => isOrbitalIntegral_scalar_eq K v c τ hr (f j) (hJ j)
    have hIr : I = (∑ j, f j (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) * (r : ℂ) :=
      isOrbitalIntegral_scalar_eq K v c τ hr _ hI
    rw [hI'sum, hIr, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (hpiece j).trans (hJ' j)

end Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end CentralTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

namespace CentralTransfer

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]

private theorem isGalois_of_finrank_prime (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hσ : σ ≠ 1) : IsGalois K L := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  have hcard : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
    have h1 : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L =
        Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) :=
      IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))
    rw [Subgroup.card_top] at h1
    rw [← h1]
    exact Dvd.intro_left _
      (Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L)
  have h2 : 1 < Nat.card (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.2 ⟨⟨σ, 1, hσ⟩⟩
  rcases (Nat.dvd_prime hdeg).1 hcard with h | h
  · omega
  · exact IsGalois.of_card_aut_eq_finrank K L h

private theorem pow_finrank_eq_one (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    σ ^ Module.finrank K L = 1 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  haveI := isGalois_of_finrank_prime K L hdeg σ hσ
  rw [← IsGalois.card_aut_eq_finrank K L]
  exact pow_card_eq_one'

end Galois
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end CentralTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

open TopologicalSpace

namespace ClopenCover

section Generic

private theorem totallySeparatedSpace_of_valued {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued F Γ₀] : TotallySeparatedSpace F := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  refine ⟨{z : F | Valued.v (z - x) < Valued.v (y - x)}, ?_, ?_, ?_⟩
  · have h : {z : F | Valued.v (z - x) < Valued.v (y - x)} = (fun z : F => z - x) ⁻¹'
        {z : F | (Valued.v : Valuation F Γ₀).restrict z < (Valued.v : Valuation F Γ₀).restrict (y - x)} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_lt_iff]
    rw [h]
    exact (Valued.isClopen_ball F _).preimage (continuous_id.sub continuous_const)
  · show Valued.v (x - x) < Valued.v (y - x)
    rw [sub_self, map_zero]
    exact (Valuation.pos_iff _).2 (sub_ne_zero.2 hxy.symm)
  · show ¬ Valued.v (y - x) < Valued.v (y - x)
    exact lt_irrefl _

private theorem totallyDisconnectedSpace_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) : TotallyDisconnectedSpace X :=
  ⟨hf.isTotallyDisconnected (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem exists_isClopen_isCompact_mem_subset {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ IsCompact V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨K₁, hK₁, hxK₁, hK₁U⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVK⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := X)).exists_subset_of_mem_open hxK₁ isOpen_interior
  have hV' : IsClopen V := hV
  exact ⟨V, hV', hK₁.of_isClosed_subset hV'.1 (hVK.trans interior_subset), hxV,
    (hVK.trans interior_subset).trans hK₁U⟩

private theorem exists_clopen_refinement {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {ι : Type*} (t : Finset ι) (V : ι → Set X) (hV : ∀ j ∈ t, IsOpen (V j))
    {D : Set X} (hD : IsCompact D) (hDV : D ⊆ ⋃ j ∈ t, V j) :
    ∃ (n : ℕ) (W : Fin n → Set X) (idx : Fin n → ι), (∀ i, idx i ∈ t) ∧ (∀ i, IsClopen (W i)) ∧
      (∀ i, IsCompact (W i)) ∧ (∀ i, W i ⊆ V (idx i)) ∧ Pairwise (Function.onFun Disjoint W) ∧
      D ⊆ ⋃ i, W i := by
  classical
  have hch : ∀ d ∈ D, ∃ j ∈ t, ∃ O : Set X, IsClopen O ∧ IsCompact O ∧ d ∈ O ∧ O ⊆ V j := by
    intro d hd
    obtain ⟨j, hj, hdj⟩ := Set.mem_iUnion₂.1 (hDV hd)
    obtain ⟨O, hO, hOc, hdO, hOV⟩ := exists_isClopen_isCompact_mem_subset (hV j hj) hdj
    exact ⟨j, hj, O, hO, hOc, hdO, hOV⟩
  choose j hj O hO hOc hdO hOV using hch
  obtain ⟨s, hs⟩ := hD.elim_finite_subcover (fun d : D => O d.1 d.2) (fun d => (hO d.1 d.2).2)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hdO x hx⟩
  let e : Fin s.card → D := fun i => (s.equivFin.symm i).1
  refine ⟨s.card, disjointed fun i => O (e i).1 (e i).2, fun i => j (e i).1 (e i).2, fun i => hj _ _, fun i => ?_,
    fun i => ?_, fun i => ?_, disjoint_disjointed _, fun x hx => ?_⟩
  · rw [disjointed_eq_inter_compl]
    exact (hO _ _).inter (isClopen_iInter_of_finite fun k => isClopen_iInter_of_finite fun _ => (hO _ _).compl)
  · exact (hOc _ _).of_isClosed_subset
      (by
        rw [disjointed_eq_inter_compl]
        exact ((hO _ _).inter
          (isClopen_iInter_of_finite fun k => isClopen_iInter_of_finite fun _ => (hO _ _).compl)).1)
      (disjointed_subset _ i)
  · exact (disjointed_subset _ i).trans (hOV _ _)
  · rw [iUnion_disjointed]
    obtain ⟨d, hd, hxd⟩ := Set.mem_iUnion₂.1 (hs hx)
    refine Set.mem_iUnion.2 ⟨s.equivFin ⟨d, hd⟩, ?_⟩
    show x ∈ O (e (s.equivFin ⟨d, hd⟩)).1 (e (s.equivFin ⟨d, hd⟩)).2
    have he : e (s.equivFin ⟨d, hd⟩) = d := by
      show (s.equivFin.symm (s.equivFin ⟨d, hd⟩)).1 = d
      rw [Equiv.symm_apply_apply]
    rw [he]
    exact hxd

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private theorem totallyDisconnectedSpace_tensor : TotallyDisconnectedSpace (L ⊗[K] v.adicCompletion K) := by
  haveI : ∀ w : v.Extension (𝓞 L), TotallyDisconnectedSpace (w.1.adicCompletion L) := fun w => by
    haveI := totallySeparatedSpace_of_valued (F := w.1.adicCompletion L)
    infer_instance
  exact totallyDisconnectedSpace_of_isEmbedding (semiLocalHomeomorph K L v).isEmbedding

private theorem totallyDisconnectedSpace_tensorGL :
    TotallyDisconnectedSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  haveI := totallyDisconnectedSpace_tensor K L v
  haveI : TotallyDisconnectedSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin 2 → Fin 2 → L ⊗[K] v.adicCompletion K))
  haveI : TotallyDisconnectedSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))ᵐᵒᵖ :=
    totallyDisconnectedSpace_of_isEmbedding MulOpposite.opHomeomorph.symm.isEmbedding
  exact totallyDisconnectedSpace_of_isEmbedding Units.isEmbedding_embedProduct

private theorem exists_isOpen_pieces (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφv : IsSemiLocalTestFn K L v φv)
    (p : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K))
    (hp : Continuous p) (y₀ : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K))
    (P : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) → Prop) (hP : ∀ g, p g = y₀ → ∃ U ∈ nhds g, P U) :
    ∃ B : Set ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)), IsOpen B ∧ y₀ ∈ B ∧
      ∃ (n : ℕ) (U : Fin n → Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
        (φ : Fin n → GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        (∀ j, P (U j)) ∧ (∀ j, IsSemiLocalTestFn K L v (φ j)) ∧ (∀ j, tsupport (φ j) ⊆ U j) ∧
        (∀ j x, φ j x ≠ 0 → φv x ≠ 0) ∧ (∀ x, p x ∈ B → φv x = ∑ j, φ j x) := by
  classical
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  haveI := totallyDisconnectedSpace_tensor K L v
  haveI := totallyDisconnectedSpace_tensorGL K L v

  have hC₀ : IsCompact (tsupport φv ∩ p ⁻¹' {y₀}) := hφv.2.isCompact.inter_right (isClosed_singleton.preimage hp)
  choose U hU hPU using hP
  have hmem : ∀ d : ↥(tsupport φv ∩ p ⁻¹' {y₀}), p d.1 = y₀ := fun d => d.2.2
  obtain ⟨s, hs⟩ := hC₀.elim_finite_subcover
    (fun d : ↥(tsupport φv ∩ p ⁻¹' {y₀}) => interior (U d.1 (hmem d))) (fun _ => isOpen_interior)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x (hmem ⟨x, hx⟩))⟩

  have hR : IsCompact (tsupport φv \ ⋃ d ∈ s, interior (U d.1 (hmem d))) :=
    hφv.2.isCompact.diff (isOpen_biUnion fun d _ => isOpen_interior)
  have hy₀ : y₀ ∉ p '' (tsupport φv \ ⋃ d ∈ s, interior (U d.1 (hmem d))) := by
    rintro ⟨r, ⟨hr, hrn⟩, hpr⟩
    exact hrn (hs ⟨hr, hpr⟩)
  obtain ⟨B, hB, -, hy₀B, hBR⟩ :=
    exists_isClopen_isCompact_mem_subset (hR.image hp).isClosed.isOpen_compl (Set.mem_compl hy₀)

  have hDc : IsCompact (tsupport φv ∩ p ⁻¹' B) := hφv.2.isCompact.inter_right (hB.1.preimage hp)
  have hDV : tsupport φv ∩ p ⁻¹' B ⊆ ⋃ d ∈ s, interior (U d.1 (hmem d)) := by
    intro x hx
    by_contra hxn
    exact (hBR hx.2) ⟨x, ⟨hx.1, hxn⟩, rfl⟩
  obtain ⟨n, W, idx, -, hWclopen, -, hWU, hWdisj, hDW⟩ := exists_clopen_refinement s
    (fun d : ↥(tsupport φv ∩ p ⁻¹' {y₀}) => interior (U d.1 (hmem d))) (fun d _ => isOpen_interior) hDc hDV

  refine ⟨B, hB.2, hy₀B, n, fun i => U (idx i).1 (hmem (idx i)),
    fun i x => φv x * (W i).indicator (fun _ => (1 : ℂ)) x, fun i => hPU _ _, fun i => ?_, fun i => ?_,
    fun i x hx => left_ne_zero_of_mul hx, fun x hx => ?_⟩
  · exact ⟨hφv.1.mul (isLocallyConstant_indicator_one (hWclopen i).2 (hWclopen i).1), hφv.2.mul_right⟩
  · exact (tsupport_mul_subset_right.trans
      ((closure_mono Set.support_indicator_subset).trans (hWclopen i).1.closure_subset)).trans
      ((hWU i).trans interior_subset)
  · by_cases hφx : φv x = 0
    · simp [hφx]
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 (hDW ⟨subset_tsupport _ hφx, hx⟩)
      rw [← Finset.mul_sum, Finset.sum_eq_single i]
      · simp only [Set.indicator_of_mem hxi, mul_one]
      · intro k _ hki
        exact Set.indicator_of_notMem (fun hxk => (hWdisj hki).le_bot ⟨hxk, hxi⟩) _
      · exact fun h => absurd (Finset.mem_univ i) h

end Local
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end ClopenCover
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers IsSemiLocalTestFn isSemiLocalTestFn_zero semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn isTwistedSectionFnOn_zero Coupled isOrbitalIntegralOn_localHaar_iff IsTwistedOrbitalIntegral AreMatchingLocal mem_integralUnitsSet IsLocalTestFn localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocallyConstant_indicator_one localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff isRegularSemisimple_iff_ne_zero mem_sigmaCentralizer_iff exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString IsOrbitalIntegralOn.unique_of_isRegularSemisimple exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime"
p2m_open "AutomorphicForm"

namespace CentralTransfer

section PointTransfer

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

private theorem forall_exists_nhds_transfer_central_of_prime (hdeg : (Module.finrank K L).Prime)
    (hσ : σ ≠ 1) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K)) :
    ∀ (δ₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ¬ IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ₁) →
      ∃ U ∈ nhds δ₁, ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
        IsSemiLocalTestFn K L v φ → tsupport φ ⊆ U →
        ∃ f : GL (Fin 2) (v.adicCompletion K) → ℂ,
          IsLocalTestFn K v f ∧ AreMatchingLocal K L v σ φ f ∧ CentralClause K L σ v φ f := by
  intro δ₁ hδ₁
  obtain ⟨U, hU, h⟩ :=
    exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime K L hdeg σ
      hσ v hι δ₁ hδ₁
  refine ⟨U, hU, fun φ hφ hsupp => ?_⟩
  obtain ⟨f, hf, hmatch, hcent⟩ := h φ hφ hsupp
  refine ⟨f, hf, hmatch, fun c₁ δ y hy τ τ' hτ hτ' hcpl => ?_⟩
  obtain ⟨h1, -, h3⟩ := hcent c₁ δ y hy τ τ' hτ hτ' hcpl
  exact ⟨h1, h3⟩

end PointTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end CentralTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm.RegularOrbit P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀))
    (c : (v.adicCompletion K)ˣ)
    (hc : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀) :
    ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
      ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv ∧
        (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) →
            ∀ γ ∈ V, AutomorphicForm.IsRegularSemisimple γ →
            ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
              (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ y τ τ' →
              ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I' = I) ∧
          (∀ γ ∈ V, AutomorphicForm.IsRegularSemisimple γ →
            (¬ ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ) →
            ∀ τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I = 0)) ∧
        (∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y →
          ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₀)
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀)),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀) τ' →
            AutomorphicForm.Coupled K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y τ τ' →
            ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ₀ τ' φv I' →
              AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv I →
                I' = I) := by
  intro φv hφv
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  haveI : IsGalois K L := CentralTransfer.isGalois_of_finrank_prime K L hdeg σ hσ
  have hσn : σ ^ Module.finrank K L = 1 := CentralTransfer.pow_finrank_eq_one K L hdeg σ hσ
  have hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ) :=
    TwistedSection.continuous_sigmaGL K L (v.adicCompletion K) σ
  have hιc : Continuous (toTensorGL K L (v.adicCompletion K)) :=
    CoupledPartner.continuous_toTensorGL K L (v.adicCompletion K)
  exact CentralTransfer.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_cover K L σ v hσc hιc
    (CoupledPartner.normString_conj K L (v.adicCompletion K) σ)
    (TwistedSection.exists_isLocallyConstant_forall_isTwistedSectionFnOn K L σ v)
    (TwistedSection.isTwistedOrbitalIntegralOn_finset_sum K L σ v hσn)
    (RegularOrbit.exists_isLocallyConstant_forall_isSectionFn K v) (isOrbitalIntegral_eq_integral_of_isSectionFn K v)
    (integrable_conj_mul_ofReal K v) c (exists_integral_sectionFn_scalar_eq c)
    (ScalarTransfer.exists_isOrbitalIntegral_scalar K v c) δ₀ hδ₀ hc
    (CentralTransfer.forall_exists_nhds_transfer_central_of_prime K L σ v hdeg hσ hι) φv hφv
    (ClopenCover.exists_isOpen_pieces K L v φv hφv (CentralTransfer.normInvariants K L σ v)
      (CentralTransfer.continuous_normInvariants K L σ v hσc) (CentralTransfer.normInvariants K L σ v δ₀))

end S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime (solution)
