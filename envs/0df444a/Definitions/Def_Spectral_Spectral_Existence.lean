-- Prove2me | Definitions.Def_Spectral_Spectral_Existence
-- name    : Spectral_Spectral_Existence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:02:08.553801+00:00
-- url     : https://prove2.me/theorems/bdf3606d-d473-4b8c-a7d1-63ad86343fee
-- title:
--   Existence
-- statement:
--   Definitions and structural lemmas for Existence, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean

import Definitions.Def_Spectral_Cayley_Inverse
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus
import Definitions.Def_Spectral_Spectral_Polarization
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_boundedSesquilinearFormOfQuadratic_apply_self
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
def realToComplexContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun z := f z
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous
@[simp]
theorem realToComplexContinuousMap_apply {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) (z : X) :
    realToComplexContinuousMap f z = (f z : ℂ) := rfl
@[simp]
theorem realToComplexContinuousMap_add {X : Type*} [TopologicalSpace X]
    (f g : C_c(X, ℝ)) :
    realToComplexContinuousMap (f + g) =
      realToComplexContinuousMap f + realToComplexContinuousMap g := by
  ext z
  exact Complex.ofReal_add (f z) (g z)
@[simp]
theorem realToComplexContinuousMap_smul {X : Type*} [TopologicalSpace X]
    (c : ℝ) (f : C_c(X, ℝ)) :
    realToComplexContinuousMap (c • f) =
      (c : ℂ) • realToComplexContinuousMap f := by
  ext z
  exact Complex.ofReal_mul c (f z)
def compactlySupportedContinuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℝ)) : C_c(X, ℝ) where
  toFun := f
  hasCompactSupport' := HasCompactSupport.of_compactSpace f
noncomputable def normalCfcQuadraticLinearMap
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    C_c(spectrum ℂ U, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (@inner ℂ E _ x
    ((cfcHom hU) (realToComplexContinuousMap f) x)).re
  map_add' f g := by
    rw [realToComplexContinuousMap_add, map_add, add_apply,
      inner_add_right, Complex.add_re]
  map_smul' c f := by
    rw [realToComplexContinuousMap_smul, map_smul, smul_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rfl
noncomputable def realSqrtContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun z := Real.sqrt (f z)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp f.continuous)
theorem realToComplexContinuousMap_eq_star_mul_self
    {X : Type*} [TopologicalSpace X] (f : C_c(X, ℝ)) (hf : 0 ≤ f) :
    realToComplexContinuousMap f =
      star (realSqrtContinuousMap f) * realSqrtContinuousMap f := by
  ext z
  change (f z : ℂ) = star (Real.sqrt (f z) : ℂ) * Real.sqrt (f z)
  rw [Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (hf z)]
theorem normalCfcQuadraticLinearMap_nonneg
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C_c(spectrum ℂ U, ℝ)) (hf : 0 ≤ f) :
    0 ≤ normalCfcQuadraticLinearMap U hU x f := by
  let q := realSqrtContinuousMap f
  have hmap : (cfcHom hU) (realToComplexContinuousMap f) =
      star ((cfcHom hU) q) * (cfcHom hU) q := by
    rw [realToComplexContinuousMap_eq_star_mul_self f hf, map_mul, map_star]
  have hpos : (0 : E →L[ℂ] E) ≤
      star ((cfcHom hU) q) * (cfcHom hU) q :=
    star_mul_self_nonneg ((cfcHom hU) q)
  have hpositive : ContinuousLinearMap.IsPositive
      (star ((cfcHom hU) q) * (cfcHom hU) q) :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos
  change 0 ≤ (@inner ℂ E _ x
    ((cfcHom hU) (realToComplexContinuousMap f) x)).re
  rw [hmap]
  exact hpositive.re_inner_nonneg_right x
noncomputable def normalCfcQuadraticFunctional
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    C_c(spectrum ℂ U, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (normalCfcQuadraticLinearMap U hU x)
    (normalCfcQuadraticLinearMap_nonneg U hU x)
noncomputable def normalCfcScalarMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    Measure (spectrum ℂ U) :=
  RealRMK.rieszMeasure (normalCfcQuadraticFunctional U hU x)
noncomputable instance normalCfcScalarMeasure_isFiniteMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    IsFiniteMeasure (normalCfcScalarMeasure U hU x) := by
  unfold normalCfcScalarMeasure
  infer_instance
theorem integral_normalCfcScalarMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C_c(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      (@inner ℂ E _ x ((cfcHom hU)
        (realToComplexContinuousMap f) x)).re := by
  exact RealRMK.integral_rieszMeasure
    (normalCfcQuadraticFunctional U hU x) f
noncomputable def continuousMapRealPart {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℂ)) : C_c(X, ℝ) where
  toFun z := (f z).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _
noncomputable def continuousMapImagPart {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℂ)) : C_c(X, ℝ) where
  toFun z := (f z).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _
noncomputable def continuousMapOfRealPart {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℂ) where
  toFun z := ((f z).re : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp f.continuous)
noncomputable def continuousMapOfImagPart {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℂ) where
  toFun z := ((f z).im : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp f.continuous)
noncomputable def normalCfcRealOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) : E →L[ℂ] E :=
  (cfcHom hU) (realToComplexContinuousMap (compactlySupportedContinuousMap f))
theorem integral_normalCfcScalarMeasure_continuous
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      (@inner ℂ E _ x (normalCfcRealOperator U hU f x)).re := by
  exact integral_normalCfcScalarMeasure U hU x (compactlySupportedContinuousMap f)
theorem normalCfcRealOperator_isPositive
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) (hf : ∀ z, 0 ≤ f z) :
    ContinuousLinearMap.IsPositive (normalCfcRealOperator U hU f) := by
  let fs : C_c(spectrum ℂ U, ℝ) := compactlySupportedContinuousMap f
  let q := realSqrtContinuousMap fs
  have hfs : 0 ≤ fs := fun z => hf z
  have hmap : normalCfcRealOperator U hU f =
      star ((cfcHom hU) q) * (cfcHom hU) q := by
    unfold normalCfcRealOperator
    rw [realToComplexContinuousMap_eq_star_mul_self fs hfs, map_mul, map_star]
  rw [hmap]
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  exact star_mul_self_nonneg ((cfcHom hU) q)
theorem normalCfcRealOperator_le_one
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) (hf : ∀ z, f z ≤ 1) :
    normalCfcRealOperator U hU f ≤ 1 := by
  let g : C(spectrum ℂ U, ℝ) := 1 - f
  have hg : ∀ z, 0 ≤ g z := fun z => sub_nonneg.mpr (hf z)
  have hmap : realToComplexContinuousMap (compactlySupportedContinuousMap g) =
      1 - realToComplexContinuousMap (compactlySupportedContinuousMap f) := by
    ext z
    change ((1 - f z : ℝ) : ℂ) = 1 - (f z : ℂ)
    push_cast
    rfl
  have hop : normalCfcRealOperator U hU g = 1 - normalCfcRealOperator U hU f := by
    unfold normalCfcRealOperator
    rw [hmap, map_sub, map_one]
  rw [← sub_nonneg, ← hop]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (normalCfcRealOperator_isPositive U hU g hg)
theorem normalCfcRealOperator_mul
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f g : C(spectrum ℂ U, ℝ)) :
    normalCfcRealOperator U hU f * normalCfcRealOperator U hU g =
      normalCfcRealOperator U hU (f * g) := by
  unfold normalCfcRealOperator
  rw [← map_mul]
  congr 1
  ext z
  change (f z : ℂ) * (g z : ℂ) = ((f z * g z : ℝ) : ℂ)
  exact (Complex.ofReal_mul (f z) (g z)).symm
theorem measureReal_le_integral_of_eq_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    {S : Set X} (hS : MeasurableSet S) (f : C(X, ℝ))
    (hf : ∀ z, 0 ≤ f z) (hfS : Set.EqOn f 1 S) :
    mu.real S ≤ ∫ z, f z ∂mu := by
  calc
    mu.real S = ∫ z, S.indicator (1 : X → ℝ) z ∂mu :=
      (integral_indicator_one hS).symm
    _ ≤ ∫ z, f z ∂mu := by
      refine integral_mono ((integrable_const 1).indicator hS)
        (compactlySupportedContinuousMap f).integrable ?_
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, hfS hz]
      · rw [Set.indicator_of_notMem hz]
        exact hf z
theorem norm_sq_apply_le_re_inner_of_nonneg_of_le_one
    (D : E →L[ℂ] E) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (x : E) :
    ‖D x‖ ^ 2 ≤ (@inner ℂ E _ (D x) x).re := by
  have hDpos : ContinuousLinearMap.IsPositive D :=
    (ContinuousLinearMap.nonneg_iff_isPositive D).mp hD0
  have h1D : 0 ≤ 1 - D := sub_nonneg.mpr hD1
  have hcomm : Commute D (1 - D) := (Commute.one_right D).sub_right rfl
  have hprod : 0 ≤ D * (1 - D) := Commute.mul_nonneg hD0 h1D hcomm
  have hsq : D * D ≤ D := by
    rw [← sub_nonneg]
    convert hprod using 1
    · noncomm_ring
  have hdiffpos : ContinuousLinearMap.IsPositive (D - D * D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive (D - D * D)).mp (sub_nonneg.mpr hsq)
  have hq := hdiffpos.re_inner_nonneg_left x
  rw [sub_apply, mul_apply_eq_comp, inner_sub_left] at hq
  change 0 ≤ (@inner ℂ E _ (D x) x).re -
    (@inner ℂ E _ (D (D x)) x).re at hq
  have hnorm : (@inner ℂ E _ (D (D x)) x).re = ‖D x‖ ^ 2 := by
    rw [hDpos.inner_left_eq_inner_right (D x) x, inner_self_eq_norm_sq_to_K]
    calc
      (((‖D x‖ : ℂ) ^ 2).re) = (((‖D x‖ ^ 2 : ℝ) : ℂ).re) :=
        congrArg Complex.re (Complex.ofReal_pow ‖D x‖ 2).symm
      _ = ‖D x‖ ^ 2 := Complex.ofReal_re _
  rw [hnorm] at hq
  linarith
noncomputable def closedSetApprox
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ) : C(X, ℝ) where
  toFun z := max 0 (1 - (n : ℝ) * Metric.infDist z K)
  continuous_toFun := continuous_const.max
    (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt K)))
omit [CompleteSpace E] in
theorem closedSetApprox_mem_Icc
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ) (z : X) :
    closedSetApprox K n z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · apply max_le zero_le_one
    have hmul : 0 ≤ (n : ℝ) * Metric.infDist z K :=
      mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg
    linarith
omit [CompleteSpace E] in
theorem closedSetApprox_eq_one
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ)
    {z : X} (hz : z ∈ K) : closedSetApprox K n z = 1 := by
  rw [closedSetApprox, ContinuousMap.coe_mk, Metric.infDist_zero_of_mem hz,
    mul_zero, sub_zero, max_eq_right zero_le_one]
omit [CompleteSpace E] in
theorem tendsto_closedSetApprox
    {X : Type*} [PseudoMetricSpace X] (K : Set X)
    (hK : IsClosed K) (hKne : K.Nonempty) (z : X) :
    Filter.Tendsto (fun n => closedSetApprox K n z) Filter.atTop
      (nhds (K.indicator (fun _ => (1 : ℝ)) z)) := by
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]
    exact tendsto_const_nhds.congr'
      (Filter.Eventually.of_forall fun n => (closedSetApprox_eq_one K n hz).symm)
  · rw [Set.indicator_of_notMem hz]
    have hd : 0 < Metric.infDist z K := (hK.notMem_iff_infDist_pos hKne).mp hz
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Metric.infDist z K)⁻¹
    have hNd : 1 < (N : ℝ) * Metric.infDist z K := by
      rw [← div_lt_iff₀ hd, one_div]
      exact hN
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hmul : (N : ℝ) * Metric.infDist z K ≤
        (n : ℝ) * Metric.infDist z K :=
      mul_le_mul_of_nonneg_right hcast hd.le
    rw [closedSetApprox, ContinuousMap.coe_mk, max_eq_left]
    linarith
omit [CompleteSpace E] in
theorem tendsto_integral_closedSetApprox
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (K : Set X) (hK : IsClosed K) (hKne : K.Nonempty)
    (mu : Measure X) [IsFiniteMeasure mu] :
    Filter.Tendsto (fun n => ∫ z, closedSetApprox K n z ∂mu) Filter.atTop
      (nhds (mu.real K)) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := mu) (fun _ => (1 : ℝ))
    (fun n => (closedSetApprox K n).continuous.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all mu fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (closedSetApprox_mem_Icc K n z).1]
      exact (closedSetApprox_mem_Icc K n z).2)
    (ae_of_all mu (tendsto_closedSetApprox K hK hKne))
  change Filter.Tendsto (fun n => ∫ z, closedSetApprox K n z ∂mu) Filter.atTop
    (nhds (∫ z, K.indicator (1 : X → ℝ) z ∂mu)) at hlim
  rw [integral_indicator_one hK.measurableSet] at hlim
  exact hlim
omit [CompleteSpace E] in
theorem tendsto_integral_closedSetApprox_mul_self
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (K : Set X) (hK : IsClosed K) (hKne : K.Nonempty)
    (mu : Measure X) [IsFiniteMeasure mu] :
    Filter.Tendsto
      (fun n => ∫ z, (closedSetApprox K n * closedSetApprox K n) z ∂mu)
      Filter.atTop (nhds (mu.real K)) := by
  refine Filter.Tendsto.squeeze
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => mu.real K)
      Filter.atTop (nhds (mu.real K)))
    (tendsto_integral_closedSetApprox K hK hKne mu) ?_ ?_
  · intro n
    exact measureReal_le_integral_of_eq_one mu hK.measurableSet
      (closedSetApprox K n * closedSetApprox K n)
      (fun z => mul_nonneg (closedSetApprox_mem_Icc K n z).1
        (closedSetApprox_mem_Icc K n z).1)
      (fun z hz => by
        change closedSetApprox K n z * closedSetApprox K n z = (1 : ℝ)
        rw [closedSetApprox_eq_one K n hz, mul_one])
  · intro n
    refine integral_mono
      (compactlySupportedContinuousMap
        (closedSetApprox K n * closedSetApprox K n)).integrable
      (compactlySupportedContinuousMap (closedSetApprox K n)).integrable ?_
    intro z
    obtain ⟨hz0, hz1⟩ := closedSetApprox_mem_Icc K n z
    change closedSetApprox K n z * closedSetApprox K n z ≤
      closedSetApprox K n z
    nlinarith only [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
omit [CompleteSpace E] in
theorem exists_isClosed_measureReal_sdiff_lt
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [mu.Regular] [IsFiniteMeasure mu]
    {S : Set X} (hS : MeasurableSet S) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : Set X, K ⊆ S ∧ IsClosed K ∧ mu.real (S \ K) < eps := by
  let epsE : ENNReal := ENNReal.ofReal eps
  have hepsE : epsE ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr heps
  obtain ⟨K, hKS, hKclosed, hdiff⟩ :=
    hS.exists_isClosed_sdiff_lt (measure_ne_top mu S) hepsE
  refine ⟨K, hKS, hKclosed, ?_⟩
  have hreal := (ENNReal.toReal_lt_toReal
    (measure_ne_top mu (S \ K)) ENNReal.ofReal_ne_top).mpr hdiff
  rw [ENNReal.toReal_ofReal heps.le] at hreal
  exact hreal
def compactlySupportedOne (X : Type*) [TopologicalSpace X]
    [CompactSpace X] : C_c(X, ℝ) where
  toFun := 1
  hasCompactSupport' := HasCompactSupport.of_compactSpace 1
@[simp]
theorem compactlySupportedOne_apply (X : Type*) [TopologicalSpace X]
    [CompactSpace X] (z : X) : compactlySupportedOne X z = 1 := rfl
theorem realToComplexContinuousMap_one
    (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    realToComplexContinuousMap (compactlySupportedOne X) = 1 := by
  ext z
  rfl
theorem normalCfcScalarMeasure_real_univ
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    (normalCfcScalarMeasure U hU x).real Set.univ = ‖x‖ ^ 2 := by
  let one : C_c(spectrum ℂ U, ℝ) := compactlySupportedOne (spectrum ℂ U)
  calc
    (normalCfcScalarMeasure U hU x).real Set.univ =
        ∫ _z, (1 : ℝ) ∂(normalCfcScalarMeasure U hU x) := by
          rw [integral_const, smul_eq_mul, mul_one]
    _ = ∫ z, one z ∂(normalCfcScalarMeasure U hU x) := by rfl
    _ = (@inner ℂ E _ x ((cfcHom hU)
        (realToComplexContinuousMap one) x)).re :=
      integral_normalCfcScalarMeasure U hU x one
    _ = (@inner ℂ E _ x x).re := by
      rw [show realToComplexContinuousMap one = 1 from
        realToComplexContinuousMap_one (spectrum ℂ U), map_one, one_apply_eq_self]
    _ = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]
      norm_num [Complex.ofReal]
      ring
theorem normalCfcScalarMeasure_real_le_norm_sq
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (S : Set (spectrum ℂ U)) :
    (normalCfcScalarMeasure U hU x).real S ≤ ‖x‖ ^ 2 := by
  rw [← normalCfcScalarMeasure_real_univ U hU x]
  exact measureReal_mono (Set.subset_univ S)
theorem normalCfcScalarMeasure_smul
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (c : ℂ) (x : E) :
    normalCfcScalarMeasure U hU (c • x) =
      ENNReal.ofReal (‖c‖ ^ 2) • normalCfcScalarMeasure U hU x := by
  let k : ENNReal := ENNReal.ofReal (‖c‖ ^ 2)
  have hk : k ≠ ⊤ := ENNReal.ofReal_ne_top
  let _ : (k • normalCfcScalarMeasure U hU x).Regular :=
    Measure.Regular.smul hk
  change normalCfcScalarMeasure U hU (c • x) =
    k • normalCfcScalarMeasure U hU x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_normalCfcScalarMeasure, integral_smul_measure,
    integral_normalCfcScalarMeasure, ENNReal.toReal_ofReal (sq_nonneg ‖c‖),
    smul_eq_mul]
  change (@inner ℂ E _ (c • x)
    ((cfcHom hU) (realToComplexContinuousMap f) (c • x))).re = _
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul, Complex.mul_re]
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  norm_num [Complex.ofReal]
theorem normalCfcScalarMeasure_parallelogram
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x y : E) :
    normalCfcScalarMeasure U hU (x + y) +
        normalCfcScalarMeasure U hU (x - y) =
      (normalCfcScalarMeasure U hU x + normalCfcScalarMeasure U hU x) +
        (normalCfcScalarMeasure U hU y + normalCfcScalarMeasure U hU y) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hxyAdd : Integrable f (normalCfcScalarMeasure U hU (x + y)) := f.integrable
  have hxySub : Integrable f (normalCfcScalarMeasure U hU (x - y)) := f.integrable
  have hx : Integrable f (normalCfcScalarMeasure U hU x) := f.integrable
  have hy : Integrable f (normalCfcScalarMeasure U hU y) := f.integrable
  rw [integral_add_measure hxyAdd hxySub,
    integral_add_measure (hx.add_measure hx) (hy.add_measure hy),
    integral_add_measure hx hx, integral_add_measure hy hy,
    integral_normalCfcScalarMeasure, integral_normalCfcScalarMeasure,
    integral_normalCfcScalarMeasure, integral_normalCfcScalarMeasure]
  let T : E →L[ℂ] E := (cfcHom hU) (realToComplexContinuousMap f)
  change (@inner ℂ E _ (x + y) (T (x + y))).re +
      (@inner ℂ E _ (x - y) (T (x - y))).re =
    (@inner ℂ E _ x (T x)).re + (@inner ℂ E _ x (T x)).re +
      ((@inner ℂ E _ y (T y)).re + (@inner ℂ E _ y (T y)).re)
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, Complex.add_re, Complex.sub_re]
  ring
noncomputable def normalCfcScalarContent
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) : ℝ :=
  (normalCfcScalarMeasure U hU x).real S
theorem normalCfcScalarContent_smul
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (c : ℂ) (x : E) :
    normalCfcScalarContent U hU S (c • x) =
      ‖c‖ ^ 2 * normalCfcScalarContent U hU S x := by
  unfold normalCfcScalarContent
  rw [normalCfcScalarMeasure_smul, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (sq_nonneg ‖c‖)]
theorem normalCfcScalarContent_parallelogram
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x y : E) :
    normalCfcScalarContent U hU S (x + y) +
        normalCfcScalarContent U hU S (x - y) =
      (normalCfcScalarContent U hU S x + normalCfcScalarContent U hU S x) +
        (normalCfcScalarContent U hU S y + normalCfcScalarContent U hU S y) := by
  have h := congrArg (fun μ : Measure (spectrum ℂ U) => μ.real S)
    (normalCfcScalarMeasure_parallelogram U hU x y)
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply,
    measureReal_add_apply] at h
  exact h
theorem normalCfcScalarContent_nonneg
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    0 ≤ normalCfcScalarContent U hU S x :=
  measureReal_nonneg
theorem normalCfcScalarContent_le_norm_sq
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    normalCfcScalarContent U hU S x ≤ ‖x‖ ^ 2 :=
  normalCfcScalarMeasure_real_le_norm_sq U hU x S
noncomputable def normalCfcSesquilinearForm
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  boundedSesquilinearFormOfQuadratic
    (normalCfcScalarContent U hU S)
    (normalCfcScalarContent_smul U hU S)
    (normalCfcScalarContent_parallelogram U hU S)
    (normalCfcScalarContent_nonneg U hU S)
    (normalCfcScalarContent_le_norm_sq U hU S)
theorem normalCfcSesquilinearForm_apply_self
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    normalCfcSesquilinearForm U hU S x x =
      (normalCfcScalarMeasure U hU x).real S := by
  exact boundedSesquilinearFormOfQuadratic_apply_self
    (normalCfcScalarContent U hU S)
    (normalCfcScalarContent_smul U hU S)
    (normalCfcScalarContent_parallelogram U hU S)
    (normalCfcScalarContent_nonneg U hU S)
    (normalCfcScalarContent_le_norm_sq U hU S) x
noncomputable def normalCfcOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) : E →L[ℂ] E :=
  InnerProductSpace.continuousLinearMapOfBilin
    (normalCfcSesquilinearForm U hU S)
theorem inner_normalCfcOperator_self
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    @inner ℂ E _ (normalCfcOperator U hU S x) x =
      (normalCfcScalarMeasure U hU x).real S := by
  rw [normalCfcOperator, InnerProductSpace.continuousLinearMapOfBilin_apply,
    normalCfcSesquilinearForm_apply_self]
omit [CompleteSpace E] in
theorem continuousLinearMap_eq_of_inner_self_eq
    (T S : E →L[ℂ] E)
    (h : ∀ x : E, @inner ℂ E _ (T x) x = @inner ℂ E _ (S x) x) :
    T = S := by
  have hzero : (T.toLinearMap - S.toLinearMap) = 0 := by
    apply (inner_map_self_eq_zero (T.toLinearMap - S.toLinearMap)).mp
    intro x
    rw [LinearMap.sub_apply, inner_sub_left]
    change @inner ℂ E _ (T x) x - @inner ℂ E _ (S x) x = 0
    rw [h, sub_self]
  rw [sub_eq_zero] at hzero
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hzero x
theorem normalCfcOperator_isPositive
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) :
    ContinuousLinearMap.IsPositive (normalCfcOperator U hU S) := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff
    (normalCfcOperator U hU S)).mp
  rw [LinearMap.isPositive_iff_complex]
  intro x
  have hx : @inner ℂ E _ (normalCfcOperator U hU S x) x =
      ((normalCfcScalarMeasure U hU x).real S : ℂ) :=
    inner_normalCfcOperator_self U hU S x
  change ((@inner ℂ E _ (normalCfcOperator U hU S x) x).re : ℂ) =
      @inner ℂ E _ (normalCfcOperator U hU S x) x ∧
    0 ≤ (@inner ℂ E _ (normalCfcOperator U hU S x) x).re
  rw [hx]
  constructor
  · norm_num
  · exact measureReal_nonneg
theorem normalCfcOperator_isSelfAdjoint
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) :
    IsSelfAdjoint (normalCfcOperator U hU S) :=
  (normalCfcOperator_isPositive U hU S).isSelfAdjoint
theorem normalCfcOperator_mono
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S T : Set (spectrum ℂ U)} (hST : S ⊆ T) :
    normalCfcOperator U hU S ≤ normalCfcOperator U hU T := by
  change ContinuousLinearMap.IsPositive
    (normalCfcOperator U hU T - normalCfcOperator U hU S)
  constructor
  · exact (normalCfcOperator_isPositive U hU T).isSymmetric.sub
      (normalCfcOperator_isPositive U hU S).isSymmetric
  · intro x
    change 0 ≤ (@inner ℂ E _
      ((normalCfcOperator U hU T - normalCfcOperator U hU S) x) x).re
    rw [sub_apply, inner_sub_left, inner_normalCfcOperator_self,
      inner_normalCfcOperator_self]
    exact sub_nonneg.mpr (measureReal_mono hST)
theorem normalCfcOperator_le_one
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) :
    normalCfcOperator U hU S ≤ 1 := by
  change ContinuousLinearMap.IsPositive (1 - normalCfcOperator U hU S)
  constructor
  · exact ContinuousLinearMap.isPositive_one.isSymmetric.sub
      (normalCfcOperator_isPositive U hU S).isSymmetric
  · intro x
    change 0 ≤ (@inner ℂ E _
      ((1 - normalCfcOperator U hU S) x) x).re
    rw [sub_apply, one_apply_eq_self, inner_sub_left,
      inner_normalCfcOperator_self, inner_self_eq_norm_sq_to_K]
    rw [Complex.sub_re, Complex.ofReal_re]
    convert sub_nonneg.mpr
      (normalCfcScalarMeasure_real_le_norm_sq U hU x S) using 1
    rw [pow_two, Complex.mul_re]
    norm_num [Complex.ofReal]
    rw [pow_two]
theorem mul_projection_eq_of_projection_le_contraction
    (Q P : E →L[ℂ] E)
    (hQid : IsIdempotentElem Q) (hQself : IsSelfAdjoint Q)
    (hP1 : P ≤ 1) (hQP : Q ≤ P) :
    P * Q = Q := by
  have hQstar : IsStarProjection Q := ⟨hQid, hQself⟩
  have hfix := hQstar.one_sub.mul_right_and_mul_left_of_nonneg_of_le
    (sub_nonneg.mpr hP1) (sub_le_sub_left hQP 1)
  have h := hfix.1
  linear_combination (norm := noncomm_ring) h
theorem normalCfcOperator_le_realOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (f : C(spectrum ℂ U, ℝ)) (hf : ∀ z, 0 ≤ f z)
    (hfS : Set.EqOn f 1 S) :
    normalCfcOperator U hU S ≤ normalCfcRealOperator U hU f := by
  have hphi := normalCfcRealOperator_isPositive U hU f hf
  change ContinuousLinearMap.IsPositive
    (normalCfcRealOperator U hU f - normalCfcOperator U hU S)
  constructor
  · exact hphi.isSymmetric.sub (normalCfcOperator_isPositive U hU S).isSymmetric
  · intro x
    change 0 ≤ (@inner ℂ E _
      ((normalCfcRealOperator U hU f - normalCfcOperator U hU S) x) x).re
    rw [sub_apply, inner_sub_left]
    change 0 ≤ (@inner ℂ E _ (normalCfcRealOperator U hU f x) x).re -
      (@inner ℂ E _ (normalCfcOperator U hU S x) x).re
    rw [inner_normalCfcOperator_self]
    rw [hphi.inner_left_eq_inner_right x x]
    rw [← integral_normalCfcScalarMeasure_continuous]
    exact sub_nonneg.mpr (measureReal_le_integral_of_eq_one
      (normalCfcScalarMeasure U hU x) hS f hf hfS)
theorem tendsto_normalCfcRealOperator_of_integral
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (hS : MeasurableSet S)
    (f : ℕ → C(spectrum ℂ U, ℝ))
    (hf0 : ∀ n z, 0 ≤ f n z) (hf1 : ∀ n z, f n z ≤ 1)
    (hfS : ∀ n, Set.EqOn (f n) 1 S) (x : E)
    (hint : Filter.Tendsto
      (fun n => ∫ z, f n z ∂(normalCfcScalarMeasure U hU x))
      Filter.atTop (nhds ((normalCfcScalarMeasure U hU x).real S))) :
    Filter.Tendsto (fun n => normalCfcRealOperator U hU (f n) x)
      Filter.atTop (nhds (normalCfcOperator U hU S x)) := by
  let phi : ℕ → E →L[ℂ] E := fun n => normalCfcRealOperator U hU (f n)
  let P : E →L[ℂ] E := normalCfcOperator U hU S
  have hD0 (n : ℕ) : 0 ≤ phi n - P := by
    exact sub_nonneg.mpr
      (normalCfcOperator_le_realOperator U hU hS (f n) (hf0 n) (hfS n))
  have hD1 (n : ℕ) : phi n - P ≤ 1 := by
    calc
      phi n - P ≤ phi n := sub_le_self _
        ((ContinuousLinearMap.nonneg_iff_isPositive P).mpr
          (normalCfcOperator_isPositive U hU S))
      _ ≤ 1 := normalCfcRealOperator_le_one U hU (f n) (hf1 n)
  have hgap : Filter.Tendsto
      (fun n => ∫ z, f n z ∂(normalCfcScalarMeasure U hU x) -
        (normalCfcScalarMeasure U hU x).real S)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using
      hint.sub (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (normalCfcScalarMeasure U hU x).real S)
        Filter.atTop (nhds ((normalCfcScalarMeasure U hU x).real S)))
  have hsqrt : Filter.Tendsto
      (fun n => Real.sqrt
        ((∫ z, f n z ∂(normalCfcScalarMeasure U hU x)) -
          (normalCfcScalarMeasure U hU x).real S))
      Filter.atTop (nhds 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hgap
    change Filter.Tendsto
      (fun n => Real.sqrt
        ((∫ z, f n z ∂(normalCfcScalarMeasure U hU x)) -
          (normalCfcScalarMeasure U hU x).real S))
      Filter.atTop (nhds (Real.sqrt 0)) at hs
    rw [Real.sqrt_zero] at hs
    exact hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ hsqrt
  intro n
  have hbound := norm_sq_apply_le_re_inner_of_nonneg_of_le_one
    (phi n - P) (hD0 n) (hD1 n) x
  rw [sub_apply, inner_sub_left] at hbound
  change ‖phi n x - P x‖ ^ 2 ≤
    (@inner ℂ E _ (phi n x) x).re - (@inner ℂ E _ (P x) x).re at hbound
  rw [show (@inner ℂ E _ (phi n x) x).re =
      ∫ z, f n z ∂(normalCfcScalarMeasure U hU x) by
        rw [(normalCfcRealOperator_isPositive U hU (f n) (hf0 n)).inner_left_eq_inner_right x x]
        exact (integral_normalCfcScalarMeasure_continuous U hU x (f n)).symm,
    show (@inner ℂ E _ (P x) x).re =
      (normalCfcScalarMeasure U hU x).real S by
        rw [inner_normalCfcOperator_self, Complex.ofReal_re]] at hbound
  exact Real.le_sqrt_of_sq_le hbound
theorem tendsto_normalCfcRealOperator_closedSetApprox
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (K : Set (spectrum ℂ U)) (hK : IsClosed K) (hKne : K.Nonempty)
    (x : E) :
    Filter.Tendsto
      (fun n => normalCfcRealOperator U hU (closedSetApprox K n) x)
      Filter.atTop (nhds (normalCfcOperator U hU K x)) := by
  exact tendsto_normalCfcRealOperator_of_integral U hU K hK.measurableSet
    (closedSetApprox K) (fun n z => (closedSetApprox_mem_Icc K n z).1)
    (fun n z => (closedSetApprox_mem_Icc K n z).2)
    (fun n z hz => closedSetApprox_eq_one K n hz) x
    (tendsto_integral_closedSetApprox K hK hKne (normalCfcScalarMeasure U hU x))
theorem normalCfcOperator_isIdempotent_of_isClosed
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (K : Set (spectrum ℂ U)) (hK : IsClosed K) :
    IsIdempotentElem (normalCfcOperator U hU K) := by
  by_cases hKne : K.Nonempty
  · let phi : ℕ → E →L[ℂ] E := fun n =>
      normalCfcRealOperator U hU (closedSetApprox K n)
    let P : E →L[ℂ] E := normalCfcOperator U hU K
    change P * P = P
    apply ContinuousLinearMap.ext
    intro x
    have hphi (y : E) : Filter.Tendsto (fun n => phi n y)
        Filter.atTop (nhds (P y)) := by
      exact tendsto_normalCfcRealOperator_closedSetApprox U hU K hK hKne y
    have hphi0 (n : ℕ) : 0 ≤ phi n := by
      exact (ContinuousLinearMap.nonneg_iff_isPositive (phi n)).mpr
        (normalCfcRealOperator_isPositive U hU (closedSetApprox K n)
          (fun z => (closedSetApprox_mem_Icc K n z).1))
    have hphi1 (n : ℕ) : phi n ≤ 1 := by
      exact normalCfcRealOperator_le_one U hU (closedSetApprox K n)
        (fun z => (closedSetApprox_mem_Icc K n z).2)
    have hphiNorm (n : ℕ) : ‖phi n‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg (phi n) (hphi0 n)).mpr (hphi1 n)
    have hfirst : Filter.Tendsto
        (fun n => phi n (phi n x - P x)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_iff_norm_sub_tendsto_zero.mp (hphi x))
      calc
        ‖phi n (phi n x - P x)‖ ≤ ‖phi n‖ * ‖phi n x - P x‖ :=
          (phi n).le_opNorm _
        _ ≤ 1 * ‖phi n x - P x‖ :=
          mul_le_mul_of_nonneg_right (hphiNorm n) (norm_nonneg _)
        _ = ‖phi n x - P x‖ := one_mul _
    have hsecond : Filter.Tendsto
        (fun n => phi n (P x) - P (P x)) Filter.atTop (nhds 0) := by
      simpa only [sub_self] using
        (hphi (P x)).sub (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ => P (P x)) Filter.atTop (nhds (P (P x))))
    have hdiff : Filter.Tendsto
        (fun n => (phi n * phi n) x - (P * P) x)
        Filter.atTop (nhds 0) := by
      have hsum : Filter.Tendsto
          (fun n => phi n (phi n x - P x) + (phi n (P x) - P (P x)))
          Filter.atTop (nhds 0) := by
        simpa only [add_zero] using hfirst.add hsecond
      refine hsum.congr'
        (Filter.Eventually.of_forall fun n => ?_)
      change phi n (phi n x - P x) + (phi n (P x) - P (P x)) =
        phi n (phi n x) - P (P x)
      rw [map_sub]
      abel
    have hmulToPSq : Filter.Tendsto (fun n => (phi n * phi n) x)
        Filter.atTop (nhds ((P * P) x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hnorm := (continuous_norm.tendsto 0).comp hdiff
      change Filter.Tendsto
        (fun n => ‖(phi n * phi n) x - (P * P) x‖)
        Filter.atTop (nhds ‖(0 : E)‖) at hnorm
      simpa only [norm_zero] using hnorm
    have hsquareToP : Filter.Tendsto
        (fun n => normalCfcRealOperator U hU
          (closedSetApprox K n * closedSetApprox K n) x)
        Filter.atTop (nhds (P x)) := by
      exact tendsto_normalCfcRealOperator_of_integral U hU K hK.measurableSet
        (fun n => closedSetApprox K n * closedSetApprox K n)
        (fun n z => mul_nonneg (closedSetApprox_mem_Icc K n z).1
          (closedSetApprox_mem_Icc K n z).1)
        (fun n z => by
          obtain ⟨hz0, hz1⟩ := closedSetApprox_mem_Icc K n z
          change closedSetApprox K n z * closedSetApprox K n z ≤ 1
          nlinarith only [mul_nonneg hz0 (sub_nonneg.mpr hz1), hz1])
        (fun n z hz => by
          change closedSetApprox K n z * closedSetApprox K n z = (1 : ℝ)
          rw [closedSetApprox_eq_one K n hz, mul_one]) x
        (tendsto_integral_closedSetApprox_mul_self K hK hKne
          (normalCfcScalarMeasure U hU x))
    have hmulToP : Filter.Tendsto (fun n => (phi n * phi n) x)
        Filter.atTop (nhds (P x)) := by
      simpa only [phi, normalCfcRealOperator_mul] using hsquareToP
    exact tendsto_nhds_unique hmulToPSq hmulToP
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    subst K
    have hzero : normalCfcOperator U hU ∅ = 0 := by
      apply continuousLinearMap_eq_of_inner_self_eq
      intro x
      rw [inner_normalCfcOperator_self, measureReal_empty,
        zero_apply, inner_zero_left]
      rfl
    rw [hzero]
    exact IsIdempotentElem.zero
theorem normalCfcOperator_isIdempotent
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    IsIdempotentElem (normalCfcOperator U hU S) := by
  classical
  let T : E →L[ℂ] E := normalCfcOperator U hU S
  change T * T = T
  apply ContinuousLinearMap.ext
  intro x
  let mu := normalCfcScalarMeasure U hU x
  have hex (n : ℕ) : ∃ K : Set (spectrum ℂ U),
      K ⊆ S ∧ IsClosed K ∧ mu.real (S \ K) < 1 / ((n : ℝ) + 1) := by
    apply exists_isClosed_measureReal_sdiff_lt mu hS
    positivity
  choose K hKS hKclosed hdiff using hex
  let Q : ℕ → E →L[ℂ] E := fun n => normalCfcOperator U hU (K n)
  let D : ℕ → E →L[ℂ] E := fun n => T - Q n
  have hQ0 (n : ℕ) : 0 ≤ Q n :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (normalCfcOperator_isPositive U hU (K n))
  have hD0 (n : ℕ) : 0 ≤ D n := by
    exact sub_nonneg.mpr (normalCfcOperator_mono U hU (hKS n))
  have hD1 (n : ℕ) : D n ≤ 1 := by
    calc
      D n ≤ T := sub_le_self T (hQ0 n)
      _ ≤ 1 := normalCfcOperator_le_one U hU S
  have hdiff_apply (n : ℕ) : Q n x - T x = -(D n x) := by
    dsimp only [D]
    rw [sub_apply]
    abel
  have hnormdiff (n : ℕ) : ‖Q n x - T x‖ ^ 2 < 1 / ((n : ℝ) + 1) := by
    rw [hdiff_apply n, norm_neg]
    apply (norm_sq_apply_le_re_inner_of_nonneg_of_le_one
      (D n) (hD0 n) (hD1 n) x).trans_lt
    dsimp only [D, T, Q]
    rw [sub_apply, inner_sub_left, inner_normalCfcOperator_self,
      inner_normalCfcOperator_self, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_re]
    rw [← measureReal_sdiff (hKS n) (hKclosed n).measurableSet]
    exact hdiff n
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound_tendsto : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hinv
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt
  have hQx : Filter.Tendsto (fun n => Q n x)
      Filter.atTop (nhds (T x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero
    · exact fun _ => norm_nonneg _
    · intro n
      exact Real.le_sqrt_of_sq_le (hnormdiff n).le
    · exact hbound_tendsto
  have hfix (n : ℕ) : T * Q n = Q n := by
    apply mul_projection_eq_of_projection_le_contraction
    · exact normalCfcOperator_isIdempotent_of_isClosed U hU (K n) (hKclosed n)
    · exact normalCfcOperator_isSelfAdjoint U hU (K n)
    · exact normalCfcOperator_le_one U hU S
    · exact normalCfcOperator_mono U hU (hKS n)
  have hleft : Filter.Tendsto (fun n => T (Q n x))
      Filter.atTop (nhds (T (T x))) :=
    T.continuous.continuousAt.tendsto.comp hQx
  have hright : Filter.Tendsto (fun n => T (Q n x))
      Filter.atTop (nhds (T x)) := by
    convert hQx using 1
    funext n
    have happ := congrArg (fun R : E →L[ℂ] E => R x) (hfix n)
    simpa only [mul_apply_eq_comp] using happ
  change T (T x) = T x
  exact tendsto_nhds_unique hleft hright
@[simp]
theorem normalCfcOperator_empty
    (U : E →L[ℂ] E) (hU : IsStarNormal U) :
    normalCfcOperator U hU ∅ = 0 := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [inner_normalCfcOperator_self, measureReal_empty,
    zero_apply, inner_zero_left]
  rfl
@[simp]
theorem normalCfcOperator_univ
    (U : E →L[ℂ] E) (hU : IsStarNormal U) :
    normalCfcOperator U hU Set.univ = 1 := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [inner_normalCfcOperator_self,
    normalCfcScalarMeasure_real_univ, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem normalCfcOperator_union
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S T : Set (spectrum ℂ U)} (hdisj : Disjoint S T)
    (hT : MeasurableSet T) :
    normalCfcOperator U hU (S ∪ T) =
      normalCfcOperator U hU S + normalCfcOperator U hU T := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [inner_normalCfcOperator_self, add_apply,
    inner_add_left, inner_normalCfcOperator_self, inner_normalCfcOperator_self,
    measureReal_union hdisj hT]
  push_cast
  rfl
def initialUnion {X : Type*} (S : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i, ⋃ (_hi : i < n), S i
def tailUnion {X : Type*} (S : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i, ⋃ (_hi : n ≤ i), S i
omit [CompleteSpace E] in
theorem initialUnion_zero {X : Type*} (S : ℕ → Set X) :
    initialUnion S 0 = ∅ := by
  ext x
  constructor
  · intro hx
    rw [initialUnion] at hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, _hx⟩ := Set.mem_iUnion.mp hx
    omega
  · intro hx
    exact False.elim hx
omit [CompleteSpace E] in
theorem initialUnion_succ {X : Type*} (S : ℕ → Set X) (n : ℕ) :
    initialUnion S (n + 1) = initialUnion S n ∪ S n := by
  ext x
  constructor
  · intro hx
    rw [initialUnion] at hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Set.mem_union_left _ (Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem hi hxi))
    · exact Set.mem_union_right _ hxi
  · intro hx
    rcases hx with hx | hx
    · rw [initialUnion] at hx ⊢
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem (Nat.lt_succ_of_lt hi) hxi)
    · rw [initialUnion]
      exact Set.mem_iUnion_of_mem n
        (Set.mem_iUnion_of_mem (Nat.lt_succ_self n) hx)
omit [CompleteSpace E] in
theorem tailUnion_measurable {X : Type*} [MeasurableSpace X]
    (S : ℕ → Set X) (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) :
    MeasurableSet (tailUnion S n) := by
  unfold tailUnion
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _hi => hS i
omit [CompleteSpace E] in
theorem initialUnion_disjoint_tailUnion {X : Type*}
    (S : ℕ → Set X) (hpair : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    Disjoint (initialUnion S n) (tailUnion S n) := by
  rw [Set.disjoint_left]
  intro x hxinit hxtail
  rw [initialUnion] at hxinit
  obtain ⟨i, hxinit⟩ := Set.mem_iUnion.mp hxinit
  obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxinit
  rw [tailUnion] at hxtail
  obtain ⟨j, hxtail⟩ := Set.mem_iUnion.mp hxtail
  obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxtail
  have hij : i ≠ j := by omega
  exact Set.disjoint_left.mp (hpair hij) hxi hxj
omit [CompleteSpace E] in
theorem iUnion_eq_initialUnion_union_tailUnion {X : Type*}
    (S : ℕ → Set X) (n : ℕ) :
    (⋃ i, S i) = initialUnion S n ∪ tailUnion S n := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i < n
    · exact Set.mem_union_left _ (Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem hi hxi))
    · exact Set.mem_union_right _ (Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem (Nat.le_of_not_gt hi) hxi))
  · intro hx
    rcases hx with hx | hx
    · rw [initialUnion] at hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion_of_mem i hxi
    · rw [tailUnion] at hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion_of_mem i hxi
theorem normalCfcOperator_initialUnion
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : ℕ → Set (spectrum ℂ U))
    (hS : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    normalCfcOperator U hU (initialUnion S n) =
      ∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) := by
  induction n with
  | zero =>
      rw [initialUnion_zero, normalCfcOperator_empty, Finset.sum_range_zero]
  | succ n ih =>
      have hdisj : Disjoint (initialUnion S n) (S n) := by
        rw [Set.disjoint_left]
        intro x hxinit hxn
        rw [initialUnion] at hxinit
        obtain ⟨i, hxinit⟩ := Set.mem_iUnion.mp hxinit
        obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxinit
        have hin : i ≠ n := by omega
        exact Set.disjoint_left.mp (hpair hin) hxi hxn
      rw [show n + 1 = Nat.succ n by omega, initialUnion_succ,
        normalCfcOperator_union U hU hdisj (hS n), ih,
        Finset.sum_range_succ]
theorem normalCfcOperator_countably_additive
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : ℕ → Set (spectrum ℂ U))
    (hS : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise fun i j => Disjoint (S i) (S j)) (x : E) :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x)
      Filter.atTop (nhds (normalCfcOperator U hU (⋃ i, S i) x)) := by
  have htailMeas (n : ℕ) : MeasurableSet (tailUnion S n) :=
    tailUnion_measurable S hS n
  have htailMeasure : Filter.Tendsto
      ((normalCfcScalarMeasure U hU x) ∘ tailUnion S)
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (fun n => normalCfcScalarMeasure U hU x
        (⋃ i, ⋃ (_hi : n ≤ i), S i)) Filter.atTop (nhds 0)
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (μ := normalCfcScalarMeasure U hU x)
      (fun i => (hS i).nullMeasurableSet) hpair
  have htailReal : Filter.Tendsto
      (fun n => (normalCfcScalarMeasure U hU x).real (tailUnion S n))
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htailMeasure
    change Filter.Tendsto
      (fun n => ENNReal.toReal
        (normalCfcScalarMeasure U hU x (tailUnion S n)))
      Filter.atTop (nhds 0)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have htailNormSq : Filter.Tendsto
      (fun n => ‖normalCfcOperator U hU (tailUnion S n) x‖ ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => sq_nonneg _)
      (Filter.Eventually.of_forall fun n => ?_) htailReal
    calc
      ‖normalCfcOperator U hU (tailUnion S n) x‖ ^ 2 ≤
          (@inner ℂ E _
            (normalCfcOperator U hU (tailUnion S n) x) x).re :=
        norm_sq_apply_le_re_inner_of_nonneg_of_le_one
          (normalCfcOperator U hU (tailUnion S n))
          ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
            (normalCfcOperator_isPositive U hU (tailUnion S n)))
          (normalCfcOperator_le_one U hU (tailUnion S n)) x
      _ = (normalCfcScalarMeasure U hU x).real (tailUnion S n) := by
        rw [inner_normalCfcOperator_self, Complex.ofReal_re]
  have htailNorm : Filter.Tendsto
      (fun n => ‖normalCfcOperator U hU (tailUnion S n) x‖)
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp htailNormSq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply htailNorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hpartial := normalCfcOperator_initialUnion U hU S hS hpair n
  have hdecomp :
      normalCfcOperator U hU (⋃ i, S i) =
        normalCfcOperator U hU (initialUnion S n) +
          normalCfcOperator U hU (tailUnion S n) := by
    rw [iUnion_eq_initialUnion_union_tailUnion S n]
    exact normalCfcOperator_union U hU
      (initialUnion_disjoint_tailUnion S hpair n) (htailMeas n)
  have happ := congrArg (fun T : E →L[ℂ] E => T x) hdecomp
  rw [add_apply, hpartial, sum_apply] at happ
  change ‖normalCfcOperator U hU (tailUnion S n) x‖ =
    ‖(∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x) -
      normalCfcOperator U hU (⋃ i, S i) x‖
  rw [happ]
  rw [show (∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x) -
      ((∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x) +
        normalCfcOperator U hU (tailUnion S n) x) =
      -normalCfcOperator U hU (tailUnion S n) x by abel, norm_neg]
theorem normalCfcOperator_compl
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    normalCfcOperator U hU Sᶜ = 1 - normalCfcOperator U hU S := by
  have hsum := normalCfcOperator_union U hU disjoint_compl_right hS.compl
  rw [Set.union_compl_self, normalCfcOperator_univ] at hsum
  symm
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using hsum
theorem normalCfcOperator_mul_eq_zero_of_disjoint
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S T : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    normalCfcOperator U hU S * normalCfcOperator U hU T = 0 := by
  have hTScompl : T ⊆ Sᶜ := by
    intro z hzT hzS
    exact Set.disjoint_left.mp hdisj hzS hzT
  have hfix : normalCfcOperator U hU Sᶜ * normalCfcOperator U hU T =
      normalCfcOperator U hU T := by
    apply mul_projection_eq_of_projection_le_contraction
    · exact normalCfcOperator_isIdempotent U hU T hT
    · exact normalCfcOperator_isSelfAdjoint U hU T
    · exact normalCfcOperator_le_one U hU Sᶜ
    · exact normalCfcOperator_mono U hU hTScompl
  rw [normalCfcOperator_compl U hU S hS] at hfix
  rw [sub_mul, one_mul] at hfix
  apply neg_eq_zero.mp
  calc
    -(normalCfcOperator U hU S * normalCfcOperator U hU T) =
        ((normalCfcOperator U hU T -
          normalCfcOperator U hU S * normalCfcOperator U hU T) -
          normalCfcOperator U hU T) := by abel
    _ = normalCfcOperator U hU T - normalCfcOperator U hU T := by
      rw [hfix]
    _ = 0 := sub_self _
theorem normalCfcOperator_inter
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S T : Set (spectrum ℂ U)) (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    normalCfcOperator U hU (S ∩ T) =
      normalCfcOperator U hU S * normalCfcOperator U hU T := by
  let R : Set (spectrum ℂ U) := T \ (S ∩ T)
  have hR : MeasurableSet R := hT.diff (hS.inter hT)
  have hinterT : S ∩ T ⊆ T := Set.inter_subset_right
  have hdecomp : normalCfcOperator U hU T =
      normalCfcOperator U hU (S ∩ T) + normalCfcOperator U hU R := by
    dsimp only [R]
    rw [← normalCfcOperator_union U hU Set.disjoint_sdiff_right hR,
      Set.union_sdiff_cancel hinterT]
  have hinterfix : normalCfcOperator U hU S *
      normalCfcOperator U hU (S ∩ T) = normalCfcOperator U hU (S ∩ T) := by
    apply mul_projection_eq_of_projection_le_contraction
    · exact normalCfcOperator_isIdempotent U hU (S ∩ T) (hS.inter hT)
    · exact normalCfcOperator_isSelfAdjoint U hU (S ∩ T)
    · exact normalCfcOperator_le_one U hU S
    · exact normalCfcOperator_mono U hU Set.inter_subset_left
  have hdisj : Disjoint S R := by
    rw [Set.disjoint_left]
    intro z hzS hzR
    exact hzR.2 ⟨hzS, hzR.1⟩
  have hzero : normalCfcOperator U hU S * normalCfcOperator U hU R = 0 :=
    normalCfcOperator_mul_eq_zero_of_disjoint U hU hS hR hdisj
  rw [hdecomp, mul_add, hinterfix, hzero, add_zero]
noncomputable def normalCfcPVM
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (g : spectrum ℂ U → ℝ) (hg : Measurable g) : PVM E where
  proj S := normalCfcOperator U hU (g ⁻¹' S)
  isOrthogonalProjection S hS :=
    ⟨normalCfcOperator_isSelfAdjoint U hU (g ⁻¹' S),
      normalCfcOperator_isIdempotent U hU (g ⁻¹' S) (hg hS)⟩
  empty := by
    rw [Set.preimage_empty, normalCfcOperator_empty]
  univ := by
    rw [Set.preimage_univ, normalCfcOperator_univ]
  inter S T hS hT := by
    rw [Set.preimage_inter, normalCfcOperator_inter U hU
      (g ⁻¹' S) (g ⁻¹' T) (hg hS) (hg hT)]
  countably_additive S hS hpair x := by
    have hpreMeas : ∀ i, MeasurableSet (g ⁻¹' S i) := fun i => hg (hS i)
    have hprePair : Pairwise fun i j => Disjoint (g ⁻¹' S i) (g ⁻¹' S j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact Set.disjoint_left.mp (hpair hij) hzi hzj
    simpa only [Set.preimage_iUnion] using
      normalCfcOperator_countably_additive U hU
        (fun i => g ⁻¹' S i) hpreMeas hprePair x
def unitPole (U : E →L[ℂ] E) : Set (spectrum ℂ U) :=
  {z | (z : ℂ) = 1}
noncomputable def distanceToOneSq (U : E →L[ℂ] E) :
    C_c(spectrum ℂ U, ℝ) where
  toFun z := ‖(z : ℂ) - 1‖ ^ 2
  continuous_toFun := ((continuous_subtype_val.sub continuous_const).norm.pow 2)
  hasCompactSupport' := HasCompactSupport.of_compactSpace _
noncomputable def distanceToOneSqComplex (U : E →L[ℂ] E) :
    C(spectrum ℂ U, ℂ) :=
  star ((ContinuousMap.id ℂ).restrict (spectrum ℂ U) - 1) *
    ((ContinuousMap.id ℂ).restrict (spectrum ℂ U) - 1)
noncomputable def inverseCayleyCoordinate (z : ℂ) : ℝ :=
  -z.im / (1 - z.re)
theorem inverseCayleyCoordinate_measurable :
    Measurable inverseCayleyCoordinate := by
  exact Complex.measurable_im.neg.div
    (measurable_const.sub Complex.measurable_re)
noncomputable def cayleyCoordinate (t : ℝ) : ℂ :=
  ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)
theorem cayleyCoordinate_measurable : Measurable cayleyCoordinate := by
  exact (Complex.measurable_ofReal.sub measurable_const).div
    (Complex.measurable_ofReal.add measurable_const)
theorem cayleyCoordinate_norm (t : ℝ) : ‖cayleyCoordinate t‖ = 1 := by
  rw [cayleyCoordinate, norm_div]
  have hden : ‖(t : ℂ) + Complex.I‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
      Complex.zero_im] at him
    exact one_ne_zero him
  rw [div_eq_one_iff_eq hden]
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im, Complex.I_im,
    zero_sub, mul_neg, neg_mul, neg_neg, Complex.add_re, add_zero,
    Complex.add_im, zero_add]
theorem cayleyCoordinate_bounded :
    ∃ C, ∀ t, ‖cayleyCoordinate t‖ ≤ C := by
  refine ⟨1, fun t => ?_⟩
  rw [cayleyCoordinate_norm]
noncomputable def inverseCayleyPVM
    (U : E →L[ℂ] E) (hU : IsStarNormal U) : PVM E :=
  normalCfcPVM U hU (fun z => inverseCayleyCoordinate z)
    (inverseCayleyCoordinate_measurable.comp measurable_subtype_coe)


