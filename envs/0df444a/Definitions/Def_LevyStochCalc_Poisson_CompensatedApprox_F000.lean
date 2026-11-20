-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F000
-- name    : LevyStochCalc_Poisson_CompensatedApprox_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T23:43:57.776904+00:00
-- url     : https://prove2.me/theorems/aa18844f-91d6-4477-98d2-02d205d45fe0
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedApprox
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedApprox. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
import Definitions.Def_LevyStochCalc_Poisson_Filtered_F000
import Definitions.Def_SourceProof_31fbb7fc7ba05924c933d0ee
import Definitions.Def_SourceProof_455c5c72b05cf697a7135f1b
import Definitions.Def_SourceProof_64b57ddfa082ba813e2cbaf7
import Definitions.Def_SourceProof_e3cec9b21be032510d9c325d
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Approximation of a square-integrable integrand by mark-step integrands

For a jointly measurable, progressively measurable integrand `φ : Ω → ℝ → E → ℝ` that is
square integrable over `Ω × [0, T] × E`, and any dyadic level `L₀` and tolerance `ε`, there is
an adapted mark-step integrand on a dyadic grid of level at least `L₀` within `ε` of `φ` in
`L²(P ⊗ ds ⊗ ν)` on `[0, T]` (`exists_markStep_close`). The integrand is first clipped and
restricted to a mark set of finite measure (`truncate`), which reduces to the bounded,
finitely supported case treated by `exists_markEval_L2_tendsto`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Truncate

/-- The integrand clipped at level `M` and restricted to marks in `S`. -/
noncomputable def truncate (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E) : Ω → ℝ → E → ℝ :=
  fun ω s e => S.indicator (fun _ => max (-M) (min M (φ ω s e))) e
lemma continuous_clip (M : ℝ) : Continuous (fun x : ℝ => max (-M) (min M x)) := by
  fun_prop
lemma abs_clip_le {M x : ℝ} (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ M := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
lemma abs_clip_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |max (-M) (min M x)| ≤ |x| := by
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (hx.trans hM)]
    rcases le_total (-M) x with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_neg, abs_of_nonneg hM, abs_of_nonpos hx]
      linarith
  · have h0 : 0 ≤ min M x := le_min hM hx
    rw [max_eq_right (by linarith), abs_of_nonneg h0, abs_of_nonneg hx]
    exact min_le_right _ _
lemma nnnorm_clip_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    (‖max (-M) (min M x)‖₊ : ℝ≥0∞) ≤ ‖x‖₊ := by
  have h : ‖max (-M) (min M x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clip_le_abs hM x
  exact_mod_cast h
variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma truncate_abs_le (hM : 0 ≤ M) (ω : Ω) (s : ℝ) (e : E) : |truncate φ M S ω s e| ≤ M := by
  unfold truncate
  by_cases he : e ∈ S
  · rw [Set.indicator_of_mem he]
    exact abs_clip_le hM
  · rw [Set.indicator_of_notMem he, abs_zero]
    exact hM
omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma truncate_eq_zero (ω : Ω) {e : E} (he : e ∉ S) (s : ℝ) : truncate φ M S ω s e = 0 :=
  Set.indicator_of_notMem he _
omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma truncate_eq_indicator :
    (fun p : Ω × ℝ × E => truncate φ M S p.1 p.2.1 p.2.2)
      = {p : Ω × ℝ × E | p.2.2 ∈ S}.indicator
          (fun p => max (-M) (min M (φ p.1 p.2.1 p.2.2))) := by
  funext p
  by_cases h : p.2.2 ∈ S
  · rw [truncate, Set.indicator_of_mem h,
    Set.indicator_of_mem (show p ∈ {q : Ω × ℝ × E | q.2.2 ∈ S} from h)]
  · rw [truncate, Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show p ∉ {q : Ω × ℝ × E | q.2.2 ∈ S} from h)]
lemma truncate_measurable (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hS : MeasurableSet S) :
    Measurable (fun p : Ω × ℝ × E => truncate φ M S p.1 p.2.1 p.2.2) := by
  rw [truncate_eq_indicator]
  exact ((continuous_clip M).measurable.comp h_meas).indicator
    ((measurable_snd.comp measurable_snd) hS)
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

lemma truncate_progMeas (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ) (hM : 0 ≤ M)
    (hS : MeasurableSet S) :
    Probability.MarkedProgressivelyMeasurable ℱ (truncate φ M S) :=
  (_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b ((continuous_clip M).comp_markedProgressivelyMeasurable
    (by rw [min_eq_right hM, max_eq_right (neg_nonpos.mpr hM)]) h_progMeas)) hS
omit [IsProbabilityMeasure P] in
/-- The `2(a² + b²)` bound for nested triple integrals: if `a` is within `ε / 4` of `b`
and `b` within `ε / 4` of `c`, then `a` is within `ε` of `c`. -/
lemma triple_sq_lt_of_lt {T : ℝ} {a b c : Ω → ℝ → E → ℝ}
    (ha : Measurable (fun p : Ω × ℝ × E => a p.1 p.2.1 p.2.2))
    (hb : Measurable (fun p : Ω × ℝ × E => b p.1 p.2.1 p.2.2)) {ε : ℝ≥0∞}
    (h1 : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε / 4)
    (h2 : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε / 4) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε := by
  have hpt : ∀ ω s e, (‖a ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s e
    rw [show a ω s e - c ω s e = (a ω s e - b ω s e) + (b ω s e - c ω s e) by ring]
    exact sq_nnnorm_add_le_two_mul _ _
  have hu : Measurable (fun p : Ω × ℝ × E =>
      (‖a p.1 p.2.1 p.2.2 - b p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (ha.sub hb).nnnorm).pow_const 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖a ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          2 * ((‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2)
          ∂ν ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
        rw [lintegral_triple_const_mul 2 (by norm_num), _root_.Prove2MeSourceProof.h_64b57ddfa082ba813e2cbaf7 hu]
    _ = ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * 2 := mul_comm _ _
    _ < (ε / 4 + ε / 4) * 2 :=
        ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) (ENNReal.add_lt_add h1 h2)
    _ = ε := by
        rw [show (ε / 4 + ε / 4) * 2 = 4 * (ε / 4) by ring,
          ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
/-- Clipping and restricting to a finite-measure mark set approximates `φ` in `L²`. -/
lemma exists_truncate_close (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {T : ℝ} (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (M : ℕ) (S : Set E), MeasurableSet S ∧ ν S ≠ ⊤ ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - truncate φ M S ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε := by
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨M, hM⟩ :=
    ((_root_.Prove2MeSourceProof.h_31fbb7fc7ba05924c933d0ee φ h_meas h_sq_int).eventually (Iio_mem_nhds hε4)).exists
  set ψ : Ω → ℝ → E → ℝ := fun ω s e => max (-(M : ℝ)) (min (M : ℝ) (φ ω s e)) with hψ
  have hψ_meas : Measurable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) :=
    (continuous_clip (M : ℝ)).measurable.comp h_meas
  have hψ_sq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt ?_ h_sq_int
    refine lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => ?_
    exact pow_le_pow_left' (nnnorm_clip_le (Nat.cast_nonneg M) _) 2
  obtain ⟨j, hj⟩ := ((_root_.Prove2MeSourceProof.h_e3cec9b21be032510d9c325d ψ hψ_meas hψ_sq
    (measurableSet_spanningSets ν) (iUnion_spanningSets ν)).eventually (Iio_mem_nhds hε4)).exists
  set S : Set E := ⋃ m ∈ Finset.range j, spanningSets ν m with hS
  have hSm : MeasurableSet S :=
    Finset.measurableSet_biUnion _ fun m _ => measurableSet_spanningSets ν m
  have hSfin : ν S ≠ ⊤ :=
    ((measure_biUnion_finset_le _ _).trans_lt
      (ENNReal.sum_lt_top.2 fun m _ => measure_spanningSets_lt_top ν m)).ne
  refine ⟨M, S, hSm, hSfin, ?_⟩
  have htr : ∀ ω s e, truncate φ M S ω s e = S.indicator (fun _ => ψ ω s e) e := fun _ _ _ => rfl
  have hc_meas : Measurable (fun p : Ω × ℝ × E => truncate φ M S p.1 p.2.1 p.2.2) :=
    truncate_measurable φ M S h_meas hSm
  simp_rw [htr] at hc_meas ⊢
  exact triple_sq_lt_of_lt h_meas hψ_meas hM hj
end Truncate

section Close

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)

end Close

section Master

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Master

section Cauchy

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Cauchy

end LevyStochCalc.Poisson.Compensated


