-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F001
-- name    : LevyStochCalc_Poisson_CompensatedApprox_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:49:12.840705+00:00
-- url     : https://prove2.me/theorems/e03d36f6-068f-48a8-9f46-82aa6d4cbb36
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedApprox
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedApprox. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000
import Definitions.Def_SourceProof_68bcc04d25dcb303fabb8713
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

variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

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

/-- The horizon `2 ^ n` of stage `n` of the master sequence. -/
def stageHorizon (n : ℕ) : ℝ := (2 : ℝ) ^ n
lemma stageHorizon_pos (n : ℕ) : 0 < stageHorizon n := pow_pos two_pos n
lemma stageHorizon_mono {n n' : ℕ} (h : n ≤ n') : stageHorizon n ≤ stageHorizon n' :=
  pow_le_pow_right₀ one_le_two h
lemma stageHorizon_eq_mul {n n' : ℕ} (h : n ≤ n') :
    stageHorizon n' = stageHorizon n * 2 ^ (n' - n) := by
  unfold stageHorizon
  rw [← pow_add, Nat.add_sub_cancel' h]
/-- The `L²` error of a mark-step integrand against `φ` on the horizon of stage `n`. -/
noncomputable def stageErr (P : Measure Ω) (n : ℕ) {ℓ : ℕ}
    (G : MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ)) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
    (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
include N h_meas h_progMeas h_sq_int_global in
lemma exists_stage (n L₀ : ℕ) :
    ∃ ℓ : ℕ, L₀ ≤ ℓ ∧
      ∃ G : MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ),
        G.Adapted ℱ ∧ stageErr φ P n G < ((n : ℝ≥0∞) + 1)⁻¹ :=
  _root_.Prove2MeSourceProof.h_68bcc04d25dcb303fabb8713 N ℱ φ h_meas h_progMeas (stageHorizon_pos n)
    (h_sq_int_global _ (stageHorizon_pos n)) L₀
    (ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
/-- The master sequence of approximants: stage `n` is an adapted mark-step integrand on a
dyadic grid of `[0, 2 ^ n]` within `(n + 1)⁻¹` of `φ` in `L²`, the levels increasing by at
least one per stage. -/
noncomputable def master :
    ∀ n : ℕ, Σ ℓ : ℕ, MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ)
  | 0 => ⟨Classical.choose (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0),
      Classical.choose
        (Classical.choose_spec (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0)).2⟩
  | n + 1 => ⟨Classical.choose (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1)
        ((master n).1 + 1)),
      Classical.choose (Classical.choose_spec (exists_stage N ℱ φ h_meas h_progMeas
        h_sq_int_global (n + 1) ((master n).1 + 1))).2⟩
lemma master_level_succ (n : ℕ) :
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).1 + 1
      ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1)).1 :=
  (Classical.choose_spec (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1)
    ((master N ℱ φ h_meas h_progMeas h_sq_int_global n).1 + 1))).1
lemma master_level_add {n n' : ℕ} (h : n ≤ n') :
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).1 + (n' - n)
      ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 := by
  induction h with
  | refl => simp
  | @step m h ih =>
    have h1 := master_level_succ N ℱ φ h_meas h_progMeas h_sq_int_global m
    change _ + (m + 1 - n) ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global (m + 1)).1
    omega
lemma master_adapted (n : ℕ) :
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.Adapted ℱ := by
  cases n with
  | zero =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0)).2).1
  | succ n =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1) _)).2).1
lemma master_err (n : ℕ) :
    stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 < ((n : ℝ≥0∞) + 1)⁻¹ :=
      by
  cases n with
  | zero =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0)).2).2
  | succ n =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1) _)).2).2
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

/-- The compensated integral of the stage-`n` approximant up to time `t`. -/
noncomputable def stageIntegral (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.integral N t ω
include hℱ in
lemma martingale_stageIntegral (n : ℕ) :
    Martingale (fun t => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t)
      ℱ P :=
  MarkStep.martingale_integral N hℱ _ (master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n)
lemma memLp_stageIntegral (n : ℕ) (t : ℝ) :
    MemLp (fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) 2 P :=
  MarkStep.memLp_integral N _ t
lemma stageIntegral_eq_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω = 0 :=
  MarkStep.integral_eq_zero_of_nonpos N _ ht ω
omit [IsProbabilityMeasure P] in
/-- Tonelli for the inner two integrals of the nested triple integral. -/
lemma lintegral_swap_es {T : ℝ} (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) (ω : Ω) :
    ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s e ∂volume ∂ν
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f ω s e ∂ν ∂volume := by
  refine lintegral_lintegral_swap ?_
  exact (hf.comp (by fun_prop :
    Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))).aemeasurable
end Cauchy

end LevyStochCalc.Poisson.Compensated


