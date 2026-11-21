-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F001
-- name    : LevyStochCalc_Brownian_ItoDensityDyadicAverages_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:06:15.710171+00:00
-- url     : https://prove2.me/theorems/c730107b-7274-471c-a257-158c2c65fa74
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityDyadicAverages
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityDyadicAverages. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F002
import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
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
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Step 1 of the density chain (Brownian, no mark dimension):** Bounded measurable
`g : Ω × [0, T] → ℝ` lies in `MemLp 2 (P × volume.restrict [0, T])`.

This gives access to Mathlib's `MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt`
which produces a Mathlib `SimpleFunc` approximation in L². The output, however, is
a Mathlib SimpleFunc (with constant range, indicator of measurable rectangles),
not yet our `SimplePredictable` form (with adapted ω-dependent coefficients on time
intervals only). Step 2 bridges this gap. -/
private lemma bounded_memLp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (_hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasureTheory.MemLp (Function.uncurry g)
      2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  -- Volume.restrict (Icc 0 T) is finite (volume(Icc 0 T) = T < ∞).
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by simp [Real.volume_Icc, ENNReal.ofReal_lt_top]⟩
  haveI : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  refine MeasureTheory.MemLp.of_bound h_meas.aestronglyMeasurable M ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  rw [Real.norm_eq_abs]
  exact h_bound p.1 p.2
/-- **Step 1.5 of the density chain (Brownian):** Mathlib SimpleFunc convergence on
the finite product space. Given `g ∈ MemLp 2` (from `bounded_memLp_brownian`), we
extract a sequence `(φ_n)` of Mathlib `SimpleFunc` such that `eLpNorm (g - φ_n) → 0`. -/
private lemma exists_simpleFunc_seq_tendsto_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ φ : ℕ → MeasureTheory.SimpleFunc (Ω × ℝ) ℝ,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (Function.uncurry g - ⇑(φ n))
          2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop (nhds 0) := by
  have h_memLp : MeasureTheory.MemLp (Function.uncurry g)
      2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    bounded_memLp_brownian hT g h_meas M h_bound
  -- For each n, get a SimpleFunc with eLpNorm-distance ≤ 1/(n+1).
  have h_choice : ∀ n : ℕ, ∃ φ : MeasureTheory.SimpleFunc (Ω × ℝ) ℝ,
      MeasureTheory.eLpNorm (Function.uncurry g - ⇑φ)
        2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps_ne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by
      apply ENNReal.inv_ne_zero.mpr
      simp
    obtain ⟨φ, hφ_lt, _⟩ := MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt
      h_memLp (by simp : (2 : ℝ≥0∞) ≠ ⊤) h_eps_ne
    exact ⟨φ, hφ_lt⟩
  choose φ hφ using h_choice
  refine ⟨φ, ?_⟩
  -- Squeeze: ‖g - φ_n‖ ≤ (n+1)⁻¹ → 0.
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) ε hε_pos
  refine ⟨N, fun n hn => ?_⟩
  exact (hφ n).le.trans (hN n hn)
/-- **Dyadic partition** of `[0, T]` at refinement level `n`:
`partition i = i * T / 2^n` for `i = 0, ..., 2^n`. -/
noncomputable def dyadicPartition_brownian (T : ℝ) (n : ℕ) :
    Fin (2 ^ n + 1) → ℝ :=
  fun i => (i : ℝ) * T / (2 ^ n : ℕ)
lemma dyadicPartition_brownian_zero (T : ℝ) (n : ℕ) :
    dyadicPartition_brownian T n 0 = 0 := by
  simp [dyadicPartition_brownian]
lemma dyadicPartition_brownian_last (T : ℝ) (n : ℕ) :
    dyadicPartition_brownian T n (Fin.last (2 ^ n)) = T := by
  unfold dyadicPartition_brownian
  rw [Fin.val_last]
  field_simp
lemma dyadicPartition_brownian_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicPartition_brownian T n) := by
  intro i j hij
  unfold dyadicPartition_brownian
  have h_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_lt : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  rw [div_lt_div_iff_of_pos_right h_pos]
  exact mul_lt_mul_of_pos_right h_lt hT
lemma dyadicPartition_brownian_le_T {T : ℝ} (_hT : 0 < T) (n : ℕ) :
    dyadicPartition_brownian T n (Fin.last (2 ^ n)) ≤ T :=
  le_of_eq (dyadicPartition_brownian_last T n)
/-- **Dyadic averaging coefficient**: the average of `g(ω, ·)` over the `i`-th
dyadic interval `(t_i, t_{i+1}]` of `[0, T]` at refinement level `n`.

Used as the ξ-coefficient of the dyadic SimplePredictable approximation. -/
noncomputable def dyadicAvg_brownian
    {T : ℝ} (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  ((2 ^ n : ℕ) / T) *
    ∫ s in Set.Ioc (dyadicPartition_brownian T n i.castSucc)
                    (dyadicPartition_brownian T n i.succ),
      g ω s
/-- Measurability of `dyadicAvg_brownian` in `ω` (Bochner integral commutes with
measurability via Fubini). -/
lemma dyadicAvg_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvg_brownian (T := T) g n i) := by
  unfold dyadicAvg_brownian
  refine Measurable.const_mul ?_ _
  -- The Bochner integral ∫ s in S, g ω s ∂volume = ∫ s, g ω s ∂(volume.restrict S)
  -- is measurable in ω by `StronglyMeasurable.integral_prod_right`.
  refine MeasureTheory.StronglyMeasurable.measurable ?_
  exact MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Set.Ioc (dyadicPartition_brownian T n i.castSucc)
                                    (dyadicPartition_brownian T n i.succ)))
    h_meas.stronglyMeasurable
/-- Length of dyadic interval at refinement level `n`: `T/2^n`. -/
lemma dyadicPartition_brownian_diff {T : ℝ} (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc
      = T / (2 ^ n : ℕ) := by
  unfold dyadicPartition_brownian
  have hi_succ : ((i.succ : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) + 1 := by
    simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by
    simp [Fin.val_castSucc]
  rw [hi_succ, hi_castSucc]
  ring
-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).

end LevyStochCalc.Brownian.Ito


