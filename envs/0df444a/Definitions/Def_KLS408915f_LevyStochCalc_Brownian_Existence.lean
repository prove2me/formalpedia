-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
-- name    : KLS408915f_LevyStochCalc_Brownian_Existence
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:15:34.678838+00:00
-- url     : https://prove2.me/theorems/7abd2178-0062-4c2b-90f1-2b358a7093fd
-- title:
--   Extension of pre-Brownian processes to real-time Brownian motion
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The definition `realTime` extends an ℝ≥0-indexed process X to real time by t ↦ X(t⁺) − X(0), and `realTime_sub` gives its increment identity; `continuous_realTime` proves pathwise continuity when the original paths are continuous. Under `IsPreBrownianReal`, measurable time slices, and continuous paths, `BrownianMotion.ofIsPreBrownianReal` constructs a `BrownianMotion P` with the required measurability, Gaussian increments, initial and nonpositive-time behavior, continuous paths, and independence of past and future increments.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Existence.lean#L35-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Existence`, definition bundle `KLS408915f_LevyStochCalc_Brownian_Existence`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.AddContent
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Existence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- Real-time extension of an `ℝ≥0`-indexed process: `t ↦ X (t⁺) − X 0`. -/
noncomputable def realTime (X : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  X (Real.toNNReal t) ω - X 0 ω
omit [MeasurableSpace Ω] in
theorem realTime_sub (X : ℝ≥0 → Ω → ℝ) (s t : ℝ) :
    (fun ω => realTime X t ω - realTime X s ω)
      = fun ω => X (Real.toNNReal t) ω - X (Real.toNNReal s) ω := by
  funext ω; simp only [realTime]; ring
omit [MeasurableSpace Ω] in
theorem continuous_realTime {X : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous (X · ω)) (ω : Ω) :
    Continuous (fun t : ℝ => realTime X t ω) :=
  ((hcont ω).comp continuous_real_toNNReal).sub continuous_const
/-- A pre-Brownian process with measurable marginals and continuous paths is a Brownian motion
in real time. -/
noncomputable def BrownianMotion.ofIsPreBrownianReal {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) (hmeas : ∀ t, Measurable (X t))
    (hcont : ∀ ω, Continuous (X · ω)) : BrownianMotion P where
  W := realTime X
  measurable_eval _ := (hmeas _).sub (hmeas 0)
  joint_measurable :=
    measurable_uncurry_of_continuous_of_measurable (continuous_realTime hcont)
      fun _ => (hmeas _).sub (hmeas 0)
  initial_zero := ae_of_all _ fun ω => by simp [realTime]
  increment_gaussian := by
    intro s t hs hst
    have ht : 0 ≤ t := hs.trans hst.le
    have hd : nndist (Real.toNNReal t).1 (Real.toNNReal s).1 = ⟨t - s, by linarith⟩ := by
      apply NNReal.coe_injective
      simp only [NNReal.val_eq_coe, coe_nndist, Real.dist_eq, Real.coe_toNNReal _ ht,
        Real.coe_toNNReal _ hs, abs_of_pos (sub_pos.mpr hst)]
      rfl
    have h := (hX.hasLaw_sub (Real.toNNReal t) (Real.toNNReal s)).map_eq
    rw [hd] at h
    rw [realTime_sub]
    exact h
  continuous_paths := ae_of_all _ (continuous_realTime hcont)
  negative_zero := fun s hs => ae_of_all _ fun ω => by
    simp [realTime, Real.toNNReal_of_nonpos hs.le]
  joint_increment_independent := by
    intro s t hs hst
    have hst' : Real.toNNReal s ≤ Real.toNNReal t := Real.toNNReal_le_toNNReal hst.le
    have h : Indep
        (MeasurableSpace.comap (fun ω (r : Set.Iic (Real.toNNReal s)) => X r ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω (r : ℝ≥0) => X (Real.toNNReal s + r) ω - X (Real.toNNReal s) ω) inferInstance)
        P :=
      (hX.indepFun_shift (Real.toNNReal s)).symm
    refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
    · rw [realTime_sub]
      have : (fun ω => X (Real.toNNReal t) ω - X (Real.toNNReal s) ω)
          = (fun p : ℝ≥0 → ℝ => p (Real.toNNReal t - Real.toNNReal s))
            ∘ (fun ω (r : ℝ≥0) => X (Real.toNNReal s + r) ω - X (Real.toNNReal s) ω) := by
        funext ω; simp [add_tsub_cancel_of_le hst']
      rw [this]
      refine Measurable.comap_le ?_
      exact (measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)
    · refine iSup₂_le fun j hj => ?_
      have hj' : Real.toNNReal j ≤ Real.toNNReal s := Real.toNNReal_le_toNNReal hj
      have : realTime X j
          = (fun p : Set.Iic (Real.toNNReal s) → ℝ => p ⟨Real.toNNReal j, hj'⟩ - p ⟨0, by simp⟩)
            ∘ (fun ω (r : Set.Iic (Real.toNNReal s)) => X r ω) := by
        funext ω; rfl
      rw [this]
      refine Measurable.comap_le (Measurable.comp ?_ (Measurable.of_comap_le le_rfl))
      exact (measurable_pi_apply _).sub (measurable_pi_apply _)
end Brownian
end LevyStochCalc


