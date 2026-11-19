-- Prove2me | Definitions.Def_SourceProof_7e6dc0a5b3abba2670f5e8de
-- name    : SourceProof_7e6dc0a5b3abba2670f5e8de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:02:23.658272+00:00
-- url     : https://prove2.me/theorems/0dda786d-1910-4b02-b8b8-3fdf9607d04c
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Process.Adapted
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
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_7e6dc0a5b3abba2670f5e8de {f g : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P)
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P)
    (hFf : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - f ω) 2 P) Filter.atTop (nhds 0))
    (hFg : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - g ω) 2 P) Filter.atTop (nhds 0)) :
    f =ᵐ[P] g := by
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hle : ∀ n : ℕ, eLpNorm (fun ω => f ω - g ω) 2 P
      ≤ eLpNorm (fun ω => F n ω - f ω) 2 P + eLpNorm (fun ω => F n ω - g ω) 2 P := by
    intro n
    have hcomm : eLpNorm (fun ω => f ω - F n ω) 2 P = eLpNorm (fun ω => F n ω - f ω) 2 P :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm])
    have hsplit : (fun ω => f ω - g ω)
        = (fun ω => f ω - F n ω) + fun ω => F n ω - g ω := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [hsplit, ← hcomm]
    exact eLpNorm_add_le (hfm.sub (hFm n)) ((hFm n).sub hgm) hp1
  have hzero : eLpNorm (fun ω => f ω - g ω) 2 P = 0 := by
    refine le_antisymm ?_ (zero_le)
    have hlim : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - f ω) 2 P
        + eLpNorm (fun ω => F n ω - g ω) 2 P) Filter.atTop (nhds 0) := by
      simpa using hFf.add hFg
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hle)
  have hae := (eLpNorm_eq_zero_iff (hfm.sub hgm) (by norm_num)).mp hzero
  filter_upwards [hae] with ω hω
  have hv : f ω - g ω = 0 := hω
  linarith
end LevyStochCalc.Brownian.Ito


