-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
-- name    : KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:24:39.35813+00:00
-- url     : https://prove2.me/theorems/6bb69038-d5b2-4a3e-bcb9-2e95f1140e58
-- title:
--   Local and asymptotic Lipschitz secants
-- statement:
--   `LocalSlope.secant` is the $[0,\infty]$-valued one-moving-point secant supremum over points in the open ball of radius $r$ around $x$. `AsymptoticLipschitz.secant` is the corresponding two-moving-point supremum, using pairs of points in that ball. These definitions are the local building blocks for the respective slope and asymptotic-Lipschitz quantities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L55-L126 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities
namespace Energy
universe u
namespace LocalSlope
section Metric
variable {X : Type*} [MetricSpace X]
/-- The one-moving-point secant supremum on the open ball of radius `r` around `x`.  The local
slope is its infimum over positive radii. -/
def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x)
end Metric
end LocalSlope
namespace AsymptoticLipschitz
section Metric
variable {X : Type*} [MetricSpace X]
/-- The two-moving-point secant supremum on the open ball of radius `r` around `x`.  The
asymptotic Lipschitz constant is its infimum over positive radii. -/
def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
    ENNReal.ofReal (dist (f y) (f z) / dist y z)
end Metric
end AsymptoticLipschitz
end Energy
end FunctionalInequalities


