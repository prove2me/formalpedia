-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
-- name    : KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:23:54.029978+00:00
-- url     : https://prove2.me/theorems/07d9c52e-3104-419f-8df3-af35cf34c902
-- title:
--   Asymptotic Lipschitz and local-slope relaxations
-- statement:
--   `AsymptoticLipschitz.apply` assigns to a real-valued function $f$ at $x$ the infimum over $r>0$ of the two-point secant supremum on the open ball $B(x,r)$, with values in $[0,\infty]$. For a probability measure $\nu$, `AsymptoticLipschitz.energy` is the unnormalized integral $\int (\operatorname{Lip}_a f(x))^2\,d\nu(x)$, and `LocalSlope.preEnergy` realizes the squared local-slope energy on admissible locally Lipschitz tests in $L^2(\nu)$. `LocalSlope.relaxation` is the sequential $L^2(\nu)$ relaxation of this pre-energy; the bundle also includes the ambient realization theorem `preEnergy_toAmbient`.
-- source:
--   Source: Ambrosio–Gigli–Savaré, Density of Lipschitz functions and equivalence of weak gradients in metric measure spaces (arXiv:1111.3730v3), item E37. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Relaxation.lean#L49-L165 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Relaxation`, definition bundle `KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
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
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities
namespace Energy
universe u
namespace AsymptoticLipschitz
section Metric
variable {X : Type*} [MetricSpace X]
/-- Pointwise asymptotic Lipschitz constant `Lip_a f (x) = inf_{r > 0} Lip(f, B(x, r))`, the
infimum over radii of the two-moving-point secant supremum on the open ball.  The real quotient
at `y = z` is zero, so coincident pairs do not change the supremum.  This is not the one-moving-
point local slope `Energy.LocalSlope.apply`, which it dominates pointwise. -/
def apply (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
    ENNReal.ofReal (dist (f y) (f z) / dist y z)
end Metric
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The unnormalized squared asymptotic-Lipschitz integral in a coordinate space. -/
def energy (ν : ProbabilityMeasure V) (f : V → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, apply f x ^ 2 ∂(ν : Measure V)
end AsymptoticLipschitz
namespace LocalSlope
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The finite squared local-slope pre-energy on the literature test domain, realized in real
`L²(ν)`.  The energy is finite on tests by `Admissible.finite_energy`, so `ENNReal.toNNReal`
loses nothing. -/
def preEnergy (ν : ProbabilityMeasure V) : PreEnergy (Lp ℝ 2 (ν : Measure V)) where
  Test := {f : V → ℝ // Admissible ν f}
  toAmbient f := f.2.memLp_two.toLp f.1
  energy f := (energy ν f.1).toNNReal
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The ambient realization of a local-slope test is its `L²(ν)` class. -/
@[simp]
theorem preEnergy_toAmbient (ν : ProbabilityMeasure V) (f : {f : V → ℝ // Admissible ν f}) :
    (preEnergy ν).toAmbient f = f.2.memLp_two.toLp f.1 :=
  rfl
/-- The sequential `L²(ν)` relaxation of the squared local-slope energy over locally Lipschitz
tests.  Twice the metric Cheeger energy in the Blueprint normalization; see `Cheeger.energy`. -/
def relaxation (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (preEnergy ν).sequentialRelaxation
end LocalSlope
end Energy
end FunctionalInequalities


