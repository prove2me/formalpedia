-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:05:38.477257+00:00
-- url     : https://prove2.me/theorems/ca946e38-4d61-43be-bede-933bf05162ef
-- title:
--   Posterior expectations and means
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space, `posteriorExpectation μ c Q f` is the integral of a real-valued function $f$ against the tilt of $\mu$ by $\langle c,x\rangle-\frac12\langle Qx,x\rangle$. Under completeness of the space, `posteriorMean μ c Q` is the vector integral $\int x\,d\mu_{c,Q}$ for that same tilted measure. These declarations are definitions only; they do not assert differentiability, covariance formulas, or a generator identity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L29-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_Generator`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Probability
namespace Posterior
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The expectation `∫ f dμ_{c,Q}` of `f` under the posterior with parameters `(c, Q)`. -/
def posteriorExpectation (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) (f : E → ℝ) : ℝ :=
  ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent c Q))
end Smooth
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The mean `a = ∫ x dμ_{c,Q}` of the posterior. -/
def posteriorMean (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) : E :=
  ∫ x, x ∂((μ : Measure E).tilted (quadraticExponent c Q))
variable {ι : Type*} [Fintype ι]
end Mean
end Posterior
end Probability
end FunctionalInequalities


