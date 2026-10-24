-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
-- name    : KLS408915f_FunctionalInequalities_KLS_Isotropic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:01:12.906167+00:00
-- url     : https://prove2.me/theorems/0549879e-7a03-4dfd-813f-e7ee7149ec52
-- title:
--   Isotropic probability law
-- statement:
--   `FunctionalInequalities.KLS.Isotropic μ` is a proposition for a probability measure $\mu$ on a complete real inner-product space requiring three fields: `memLp_two` says that the identity map has finite second moment, `mean_zero` says $\int x\,d\mu=0$, and `covariance_identity` says the centered covariance operator `Covariance.operator` is the identity continuous linear map. The structure is only a definition of isotropy and includes no whitening or equivalence theorem.
-- source:
--   Source: Guédon–Milman, Interpolating thin-shell and sharp large-deviation estimates for isotropic log-concave measures (arXiv:1011.0943v3), item DISO; Jambulapati–Lee–Vempala, A slightly improved bound for the KLS constant (arXiv:2208.11644v2), item D3; Klartag–Lehec, Bourgain’s slicing problem and KLS isoperimetry up to polylog (arXiv:2203.15551v2), item D3; Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), item DISO. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Isotropic.lean#L30-L35 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Isotropic`, definition bundle `KLS408915f_FunctionalInequalities_KLS_Isotropic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
/-- A probability law with finite second moment, mean zero, and identity centered covariance.
The moment field prevents the totalized integral/covariance from encoding integrability. -/
structure Isotropic (μ : ProbabilityMeasure E) : Prop where
  memLp_two : MemLp id 2 (μ : Measure E)
  mean_zero : ∫ x, x ∂(μ : Measure E) = 0
  covariance_identity : Covariance.operator (μ : Measure E) = ContinuousLinearMap.id ℝ E
end KLS
end FunctionalInequalities


