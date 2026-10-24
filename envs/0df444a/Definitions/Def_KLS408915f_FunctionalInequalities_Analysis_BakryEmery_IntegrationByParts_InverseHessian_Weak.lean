-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:49:27.848244+00:00
-- url     : https://prove2.me/theorems/f29f5839-0a6a-4683-b367-d13411f6a6a0
-- title:
--   Coordinate densities for weak inverse-Hessian identities
-- statement:
--   For functions on `EuclideanSpace ℝ (Fin n)`, `coord f i x` is the directional derivative $Df(x)[e_i]$, `weightedTest u a f i x` is $a(x)e^{-u(x)}\,\operatorname{coord}(f,i,x)$, and `energyDensity u a f x` is $e^{-u(x)}$ times the inverse-Hessian contraction $\sum_{i,j}(\nabla^2u(x))^{-1}_{ij}\,\operatorname{coord}(a,i,x)\operatorname{coord}(f,j,x)$. `generatorDensity u V a f x` is $a(x)e^{-u(x)}$ times $\operatorname{tr}((\nabla^2u(x))^{-1}\nabla^2f(x))-DV(\nabla u(x))[\nabla f(x)]$. These private definitions support the weak integration-by-parts identities; the displayed bundle does not change their stated measurability or regularity assumptions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L383-L402 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities
namespace Analysis
 abbrev coord {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)
 def weightedTest {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * Real.exp (-u x) * FunctionalInequalities.Analysis.coord f i x
 def energyDensity {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j * FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x) *
    Real.exp (-u x)
 def generatorDensity {n : ℕ}
    (u V a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * (((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
    fderiv ℝ V (gradient u x) (gradient f x)) * Real.exp (-u x)
end Analysis
end FunctionalInequalities
end GeneratorIdentities


