-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
-- name    : KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:47:41.376473+00:00
-- url     : https://prove2.me/theorems/9b6797f6-94f3-42de-b251-b6a20813e4ac
-- title:
--   Action of a Stein kernel matrix
-- statement:
--   For a `KernelMatrix n` $T$ and $v \in \operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin} n)$, `action T v` is the Euclidean vector obtained by applying the matrix-vector product $T v$ in the underlying $L^2$ representation and converting it back to `EuclideanSpace`. This is the basic action associated with the Stein-kernel object.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Stein/Kernel.lean#L24-L26 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Stein.Kernel`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Stein_Kernel`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff Matrix.Norms.Frobenius
noncomputable section
namespace FunctionalInequalities
namespace Probability
namespace Stein
/-- The action `T v` of a kernel matrix on a Euclidean vector. -/
def action {n : ℕ} (T : KernelMatrix n) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (T.mulVec v.ofLp)
end Stein
end Probability
end FunctionalInequalities
end


