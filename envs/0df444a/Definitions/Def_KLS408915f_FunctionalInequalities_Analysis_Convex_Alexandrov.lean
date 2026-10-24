-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:50:45.674934+00:00
-- url     : https://prove2.me/theorems/f51bb7c1-9fa3-44a1-85df-7926e918407e
-- title:
--   Quadratic test function at a point
-- statement:
--   For $A\in\mathbb{R}^{n\times n}$, $x_0,b,x\in\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin} n)$, and $c\in\mathbb{R}$, `quadraticAt A x₀ b c x` is $c+\langle b,x-x_0\rangle+\frac12\langle x-x_0,A(x-x_0)\rangle$. It is the quadratic test used in the weak Alexandrov and viscosity development, which also contains push-forward and geometric auxiliary results.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1414-L1418 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal
namespace FunctionalInequalities
namespace Analysis
/-- The quadratic function with constant `c`, slope `b` and Hessian matrix `A` centred at `x₀`:
`Q x = c + ⟪b, x − x₀⟫ + ½ ⟪x − x₀, A (x − x₀)⟫` (weak Letwin route, viscosity tests). -/
def quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  c + ⟪b, x - x₀⟫ + (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin A (x - x₀)⟫
end Analysis
end FunctionalInequalities
end LT12C1QuadraticSubgradientImage


