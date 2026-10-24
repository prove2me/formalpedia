-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:50:22.427131+00:00
-- url     : https://prove2.me/theorems/ce4f2164-b329-4833-885c-779ac1191b57
-- title:
--   Subgradient image of a set
-- statement:
--   For $u:E\to\mathbb{R}$ on a real inner-product space and $S\subset E$, `subgradientImage u S` is the set of all $p\in E$ for which there exists $x\in S$ such that $u(x)+\langle p,y-x\rangle\le u(y)$ for every $y\in E$. Thus it is the image, over $S$, of the pointwise subdifferential; the module also contains differentiability, gradient-image, and injectivity auxiliary results for convex functions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L983-L987 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
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
open scoped RealInnerProductSpace
section LT12ASubgradientImageMonotone
open Set
open scoped RealInnerProductSpace
open scoped Topology
namespace FunctionalInequalities
namespace Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The **subgradient image** `∂u(S) = {p | ∃ x ∈ S, p is a subgradient of u at x}` (weak Letwin
route, routes/letwin-weak-definitions.md item 2). -/
def subgradientImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (S : Set E) : Set E :=
  {p | ∃ x ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}
end InnerProduct
end Analysis
end FunctionalInequalities
end LT12ASubgradientImageMonotone


