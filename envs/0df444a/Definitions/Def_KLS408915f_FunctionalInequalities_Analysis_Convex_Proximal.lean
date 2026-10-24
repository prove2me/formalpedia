-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:51:11.526572+00:00
-- url     : https://prove2.me/theorems/8c9fa085-0363-4ec3-abe2-5c4b78739f54
-- title:
--   Proximal point selector
-- statement:
--   For $f:E\to\mathbb{R}$ and $z\in E$, `proximalPoint f z` is the classical choice of a point $x$ satisfying $f(x)+\langle z-x,y-x\rangle\le f(y)$ for every $y\in E$, selected by `Classical.epsilon`. This expresses the resolvent condition $z-x\in\partial f(x)$; existence and uniqueness for convex finite-dimensional functions are discussed by the surrounding development rather than assumed in this definition.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L126-L130 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
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
section LT12D2ProximalPoint
open Set
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The **proximal point** (resolvent of the subdifferential) of `f` at `z`: a point `x` such that
`z − x` is a subgradient of `f` at `x`, i.e. the minimiser of `x ↦ f x + ½‖x − z‖²` (weak Letwin route,
Alexandrov's theorem). For convex `f` on a finite-dimensional space it exists and is unique. -/
def proximalPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) (z : E) : E :=
  Classical.epsilon fun x => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y
end InnerProduct
end Analysis
end FunctionalInequalities
end LT12D2ProximalPoint


