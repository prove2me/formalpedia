-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:52:38.813469+00:00
-- url     : https://prove2.me/theorems/6de8b4f3-82d1-49ee-b142-fc0f4080edbc
-- title:
--   Ball-truncated convex conjugate
-- statement:
--   For a real inner-product space $E$, a real function $u:E\to\mathbb{R}$, $M\in\mathbb{R}$, and $p\in E$, `truncatedConjugate u M p` is the supremum of $\langle p,x\rangle-u(x)$ over the closed ball $\{x:\|x\|\le M\}$. It is the finite-ball truncation used in the weak Caffarelli strict-convexity development, which also contains geometric comparison lemmas.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1279-L1284 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F2TruncatedConjugate
open Set Metric
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
/-- The **ball-truncated conjugate** `p ↦ sup_{‖x‖ ≤ M} (⟪p, x⟫ − u x)` (weak Letwin route;
KLS500 `truncatedLegendrePotential`): a globally finite convex function that agrees with the Legendre
transform of `u` wherever the supremum is attained inside the ball. -/
def truncatedConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (M : ℝ) (p : E) : ℝ :=
  sSup ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M)
end Analysis
end FunctionalInequalities
end LT11F2TruncatedConjugate


