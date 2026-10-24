-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:52:53.185544+00:00
-- url     : https://prove2.me/theorems/187571dc-ceb1-46ad-95b1-a61f71e8bf7f
-- title:
--   Affine subtraction from an extended-real potential
-- statement:
--   For $f:E\to\overline{\mathbb{R}}$, $a\in E$, $b\in\mathbb{R}$, and $x\in E$, `affineSubtract f a b x` is $f(x)-(\langle a,x\rangle+b)$, with the affine function coerced into the extended reals. The module records pointwise transformation properties of Legendre transforms, epigraph convexity, and normalization under such affine shifts.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L24-L26 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Affine`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
namespace FunctionalInequalities
namespace Analysis
section
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Subtract the actual affine function `inner a x + b`. -/
def affineSubtract (f : E → EReal) (a : E) (b : ℝ) (x : E) : EReal :=
  f x - ((inner ℝ a x + b : ℝ) : EReal)
end
end Analysis
end FunctionalInequalities


