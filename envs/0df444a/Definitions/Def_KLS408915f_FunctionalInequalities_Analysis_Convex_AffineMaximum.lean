-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:49:59.093423+00:00
-- url     : https://prove2.me/theorems/823e1712-8a1f-4864-9111-64f7cd8f0d45
-- title:
--   Finite affine maximum
-- statement:
--   For a nonempty finite set $s\subset E$, a real function $a:E\to\mathbb{R}$, and $y\in E$, `affineMaximum s hs a y` is the genuine finite maximum of $\langle x,y\rangle-a(x)$ over $x\in s$. The bundle also contains geometric auxiliary results controlling these maxima and comparing them with the extended-real Legendre transform.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L27-L29 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.AffineMaximum`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Filter Set
open scoped Topology
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A genuine finite maximum of the affine summands of a conjugate. -/
def affineMaximum (s : Finset E) (hs : s.Nonempty) (a : E → ℝ) (y : E) : ℝ :=
  s.sup' hs (fun x => inner ℝ x y - a x)
end Analysis
end FunctionalInequalities


