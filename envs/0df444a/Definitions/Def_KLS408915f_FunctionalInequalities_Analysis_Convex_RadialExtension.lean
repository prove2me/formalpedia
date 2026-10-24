-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:53:22.2922+00:00
-- url     : https://prove2.me/theorems/708088bd-fbf2-4bcf-abcc-14a74c94fe96
-- title:
--   Radial truncations and extension
-- statement:
--   For a set $K\subset E$, a real function $g$, a scalar $a$, and $x\in E$, `radialCut K g a x` equals $g(a x)$ as an extended-real value when $a x\in K$ and equals $+\infty$ otherwise. `radialScale n` is $1-1/(n+2)$, and `radialExtension K g x` is the supremum over $n$ of these radial cuts; the bundle includes auxiliary results identifying this construction with the radial extension under the stated convexity hypotheses.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean#L54-L140 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.RadialExtension`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open Set Filter
namespace FunctionalInequalities
namespace Analysis
section NormedSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
 def radialCut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (g : E → ℝ) (a : ℝ) (x : E) : EReal := by
  classical
  exact if a • x ∈ K then (g (a • x) : EReal) else ⊤
 def radialScale (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)
 def radialExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (g : E → ℝ) (x : E) : EReal :=
  ⨆ n, FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x
end NormedSpace
end Analysis
end FunctionalInequalities


