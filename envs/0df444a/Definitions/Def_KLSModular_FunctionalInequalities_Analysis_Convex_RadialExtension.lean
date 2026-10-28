-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_RadialExtension
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_RadialExtension
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:58:29.337727+00:00
-- url     : https://prove2.me/theorems/da2489dd-75ed-4659-a13a-f2ad3f5ccb75
-- title:
--   Radial truncations and extension
-- statement:
--   For a set $K\subset E$, a real function $g$, a scalar $a$, and $x\in E$, `radialCut K g a x` equals $g(a x)$ as an extended-real value when $a x\in K$ and equals $+\infty$ otherwise. `radialScale n` is $1-1/(n+2)$, and `radialExtension K g x` is the supremum over $n$ of these radial cuts; the bundle includes auxiliary results identifying this construction with the radial extension under the stated convexity hypotheses.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Convex.Continuous
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Analysis.Convex.Topology
--   import Mathlib.Data.EReal.Operations
--   import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
--   import Mathlib.Topology.Instances.EReal.Lemmas
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def radialCut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--       (K : Set E) (g : E → ℝ) (a : ℝ) (x : E) : EReal := by
--     classical
--     exact if a • x ∈ K then (g (a • x) : EReal) else ⊤
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`radialExtension_radial_limit`](https://prove2.me/theorems/bbb9246f-b710-4e74-a805-3997176540ae)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean) · `FunctionalInequalities.Analysis.Convex.RadialExtension` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean#L54-L140 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.RadialExtension`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_RadialExtension`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
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


