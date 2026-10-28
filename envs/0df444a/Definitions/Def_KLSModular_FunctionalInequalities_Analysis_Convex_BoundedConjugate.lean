-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:58:51.327148+00:00
-- url     : https://prove2.me/theorems/04a83231-075b-4ff4-b344-919421d39a97
-- title:
--   Closed-ball cap of an extended-real potential
-- statement:
--   For an extended-real potential $\varphi:E\to\overline{\mathbb{R}}$ and $L\in\mathbb{R}_{\ge0}$, `closedBallCap φ L` equals $\varphi$ on the closed ball of radius $L$ centered at $0$ and equals $+\infty$ outside that ball. The surrounding results establish lower semicontinuity and bounded-domain consequences for the Legendre transform, including finiteness and Lipschitz bounds under the listed hypotheses.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Legendre
--   import Mathlib.Analysis.Normed.Module.Convex
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Topology.Semicontinuity.Basic
--   import Mathlib.Topology.MetricSpace.Lipschitz
--   import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def closedBallCap (φ : E → EReal) (L : NNReal) : E → EReal := by
--     classical
--     exact fun x => if x ∈ closedBall (0 : E) (L : ℝ) then φ x else ⊤
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Theorems in source order:
--
--   - [`closedBallCap_lowerSemicontinuous`](https://prove2.me/theorems/de51ab97-7601-407d-8eec-11705d7f5fe2)
--   - [`exists_real_global_minimum_of_bounded_domain`](https://prove2.me/theorems/7afbf80a-1864-49d4-8e93-ff4674a5643f)
--   - [`legendre_le_of_real_lower_bound`](https://prove2.me/theorems/36c3f5d5-3ca4-4d66-abff-68d4394870f7)
--   - [`real_convexOn_legendre`](https://prove2.me/theorems/fbb08d4f-988c-4d02-8aba-5ffd7f1a1919)
--   - [`lipschitzWith_real_legendre`](https://prove2.me/theorems/a855a68c-6e7d-4b04-a93c-aa344c92d581)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean) · `FunctionalInequalities.Analysis.Convex.BoundedConjugate` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L35-L38 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section
namespace FunctionalInequalities
namespace Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Restrict an extended-real potential to the closed ball, assigning top outside. -/
noncomputable def closedBallCap (φ : E → EReal) (L : NNReal) : E → EReal := by
  classical
  exact fun x => if x ∈ closedBall (0 : E) (L : ℝ) then φ x else ⊤
end Analysis
end FunctionalInequalities


