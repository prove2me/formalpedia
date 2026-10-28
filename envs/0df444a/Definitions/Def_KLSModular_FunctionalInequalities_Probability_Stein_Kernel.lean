-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
-- name    : KLSModular_FunctionalInequalities_Probability_Stein_Kernel
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:25:19.55716+00:00
-- url     : https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e
-- title:
--   Action of a Stein kernel matrix
-- statement:
--   For a `KernelMatrix n` $T$ and $v \in \operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin} n)$, `action T v` is the Euclidean vector obtained by applying the matrix-vector product $T v$ in the underlying $L^2$ representation and converting it back to `EuclideanSpace`. This is the basic action associated with the Stein-kernel object.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.Analysis.Matrix.Normed
--   import Mathlib.MeasureTheory.Function.LocallyIntegrable
--   import FunctionalInequalities.L2.Pairing
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def action {n : ℕ} (T : KernelMatrix n) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
--     WithLp.toLp 2 (T.mulVec v.ofLp)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`L2/Pairing`](https://prove2.me/theorems/a600d495-e861-43ba-9e2e-1a9a446c488b), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Stein/Kernel.lean) · `FunctionalInequalities.Probability.Stein.Kernel` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Stein/Kernel.lean#L24-L26 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Stein.Kernel`, definition bundle `KLSModular_FunctionalInequalities_Probability_Stein_Kernel`; the repository is private at upload time).

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_L2_Pairing
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates

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


