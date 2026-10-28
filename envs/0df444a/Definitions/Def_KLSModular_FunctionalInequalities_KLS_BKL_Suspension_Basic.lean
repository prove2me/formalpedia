-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:04:41.393398+00:00
-- url     : https://prove2.me/theorems/aaa7527c-3ccd-45dd-876d-0915bc183526
-- title:
--   Finite-copy suspension potential
-- statement:
--   For a potential $V:E\to\mathbb{R}$, function $f:E\to\mathbb{R}$, real parameters $\beta,\sigma$, copy count $N$, and point $(s,x_1,\ldots,x_N)$, `potential V f beta sigma N` is $\sum_iV(x_i)+\beta\left|\sigma s-\frac{\sum_i f(x_i)}{\sqrt N}\right|$. The definition is made on $\mathbb{R}\times(\mathrm{Fin}\,N\to E)$ and does not impose positivity of $\beta$, a relation between $\sigma$ and $\beta$, or convexity.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Curvature
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def potential (V f : E → ℝ) (beta sigma : ℝ) (N : ℕ) (p : ℝ × (Fin N → E)) : ℝ :=
--     (∑ i, V (p.2 i)) + beta * |sigma * p.1 - (∑ i, f (p.2 i)) / Real.sqrt N|
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461).
--
--   Theorems in source order:
--
--   - [`convexOn_potential`](https://prove2.me/theorems/8bd14eff-e39b-41f3-a887-8c1cbe3d5c1e)
--   - [`exists_copies`](https://prove2.me/theorems/5967f3b2-764f-4fd4-8e97-8cae228211c5)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean) · `FunctionalInequalities.KLS.BKL.Suspension.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L24-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace Suspension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The potential (109) on one auxiliary coordinate and `N` copies of the original space.
In the paper `sigma = sqrt (1 + 2 / beta²)`. Convexity holds for every real `sigma`. -/
def potential (V f : E → ℝ) (beta sigma : ℝ) (N : ℕ) (p : ℝ × (Fin N → E)) : ℝ :=
  (∑ i, V (p.2 i)) + beta * |sigma * p.1 - (∑ i, f (p.2 i)) / Real.sqrt N|
end Suspension
end LogConcave
end KLS
end FunctionalInequalities


