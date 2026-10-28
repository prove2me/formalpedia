-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:18:51.644633+00:00
-- url     : https://prove2.me/theorems/ec55966f-66a5-4e3f-9fc7-b3e724ac29c7
-- title:
--   Import context: Analysis/BakryEmery/IteratedDerivative
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Analysis.InnerProductSpace.Calculus`, `Mathlib.Analysis.Calculus.FDeriv.Symmetric`, `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`, `Mathlib.Analysis.Calculus.BumpFunction.Normed`, and `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.Calculus
--   import Mathlib.Analysis.Calculus.FDeriv.Symmetric
--   import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
--   import Mathlib.Analysis.Calculus.BumpFunction.Normed
--   import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`iteratedFDeriv_inner_self_apply`](https://prove2.me/theorems/93b102a6-8056-49d9-b513-0807baf24636)
--   - [`iteratedFDeriv_succ_comp_perm_of_fix_zero`](https://prove2.me/theorems/cc6ef6bd-ffe5-427d-b172-1c1aebc1558a)
--   - [`iteratedFDeriv_comp_swap_zero_one`](https://prove2.me/theorems/b0248a78-8f38-49b0-948c-7fe54558fabb)
--   - [`iteratedFDeriv_comp_perm_of_contDiff`](https://prove2.me/theorems/62e73549-6b73-43c8-a852-062236b36219)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean) · `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L1-L445 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct


