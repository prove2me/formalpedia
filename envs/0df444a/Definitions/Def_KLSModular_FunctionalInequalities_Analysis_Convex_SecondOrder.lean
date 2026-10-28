-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:00:24.828091+00:00
-- url     : https://prove2.me/theorems/25ef7ab1-0f22-4192-9c58-d196bc21f161
-- title:
--   Import context: Analysis/Convex/SecondOrder
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Convex.SecondOrder` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Convex.Subgradient`, `FunctionalInequalities.Analysis.Convex.Proximal`, and `FunctionalInequalities.Analysis.Sard.Equidimensional`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Integral.Lebesgue.Add`, `Mathlib.Analysis.Calculus.Taylor`, `Mathlib.Analysis.Calculus.ContDiff.Convolution`, `Mathlib.Analysis.Calculus.Rademacher`, and `Mathlib.MeasureTheory.Function.Jacobian`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Subgradient
--   import FunctionalInequalities.Analysis.Convex.Proximal
--   import Mathlib.MeasureTheory.Integral.Lebesgue.Add
--   import Mathlib.Analysis.Calculus.Taylor
--   import Mathlib.Analysis.Calculus.ContDiff.Convolution
--   import FunctionalInequalities.Analysis.Sard.Equidimensional
--   import Mathlib.Analysis.Calculus.Rademacher
--   import Mathlib.MeasureTheory.Function.Jacobian
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7), [`Analysis/Convex/Proximal`](https://prove2.me/theorems/1d665bc1-5792-4d08-9238-1bf12adef58c), [`Analysis/Sard/Equidimensional`](https://prove2.me/theorems/80d2be47-45ea-475d-bc64-280cf904a801).
--
--   Theorems in source order:
--
--   - [`resolvent_preimage_near`](https://prove2.me/theorems/253f1fd8-dbe8-46e5-8918-38675b5d625a)
--   - [`subgradient_expansion_of_hasFDerivAt_resolvent`](https://prove2.me/theorems/87eddc48-68f3-46a2-9e7f-49882aba3799)
--   - [`tendsto_integral_secondDifference_mul`](https://prove2.me/theorems/4354b6fd-00d6-4dd4-9dfb-0b7b24838470)
--   - [`integral_mul_le_integral_mul_sum_iteratedFDeriv`](https://prove2.me/theorems/a34ffeae-071d-4fec-b551-07733fa204a2)
--   - [`ae_exists_secondOrder_expansion`](https://prove2.me/theorems/5eb08b15-cdd6-4026-aca8-c20821e30f23)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean) · `FunctionalInequalities.Analysis.Convex.SecondOrder` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L1-L682 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Sard_Equidimensional
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian


