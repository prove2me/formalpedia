-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Dirichlet
-- name    : KLSModular_FunctionalInequalities_Energy_SmoothGradient_Dirichlet
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:12:45.41079+00:00
-- url     : https://prove2.me/theorems/9a06f3bf-ecba-4615-9943-6924b56d5b2f
-- title:
--   Import context: Energy/SmoothGradient/Dirichlet
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Energy.SmoothGradient.Dirichlet` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Energy.Form.Dirichlet`, `FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel`, `FunctionalInequalities.Energy.Relaxation.Contraction`, `FunctionalInequalities.Energy.SmoothGradient.Closed`, and `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Form.Dirichlet
--   import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel
--   import FunctionalInequalities.Energy.Relaxation.Contraction
--   import FunctionalInequalities.Energy.SmoothGradient.Closed
--   import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Form/Dirichlet`](https://prove2.me/theorems/0025f099-fed1-4255-868b-7850dd566303), [`Energy/Euclidean/LipschitzApproximation/Kernel`](https://prove2.me/theorems/d8350731-5ebe-4c22-a05d-d6b04921850a), [`Energy/Relaxation/Contraction`](https://prove2.me/theorems/5e5bc07e-0564-4f87-ab6c-1664038a9b10), [`Energy/SmoothGradient/Closed`](https://prove2.me/theorems/610cfdca-744b-4a8e-b534-46985471ae23), [`Energy/SmoothGradient/Intrinsic/Closed`](https://prove2.me/theorems/68a98bd0-06ea-4f37-962c-da6ced53e691).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) · `FunctionalInequalities.Energy.SmoothGradient.Dirichlet` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean#L1-L222 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Energy.SmoothGradient.Dirichlet`, import-context bundle `KLSModular_FunctionalInequalities_Energy_SmoothGradient_Dirichlet`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Dirichlet
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Contraction
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Closed
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Closed


