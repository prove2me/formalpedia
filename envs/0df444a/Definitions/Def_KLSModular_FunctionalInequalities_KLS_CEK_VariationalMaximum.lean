-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:05:16.587724+00:00
-- url     : https://prove2.me/theorems/60547a65-c647-4027-80b6-d75ac35d269f
-- title:
--   Import context: KLS/CEK/VariationalMaximum
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.VariationalMaximum` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.CEK.Competitors`, `FunctionalInequalities.Probability.MomentMeasure.Baseline`, `FunctionalInequalities.Probability.MomentMeasure.Compactness`, and `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`. It also directly imports the external prerequisite modules `Mathlib.Topology.Sequences` and `Mathlib.Topology.Order.IsLUB`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.CEK.Competitors
--   import FunctionalInequalities.Probability.MomentMeasure.Baseline
--   import FunctionalInequalities.Probability.MomentMeasure.Compactness
--   import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
--   import Mathlib.Topology.Sequences
--   import Mathlib.Topology.Order.IsLUB
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/CEK/Competitors`](https://prove2.me/theorems/410b5025-3a6c-4242-b99c-d26173c8306c), [`Probability/MomentMeasure/Baseline`](https://prove2.me/theorems/331104f9-69be-4e37-ad3b-9f7a18fb9444), [`Probability/MomentMeasure/Compactness`](https://prove2.me/theorems/cbdff6c6-a5ae-41ee-946b-9f0ca1da6699), [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Theorems in source order:
--
--   - [`exists_normalized_maximizing_sequence`](https://prove2.me/theorems/11706c73-d73a-45ce-a370-2f9ff07f3e79)
--   - [`exists_limit_ge_normalized_supremum`](https://prove2.me/theorems/9ad1f752-005f-403f-b340-5ef5a45400a5)
--   - [`exists_variational_maximum`](https://prove2.me/theorems/2658ff47-5952-426e-98f9-f3b3ec7e8d7b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean) · `FunctionalInequalities.KLS.CEK.VariationalMaximum` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L1-L216 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_Competitors
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Baseline
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.IsLUB


