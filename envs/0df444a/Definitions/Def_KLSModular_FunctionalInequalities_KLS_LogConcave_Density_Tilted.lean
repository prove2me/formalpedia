-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:27:36.474804+00:00
-- url     : https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38
-- title:
--   Import context: KLS/LogConcave/Density/Tilted
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.Density.Tilted` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Density.FromBorell`, `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction`, `FunctionalInequalities.Probability.LogConcave`, and `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic`. It also directly imports the external prerequisite module `Mathlib.MeasureTheory.Measure.Tilted`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.FromBorell
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction
--   import FunctionalInequalities.Probability.LogConcave
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/FromBorell`](https://prove2.me/theorems/00e3f459-8f58-45e1-b963-0ebabbdb71ad), [`KLS/LogConcave/Density/BorellRepresentation/Construction`](https://prove2.me/theorems/533a10b6-a945-4efc-bb81-9cda52d67d80), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548).
--
--   Theorems in source order:
--
--   - [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70)
--   - [`integral_exp_neg_pos_of_eq_tilted`](https://prove2.me/theorems/fb765bf9-81da-4922-b614-0b50e7223f1c)
--   - [`rpow_mul_rpow_le_of_convexOn`](https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5)
--   - [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de)
--   - [`interior_support_nonempty_of_eq_tilted`](https://prove2.me/theorems/f9e547f0-9041-4fe6-9d08-ab4991b4217f)
--   - [`convexOn_of_eq_tilted`](https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc)
--   - [`logConcave_of_eq_regularClass`](https://prove2.me/theorems/a4ee60d4-3b28-491b-804e-e9c2455e28ed)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean) · `FunctionalInequalities.KLS.LogConcave.Density.Tilted` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L1-L315 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Mathlib.MeasureTheory.Measure.Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic


