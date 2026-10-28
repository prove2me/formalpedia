-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:08:26.434886+00:00
-- url     : https://prove2.me/theorems/34f067f9-b370-4131-a2be-776da314cea2
-- title:
--   Import context: KLS/BKL/Suspension/Density
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Suspension.Density` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Suspension.Law`, `FunctionalInequalities.Probability.Product`, `FunctionalInequalities.Probability.Transport`, and `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments`. It also directly imports the external prerequisite module `Mathlib.MeasureTheory.Measure.Tilted`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Suspension.Law
--   import FunctionalInequalities.Probability.Product
--   import FunctionalInequalities.Probability.Transport
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`KLS/LogConcave/Density/BorellRepresentation/Moments`](https://prove2.me/theorems/e5df2dc6-6ebd-4244-bfb5-41d46b1c70d1).
--
--   Theorems in source order:
--
--   - [`map_density_shift_scale`](https://prove2.me/theorems/09fdc8e8-bedc-44df-98aa-24cf3f553bd2)
--   - [`jointLaw_eq_tilted`](https://prove2.me/theorems/a3adf66f-9b93-4f82-ab91-3e0f0b7f991d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean) · `FunctionalInequalities.KLS.BKL.Suspension.Density` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean#L1-L405 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Suspension.Density`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Mathlib.MeasureTheory.Measure.Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments


