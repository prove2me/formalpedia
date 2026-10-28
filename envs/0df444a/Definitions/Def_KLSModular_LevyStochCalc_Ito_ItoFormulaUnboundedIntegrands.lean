-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands
-- name    : KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:15:00.330984+00:00
-- url     : https://prove2.me/theorems/93dff424-3aa2-4db6-a70a-d760c8275626
-- title:
--   Import context: LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.ItoFormulaUnboundedClamp
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Theorems in source order:
--
--   - [`ae_tendsto_drift_clamp`](https://prove2.me/theorems/0d88cd49-1116-49bb-b468-6962f08cda7d)
--   - [`ae_tendsto_quadVar_clamp`](https://prove2.me/theorems/16916452-8c4c-472a-be6e-b3b0e160f768)
--   - [`tendsto_energy_coordDeriv_diff`](https://prove2.me/theorems/e842477b-9ddd-4040-94c5-e3ad7ba70732)
--   - [`tendsto_energy_diffusionIntegrand_clamp`](https://prove2.me/theorems/9cee699e-7563-482a-af58-2791b1f7cffd)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean) · `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L1-L402 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`, import-context bundle `KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


