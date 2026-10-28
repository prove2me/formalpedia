-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedLimit
-- name    : KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:17:10.645357+00:00
-- url     : https://prove2.me/theorems/8c696e51-9810-4fbb-b0f0-ded116e9b79e
-- title:
--   Import context: LevyStochCalc/Ito/ItoFormulaUnboundedLimit
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.ItoFormulaUnboundedLimit` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands`](https://prove2.me/theorems/93dff424-3aa2-4db6-a70a-d760c8275626).
--
--   Theorems in source order:
--
--   - [`exists_seq_ae_tendsto_stochInt_clamp`](https://prove2.me/theorems/bdc5e606-3379-4cae-bf91-d24473c129d6)
--   - [`itoFormula_of_unbounded_coeff`](https://prove2.me/theorems/26b3bb9f-845f-407e-8e95-6d9fce1413b9)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean) · `LevyStochCalc.Ito.ItoFormulaUnboundedLimit` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean#L1-L367 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.ItoFormulaUnboundedLimit`, import-context bundle `KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedLimit`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


