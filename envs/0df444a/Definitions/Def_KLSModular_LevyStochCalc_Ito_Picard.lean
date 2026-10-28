-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_Picard
-- name    : KLSModular_LevyStochCalc_Ito_Picard
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:40:16.599176+00:00
-- url     : https://prove2.me/theorems/641877d8-7533-4330-9f7d-6b397b95165e
-- title:
--   Import context: LevyStochCalc/Ito/Picard
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.Picard` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Ito.PicardBieleckiNorm`, `LevyStochCalc.Ito.PicardStepMap`, `LevyStochCalc.Ito.PicardStochasticLipschitz`, `LevyStochCalc.Ito.PicardSelfMap`, `LevyStochCalc.Ito.PicardBieleckiContraction`, and `LevyStochCalc.Ito.PicardBieleckiContractionTight`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardBieleckiNorm
--   import LevyStochCalc.Ito.PicardStepMap
--   import LevyStochCalc.Ito.PicardStochasticLipschitz
--   import LevyStochCalc.Ito.PicardSelfMap
--   import LevyStochCalc.Ito.PicardBieleckiContraction
--   import LevyStochCalc.Ito.PicardBieleckiContractionTight
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd), [`LevyStochCalc/Ito/PicardStochasticLipschitz`](https://prove2.me/theorems/066a9b23-cba1-4058-a128-4d6a2feafaa6), [`LevyStochCalc/Ito/PicardSelfMap`](https://prove2.me/theorems/4005f73f-935b-4e7c-91e0-bf0d00e64657), [`LevyStochCalc/Ito/PicardBieleckiContraction`](https://prove2.me/theorems/4df7fed3-8c28-4531-b919-48a33d4a3638), [`LevyStochCalc/Ito/PicardBieleckiContractionTight`](https://prove2.me/theorems/1f650c26-7cae-4962-a900-d945b5cea83a).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/Picard.lean) · `LevyStochCalc.Ito.Picard` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/Picard.lean#L1-L43 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.Picard`, import-context bundle `KLSModular_LevyStochCalc_Ito_Picard`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/Picard.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardBieleckiNorm
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardStepMap
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardStochasticLipschitz
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSelfMap
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardBieleckiContraction
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardBieleckiContractionTight

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/Picard.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


