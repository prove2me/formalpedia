-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaScalar
-- name    : KLSModular_LevyStochCalc_Brownian_ItoFormulaScalar
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:21:56.69031+00:00
-- url     : https://prove2.me/theorems/58932039-f65d-4b41-a617-bf3796b6492d
-- title:
--   Import context: LevyStochCalc/Brownian/ItoFormulaScalar
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoFormulaScalar` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.ItoQuadVarRiemann`, `LevyStochCalc.Brownian.ItoMartingaleRiemann`, and `LevyStochCalc.Brownian.ItoFormula`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoQuadVarRiemann
--   import LevyStochCalc.Brownian.ItoMartingaleRiemann
--   import LevyStochCalc.Brownian.ItoFormula
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoQuadVarRiemann`](https://prove2.me/theorems/b1a0e0c3-5d29-41b6-8cdf-5219bb6f71f9), [`LevyStochCalc/Brownian/ItoMartingaleRiemann`](https://prove2.me/theorems/a19ff47c-1595-4931-a8e8-afa8cea42789), [`LevyStochCalc/Brownian/ItoFormula`](https://prove2.me/theorems/9a3a4ed3-a4e2-4928-847c-4dc846ca923d).
--
--   Theorems in source order:
--
--   - [`integral_abs_le_sqrt_of_lintegral_sq_le`](https://prove2.me/theorems/fabb0c45-93fb-4537-bc15-bc10719aac9e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFormulaScalar.lean) · `LevyStochCalc.Brownian.ItoFormulaScalar` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFormulaScalar.lean#L1-L360 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoFormulaScalar`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoFormulaScalar`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFormulaScalar.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoMartingaleRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormula

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaScalar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


