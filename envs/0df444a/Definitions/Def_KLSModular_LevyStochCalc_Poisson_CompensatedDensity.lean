-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensity
-- name    : KLSModular_LevyStochCalc_Poisson_CompensatedDensity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:24:29.875866+00:00
-- url     : https://prove2.me/theorems/5d793dac-4291-45a9-8c8f-10ac2e8f5a60
-- title:
--   Import context: LevyStochCalc/Poisson/CompensatedDensity
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Poisson.CompensatedDensity` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Poisson.CompensatedDensityTruncation`, `LevyStochCalc.Poisson.CompensatedDensityDyadic`, `LevyStochCalc.Poisson.CompensatedDensityShifted`, `LevyStochCalc.Poisson.CompensatedDensityRectSimple`, `LevyStochCalc.Poisson.CompensatedDensityMarkApprox`, `LevyStochCalc.Poisson.CompensatedDensityStepIntegral`, `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry`, `LevyStochCalc.Poisson.CompensatedDensityMarkSum`, `LevyStochCalc.Poisson.CompensatedDensityRefinement`, and `LevyStochCalc.Poisson.CompensatedDensityLimit`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.CompensatedDensityTruncation
--   import LevyStochCalc.Poisson.CompensatedDensityDyadic
--   import LevyStochCalc.Poisson.CompensatedDensityShifted
--   import LevyStochCalc.Poisson.CompensatedDensityRectSimple
--   import LevyStochCalc.Poisson.CompensatedDensityMarkApprox
--   import LevyStochCalc.Poisson.CompensatedDensityStepIntegral
--   import LevyStochCalc.Poisson.CompensatedDensityBoxIsometry
--   import LevyStochCalc.Poisson.CompensatedDensityMarkSum
--   import LevyStochCalc.Poisson.CompensatedDensityRefinement
--   import LevyStochCalc.Poisson.CompensatedDensityLimit
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/CompensatedDensityTruncation`](https://prove2.me/theorems/e036c7a8-99df-4c79-aaff-e942d6a377f3), [`LevyStochCalc/Poisson/CompensatedDensityDyadic`](https://prove2.me/theorems/1618166b-58d5-4b93-9f6e-e8ddd00b5532), [`LevyStochCalc/Poisson/CompensatedDensityShifted`](https://prove2.me/theorems/73d7f46e-5093-4665-887a-486735f73664), [`LevyStochCalc/Poisson/CompensatedDensityRectSimple`](https://prove2.me/theorems/3d1318b8-9b64-4ef2-92b7-cbf5b3e283ed), [`LevyStochCalc/Poisson/CompensatedDensityMarkApprox`](https://prove2.me/theorems/470e9703-aae6-4004-b5af-bb537a6daf3c), [`LevyStochCalc/Poisson/CompensatedDensityStepIntegral`](https://prove2.me/theorems/70765d64-5747-4f68-bb02-dbe01c7e590f), [`LevyStochCalc/Poisson/CompensatedDensityBoxIsometry`](https://prove2.me/theorems/f4d95c36-a6bd-4c97-ab03-197928b1aa9c), [`LevyStochCalc/Poisson/CompensatedDensityMarkSum`](https://prove2.me/theorems/753742de-bdd6-47cf-900f-79bc1629dbd3), [`LevyStochCalc/Poisson/CompensatedDensityRefinement`](https://prove2.me/theorems/b7324db9-d782-48ee-a64f-05a34047f6e5), [`LevyStochCalc/Poisson/CompensatedDensityLimit`](https://prove2.me/theorems/765e73df-8878-4970-8619-4e6895222e7b).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedDensity.lean) · `LevyStochCalc.Poisson.CompensatedDensity` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedDensity.lean#L1-L38 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Poisson.CompensatedDensity`, import-context bundle `KLSModular_LevyStochCalc_Poisson_CompensatedDensity`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedDensity.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedDensity.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


