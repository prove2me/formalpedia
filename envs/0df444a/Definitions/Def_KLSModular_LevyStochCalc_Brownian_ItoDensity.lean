-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensity
-- name    : KLSModular_LevyStochCalc_Brownian_ItoDensity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:59:59.098832+00:00
-- url     : https://prove2.me/theorems/bfa7a398-2539-4893-bbe5-a70374f778e6
-- title:
--   Import context: LevyStochCalc/Brownian/ItoDensity
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoDensity` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.ItoDensityDyadicAverages`, `LevyStochCalc.Brownian.ItoDensityShiftedAverages`, `LevyStochCalc.Brownian.ItoDensityPointwise`, `LevyStochCalc.Brownian.ItoDensityPredictableL2`, and `LevyStochCalc.Brownian.ItoDensityUnbounded`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoDensityDyadicAverages
--   import LevyStochCalc.Brownian.ItoDensityShiftedAverages
--   import LevyStochCalc.Brownian.ItoDensityPointwise
--   import LevyStochCalc.Brownian.ItoDensityPredictableL2
--   import LevyStochCalc.Brownian.ItoDensityUnbounded
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoDensityDyadicAverages`](https://prove2.me/theorems/0b508cbb-d331-4203-8be8-f69491695e96), [`LevyStochCalc/Brownian/ItoDensityShiftedAverages`](https://prove2.me/theorems/cd4e145d-263d-4ccd-8e8e-46421cf25253), [`LevyStochCalc/Brownian/ItoDensityPointwise`](https://prove2.me/theorems/a6789458-c313-4564-9fce-c87a1818fed2), [`LevyStochCalc/Brownian/ItoDensityPredictableL2`](https://prove2.me/theorems/36feb9b9-02b5-4c75-821f-6ecf3c0909c9), [`LevyStochCalc/Brownian/ItoDensityUnbounded`](https://prove2.me/theorems/1e3b7a6b-90eb-449e-b4d9-54ddf0f67a58).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoDensity.lean) · `LevyStochCalc.Brownian.ItoDensity` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoDensity.lean#L1-L26 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoDensity`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoDensity`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoDensity.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityUnbounded

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoDensity.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


