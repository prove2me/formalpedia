-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum
-- name    : KLSModular_LevyStochCalc_Brownian_ItoFinsetSum
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:54:10.355454+00:00
-- url     : https://prove2.me/theorems/3c65a1ac-837e-48a1-b323-dc87feeb6397
-- title:
--   Import context: LevyStochCalc/Brownian/ItoFinsetSum
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoFinsetSum` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.ItoLinear`, `LevyStochCalc.Brownian.ItoAlgebra`, and `LevyStochCalc.Brownian.ItoZero`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoLinear
--   import LevyStochCalc.Brownian.ItoAlgebra
--   import LevyStochCalc.Brownian.ItoZero
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a), [`LevyStochCalc/Brownian/ItoAlgebra`](https://prove2.me/theorems/602bc476-bf93-48d5-972e-3d6b80e662e4), [`LevyStochCalc/Brownian/ItoZero`](https://prove2.me/theorems/77654a98-9480-46ac-8fe1-93718b5d7f8a).
--
--   Theorems in source order:
--
--   - [`stochasticIntegralBrownian_neg`](https://prove2.me/theorems/5492f889-dcf9-4710-b8c2-bd3dcd30d16a)
--   - [`stochasticIntegralBrownian_sub`](https://prove2.me/theorems/a954497d-231b-4ebc-910f-e11817f51410)
--   - [`exists_stochasticIntegralBrownian_finsetSum`](https://prove2.me/theorems/b0d141d4-c156-4326-80cf-9bf508518511)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFinsetSum.lean) · `LevyStochCalc.Brownian.ItoFinsetSum` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFinsetSum.lean#L1-L179 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoFinsetSum`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoFinsetSum`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFinsetSum.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebra
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoZero

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFinsetSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


