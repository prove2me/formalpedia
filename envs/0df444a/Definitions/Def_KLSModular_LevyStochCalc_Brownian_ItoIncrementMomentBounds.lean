-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
-- name    : KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:06:20.427976+00:00
-- url     : https://prove2.me/theorems/c885777c-b44d-403b-b189-0d5182c90d15
-- title:
--   Import context: LevyStochCalc/Brownian/ItoIncrementMomentBounds
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoIncrementMomentBounds` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.ItoIncrementMomentRestrict`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoIncrementMomentRestrict
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoIncrementMomentRestrict`](https://prove2.me/theorems/6729fab9-4d54-4cac-a286-3a20b472164d).
--
--   Theorems in source order:
--
--   - [`lintegral_stochasticIntegralBrownian_pow_four_le_Ioc`](https://prove2.me/theorems/3c8eb92c-71e5-402e-87c0-a64cd8942cd0)
--   - [`lintegral_stochasticIntegralBrownian_sub_pow_four_le`](https://prove2.me/theorems/65902486-10fb-4581-8867-4b4a6cc14280)
--   - [`lintegral_stochasticIntegralBrownian_sub_sq_le`](https://prove2.me/theorems/0e7c5bb8-1257-4ddd-a411-f3d6af20e053)
--   - [`integral_sub_pow_four_le`](https://prove2.me/theorems/12ff2533-d8a3-4978-a4f3-a45469d7fa7c)
--   - [`integral_sub_sq_le`](https://prove2.me/theorems/943c5a51-ca07-4807-82e3-773eb2dc5277)
--   - [`integral_abs_sub_pow_three_le`](https://prove2.me/theorems/a7606041-e2f6-444b-9bd8-b9c435c0037c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean) · `LevyStochCalc.Brownian.ItoIncrementMomentBounds` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L1-L551 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoIncrementMomentBounds`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


