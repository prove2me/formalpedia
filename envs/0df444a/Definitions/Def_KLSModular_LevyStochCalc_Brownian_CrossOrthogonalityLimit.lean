-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit
-- name    : KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:06:26.899418+00:00
-- url     : https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74
-- title:
--   Import context: LevyStochCalc/Brownian/CrossOrthogonalityLimit
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.CrossOrthogonalityLimit` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.CrossOrthogonalityDirectCross
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/CrossOrthogonalityDirectCross`](https://prove2.me/theorems/fd42d764-e99f-4994-8020-f8822509f5ef).
--
--   Theorems in source order:
--
--   - [`integrable_cross_term`](https://prove2.me/theorems/7e5b804f-7b35-4962-9762-372081226c2c)
--   - [`integral_cross_increment_eq_zero_of_le`](https://prove2.me/theorems/cad27d60-eab1-4df3-bc16-26fa2ac60f01)
--   - [`integrable_and_integral_cross_clamped`](https://prove2.me/theorems/79cd0607-bfb0-45c8-8086-36a38db2872c)
--   - [`integral_simpleIntegral_mul_eq_zero`](https://prove2.me/theorems/86d5362c-5613-4331-b577-05629cdbfba1)
--   - [`memLp_simpleIntegral`](https://prove2.me/theorems/7c5f50d8-edb5-487c-a4bf-6c19ad9a378c)
--   - [`integral_mul_eq_zero_of_tendsto_eLpNorm`](https://prove2.me/theorems/9e82e98b-0377-41ae-b977-70c8c0709ea7)
--   - [`integral_stochasticIntegral_mul_eq_zero`](https://prove2.me/theorems/a9eee61c-6570-4194-86d3-3b8045d9de2c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean) · `LevyStochCalc.Brownian.CrossOrthogonalityLimit` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L1-L405 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, import-context bundle `KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


