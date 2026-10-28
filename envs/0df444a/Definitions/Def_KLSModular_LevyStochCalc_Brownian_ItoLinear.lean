-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
-- name    : KLSModular_LevyStochCalc_Brownian_ItoLinear
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:22:40.243784+00:00
-- url     : https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a
-- title:
--   Import context: LevyStochCalc/Brownian/ItoLinear
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoLinear` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.ItoL2Completion`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoL2Completion
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoL2Completion`](https://prove2.me/theorems/15202148-c170-44c6-9af7-b9de285595f1).
--
--   Theorems in source order:
--
--   - [`lintegral_energy_parallelogram`](https://prove2.me/theorems/96c5aee3-d8ba-4423-8ee1-8a16ceb44213)
--   - [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315)
--   - [`lintegral_energy_const_mul`](https://prove2.me/theorems/ce857bc0-8f4c-4f64-b3bd-5184a06ec375)
--   - [`ae_eq_add_of_sq_distances`](https://prove2.me/theorems/99e33505-e2ff-46c1-a724-6a8f67657125)
--   - [`stochasticIntegralBrownian_add`](https://prove2.me/theorems/63f87c77-88d3-49b3-b12f-0856c509d6a6)
--   - [`ae_eq_const_mul_of_sq_distances`](https://prove2.me/theorems/bfc53c08-9b3b-4e24-881f-cb00e6aeeb58)
--   - [`stochasticIntegralBrownian_const_mul`](https://prove2.me/theorems/ac110cf4-8674-43ad-ab92-f7fde08971b6)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean) · `LevyStochCalc.Brownian.ItoLinear` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L1-L377 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoLinear`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoLinear`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2Completion

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


