-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds
-- name    : KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:37:46.283799+00:00
-- url     : https://prove2.me/theorems/db501a14-f954-4e21-a7e6-2ee411f6aff8
-- title:
--   Import context: LevyStochCalc/Brownian/ContinuityKolmogorovBounds
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.ContinuityDyadicChaining`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ContinuityDyadicChaining
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Theorems in source order:
--
--   - [`kolmogorov_markov_bound`](https://prove2.me/theorems/cc3bbae1-93c7-4b2a-a726-18938f9d796c)
--   - [`kc_level_bad_measure`](https://prove2.me/theorems/0aab2f8f-d712-4737-86f0-b7eebb793739)
--   - [`exists_tendsto_of_local_holder`](https://prove2.me/theorems/46c83da3-bc37-4fcf-a556-d68a3d13e420)
--   - [`kc_ae_increment_bound`](https://prove2.me/theorems/87c978a6-33c4-4d46-8fa8-81294193f4ae)
--   - [`kc_ae_interval_holder`](https://prove2.me/theorems/4c8f4cad-b521-472c-8c8e-9ef103021114)
--   - [`kc_ae_nbhd_holder`](https://prove2.me/theorems/61ee6149-778a-4170-b841-7de89dc30569)
--   - [`kolmogorov_modification_ae_eq`](https://prove2.me/theorems/82073c74-a718-40a3-bc28-fdee99fa3cee)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean) · `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L1-L518 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


