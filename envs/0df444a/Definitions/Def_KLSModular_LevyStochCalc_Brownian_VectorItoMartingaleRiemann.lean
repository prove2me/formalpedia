-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoMartingaleRiemann
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoMartingaleRiemann
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:16:58.693671+00:00
-- url     : https://prove2.me/theorems/a66fc89f-aa33-4950-8eab-8f30c14892aa
-- title:
--   Import context: LevyStochCalc/Brownian/VectorItoMartingaleRiemann
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.VectorItoMartingaleRiemann` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.VectorItoProcessWindow` and `LevyStochCalc.Brownian.ItoMartingaleRiemann`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoProcessWindow
--   import LevyStochCalc.Brownian.ItoMartingaleRiemann
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoProcessWindow`](https://prove2.me/theorems/f50cced8-08df-49bf-bf67-426674e3401c), [`LevyStochCalc/Brownian/ItoMartingaleRiemann`](https://prove2.me/theorems/a19ff47c-1595-4931-a8e8-afa8cea42789).
--
--   Theorems in source order:
--
--   - [`IsVectorItoVersion.lintegral_sq_frozen_sub_le`](https://prove2.me/theorems/9644b3b1-54f1-4a8b-9c01-eff516b61ba6)
--   - [`IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le`](https://prove2.me/theorems/74d597a9-d0f7-4590-b8a5-d44291007272)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean) · `LevyStochCalc.Brownian.VectorItoMartingaleRiemann` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean#L1-L232 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.VectorItoMartingaleRiemann`, import-context bundle `KLSModular_LevyStochCalc_Brownian_VectorItoMartingaleRiemann`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessWindow
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoMartingaleRiemann

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


