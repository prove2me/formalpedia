-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:14:00.468+00:00
-- url     : https://prove2.me/theorems/8f8fed5f-bb75-4985-83e7-6765eeac8110
-- title:
--   Import context: LevyStochCalc/Brownian/VectorItoFormulaDecomp
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.VectorItoFormulaDecomp` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.VectorItoTaylor`, `LevyStochCalc.Brownian.CoordDerivative`, and `LevyStochCalc.Brownian.VectorItoProcessVersion`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoTaylor
--   import LevyStochCalc.Brownian.CoordDerivative
--   import LevyStochCalc.Brownian.VectorItoProcessVersion
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoTaylor`](https://prove2.me/theorems/e2f63476-dcbb-4f48-b908-f9b176dad140), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Theorems in source order:
--
--   - [`sum_range_add_sum_comm`](https://prove2.me/theorems/3691605f-5bd6-4983-af72-18ade5e5f6bc)
--   - [`sum_apply_fderiv₂_eq`](https://prove2.me/theorems/e68e16a1-d8ff-49b3-9798-30a9e8ff8724)
--   - [`sum_apply_fderiv_eq`](https://prove2.me/theorems/77c8b45b-4dd4-41fe-8c61-8f62aefbbe0d)
--   - [`IsVectorItoVersion.vectorItoFormula_decomp_ae`](https://prove2.me/theorems/33331f90-4a12-4797-b7d5-47e2dc7611ad)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean) · `LevyStochCalc.Brownian.VectorItoFormulaDecomp` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L1-L224 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.VectorItoFormulaDecomp`, import-context bundle `KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTaylor
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


