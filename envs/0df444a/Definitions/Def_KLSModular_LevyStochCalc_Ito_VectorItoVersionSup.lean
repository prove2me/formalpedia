-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionSup
-- name    : KLSModular_LevyStochCalc_Ito_VectorItoVersionSup
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:08:32.012248+00:00
-- url     : https://prove2.me/theorems/eac19afb-1a3e-420c-b0c9-4e8c576afefc
-- title:
--   Import context: LevyStochCalc/Ito/VectorItoVersionSup
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.VectorItoVersionSup` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Ito.VectorItoProcessDiff` and `LevyStochCalc.Probability.DoobContinuous`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.VectorItoProcessDiff
--   import LevyStochCalc.Probability.DoobContinuous
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/VectorItoProcessDiff`](https://prove2.me/theorems/cd1eb156-9d40-4d90-80b1-58b54714509a), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Theorems in source order:
--
--   - [`martingale_finsetSum`](https://prove2.me/theorems/fba98d15-9105-40a1-9195-5076f35b1f94)
--   - [`lintegral_iSup_sq_norm_version_sub_le`](https://prove2.me/theorems/3d71b361-cb18-4a6b-a812-4786fccd9817)
--   - [`lintegral_energy_sub_le`](https://prove2.me/theorems/b2a75191-454e-466b-aa72-6635b7bb48fd)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionSup.lean) · `LevyStochCalc.Ito.VectorItoVersionSup` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionSup.lean#L1-L422 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.VectorItoVersionSup`, import-context bundle `KLSModular_LevyStochCalc_Ito_VectorItoVersionSup`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionSup.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


