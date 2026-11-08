-- Prove2me | Definitions.Def_OAIQ098G305
-- name    : OAIQ098G305
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:14:53.359562+00:00
-- url     : https://prove2.me/theorems/ddafe647-42da-4890-bc62-392fa6277383
-- title:
--   Definitions bundle OAIQ098G305 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.trans12_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G235`, `OAIQ098G237`, `OAIQ098G240`, `OAIQ098G242`, `OAIQ098G250`, `OAIQ098G256`, `OAIQ098G271`, `OAIQ098G274`, `OAIQ098G292` and `OAIQ098G299` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G307`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G235
import Definitions.Def_OAIQ098G237
import Definitions.Def_OAIQ098G240
import Definitions.Def_OAIQ098G242
import Definitions.Def_OAIQ098G250
import Definitions.Def_OAIQ098G256
import Definitions.Def_OAIQ098G271
import Definitions.Def_OAIQ098G274
import Definitions.Def_OAIQ098G292
import Definitions.Def_OAIQ098G299

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans12_r0 : Fin 16 → Fin 16 → CBox := ![trans12_r0_0,trans12_r0_1,trans12_r0_2,trans12_r0_3,trans12_r0_4,trans12_r0_5,trans12_r0_6,trans12_r0_7,trans12_r0_8,trans12_r0_9,trans12_r0_10,trans12_r0_11,trans12_r0_12,trans12_r0_13,trans12_r0_14,trans12_r0_15]
end SharpPlanar.CachedData

end OAI
end


