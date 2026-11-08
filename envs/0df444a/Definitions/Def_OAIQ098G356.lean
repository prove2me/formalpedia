-- Prove2me | Definitions.Def_OAIQ098G356
-- name    : OAIQ098G356
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:16:59.905208+00:00
-- url     : https://prove2.me/theorems/ba64cc9f-057a-4c03-baf0-9c665badc0ee
-- title:
--   Definitions bundle OAIQ098G356 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.trans10_r1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G308`, `OAIQ098G311`, `OAIQ098G314`, `OAIQ098G317`, `OAIQ098G324`, `OAIQ098G326`, `OAIQ098G328`, `OAIQ098G338` and `OAIQ098G345` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G358`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G308
import Definitions.Def_OAIQ098G311
import Definitions.Def_OAIQ098G314
import Definitions.Def_OAIQ098G317
import Definitions.Def_OAIQ098G324
import Definitions.Def_OAIQ098G326
import Definitions.Def_OAIQ098G328
import Definitions.Def_OAIQ098G338
import Definitions.Def_OAIQ098G345

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def trans10_r1 : Fin 16 → Fin 16 → CBox := ![trans10_r1_0,trans10_r1_1,trans10_r1_2,trans10_r1_3,trans10_r1_4,trans10_r1_5,trans10_r1_6,trans10_r1_7,trans10_r1_8,trans10_r1_9,trans10_r1_10,trans10_r1_11,trans10_r1_12,trans10_r1_13,trans10_r1_14,trans10_r1_15]
end SharpPlanar.CachedData

end OAI
end


