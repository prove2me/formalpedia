-- Prove2me | Definitions.Def_OAIQ098G436
-- name    : OAIQ098G436
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:42:23.079243+00:00
-- url     : https://prove2.me/theorems/5bf8d745-3650-47af-ac88-4214fbc4fedd
-- title:
--   Definitions bundle OAIQ098G436 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_7`, `OAI.SharpPlanar.CachedData.mpower0_7_r5`, `OAI.SharpPlanar.CachedData.mpower0_8`, `OAI.SharpPlanar.CachedData.mpower0_8_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G431` and `OAIQ098G435` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1472`, `OAIQ098G437`, `OAIQ098G484`, `OAIQ098G502`, `OAIQ098G519`, `OAIQ098G528`, `OAIQ098G551`, `OAIQ098G583`, `OAIQ098G598`, `OAIQ098G606`, `OAIQ098G630`, `OAIQ098G638`, `OAIQ098G646`, `OAIQ098G654`, `OAIQ098G668`, `OAIQ098G686`, `OAIQ098G710` and `OAIQ098G730`; the statements `OAI.SharpPlanar.CachedData.mpower0_7_contains_g` and `OAI.SharpPlanar.CachedData.mpower0_8_contains_g`; the proof of `OAI.SharpPlanar.CachedData.mpower0_7_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G431
import Definitions.Def_OAIQ098G435

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers10
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
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def mpower0_7_r5 : Fin 16 → Fin 16 → CBox := ![mpower0_7_r5_0,mpower0_7_r5_1,mpower0_7_r5_2,mpower0_7_r5_3,mpower0_7_r5_4,mpower0_7_r5_5,mpower0_7_r5_6,mpower0_7_r5_7,mpower0_7_r5_8,mpower0_7_r5_9,mpower0_7_r5_10,mpower0_7_r5_11,mpower0_7_r5_12,mpower0_7_r5_13,mpower0_7_r5_14,mpower0_7_r5_15]
noncomputable def mpower0_7 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_7_r0,mpower0_7_r1,mpower0_7_r2,mpower0_7_r3,mpower0_7_r4,mpower0_7_r5]
noncomputable def mpower0_8_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_8_r0_0,mpower0_8_r0_1,mpower0_8_r0_2,mpower0_8_r0_3,mpower0_8_r0_4,mpower0_8_r0_5,mpower0_8_r0_6,mpower0_8_r0_7,mpower0_8_r0_8,mpower0_8_r0_9,mpower0_8_r0_10,mpower0_8_r0_11,mpower0_8_r0_12,mpower0_8_r0_13,mpower0_8_r0_14,mpower0_8_r0_15]
noncomputable def mpower0_8 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_8_r0,mpower0_8_r1,mpower0_8_r2,mpower0_8_r3,mpower0_8_r4,mpower0_8_r5]
end SharpPlanar.CachedData

end OAI
end


