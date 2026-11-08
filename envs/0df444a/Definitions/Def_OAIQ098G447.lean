-- Prove2me | Definitions.Def_OAIQ098G447
-- name    : OAIQ098G447
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:43:55.291232+00:00
-- url     : https://prove2.me/theorems/e8fe222e-b07f-4a23-b59d-2ffe11cf1403
-- title:
--   Definitions bundle OAIQ098G447 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower1_15`, `OAI.SharpPlanar.CachedData.mpower1_15_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G442` and `OAIQ098G446` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1476`, `OAIQ098G448`, `OAIQ098G557`, `OAIQ098G692`, `OAIQ098G715` and `OAIQ098G735`; the statement `OAI.SharpPlanar.CachedData.mpower1_15_contains_g`; the proof of `OAI.SharpPlanar.CachedData.mpower1_15_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G442
import Definitions.Def_OAIQ098G446

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers15
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
noncomputable def mpower1_15_r0 : Fin 16 → Fin 16 → CBox := ![mpower1_15_r0_0,mpower1_15_r0_1,mpower1_15_r0_2,mpower1_15_r0_3,mpower1_15_r0_4,mpower1_15_r0_5,mpower1_15_r0_6,mpower1_15_r0_7,mpower1_15_r0_8,mpower1_15_r0_9,mpower1_15_r0_10,mpower1_15_r0_11,mpower1_15_r0_12,mpower1_15_r0_13,mpower1_15_r0_14,mpower1_15_r0_15]
noncomputable def mpower1_15 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_15_r0,mpower1_15_r1,mpower1_15_r2,mpower1_15_r3,mpower1_15_r4,mpower1_15_r5]
end SharpPlanar.CachedData

end OAI
end


