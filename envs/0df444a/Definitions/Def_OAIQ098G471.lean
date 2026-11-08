-- Prove2me | Definitions.Def_OAIQ098G471
-- name    : OAIQ098G471
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:46:31.575846+00:00
-- url     : https://prove2.me/theorems/0b0dc18f-cc21-4052-93b0-7ceef50c55c2
-- title:
--   Definitions bundle OAIQ098G471 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower1_5`, `OAI.SharpPlanar.CachedData.mpower1_5_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G466` and `OAIQ098G470` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1490`, `OAIQ098G472`, `OAIQ098G492`, `OAIQ098G509`, `OAIQ098G538`, `OAIQ098G573`, `OAIQ098G589`, `OAIQ098G613`, `OAIQ098G620`, `OAIQ098G661`, `OAIQ098G676`, `OAIQ098G699`, `OAIQ098G719` and `OAIQ098G739`; the statement `OAI.SharpPlanar.CachedData.mpower1_5_contains_g`; the proof of `OAI.SharpPlanar.CachedData.mpower1_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G466
import Definitions.Def_OAIQ098G470

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers5
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
noncomputable def mpower1_5_r5 : Fin 16 → Fin 16 → CBox := ![mpower1_5_r5_0,mpower1_5_r5_1,mpower1_5_r5_2,mpower1_5_r5_3,mpower1_5_r5_4,mpower1_5_r5_5,mpower1_5_r5_6,mpower1_5_r5_7,mpower1_5_r5_8,mpower1_5_r5_9,mpower1_5_r5_10,mpower1_5_r5_11,mpower1_5_r5_12,mpower1_5_r5_13,mpower1_5_r5_14,mpower1_5_r5_15]
noncomputable def mpower1_5 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_5_r0,mpower1_5_r1,mpower1_5_r2,mpower1_5_r3,mpower1_5_r4,mpower1_5_r5]
end SharpPlanar.CachedData

end OAI
end


