-- Prove2me | Definitions.Def_OAIQ098G105
-- name    : OAIQ098G105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:08:47.410845+00:00
-- url     : https://prove2.me/theorems/51c9b132-95ae-42aa-9687-55422bcd542a
-- title:
--   Definitions bundle OAIQ098G105 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.amp7_1`, `OAI.SharpPlanar.CachedData.amp7_10`, `OAI.SharpPlanar.CachedData.amp7_15`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Amplitudes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G103` and `OAIQ098G104` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G245`, `OAIQ098G253`, `OAIQ098G261`, `OAIQ098G269`, `OAIQ098G277`, `OAIQ098G285`, `OAIQ098G289` and `OAIQ098G297`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G103
import Definitions.Def_OAIQ098G104

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
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
noncomputable def amp7_10 : Fin 16 → Fin 16 → CBox := ![amp7_10_0,amp7_10_1,amp7_10_2,amp7_10_3,amp7_10_4,amp7_10_5,amp7_10_6,amp7_10_7,amp7_10_8,amp7_10_9,amp7_10_10,amp7_10_11,amp7_10_12,amp7_10_13,amp7_10_14,amp7_10_15]
noncomputable def amp7_15 : Fin 16 → Fin 16 → CBox := ![amp7_15_0,amp7_15_1,amp7_15_2,amp7_15_3,amp7_15_4,amp7_15_5,amp7_15_6,amp7_15_7,amp7_15_8,amp7_15_9,amp7_15_10,amp7_15_11,amp7_15_12,amp7_15_13,amp7_15_14,amp7_15_15]
noncomputable def amp7_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp7_10,amp7_11,amp7_12,amp7_13,amp7_14,amp7_15]
end SharpPlanar.CachedData

end OAI
end


