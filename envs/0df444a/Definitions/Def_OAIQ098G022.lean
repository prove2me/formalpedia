-- Prove2me | Definitions.Def_OAIQ098G022
-- name    : OAIQ098G022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:29:47.765871+00:00
-- url     : https://prove2.me/theorems/1937ff90-b9b5-4e93-a19e-9c7ef5cf9e26
-- title:
--   Definitions bundle OAIQ098G022 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.amp3_1`, `OAI.SharpPlanar.CachedData.amp3_15`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Amplitudes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G019` and `OAIQ098G021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G057`, `OAIQ098G241`, `OAIQ098G248`, `OAIQ098G256`, `OAIQ098G263`, `OAIQ098G271`, `OAIQ098G283`, `OAIQ098G292` and `OAIQ098G299`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G019
import Definitions.Def_OAIQ098G021

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
noncomputable def amp3_15 : Fin 16 → Fin 16 → CBox := ![amp3_15_0,amp3_15_1,amp3_15_2,amp3_15_3,amp3_15_4,amp3_15_5,amp3_15_6,amp3_15_7,amp3_15_8,amp3_15_9,amp3_15_10,amp3_15_11,amp3_15_12,amp3_15_13,amp3_15_14,amp3_15_15]
noncomputable def amp3_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp3_10,amp3_11,amp3_12,amp3_13,amp3_14,amp3_15]
end SharpPlanar.CachedData

end OAI
end


