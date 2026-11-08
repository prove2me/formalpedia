-- Prove2me | Definitions.Def_OAIQ098G312
-- name    : OAIQ098G312
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:08:59.135896+00:00
-- url     : https://prove2.me/theorems/255e313f-a146-4a5d-951f-934ee93f2f91
-- title:
--   Definitions bundle OAIQ098G312 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power11`, `OAI.SharpPlanar.CachedData.power11_r3`, `OAI.SharpPlanar.CachedData.power12Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G308` and `OAIQ098G311` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SharpPlanar.CachedData.power12_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G308
import Definitions.Def_OAIQ098G311

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers20
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
noncomputable def power11_r3 : Fin 16 → Fin 16 → CBox := ![power11_r3_0,power11_r3_1,power11_r3_2,power11_r3_3,power11_r3_4,power11_r3_5,power11_r3_6,power11_r3_7,power11_r3_8,power11_r3_9,power11_r3_10,power11_r3_11,power11_r3_12,power11_r3_13,power11_r3_14,power11_r3_15]
noncomputable def power11 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power11_r0,power11_r1,power11_r2,power11_r3,power11_r4,power11_r5]
noncomputable def power12Expr (j : Fin 6) (i k : Fin 16) : CBox := (power11 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


