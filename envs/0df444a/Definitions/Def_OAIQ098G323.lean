-- Prove2me | Definitions.Def_OAIQ098G323
-- name    : OAIQ098G323
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:48:05.491168+00:00
-- url     : https://prove2.me/theorems/dfee2dbb-7f53-4910-85ee-e3c99772b56c
-- title:
--   Definitions bundle OAIQ098G323 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power34`, `OAI.SharpPlanar.CachedData.power34_r3`, `OAI.SharpPlanar.CachedData.power35Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G319` and `OAIQ098G322` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SharpPlanar.CachedData.power36_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G319
import Definitions.Def_OAIQ098G322

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
noncomputable def power34_r3 : Fin 16 → Fin 16 → CBox := ![power34_r3_0,power34_r3_1,power34_r3_2,power34_r3_3,power34_r3_4,power34_r3_5,power34_r3_6,power34_r3_7,power34_r3_8,power34_r3_9,power34_r3_10,power34_r3_11,power34_r3_12,power34_r3_13,power34_r3_14,power34_r3_15]
noncomputable def power34 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power34_r0,power34_r1,power34_r2,power34_r3,power34_r4,power34_r5]
noncomputable def power35Expr (j : Fin 6) (i k : Fin 16) : CBox := (power34 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


