-- Prove2me | Definitions.Def_OAIQ098G243
-- name    : OAIQ098G243
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:37:38.796385+00:00
-- url     : https://prove2.me/theorems/25a6a2a3-40ac-4b49-8601-5710b9e5e8d5
-- title:
--   Definitions bundle OAIQ098G243 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power19`, `OAI.SharpPlanar.CachedData.power19_r5`, `OAI.SharpPlanar.CachedData.power20Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020`, `OAIQ098G240` and `OAIQ098G242` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G244`, `OAIQ098G245`, `OAIQ098G522`, `OAIQ098G523`, `OAIQ098G524`, `OAIQ098G525`, `OAIQ098G526`, `OAIQ098G527`, `OAIQ098G528` and `OAIQ098G529`; the statement `OAI.SharpPlanar.CachedData.power19_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.power19_contains_g` and `OAI.SharpPlanar.CachedData.power21_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G240
import Definitions.Def_OAIQ098G242

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
noncomputable def power19_r5 : Fin 16 → Fin 16 → CBox := ![power19_r5_0,power19_r5_1,power19_r5_2,power19_r5_3,power19_r5_4,power19_r5_5,power19_r5_6,power19_r5_7,power19_r5_8,power19_r5_9,power19_r5_10,power19_r5_11,power19_r5_12,power19_r5_13,power19_r5_14,power19_r5_15]
noncomputable def power19 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power19_r0,power19_r1,power19_r2,power19_r3,power19_r4,power19_r5]
noncomputable def power20Expr (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


