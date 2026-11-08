-- Prove2me | Definitions.Def_OAIQ098G342
-- name    : OAIQ098G342
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:13:12.35568+00:00
-- url     : https://prove2.me/theorems/954d1d17-c883-41eb-a997-72f9cc183c9e
-- title:
--   Definitions bundle OAIQ098G342 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power74`, `OAI.SharpPlanar.CachedData.power74_r4`, `OAI.SharpPlanar.CachedData.power75Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G338` and `OAIQ098G341` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column75_0_contains_g`, `OAI.SharpPlanar.CachedData.column75_1_contains_g`, `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.CachedData.column76_1_contains_g` and `OAI.SharpPlanar.CachedData.power78_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G338
import Definitions.Def_OAIQ098G341

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers80
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
noncomputable def power74_r4 : Fin 16 → Fin 16 → CBox := ![power74_r4_0,power74_r4_1,power74_r4_2,power74_r4_3,power74_r4_4,power74_r4_5,power74_r4_6,power74_r4_7,power74_r4_8,power74_r4_9,power74_r4_10,power74_r4_11,power74_r4_12,power74_r4_13,power74_r4_14,power74_r4_15]
noncomputable def power74 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power74_r0,power74_r1,power74_r2,power74_r3,power74_r4,power74_r5]
noncomputable def power75Expr (j : Fin 6) (i k : Fin 16) : CBox := (power74 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


