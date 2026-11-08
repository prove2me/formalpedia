-- Prove2me | Definitions.Def_OAIQ098G350
-- name    : OAIQ098G350
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:13:48.414494+00:00
-- url     : https://prove2.me/theorems/0bc0f3d2-87fb-45cf-85aa-269ef53514d4
-- title:
--   Definitions bundle OAIQ098G350 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power90`, `OAI.SharpPlanar.CachedData.power90_r0`, `OAI.SharpPlanar.CachedData.power91Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers100.lean), [`PlanarPacking_Certificate_Powers90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers90.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G347` and `OAIQ098G349` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column91_0_contains_g`, `OAI.SharpPlanar.CachedData.column91_1_contains_g` and `OAI.SharpPlanar.CachedData.power93_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G347
import Definitions.Def_OAIQ098G349

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers90
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
noncomputable def power90_r0 : Fin 16 → Fin 16 → CBox := ![power90_r0_0,power90_r0_1,power90_r0_2,power90_r0_3,power90_r0_4,power90_r0_5,power90_r0_6,power90_r0_7,power90_r0_8,power90_r0_9,power90_r0_10,power90_r0_11,power90_r0_12,power90_r0_13,power90_r0_14,power90_r0_15]
noncomputable def power90 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power90_r0,power90_r1,power90_r2,power90_r3,power90_r4,power90_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers100
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
noncomputable def power91Expr (j : Fin 6) (i k : Fin 16) : CBox := (power90 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


