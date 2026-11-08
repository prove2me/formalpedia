-- Prove2me | Definitions.Def_OAIQ098G283
-- name    : OAIQ098G283
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:40:12.411675+00:00
-- url     : https://prove2.me/theorems/2567e412-11bf-4d64-ae7e-b56e61f4f0c3
-- title:
--   Definitions bundle OAIQ098G283 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column75_0Expr`, `OAI.SharpPlanar.CachedData.column75_1Expr`, `OAI.SharpPlanar.CachedData.power75`, `OAI.SharpPlanar.CachedData.power75_r3`, `OAI.SharpPlanar.CachedData.power76Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns80.lean), [`PlanarPacking_Certificate_Powers80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020`, `OAIQ098G022`, `OAIQ098G278` and `OAIQ098G282` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column75_0_contains_g`, `OAI.SharpPlanar.CachedData.column75_1_contains_g`, `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.CachedData.column76_1_contains_g` and `OAI.SharpPlanar.CachedData.power78_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G022
import Definitions.Def_OAIQ098G278
import Definitions.Def_OAIQ098G282

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
noncomputable def power75_r3 : Fin 16 → Fin 16 → CBox := ![power75_r3_0,power75_r3_1,power75_r3_2,power75_r3_3,power75_r3_4,power75_r3_5,power75_r3_6,power75_r3_7,power75_r3_8,power75_r3_9,power75_r3_10,power75_r3_11,power75_r3_12,power75_r3_13,power75_r3_14,power75_r3_15]
noncomputable def power75 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power75_r0,power75_r1,power75_r2,power75_r3,power75_r4,power75_r5]
noncomputable def power76Expr (j : Fin 6) (i k : Fin 16) : CBox := (power75 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns80
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
noncomputable def column75_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power75 j i k)
noncomputable def column75_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power75 j i k)
end SharpPlanar.CachedData

end OAI
end


