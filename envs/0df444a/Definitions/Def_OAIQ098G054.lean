-- Prove2me | Definitions.Def_OAIQ098G054
-- name    : OAIQ098G054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:02:04.435199+00:00
-- url     : https://prove2.me/theorems/38799377-5a8a-4e87-96b3-5170a904082c
-- title:
--   Definitions bundle OAIQ098G054 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column1_0Expr`, `OAI.SharpPlanar.CachedData.power1`, `OAI.SharpPlanar.CachedData.power1_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean), [`PlanarPacking_Certificate_Powers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G047` and `OAIQ098G053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G055`, `OAIQ098G066`, `OAIQ098G540`, `OAIQ098G541`, `OAIQ098G542`, `OAIQ098G543`, `OAIQ098G544`, `OAIQ098G545`, `OAIQ098G546`, `OAIQ098G547`, `OAIQ098G548`, `OAIQ098G549`, `OAIQ098G550`, `OAIQ098G551` and `OAIQ098G552`; the statement `OAI.SharpPlanar.CachedData.power1_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.column1_0_contains_g` and `OAI.SharpPlanar.CachedData.power1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G053

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
noncomputable def power1_r5 : Fin 16 → Fin 16 → CBox := ![power1_r5_0,power1_r5_1,power1_r5_2,power1_r5_3,power1_r5_4,power1_r5_5,power1_r5_6,power1_r5_7,power1_r5_8,power1_r5_9,power1_r5_10,power1_r5_11,power1_r5_12,power1_r5_13,power1_r5_14,power1_r5_15]
noncomputable def power1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power1_r0,power1_r1,power1_r2,power1_r3,power1_r4,power1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
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
noncomputable def column1_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power1 j i k)
end SharpPlanar.CachedData

end OAI
end


