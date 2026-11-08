-- Prove2me | Definitions.Def_OAIQ098G238
-- name    : OAIQ098G238
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:59:36.669204+00:00
-- url     : https://prove2.me/theorems/4446b0a3-90c2-4771-9395-022138e1cc96
-- title:
--   Definitions bundle OAIQ098G238 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column100_0Expr`, `OAI.SharpPlanar.CachedData.column100_1Expr`, `OAI.SharpPlanar.CachedData.power100`, `OAI.SharpPlanar.CachedData.power100_r1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean), [`PlanarPacking_Certificate_Powers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G021`, `OAIQ098G235` and `OAIQ098G237` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column100_0_contains_g` and `OAI.SharpPlanar.CachedData.column100_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G021
import Definitions.Def_OAIQ098G235
import Definitions.Def_OAIQ098G237

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
noncomputable def power100_r1 : Fin 16 → Fin 16 → CBox := ![power100_r1_0,power100_r1_1,power100_r1_2,power100_r1_3,power100_r1_4,power100_r1_5,power100_r1_6,power100_r1_7,power100_r1_8,power100_r1_9,power100_r1_10,power100_r1_11,power100_r1_12,power100_r1_13,power100_r1_14,power100_r1_15]
noncomputable def power100 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power100_r0,power100_r1,power100_r2,power100_r3,power100_r4,power100_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
noncomputable def column100_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power100 j i k)
noncomputable def column100_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power100 j i k)
end SharpPlanar.CachedData

end OAI
end


