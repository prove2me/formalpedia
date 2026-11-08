-- Prove2me | Definitions.Def_OAIQ098G272
-- name    : OAIQ098G272
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:04:44.960071+00:00
-- url     : https://prove2.me/theorems/17b0aed0-f108-4699-8f64-68144f838652
-- title:
--   Definitions bundle OAIQ098G272 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power60`, `OAI.SharpPlanar.CachedData.power60_r1`, `OAI.SharpPlanar.CachedData.power61Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers60.lean), [`PlanarPacking_Certificate_Powers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020`, `OAIQ098G266` and `OAIQ098G271` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G273`; the proof of `OAI.SharpPlanar.CachedData.power61_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G266
import Definitions.Def_OAIQ098G271

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers60
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
noncomputable def power60_r1 : Fin 16 → Fin 16 → CBox := ![power60_r1_0,power60_r1_1,power60_r1_2,power60_r1_3,power60_r1_4,power60_r1_5,power60_r1_6,power60_r1_7,power60_r1_8,power60_r1_9,power60_r1_10,power60_r1_11,power60_r1_12,power60_r1_13,power60_r1_14,power60_r1_15]
noncomputable def power60 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power60_r0,power60_r1,power60_r2,power60_r3,power60_r4,power60_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers70
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
noncomputable def power61Expr (j : Fin 6) (i k : Fin 16) : CBox := (power60 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


