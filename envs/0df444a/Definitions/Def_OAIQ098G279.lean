-- Prove2me | Definitions.Def_OAIQ098G279
-- name    : OAIQ098G279
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:05:20.20356+00:00
-- url     : https://prove2.me/theorems/f40e06c8-b725-4e72-8c06-d6cd5bf3b2f7
-- title:
--   Definitions bundle OAIQ098G279 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power69`, `OAI.SharpPlanar.CachedData.power69_r5`, `OAI.SharpPlanar.CachedData.power70Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G274` and `OAIQ098G278` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G280`; the statement `OAI.SharpPlanar.CachedData.power69_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.power69_contains_g` and `OAI.SharpPlanar.CachedData.power70_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G274
import Definitions.Def_OAIQ098G278

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
noncomputable def power69_r5 : Fin 16 → Fin 16 → CBox := ![power69_r5_0,power69_r5_1,power69_r5_2,power69_r5_3,power69_r5_4,power69_r5_5,power69_r5_6,power69_r5_7,power69_r5_8,power69_r5_9,power69_r5_10,power69_r5_11,power69_r5_12,power69_r5_13,power69_r5_14,power69_r5_15]
noncomputable def power69 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power69_r0,power69_r1,power69_r2,power69_r3,power69_r4,power69_r5]
noncomputable def power70Expr (j : Fin 6) (i k : Fin 16) : CBox := (power69 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


