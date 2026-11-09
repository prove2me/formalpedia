-- Prove2me | Definitions.Def_OAIQ098G325
-- name    : OAIQ098G325
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:46:51.718376+00:00
-- url     : https://prove2.me/theorems/cc67ac3d-95cf-4e0e-87e8-79deef317e0d
-- title:
--   Definitions bundle OAIQ098G325 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power41`, `OAI.SharpPlanar.CachedData.power41_r2`, `OAI.SharpPlanar.CachedData.power42Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G322` and `OAIQ098G324` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column43_0_contains_g`, `OAI.SharpPlanar.CachedData.column43_1_contains_g` and `OAI.SharpPlanar.CachedData.power45_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G322
import Definitions.Def_OAIQ098G324

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers50
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
noncomputable def power41_r2 : Fin 16 → Fin 16 → CBox := ![power41_r2_0,power41_r2_1,power41_r2_2,power41_r2_3,power41_r2_4,power41_r2_5,power41_r2_6,power41_r2_7,power41_r2_8,power41_r2_9,power41_r2_10,power41_r2_11,power41_r2_12,power41_r2_13,power41_r2_14,power41_r2_15]
noncomputable def power41 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power41_r0,power41_r1,power41_r2,power41_r3,power41_r4,power41_r5]
noncomputable def power42Expr (j : Fin 6) (i k : Fin 16) : CBox := (power41 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


