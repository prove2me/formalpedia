-- Prove2me | Definitions.Def_OAIQ098G1426
-- name    : OAIQ098G1426
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:23:38.45236+00:00
-- url     : https://prove2.me/theorems/3dcc74e8-29e9-4ef5-83fa-079042dfaa57
-- title:
--   Definitions bundle OAIQ098G1426 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel48_1`, `OAI.SharpPlanar.CachedData.kernel48_1_r1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues50.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1422` and `OAIQ098G1425` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1522` and `OAIQ098G1569`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1422
import Definitions.Def_OAIQ098G1425

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues50
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
noncomputable def kernel48_1_r1 : Fin 16 → Fin 16 → CBox := ![kernel48_1_r1_0,kernel48_1_r1_1,kernel48_1_r1_2,kernel48_1_r1_3,kernel48_1_r1_4,kernel48_1_r1_5,kernel48_1_r1_6,kernel48_1_r1_7,kernel48_1_r1_8,kernel48_1_r1_9,kernel48_1_r1_10,kernel48_1_r1_11,kernel48_1_r1_12,kernel48_1_r1_13,kernel48_1_r1_14,kernel48_1_r1_15]
noncomputable def kernel48_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel48_1_r0,kernel48_1_r1,kernel48_1_r2,kernel48_1_r3,kernel48_1_r4,kernel48_1_r5]
end SharpPlanar.CachedData

end OAI
end


