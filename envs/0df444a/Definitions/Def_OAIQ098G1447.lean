-- Prove2me | Definitions.Def_OAIQ098G1447
-- name    : OAIQ098G1447
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:24:40.794728+00:00
-- url     : https://prove2.me/theorems/3ee0b7ac-6a3f-480c-b2da-256d34b4ea5b
-- title:
--   Definitions bundle OAIQ098G1447 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel81_0`, `OAI.SharpPlanar.CachedData.kernel81_0_r1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1443` and `OAIQ098G1446` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1539` and `OAIQ098G1586`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1443
import Definitions.Def_OAIQ098G1446

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues90
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
noncomputable def kernel81_0_r1 : Fin 16 → Fin 16 → CBox := ![kernel81_0_r1_0,kernel81_0_r1_1,kernel81_0_r1_2,kernel81_0_r1_3,kernel81_0_r1_4,kernel81_0_r1_5,kernel81_0_r1_6,kernel81_0_r1_7,kernel81_0_r1_8,kernel81_0_r1_9,kernel81_0_r1_10,kernel81_0_r1_11,kernel81_0_r1_12,kernel81_0_r1_13,kernel81_0_r1_14,kernel81_0_r1_15]
noncomputable def kernel81_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel81_0_r0,kernel81_0_r1,kernel81_0_r2,kernel81_0_r3,kernel81_0_r4,kernel81_0_r5]
end SharpPlanar.CachedData

end OAI
end


