-- Prove2me | Definitions.Def_OAIQ098G1444
-- name    : OAIQ098G1444
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:24:23.977791+00:00
-- url     : https://prove2.me/theorems/77991f4c-6557-4fbd-86f0-9b0c4e2b0429
-- title:
--   Definitions bundle OAIQ098G1444 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel75_0`, `OAI.SharpPlanar.CachedData.kernel75_0_r3`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1439` and `OAIQ098G1443` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1535` and `OAIQ098G1582`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1439
import Definitions.Def_OAIQ098G1443

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues80
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
noncomputable def kernel75_0_r3 : Fin 16 → Fin 16 → CBox := ![kernel75_0_r3_0,kernel75_0_r3_1,kernel75_0_r3_2,kernel75_0_r3_3,kernel75_0_r3_4,kernel75_0_r3_5,kernel75_0_r3_6,kernel75_0_r3_7,kernel75_0_r3_8,kernel75_0_r3_9,kernel75_0_r3_10,kernel75_0_r3_11,kernel75_0_r3_12,kernel75_0_r3_13,kernel75_0_r3_14,kernel75_0_r3_15]
noncomputable def kernel75_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel75_0_r0,kernel75_0_r1,kernel75_0_r2,kernel75_0_r3,kernel75_0_r4,kernel75_0_r5]
end SharpPlanar.CachedData

end OAI
end


