-- Prove2me | Definitions.Def_OAIQ098G1433
-- name    : OAIQ098G1433
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:23:23.913943+00:00
-- url     : https://prove2.me/theorems/5dc3eff2-970b-4904-9af7-8c6a53f0420e
-- title:
--   Definitions bundle OAIQ098G1433 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel57_1`, `OAI.SharpPlanar.CachedData.kernel60_0`, `OAI.SharpPlanar.CachedData.kernel60_0_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues60.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1428` and `OAIQ098G1432` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1528` and `OAIQ098G1577`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1428
import Definitions.Def_OAIQ098G1432

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues60
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
noncomputable def kernel57_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel57_1_r0,kernel57_1_r1,kernel57_1_r2,kernel57_1_r3,kernel57_1_r4,kernel57_1_r5]
noncomputable def kernel60_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel60_0_r0_0,kernel60_0_r0_1,kernel60_0_r0_2,kernel60_0_r0_3,kernel60_0_r0_4,kernel60_0_r0_5,kernel60_0_r0_6,kernel60_0_r0_7,kernel60_0_r0_8,kernel60_0_r0_9,kernel60_0_r0_10,kernel60_0_r0_11,kernel60_0_r0_12,kernel60_0_r0_13,kernel60_0_r0_14,kernel60_0_r0_15]
noncomputable def kernel60_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel60_0_r0,kernel60_0_r1,kernel60_0_r2,kernel60_0_r3,kernel60_0_r4,kernel60_0_r5]
end SharpPlanar.CachedData

end OAI
end


