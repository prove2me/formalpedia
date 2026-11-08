-- Prove2me | Definitions.Def_OAIQ098G1407
-- name    : OAIQ098G1407
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:20:45.760179+00:00
-- url     : https://prove2.me/theorems/a96efc58-db79-4592-91a0-f2fb0c636a65
-- title:
--   Definitions bundle OAIQ098G1407 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.kernel100_1_r2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues100.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G1392` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1409`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1392

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues100
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
noncomputable def kernel100_1_r2 : Fin 16 → Fin 16 → CBox := ![kernel100_1_r2_0,kernel100_1_r2_1,kernel100_1_r2_2,kernel100_1_r2_3,kernel100_1_r2_4,kernel100_1_r2_5,kernel100_1_r2_6,kernel100_1_r2_7,kernel100_1_r2_8,kernel100_1_r2_9,kernel100_1_r2_10,kernel100_1_r2_11,kernel100_1_r2_12,kernel100_1_r2_13,kernel100_1_r2_14,kernel100_1_r2_15]
end SharpPlanar.CachedData

end OAI
end


