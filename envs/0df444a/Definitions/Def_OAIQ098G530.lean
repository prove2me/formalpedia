-- Prove2me | Definitions.Def_OAIQ098G530
-- name    : OAIQ098G530
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:48:28.565668+00:00
-- url     : https://prove2.me/theorems/b0e4b449-fee4-4bb9-addb-96b5e41f7c0f
-- title:
--   Definitions bundle OAIQ098G530 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.kernel19_0_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G435`, `OAIQ098G446`, `OAIQ098G454`, `OAIQ098G466`, `OAIQ098G470` and `OAIQ098G474` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G532`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G435
import Definitions.Def_OAIQ098G446
import Definitions.Def_OAIQ098G454
import Definitions.Def_OAIQ098G466
import Definitions.Def_OAIQ098G470
import Definitions.Def_OAIQ098G474

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues20
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
noncomputable def kernel19_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel19_0_r0_0,kernel19_0_r0_1,kernel19_0_r0_2,kernel19_0_r0_3,kernel19_0_r0_4,kernel19_0_r0_5,kernel19_0_r0_6,kernel19_0_r0_7,kernel19_0_r0_8,kernel19_0_r0_9,kernel19_0_r0_10,kernel19_0_r0_11,kernel19_0_r0_12,kernel19_0_r0_13,kernel19_0_r0_14,kernel19_0_r0_15]
end SharpPlanar.CachedData

end OAI
end


