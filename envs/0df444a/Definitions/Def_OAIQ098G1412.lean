-- Prove2me | Definitions.Def_OAIQ098G1412
-- name    : OAIQ098G1412
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:21:48.286558+00:00
-- url     : https://prove2.me/theorems/f356fc30-557a-4381-98ee-e031762765a0
-- title:
--   Definitions bundle OAIQ098G1412 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel24_1`, `OAI.SharpPlanar.CachedData.kernel24_1_r2`, `OAI.SharpPlanar.CachedData.trans27`, `OAI.SharpPlanar.CachedData.trans27_r3`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues30.lean), [`PlanarPacking_Certificate_TransformedPowers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1408` and `OAIQ098G1411` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1414`, `OAIQ098G1507`, `OAIQ098G1557` and `OAIQ098G1606`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1408
import Definitions.Def_OAIQ098G1411

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers30
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
noncomputable def trans27_r3 : Fin 16 → Fin 16 → CBox := ![trans27_r3_0,trans27_r3_1,trans27_r3_2,trans27_r3_3,trans27_r3_4,trans27_r3_5,trans27_r3_6,trans27_r3_7,trans27_r3_8,trans27_r3_9,trans27_r3_10,trans27_r3_11,trans27_r3_12,trans27_r3_13,trans27_r3_14,trans27_r3_15]
noncomputable def trans27 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans27_r0,trans27_r1,trans27_r2,trans27_r3,trans27_r4,trans27_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues30
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
noncomputable def kernel24_1_r2 : Fin 16 → Fin 16 → CBox := ![kernel24_1_r2_0,kernel24_1_r2_1,kernel24_1_r2_2,kernel24_1_r2_3,kernel24_1_r2_4,kernel24_1_r2_5,kernel24_1_r2_6,kernel24_1_r2_7,kernel24_1_r2_8,kernel24_1_r2_9,kernel24_1_r2_10,kernel24_1_r2_11,kernel24_1_r2_12,kernel24_1_r2_13,kernel24_1_r2_14,kernel24_1_r2_15]
noncomputable def kernel24_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel24_1_r0,kernel24_1_r1,kernel24_1_r2,kernel24_1_r3,kernel24_1_r4,kernel24_1_r5]
end SharpPlanar.CachedData

end OAI
end


