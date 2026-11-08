-- Prove2me | Definitions.Def_OAIQ098G1453
-- name    : OAIQ098G1453
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:26:40.944183+00:00
-- url     : https://prove2.me/theorems/664421a1-1bcb-4396-8950-4155467487d3
-- title:
--   Definitions bundle OAIQ098G1453 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel93_0`, `OAI.SharpPlanar.CachedData.kernel93_0_r0`, `OAI.SharpPlanar.CachedData.trans97`, `OAI.SharpPlanar.CachedData.trans97_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues100.lean), [`PlanarPacking_Certificate_TransformedPowers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1449` and `OAIQ098G1452` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1455`, `OAIQ098G1543`, `OAIQ098G1592` and `OAIQ098G1641`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1449
import Definitions.Def_OAIQ098G1452

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers100
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
noncomputable def trans97_r5 : Fin 16 → Fin 16 → CBox := ![trans97_r5_0,trans97_r5_1,trans97_r5_2,trans97_r5_3,trans97_r5_4,trans97_r5_5,trans97_r5_6,trans97_r5_7,trans97_r5_8,trans97_r5_9,trans97_r5_10,trans97_r5_11,trans97_r5_12,trans97_r5_13,trans97_r5_14,trans97_r5_15]
noncomputable def trans97 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans97_r0,trans97_r1,trans97_r2,trans97_r3,trans97_r4,trans97_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def kernel93_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel93_0_r0_0,kernel93_0_r0_1,kernel93_0_r0_2,kernel93_0_r0_3,kernel93_0_r0_4,kernel93_0_r0_5,kernel93_0_r0_6,kernel93_0_r0_7,kernel93_0_r0_8,kernel93_0_r0_9,kernel93_0_r0_10,kernel93_0_r0_11,kernel93_0_r0_12,kernel93_0_r0_13,kernel93_0_r0_14,kernel93_0_r0_15]
noncomputable def kernel93_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel93_0_r0,kernel93_0_r1,kernel93_0_r2,kernel93_0_r3,kernel93_0_r4,kernel93_0_r5]
end SharpPlanar.CachedData

end OAI
end


