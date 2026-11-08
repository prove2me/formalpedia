-- Prove2me | Definitions.Def_OAIQ098G1429
-- name    : OAIQ098G1429
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:23:22.289627+00:00
-- url     : https://prove2.me/theorems/ce1a9aff-61f0-4406-93bb-641719b55a58
-- title:
--   Definitions bundle OAIQ098G1429 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel52_0`, `OAI.SharpPlanar.CachedData.kernel52_0_r5`, `OAI.SharpPlanar.CachedData.trans52`, `OAI.SharpPlanar.CachedData.trans52_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues60.lean), [`PlanarPacking_Certificate_TransformedPowers60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers60.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1425` and `OAIQ098G1428` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1430`, `OAIQ098G1526`, `OAIQ098G1575` and `OAIQ098G1618`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1425
import Definitions.Def_OAIQ098G1428

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers60
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
noncomputable def trans52_r0 : Fin 16 → Fin 16 → CBox := ![trans52_r0_0,trans52_r0_1,trans52_r0_2,trans52_r0_3,trans52_r0_4,trans52_r0_5,trans52_r0_6,trans52_r0_7,trans52_r0_8,trans52_r0_9,trans52_r0_10,trans52_r0_11,trans52_r0_12,trans52_r0_13,trans52_r0_14,trans52_r0_15]
noncomputable def trans52 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans52_r0,trans52_r1,trans52_r2,trans52_r3,trans52_r4,trans52_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def kernel52_0_r5 : Fin 16 → Fin 16 → CBox := ![kernel52_0_r5_0,kernel52_0_r5_1,kernel52_0_r5_2,kernel52_0_r5_3,kernel52_0_r5_4,kernel52_0_r5_5,kernel52_0_r5_6,kernel52_0_r5_7,kernel52_0_r5_8,kernel52_0_r5_9,kernel52_0_r5_10,kernel52_0_r5_11,kernel52_0_r5_12,kernel52_0_r5_13,kernel52_0_r5_14,kernel52_0_r5_15]
noncomputable def kernel52_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel52_0_r0,kernel52_0_r1,kernel52_0_r2,kernel52_0_r3,kernel52_0_r4,kernel52_0_r5]
end SharpPlanar.CachedData

end OAI
end


