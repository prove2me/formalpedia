-- Prove2me | Definitions.Def_OAIQ098G1436
-- name    : OAIQ098G1436
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:23:25.716732+00:00
-- url     : https://prove2.me/theorems/43fd02ea-ce4d-4ee9-a9c4-34005eccbc4c
-- title:
--   Definitions bundle OAIQ098G1436 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel63_1`, `OAI.SharpPlanar.CachedData.kernel63_1_r0`, `OAI.SharpPlanar.CachedData.trans63`, `OAI.SharpPlanar.CachedData.trans63_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues70.lean), [`PlanarPacking_Certificate_TransformedPowers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1432` and `OAIQ098G1435` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1437`, `OAIQ098G1530`, `OAIQ098G1579` and `OAIQ098G1623`; the statement `OAI.SharpPlanar.CachedData.kernel63_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1432
import Definitions.Def_OAIQ098G1435

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers70
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
noncomputable def trans63_r5 : Fin 16 → Fin 16 → CBox := ![trans63_r5_0,trans63_r5_1,trans63_r5_2,trans63_r5_3,trans63_r5_4,trans63_r5_5,trans63_r5_6,trans63_r5_7,trans63_r5_8,trans63_r5_9,trans63_r5_10,trans63_r5_11,trans63_r5_12,trans63_r5_13,trans63_r5_14,trans63_r5_15]
noncomputable def trans63 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans63_r0,trans63_r1,trans63_r2,trans63_r3,trans63_r4,trans63_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues70
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
noncomputable def kernel63_1_r0 : Fin 16 → Fin 16 → CBox := ![kernel63_1_r0_0,kernel63_1_r0_1,kernel63_1_r0_2,kernel63_1_r0_3,kernel63_1_r0_4,kernel63_1_r0_5,kernel63_1_r0_6,kernel63_1_r0_7,kernel63_1_r0_8,kernel63_1_r0_9,kernel63_1_r0_10,kernel63_1_r0_11,kernel63_1_r0_12,kernel63_1_r0_13,kernel63_1_r0_14,kernel63_1_r0_15]
noncomputable def kernel63_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel63_1_r0,kernel63_1_r1,kernel63_1_r2,kernel63_1_r3,kernel63_1_r4,kernel63_1_r5]
end SharpPlanar.CachedData

end OAI
end


