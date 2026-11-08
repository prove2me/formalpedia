-- Prove2me | Definitions.Def_OAIQ098G1609
-- name    : OAIQ098G1609
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:31:18.651199+00:00
-- url     : https://prove2.me/theorems/34747b89-14b6-41d6-af70-cd84ee38f58f
-- title:
--   Definitions bundle OAIQ098G1609 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans35`, `OAI.SharpPlanar.CachedData.trans35_r5`, `OAI.SharpPlanar.CachedData.trans38`, `OAI.SharpPlanar.CachedData.trans38_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1601` and `OAIQ098G1608` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1610`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1601
import Definitions.Def_OAIQ098G1608

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers40
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
noncomputable def trans35_r5 : Fin 16 → Fin 16 → CBox := ![trans35_r5_0,trans35_r5_1,trans35_r5_2,trans35_r5_3,trans35_r5_4,trans35_r5_5,trans35_r5_6,trans35_r5_7,trans35_r5_8,trans35_r5_9,trans35_r5_10,trans35_r5_11,trans35_r5_12,trans35_r5_13,trans35_r5_14,trans35_r5_15]
noncomputable def trans35 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans35_r0,trans35_r1,trans35_r2,trans35_r3,trans35_r4,trans35_r5]
noncomputable def trans38_r0 : Fin 16 → Fin 16 → CBox := ![trans38_r0_0,trans38_r0_1,trans38_r0_2,trans38_r0_3,trans38_r0_4,trans38_r0_5,trans38_r0_6,trans38_r0_7,trans38_r0_8,trans38_r0_9,trans38_r0_10,trans38_r0_11,trans38_r0_12,trans38_r0_13,trans38_r0_14,trans38_r0_15]
noncomputable def trans38 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans38_r0,trans38_r1,trans38_r2,trans38_r3,trans38_r4,trans38_r5]
end SharpPlanar.CachedData

end OAI
end


