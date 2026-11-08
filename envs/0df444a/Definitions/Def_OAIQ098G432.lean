-- Prove2me | Definitions.Def_OAIQ098G432
-- name    : OAIQ098G432
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:43:22.42388+00:00
-- url     : https://prove2.me/theorems/c8ba98af-e85c-4d35-ac06-92d6b3fe3375
-- title:
--   Definitions bundle OAIQ098G432 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_3`, `OAI.SharpPlanar.CachedData.mpower0_3_r0`, `OAI.SharpPlanar.CachedData.mpower0_4`, `OAI.SharpPlanar.CachedData.mpower0_4_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G427` and `OAIQ098G431` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1470`, `OAIQ098G433`, `OAIQ098G482`, `OAIQ098G500`, `OAIQ098G517`, `OAIQ098G526`, `OAIQ098G549`, `OAIQ098G581`, `OAIQ098G596`, `OAIQ098G604`, `OAIQ098G628`, `OAIQ098G636`, `OAIQ098G644`, `OAIQ098G652`, `OAIQ098G666`, `OAIQ098G684`, `OAIQ098G708` and `OAIQ098G728`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G427
import Definitions.Def_OAIQ098G431

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers5
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
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def mpower0_3_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_3_r0_0,mpower0_3_r0_1,mpower0_3_r0_2,mpower0_3_r0_3,mpower0_3_r0_4,mpower0_3_r0_5,mpower0_3_r0_6,mpower0_3_r0_7,mpower0_3_r0_8,mpower0_3_r0_9,mpower0_3_r0_10,mpower0_3_r0_11,mpower0_3_r0_12,mpower0_3_r0_13,mpower0_3_r0_14,mpower0_3_r0_15]
noncomputable def mpower0_3 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_3_r0,mpower0_3_r1,mpower0_3_r2,mpower0_3_r3,mpower0_3_r4,mpower0_3_r5]
noncomputable def mpower0_4_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_4_r0_0,mpower0_4_r0_1,mpower0_4_r0_2,mpower0_4_r0_3,mpower0_4_r0_4,mpower0_4_r0_5,mpower0_4_r0_6,mpower0_4_r0_7,mpower0_4_r0_8,mpower0_4_r0_9,mpower0_4_r0_10,mpower0_4_r0_11,mpower0_4_r0_12,mpower0_4_r0_13,mpower0_4_r0_14,mpower0_4_r0_15]
noncomputable def mpower0_4 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_4_r0,mpower0_4_r1,mpower0_4_r2,mpower0_4_r3,mpower0_4_r4,mpower0_4_r5]
end SharpPlanar.CachedData

end OAI
end


