-- Prove2me | Definitions.Def_OAIQ098G414
-- name    : OAIQ098G414
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:39:51.703022+00:00
-- url     : https://prove2.me/theorems/5d03d3ac-d1df-42ae-b3d2-e3ef93f171d8
-- title:
--   Definitions bundle OAIQ098G414 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_1_r4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G398` and `OAIQ098G402` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G415`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G398
import Definitions.Def_OAIQ098G402

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
noncomputable def mpower0_1_r4 : Fin 16 → Fin 16 → CBox := ![mpower0_1_r4_0,mpower0_1_r4_1,mpower0_1_r4_2,mpower0_1_r4_3,mpower0_1_r4_4,mpower0_1_r4_5,mpower0_1_r4_6,mpower0_1_r4_7,mpower0_1_r4_8,mpower0_1_r4_9,mpower0_1_r4_10,mpower0_1_r4_11,mpower0_1_r4_12,mpower0_1_r4_13,mpower0_1_r4_14,mpower0_1_r4_15]
end SharpPlanar.CachedData

end OAI
end


