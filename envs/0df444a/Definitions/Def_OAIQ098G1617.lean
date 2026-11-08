-- Prove2me | Definitions.Def_OAIQ098G1617
-- name    : OAIQ098G1617
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:33:58.07397+00:00
-- url     : https://prove2.me/theorems/f89ee790-ed00-4959-80cd-b94e5fb58435
-- title:
--   Definitions bundle OAIQ098G1617 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans53`, `OAI.SharpPlanar.CachedData.trans53_r2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers60.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1608` and `OAIQ098G1616` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1619`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1608
import Definitions.Def_OAIQ098G1616

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
noncomputable def trans53_r2 : Fin 16 → Fin 16 → CBox := ![trans53_r2_0,trans53_r2_1,trans53_r2_2,trans53_r2_3,trans53_r2_4,trans53_r2_5,trans53_r2_6,trans53_r2_7,trans53_r2_8,trans53_r2_9,trans53_r2_10,trans53_r2_11,trans53_r2_12,trans53_r2_13,trans53_r2_14,trans53_r2_15]
noncomputable def trans53 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans53_r0,trans53_r1,trans53_r2,trans53_r3,trans53_r4,trans53_r5]
end SharpPlanar.CachedData

end OAI
end


