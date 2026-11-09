-- Prove2me | Definitions.Def_OAIQ098G177
-- name    : OAIQ098G177
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:43:42.619539+00:00
-- url     : https://prove2.me/theorems/b7d83be9-0cd1-471e-a1f6-b37295ba88a0
-- title:
--   Definitions bundle OAIQ098G177 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm49_4_0_0.s1`, `OAI.SharpPlanar.CachedData.cm49_4_0_0.sums`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_UMoments49`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments49.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G173` and `OAIQ098G176` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.U49.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U49.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G173
import Definitions.Def_OAIQ098G176

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments49
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
namespace cm49_4_0_0
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm49_4_0_0
end SharpPlanar.CachedData

end OAI
end


