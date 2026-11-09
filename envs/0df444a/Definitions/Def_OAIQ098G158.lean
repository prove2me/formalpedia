-- Prove2me | Definitions.Def_OAIQ098G158
-- name    : OAIQ098G158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T09:03:45.013539+00:00
-- url     : https://prove2.me/theorems/55837388-62b2-4390-a9f9-5cd8c1c12e3a
-- title:
--   Definitions bundle OAIQ098G158 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm3_12_0_0.s0`, `OAI.SharpPlanar.CachedData.cm3_12_0_0.sums`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LMoments12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments12.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G136`, `OAIQ098G139`, `OAIQ098G151` and `OAIQ098G154` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.lentry2_1_contains_g` and `OAI.SharpPlanar.Numerical.lentry8_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G136
import Definitions.Def_OAIQ098G139
import Definitions.Def_OAIQ098G151
import Definitions.Def_OAIQ098G154

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments12
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
namespace cm3_12_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm3_12_0_0
end SharpPlanar.CachedData

end OAI
end


