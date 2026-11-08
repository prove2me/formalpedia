-- Prove2me | Definitions.Def_OAIQ098G028
-- name    : OAIQ098G028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:31:20.524907+00:00
-- url     : https://prove2.me/theorems/e3b75da7-3ce6-4f85-ae54-ae50f10c6bc8
-- title:
--   Definitions bundle OAIQ098G028 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm1_1_1_0.s0`, `OAI.SharpPlanar.CachedData.cm1_1_1_0.sums`, `OAI.SharpPlanar.CachedData.column1_1`, `OAI.SharpPlanar.CachedData.column1_1_r3`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean), [`PlanarPacking_Certificate_DMoments1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DMoments1.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G023` and `OAIQ098G027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G029`, `OAIQ098G035`, `OAIQ098G036`, `OAIQ098G118`, `OAIQ098G121`, `OAIQ098G123` and `OAIQ098G385`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G027

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
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
noncomputable def column1_1_r3 : Fin 16 → Fin 16 → CBox := ![column1_1_r3_0,column1_1_r3_1,column1_1_r3_2,column1_1_r3_3,column1_1_r3_4,column1_1_r3_5,column1_1_r3_6,column1_1_r3_7,column1_1_r3_8,column1_1_r3_9,column1_1_r3_10,column1_1_r3_11,column1_1_r3_12,column1_1_r3_13,column1_1_r3_14,column1_1_r3_15]
noncomputable def column1_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column1_1_r0,column1_1_r1,column1_1_r2,column1_1_r3,column1_1_r4,column1_1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments1
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
namespace cm1_1_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_1_1_0
end SharpPlanar.CachedData

end OAI
end


