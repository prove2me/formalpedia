-- Prove2me | Definitions.Def_OAIQ098G455
-- name    : OAIQ098G455
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:45:32.061114+00:00
-- url     : https://prove2.me/theorems/8ce40b18-6e67-41cc-88e5-9fc66bcee89b
-- title:
--   Definitions bundle OAIQ098G455 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower1_2`, `OAI.SharpPlanar.CachedData.mpower1_21`, `OAI.SharpPlanar.CachedData.mpower1_21_r4`, `OAI.SharpPlanar.CachedData.mpower1_2_r4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers25.lean), [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G450` and `OAIQ098G454` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1481`, `OAIQ098G456`, `OAIQ098G489`, `OAIQ098G506`, `OAIQ098G536`, `OAIQ098G561`, `OAIQ098G586`, `OAIQ098G610`, `OAIQ098G617`, `OAIQ098G658`, `OAIQ098G673`, `OAIQ098G696`, `OAIQ098G716` and `OAIQ098G736`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G450
import Definitions.Def_OAIQ098G454

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
noncomputable def mpower1_2_r4 : Fin 16 → Fin 16 → CBox := ![mpower1_2_r4_0,mpower1_2_r4_1,mpower1_2_r4_2,mpower1_2_r4_3,mpower1_2_r4_4,mpower1_2_r4_5,mpower1_2_r4_6,mpower1_2_r4_7,mpower1_2_r4_8,mpower1_2_r4_9,mpower1_2_r4_10,mpower1_2_r4_11,mpower1_2_r4_12,mpower1_2_r4_13,mpower1_2_r4_14,mpower1_2_r4_15]
noncomputable def mpower1_2 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_2_r0,mpower1_2_r1,mpower1_2_r2,mpower1_2_r3,mpower1_2_r4,mpower1_2_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers25
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
noncomputable def mpower1_21_r4 : Fin 16 → Fin 16 → CBox := ![mpower1_21_r4_0,mpower1_21_r4_1,mpower1_21_r4_2,mpower1_21_r4_3,mpower1_21_r4_4,mpower1_21_r4_5,mpower1_21_r4_6,mpower1_21_r4_7,mpower1_21_r4_8,mpower1_21_r4_9,mpower1_21_r4_10,mpower1_21_r4_11,mpower1_21_r4_12,mpower1_21_r4_13,mpower1_21_r4_14,mpower1_21_r4_15]
noncomputable def mpower1_21 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_21_r0,mpower1_21_r1,mpower1_21_r2,mpower1_21_r3,mpower1_21_r4,mpower1_21_r5]
end SharpPlanar.CachedData

end OAI
end


