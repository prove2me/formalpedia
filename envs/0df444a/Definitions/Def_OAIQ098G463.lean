-- Prove2me | Definitions.Def_OAIQ098G463
-- name    : OAIQ098G463
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:45:48.437535+00:00
-- url     : https://prove2.me/theorems/c90489cc-00f2-485f-844f-61c00aa5be56
-- title:
--   Definitions bundle OAIQ098G463 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower1_25`, `OAI.SharpPlanar.CachedData.mpower1_25_r5`, `OAI.SharpPlanar.CachedData.mpower1_26`, `OAI.SharpPlanar.CachedData.mpower1_26_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers25.lean), [`PlanarPacking_Certificate_MomentPowers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G458` and `OAIQ098G462` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1484`, `OAIQ098G464` and `OAIQ098G565`; the statement `OAI.SharpPlanar.CachedData.mpower1_25_contains_g`; the proof of `OAI.SharpPlanar.CachedData.mpower1_25_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G458
import Definitions.Def_OAIQ098G462

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
noncomputable def mpower1_25_r5 : Fin 16 → Fin 16 → CBox := ![mpower1_25_r5_0,mpower1_25_r5_1,mpower1_25_r5_2,mpower1_25_r5_3,mpower1_25_r5_4,mpower1_25_r5_5,mpower1_25_r5_6,mpower1_25_r5_7,mpower1_25_r5_8,mpower1_25_r5_9,mpower1_25_r5_10,mpower1_25_r5_11,mpower1_25_r5_12,mpower1_25_r5_13,mpower1_25_r5_14,mpower1_25_r5_15]
noncomputable def mpower1_25 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_25_r0,mpower1_25_r1,mpower1_25_r2,mpower1_25_r3,mpower1_25_r4,mpower1_25_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers30
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
noncomputable def mpower1_26_r5 : Fin 16 → Fin 16 → CBox := ![mpower1_26_r5_0,mpower1_26_r5_1,mpower1_26_r5_2,mpower1_26_r5_3,mpower1_26_r5_4,mpower1_26_r5_5,mpower1_26_r5_6,mpower1_26_r5_7,mpower1_26_r5_8,mpower1_26_r5_9,mpower1_26_r5_10,mpower1_26_r5_11,mpower1_26_r5_12,mpower1_26_r5_13,mpower1_26_r5_14,mpower1_26_r5_15]
noncomputable def mpower1_26 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_26_r0,mpower1_26_r1,mpower1_26_r2,mpower1_26_r3,mpower1_26_r4,mpower1_26_r5]
end SharpPlanar.CachedData

end OAI
end


