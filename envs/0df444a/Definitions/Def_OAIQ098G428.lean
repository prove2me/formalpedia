-- Prove2me | Definitions.Def_OAIQ098G428
-- name    : OAIQ098G428
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:42:09.84712+00:00
-- url     : https://prove2.me/theorems/312e18a0-89b2-450d-9766-ff8abacb751e
-- title:
--   Definitions bundle OAIQ098G428 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_20`, `OAI.SharpPlanar.CachedData.mpower0_20_r5`, `OAI.SharpPlanar.CachedData.mpower0_21`, `OAI.SharpPlanar.CachedData.mpower0_21_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers20.lean), [`PlanarPacking_Certificate_MomentPowers25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers25.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G423` and `OAIQ098G427` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1466`, `OAIQ098G429` and `OAIQ098G546`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G423
import Definitions.Def_OAIQ098G427

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers20
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
noncomputable def mpower0_20_r5 : Fin 16 → Fin 16 → CBox := ![mpower0_20_r5_0,mpower0_20_r5_1,mpower0_20_r5_2,mpower0_20_r5_3,mpower0_20_r5_4,mpower0_20_r5_5,mpower0_20_r5_6,mpower0_20_r5_7,mpower0_20_r5_8,mpower0_20_r5_9,mpower0_20_r5_10,mpower0_20_r5_11,mpower0_20_r5_12,mpower0_20_r5_13,mpower0_20_r5_14,mpower0_20_r5_15]
noncomputable def mpower0_20 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_20_r0,mpower0_20_r1,mpower0_20_r2,mpower0_20_r3,mpower0_20_r4,mpower0_20_r5]
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
noncomputable def mpower0_21_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_21_r0_0,mpower0_21_r0_1,mpower0_21_r0_2,mpower0_21_r0_3,mpower0_21_r0_4,mpower0_21_r0_5,mpower0_21_r0_6,mpower0_21_r0_7,mpower0_21_r0_8,mpower0_21_r0_9,mpower0_21_r0_10,mpower0_21_r0_11,mpower0_21_r0_12,mpower0_21_r0_13,mpower0_21_r0_14,mpower0_21_r0_15]
noncomputable def mpower0_21 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_21_r0,mpower0_21_r1,mpower0_21_r2,mpower0_21_r3,mpower0_21_r4,mpower0_21_r5]
end SharpPlanar.CachedData

end OAI
end


