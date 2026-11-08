-- Prove2me | Definitions.Def_OAIQ098G1634
-- name    : OAIQ098G1634
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:38:53.693047+00:00
-- url     : https://prove2.me/theorems/320aaf09-9fbc-4065-9a69-1a462d110932
-- title:
--   Definitions bundle OAIQ098G1634 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans86`, `OAI.SharpPlanar.CachedData.trans86_r3`, `OAI.SharpPlanar.CachedData.trans95`, `OAI.SharpPlanar.CachedData.trans95_r4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers100.lean), [`PlanarPacking_Certificate_TransformedPowers90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers90.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1625` and `OAIQ098G1633` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1635`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1625
import Definitions.Def_OAIQ098G1633

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers90
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
noncomputable def trans86_r3 : Fin 16 → Fin 16 → CBox := ![trans86_r3_0,trans86_r3_1,trans86_r3_2,trans86_r3_3,trans86_r3_4,trans86_r3_5,trans86_r3_6,trans86_r3_7,trans86_r3_8,trans86_r3_9,trans86_r3_10,trans86_r3_11,trans86_r3_12,trans86_r3_13,trans86_r3_14,trans86_r3_15]
noncomputable def trans86 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans86_r0,trans86_r1,trans86_r2,trans86_r3,trans86_r4,trans86_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers100
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
noncomputable def trans95_r4 : Fin 16 → Fin 16 → CBox := ![trans95_r4_0,trans95_r4_1,trans95_r4_2,trans95_r4_3,trans95_r4_4,trans95_r4_5,trans95_r4_6,trans95_r4_7,trans95_r4_8,trans95_r4_9,trans95_r4_10,trans95_r4_11,trans95_r4_12,trans95_r4_13,trans95_r4_14,trans95_r4_15]
noncomputable def trans95 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans95_r0,trans95_r1,trans95_r2,trans95_r3,trans95_r4,trans95_r5]
end SharpPlanar.CachedData

end OAI
end


