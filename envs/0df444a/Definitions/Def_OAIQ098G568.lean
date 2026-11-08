-- Prove2me | Definitions.Def_OAIQ098G568
-- name    : OAIQ098G568
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:49:39.16059+00:00
-- url     : https://prove2.me/theorems/dcf61a12-8878-467a-90d1-8278c2dfdeae
-- title:
--   Definitions bundle OAIQ098G568 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hk21_1_9`, `OAI.SharpPlanar.CachedData.hk24_1_9`, `OAI.SharpPlanar.CachedData.hk25_1_9`, `OAI.SharpPlanar.CachedData.mpower1_29`, `OAI.SharpPlanar.CachedData.mpower1_29_r1`, `OAI.SharpPlanar.CachedData.mpower1_29_r2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighHeaders21`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders21.lean), [`PlanarPacking_Certificate_HighHeaders24`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders24.lean), [`PlanarPacking_Certificate_HighHeaders25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders25.lean), [`PlanarPacking_Certificate_MomentPowers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G474` and `OAIQ098G567` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1027`, `OAIQ098G1047`, `OAIQ098G1487` and `OAIQ098G569`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G474
import Definitions.Def_OAIQ098G567

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
noncomputable def mpower1_29_r1 : Fin 16 → Fin 16 → CBox := ![mpower1_29_r1_0,mpower1_29_r1_1,mpower1_29_r1_2,mpower1_29_r1_3,mpower1_29_r1_4,mpower1_29_r1_5,mpower1_29_r1_6,mpower1_29_r1_7,mpower1_29_r1_8,mpower1_29_r1_9,mpower1_29_r1_10,mpower1_29_r1_11,mpower1_29_r1_12,mpower1_29_r1_13,mpower1_29_r1_14,mpower1_29_r1_15]
noncomputable def mpower1_29_r2 : Fin 16 → Fin 16 → CBox := ![mpower1_29_r2_0,mpower1_29_r2_1,mpower1_29_r2_2,mpower1_29_r2_3,mpower1_29_r2_4,mpower1_29_r2_5,mpower1_29_r2_6,mpower1_29_r2_7,mpower1_29_r2_8,mpower1_29_r2_9,mpower1_29_r2_10,mpower1_29_r2_11,mpower1_29_r2_12,mpower1_29_r2_13,mpower1_29_r2_14,mpower1_29_r2_15]
noncomputable def mpower1_29 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_29_r0,mpower1_29_r1,mpower1_29_r2,mpower1_29_r3,mpower1_29_r4,mpower1_29_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders21
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
noncomputable def hk21_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_9 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders24
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
noncomputable def hk24_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_9 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders25
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
noncomputable def hk25_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_9 j i k)
end SharpPlanar.CachedData

end OAI
end


