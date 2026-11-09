-- Prove2me | Definitions.Def_OAIQ098G309
-- name    : OAIQ098G309
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:46:45.074027+00:00
-- url     : https://prove2.me/theorems/44ba6a11-6849-4864-872f-d770f02f7823
-- title:
--   Definitions bundle OAIQ098G309 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel7_0Expr`, `OAI.SharpPlanar.CachedData.kernel7_1Expr`, `OAI.SharpPlanar.CachedData.trans7`, `OAI.SharpPlanar.CachedData.trans7_r1`, `OAI.SharpPlanar.CachedData.trans8Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean), [`PlanarPacking_Certificate_TransformedPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G302` and `OAIQ098G308` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.kernel7_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel7_1_contains_g` and `OAI.SharpPlanar.CachedData.trans8_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G302
import Definitions.Def_OAIQ098G308

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def trans7_r1 : Fin 16 → Fin 16 → CBox := ![trans7_r1_0,trans7_r1_1,trans7_r1_2,trans7_r1_3,trans7_r1_4,trans7_r1_5,trans7_r1_6,trans7_r1_7,trans7_r1_8,trans7_r1_9,trans7_r1_10,trans7_r1_11,trans7_r1_12,trans7_r1_13,trans7_r1_14,trans7_r1_15]
noncomputable def trans7 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans7_r0,trans7_r1,trans7_r2,trans7_r3,trans7_r4,trans7_r5]
noncomputable def trans8Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans7 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
noncomputable def kernel7_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans7 j i k)
noncomputable def kernel7_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans7 j i k)).mul (piI.mul (gridRows j i k).z)
end SharpPlanar.CachedData

end OAI
end


