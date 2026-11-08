-- Prove2me | Definitions.Def_OAIQ098G1467
-- name    : OAIQ098G1467
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:18:00.902742+00:00
-- url     : https://prove2.me/theorems/d27b004e-3f04-48b7-af92-9581b554164a
-- title:
--   Definitions bundle OAIQ098G1467 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_23Expr`, `OAI.SharpPlanar.CachedData.mpower0_24Expr`, `OAI.SharpPlanar.CachedData.mpower0_25Expr`, `OAI.SharpPlanar.CachedData.mpower0_26Expr`, `OAI.SharpPlanar.CachedData.mpower0_27Expr`, `OAI.SharpPlanar.CachedData.mpower0_28Expr`, `OAI.SharpPlanar.CachedData.mpower0_29Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers25.lean), [`PlanarPacking_Certificate_MomentPowers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G427` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein0.N1_right.t23_contains_g`, `OAI.SharpPlanar.Bernstein0.N1_right.t24_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t22_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t23_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t21_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t22_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t21_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t22_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_29_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_30_contains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_25.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_26.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_27.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_28.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_25.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_26.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_27.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_28.contains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_25.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_26.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_27.realContains_g` and `OAI.SharpPlanar.CachedData.hm1_1_0_28.contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G427

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
noncomputable def mpower0_23Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_22 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 23
noncomputable def mpower0_24Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_23 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 24
noncomputable def mpower0_25Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_24 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 25
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
noncomputable def mpower0_26Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_25 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 26
noncomputable def mpower0_27Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_26 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 27
noncomputable def mpower0_28Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_27 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 28
noncomputable def mpower0_29Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_28 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 29
end SharpPlanar.CachedData

end OAI
end


