-- Prove2me | Definitions.Def_OAIQ098G1463
-- name    : OAIQ098G1463
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:17:34.504619+00:00
-- url     : https://prove2.me/theorems/3fcf25ca-5b95-4060-9627-a48b54f210a1
-- title:
--   Definitions bundle OAIQ098G1463 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_16Expr`, `OAI.SharpPlanar.CachedData.mpower0_17Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G424` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.hk0_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk4_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_0_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_0_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_1_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_1_0_17.realContains_g` and `OAI.SharpPlanar.CachedData.mpower0_19_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G424

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
noncomputable def mpower0_16Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_15 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 16
noncomputable def mpower0_17Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_16 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 17
end SharpPlanar.CachedData

end OAI
end


