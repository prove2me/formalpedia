-- Prove2me | Definitions.Def_OAIQ098G1486
-- name    : OAIQ098G1486
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:22:57.961013+00:00
-- url     : https://prove2.me/theorems/5751851a-8103-4de4-9d27-26bb51d0ed1d
-- title:
--   Definitions bundle OAIQ098G1486 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.mpower1_2Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G441` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein12.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein13.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein13.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein13.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein13.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein21.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein21.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein27.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein27.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein27.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein27.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein27.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein27.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein27.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein27.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t0_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk24_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk25_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk31_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk37_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk39_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk3_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hm0_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm13_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm13_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm21_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm21_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm31_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm31_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm36_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm36_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm37_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm37_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm39_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm39_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_2.realContains_g` and `OAI.SharpPlanar.CachedData.mpower1_4_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G441

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
noncomputable def mpower1_2Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower1_1 j i k).mul (piI.mul (gridRows j i k).z)).scale 1 2
end SharpPlanar.CachedData

end OAI
end


