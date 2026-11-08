-- Prove2me | Definitions.Def_OAIQ098G1462
-- name    : OAIQ098G1462
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:15:59.257003+00:00
-- url     : https://prove2.me/theorems/11d2b19e-b5f5-41f4-9885-7adbab43251d
-- title:
--   Definitions bundle OAIQ098G1462 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_13Expr`, `OAI.SharpPlanar.CachedData.mpower0_14Expr`, `OAI.SharpPlanar.CachedData.mpower0_15Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G408` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein0.N1_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein0.N1_right.t14_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein21.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein21.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein28.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein28.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein28.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein28.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t13_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_left.t13_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t12_contains_g`, `OAI.SharpPlanar.CachedData.hk0_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_13_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk4_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_15_contains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_0_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_0_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_1_0_16.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_1_0_17.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_0_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_1_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_14.contains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_14.contains_g` and `OAI.SharpPlanar.CachedData.mpower0_19_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G408

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers15
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
noncomputable def mpower0_13Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_12 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 13
noncomputable def mpower0_14Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_13 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 14
noncomputable def mpower0_15Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower0_14 j i k).mul (piI.mul (rcast (gridRows j i k).t))).scale 1 15
end SharpPlanar.CachedData

end OAI
end


