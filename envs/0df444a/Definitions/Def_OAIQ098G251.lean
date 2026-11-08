-- Prove2me | Definitions.Def_OAIQ098G251
-- name    : OAIQ098G251
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:02:26.070126+00:00
-- url     : https://prove2.me/theorems/277d068b-0f52-4950-9c3b-e523807105b2
-- title:
--   Definitions bundle OAIQ098G251 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power31`, `OAI.SharpPlanar.CachedData.power31_r2`, `OAI.SharpPlanar.CachedData.power32Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G248` and `OAIQ098G250` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G252`, `OAIQ098G253`, `OAIQ098G624`, `OAIQ098G625`, `OAIQ098G626`, `OAIQ098G627`, `OAIQ098G628`, `OAIQ098G629`, `OAIQ098G630` and `OAIQ098G631`; the proofs of `OAI.SharpPlanar.Bernstein33.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk33_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_1_0_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.power36_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm33_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.wuminus_contains_g` and `OAI.SharpPlanar.Numerical.U33.wuplus_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G248
import Definitions.Def_OAIQ098G250

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
noncomputable def power31_r2 : Fin 16 → Fin 16 → CBox := ![power31_r2_0,power31_r2_1,power31_r2_2,power31_r2_3,power31_r2_4,power31_r2_5,power31_r2_6,power31_r2_7,power31_r2_8,power31_r2_9,power31_r2_10,power31_r2_11,power31_r2_12,power31_r2_13,power31_r2_14,power31_r2_15]
noncomputable def power31 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power31_r0,power31_r1,power31_r2,power31_r3,power31_r4,power31_r5]
noncomputable def power32Expr (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


