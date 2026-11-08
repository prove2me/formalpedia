-- Prove2me | Definitions.Def_OAIQ098G318
-- name    : OAIQ098G318
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:09:50.125975+00:00
-- url     : https://prove2.me/theorems/b9f720ed-dec8-4a38-8319-ae6bb8c48b35
-- title:
--   Definitions bundle OAIQ098G318 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power23`, `OAI.SharpPlanar.CachedData.power23_r0`, `OAI.SharpPlanar.CachedData.power24Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G314` and `OAIQ098G317` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein24.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hm24_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_0_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_1_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.power27_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm24_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm25_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U25.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G314
import Definitions.Def_OAIQ098G317

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
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
noncomputable def power23_r0 : Fin 16 → Fin 16 → CBox := ![power23_r0_0,power23_r0_1,power23_r0_2,power23_r0_3,power23_r0_4,power23_r0_5,power23_r0_6,power23_r0_7,power23_r0_8,power23_r0_9,power23_r0_10,power23_r0_11,power23_r0_12,power23_r0_13,power23_r0_14,power23_r0_15]
noncomputable def power23 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power23_r0,power23_r1,power23_r2,power23_r3,power23_r4,power23_r5]
noncomputable def power24Expr (j : Fin 6) (i k : Fin 16) : CBox := (power23 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


