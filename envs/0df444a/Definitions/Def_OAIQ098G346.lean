-- Prove2me | Definitions.Def_OAIQ098G346
-- name    : OAIQ098G346
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:12:20.448198+00:00
-- url     : https://prove2.me/theorems/5c1ca82b-6d00-4cbd-80a9-5a3001921e26
-- title:
--   Definitions bundle OAIQ098G346 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power8`, `OAI.SharpPlanar.CachedData.power8_r3`, `OAI.SharpPlanar.CachedData.power9Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G341` and `OAIQ098G345` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein9.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_15_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_14.contains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_14.contains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.power12_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm9_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U9.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G341
import Definitions.Def_OAIQ098G345

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
noncomputable def power8_r3 : Fin 16 → Fin 16 → CBox := ![power8_r3_0,power8_r3_1,power8_r3_2,power8_r3_3,power8_r3_4,power8_r3_5,power8_r3_6,power8_r3_7,power8_r3_8,power8_r3_9,power8_r3_10,power8_r3_11,power8_r3_12,power8_r3_13,power8_r3_14,power8_r3_15]
noncomputable def power8 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power8_r0,power8_r1,power8_r2,power8_r3,power8_r4,power8_r5]
noncomputable def power9Expr (j : Fin 6) (i k : Fin 16) : CBox := (power8 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


