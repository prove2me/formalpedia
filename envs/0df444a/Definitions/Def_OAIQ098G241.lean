-- Prove2me | Definitions.Def_OAIQ098G241
-- name    : OAIQ098G241
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:59:37.231882+00:00
-- url     : https://prove2.me/theorems/79cac51b-43e7-4a3d-bd40-d1f70ed76a9e
-- title:
--   Definitions bundle OAIQ098G241 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column15_0Expr`, `OAI.SharpPlanar.CachedData.column15_1Expr`, `OAI.SharpPlanar.CachedData.power15`, `OAI.SharpPlanar.CachedData.power15_r0`, `OAI.SharpPlanar.CachedData.power16Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns20.lean), [`PlanarPacking_Certificate_Powers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G022`, `OAIQ098G237` and `OAIQ098G240` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G496`, `OAIQ098G497`, `OAIQ098G498`, `OAIQ098G499`, `OAIQ098G500`, `OAIQ098G501`, `OAIQ098G502` and `OAIQ098G503`; the proofs of `OAI.SharpPlanar.Bernstein16.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.power19_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm15_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm16_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U15.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U16.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G022
import Definitions.Def_OAIQ098G237
import Definitions.Def_OAIQ098G240

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers20
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
noncomputable def power15_r0 : Fin 16 → Fin 16 → CBox := ![power15_r0_0,power15_r0_1,power15_r0_2,power15_r0_3,power15_r0_4,power15_r0_5,power15_r0_6,power15_r0_7,power15_r0_8,power15_r0_9,power15_r0_10,power15_r0_11,power15_r0_12,power15_r0_13,power15_r0_14,power15_r0_15]
noncomputable def power15 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power15_r0,power15_r1,power15_r2,power15_r3,power15_r4,power15_r5]
noncomputable def power16Expr (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns20
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
noncomputable def column15_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power15 j i k)
noncomputable def column15_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power15 j i k)
end SharpPlanar.CachedData

end OAI
end


