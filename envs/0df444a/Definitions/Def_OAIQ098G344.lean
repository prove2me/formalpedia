-- Prove2me | Definitions.Def_OAIQ098G344
-- name    : OAIQ098G344
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:55:32.33334+00:00
-- url     : https://prove2.me/theorems/14b2cf40-655b-41e3-b3fd-f3fea9e3ffd1
-- title:
--   Definitions bundle OAIQ098G344 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power7Expr`, `OAI.SharpPlanar.Numerical.U16.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean), [`PlanarPacking_Certificate_WUCert16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert16.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G004` and `OAIQ098G333` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U16.wuplus_column_g`; the proofs of `OAI.SharpPlanar.Bernstein7.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_15_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hm7_0_0_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_0_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_1_0_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_1_0_15.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_14.contains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_14.contains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.power12_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm7_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm9_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U16.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U7.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U7.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U9.wuplus_column_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G333

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
noncomputable def power7Expr (j : Fin 6) (i k : Fin 16) : CBox := (power6 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert16
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

namespace SharpPlanar.Numerical.U16
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U16

end OAI
end


