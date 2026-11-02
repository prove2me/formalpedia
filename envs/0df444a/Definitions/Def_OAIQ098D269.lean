-- Prove2me | Definitions.Def_OAIQ098D269
-- name    : OAIQ098D269
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:46:55.987841+00:00
-- url     : https://prove2.me/theorems/f18590c2-9f9e-48ef-b02d-036874a8c295
-- title:
--   Definitions bundle OAIQ098D269 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 726 declarations of OpenAI's Lean: 37 definitions and 689 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.cm84_4_0_1.s0`, `OAI.SharpPlanar.CachedData.cm84_4_0_1.s1`, `OAI.SharpPlanar.CachedData.cm84_4_0_1.s2`, `OAI.SharpPlanar.CachedData.cm84_4_0_1.s3`, `OAI.SharpPlanar.CachedData.cm84_4_0_1.sums`, `OAI.SharpPlanar.CachedData.cm84_4_1_0.s0`, `OAI.SharpPlanar.CachedData.cm84_4_1_0.sums`, `OAI.SharpPlanar.CachedData.cm87_1_1_1.s0`, `OAI.SharpPlanar.CachedData.cm87_1_1_1.s1`, `OAI.SharpPlanar.CachedData.cm87_1_1_1.s2`, `OAI.SharpPlanar.CachedData.cm87_1_1_1.s3`, `OAI.SharpPlanar.CachedData.cm87_1_1_1.sums`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.s0`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.s1`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.s2`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.s3`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.s4`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.s5`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.sums`, `OAI.SharpPlanar.CachedData.cm93_1_0_1.s0`, `OAI.SharpPlanar.CachedData.cm93_1_0_1.s1`, `OAI.SharpPlanar.CachedData.cm93_1_0_1.s2`, `OAI.SharpPlanar.CachedData.cm93_1_0_1.s3`, `OAI.SharpPlanar.CachedData.cm93_1_0_1.sums`, `OAI.SharpPlanar.CachedData.cm96_4_1_1.s0`, `OAI.SharpPlanar.CachedData.cm96_4_1_1.s1`, `OAI.SharpPlanar.CachedData.cm96_4_1_1.sums`, `OAI.SharpPlanar.CachedData.cm99_4_0_0.s0`, `OAI.SharpPlanar.CachedData.column81_1Expr`, `OAI.SharpPlanar.CachedData.column84_0Expr`, `OAI.SharpPlanar.CachedData.column84_1Expr`, `OAI.SharpPlanar.CachedData.column87_0Expr`, `OAI.SharpPlanar.CachedData.column87_1Expr`, `OAI.SharpPlanar.CachedData.column91_0Expr`, `OAI.SharpPlanar.CachedData.column97_0Expr`, `OAI.SharpPlanar.CachedData.mpower0_0`, `OAI.SharpPlanar.CachedData.mpower1_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean), [`PlanarPacking_Certificate_Columns90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns90.lean), [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean), [`PlanarPacking_Certificate_UMoments84`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments84.lean), [`PlanarPacking_Certificate_UMoments87`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments87.lean), [`PlanarPacking_Certificate_UMoments88`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments88.lean), [`PlanarPacking_Certificate_UMoments93`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments93.lean), [`PlanarPacking_Certificate_UMoments96`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments96.lean), [`PlanarPacking_Certificate_UMoments99`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments99.lean).
--
--   **Imports.** It imports the bundles `OAIQ098D033`, `OAIQ098D034`, `OAIQ098D035`, `OAIQ098D036`, `OAIQ098D037`, `OAIQ098D039`, `OAIQ098D041`, `OAIQ098D042`, `OAIQ098D043`, `OAIQ098D044`, `OAIQ098D045`, `OAIQ098D047`, `OAIQ098D049`, `OAIQ098D051`, `OAIQ098D052`, `OAIQ098D053`, `OAIQ098D109`, `OAIQ098D117`, `OAIQ098D118`, `OAIQ098D119`, `OAIQ098D120`, `OAIQ098D121`, `OAIQ098D122` and `OAIQ098D123` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D300`, `OAIQ098D326`, `OAIQ098D342`, `OAIQ098D343`, `OAIQ098D345`, `OAIQ098D347`, `OAIQ098D349`, `OAIQ098D351`, `OAIQ098D353`, `OAIQ098D355` and `OAIQ098D543`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D033
import Definitions.Def_OAIQ098D034
import Definitions.Def_OAIQ098D035
import Definitions.Def_OAIQ098D036
import Definitions.Def_OAIQ098D037
import Definitions.Def_OAIQ098D039
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D042
import Definitions.Def_OAIQ098D043
import Definitions.Def_OAIQ098D044
import Definitions.Def_OAIQ098D045
import Definitions.Def_OAIQ098D047
import Definitions.Def_OAIQ098D049
import Definitions.Def_OAIQ098D051
import Definitions.Def_OAIQ098D052
import Definitions.Def_OAIQ098D053
import Definitions.Def_OAIQ098D109
import Definitions.Def_OAIQ098D117
import Definitions.Def_OAIQ098D118
import Definitions.Def_OAIQ098D119
import Definitions.Def_OAIQ098D120
import Definitions.Def_OAIQ098D121
import Definitions.Def_OAIQ098D122
import Definitions.Def_OAIQ098D123

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
noncomputable def column91_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power91 j i k)
lemma column91_0_r0_0_eq : ∀ k : Fin 16, column91_0Expr 0 0 k = column91_0_r0_0 k := by decide +kernel
lemma column91_0_r0_1_eq : ∀ k : Fin 16, column91_0Expr 0 1 k = column91_0_r0_1 k := by decide +kernel
lemma column91_0_r0_2_eq : ∀ k : Fin 16, column91_0Expr 0 2 k = column91_0_r0_2 k := by decide +kernel
lemma column91_0_r0_3_eq : ∀ k : Fin 16, column91_0Expr 0 3 k = column91_0_r0_3 k := by decide +kernel
lemma column91_0_r0_4_eq : ∀ k : Fin 16, column91_0Expr 0 4 k = column91_0_r0_4 k := by decide +kernel
lemma column91_0_r0_5_eq : ∀ k : Fin 16, column91_0Expr 0 5 k = column91_0_r0_5 k := by decide +kernel
lemma column91_0_r0_6_eq : ∀ k : Fin 16, column91_0Expr 0 6 k = column91_0_r0_6 k := by decide +kernel
lemma column91_0_r0_7_eq : ∀ k : Fin 16, column91_0Expr 0 7 k = column91_0_r0_7 k := by decide +kernel
lemma column91_0_r0_8_eq : ∀ k : Fin 16, column91_0Expr 0 8 k = column91_0_r0_8 k := by decide +kernel
lemma column91_0_r0_9_eq : ∀ k : Fin 16, column91_0Expr 0 9 k = column91_0_r0_9 k := by decide +kernel
lemma column91_0_r0_10_eq : ∀ k : Fin 16, column91_0Expr 0 10 k = column91_0_r0_10 k := by decide +kernel
lemma column91_0_r0_11_eq : ∀ k : Fin 16, column91_0Expr 0 11 k = column91_0_r0_11 k := by decide +kernel
lemma column91_0_r0_12_eq : ∀ k : Fin 16, column91_0Expr 0 12 k = column91_0_r0_12 k := by decide +kernel
lemma column91_0_r0_13_eq : ∀ k : Fin 16, column91_0Expr 0 13 k = column91_0_r0_13 k := by decide +kernel
lemma column91_0_r0_14_eq : ∀ k : Fin 16, column91_0Expr 0 14 k = column91_0_r0_14 k := by decide +kernel
lemma column91_0_r0_15_eq : ∀ k : Fin 16, column91_0Expr 0 15 k = column91_0_r0_15 k := by decide +kernel
lemma column91_0_r0_eq (i k : Fin 16) : column91_0Expr 0 i k = column91_0_r0 i k := by
  fin_cases i
  · exact column91_0_r0_0_eq k
  · exact column91_0_r0_1_eq k
  · exact column91_0_r0_2_eq k
  · exact column91_0_r0_3_eq k
  · exact column91_0_r0_4_eq k
  · exact column91_0_r0_5_eq k
  · exact column91_0_r0_6_eq k
  · exact column91_0_r0_7_eq k
  · exact column91_0_r0_8_eq k
  · exact column91_0_r0_9_eq k
  · exact column91_0_r0_10_eq k
  · exact column91_0_r0_11_eq k
  · exact column91_0_r0_12_eq k
  · exact column91_0_r0_13_eq k
  · exact column91_0_r0_14_eq k
  · exact column91_0_r0_15_eq k
lemma column91_0_r1_0_eq : ∀ k : Fin 16, column91_0Expr 1 0 k = column91_0_r1_0 k := by decide +kernel
lemma column91_0_r1_1_eq : ∀ k : Fin 16, column91_0Expr 1 1 k = column91_0_r1_1 k := by decide +kernel
lemma column91_0_r1_2_eq : ∀ k : Fin 16, column91_0Expr 1 2 k = column91_0_r1_2 k := by decide +kernel
lemma column91_0_r1_3_eq : ∀ k : Fin 16, column91_0Expr 1 3 k = column91_0_r1_3 k := by decide +kernel
lemma column91_0_r1_4_eq : ∀ k : Fin 16, column91_0Expr 1 4 k = column91_0_r1_4 k := by decide +kernel
lemma column91_0_r1_5_eq : ∀ k : Fin 16, column91_0Expr 1 5 k = column91_0_r1_5 k := by decide +kernel
lemma column91_0_r1_6_eq : ∀ k : Fin 16, column91_0Expr 1 6 k = column91_0_r1_6 k := by decide +kernel
lemma column91_0_r1_7_eq : ∀ k : Fin 16, column91_0Expr 1 7 k = column91_0_r1_7 k := by decide +kernel
lemma column91_0_r1_8_eq : ∀ k : Fin 16, column91_0Expr 1 8 k = column91_0_r1_8 k := by decide +kernel
lemma column91_0_r1_9_eq : ∀ k : Fin 16, column91_0Expr 1 9 k = column91_0_r1_9 k := by decide +kernel
lemma column91_0_r1_10_eq : ∀ k : Fin 16, column91_0Expr 1 10 k = column91_0_r1_10 k := by decide +kernel
lemma column91_0_r1_11_eq : ∀ k : Fin 16, column91_0Expr 1 11 k = column91_0_r1_11 k := by decide +kernel
lemma column91_0_r1_12_eq : ∀ k : Fin 16, column91_0Expr 1 12 k = column91_0_r1_12 k := by decide +kernel
lemma column91_0_r1_13_eq : ∀ k : Fin 16, column91_0Expr 1 13 k = column91_0_r1_13 k := by decide +kernel
lemma column91_0_r1_14_eq : ∀ k : Fin 16, column91_0Expr 1 14 k = column91_0_r1_14 k := by decide +kernel
lemma column91_0_r1_15_eq : ∀ k : Fin 16, column91_0Expr 1 15 k = column91_0_r1_15 k := by decide +kernel
lemma column91_0_r1_eq (i k : Fin 16) : column91_0Expr 1 i k = column91_0_r1 i k := by
  fin_cases i
  · exact column91_0_r1_0_eq k
  · exact column91_0_r1_1_eq k
  · exact column91_0_r1_2_eq k
  · exact column91_0_r1_3_eq k
  · exact column91_0_r1_4_eq k
  · exact column91_0_r1_5_eq k
  · exact column91_0_r1_6_eq k
  · exact column91_0_r1_7_eq k
  · exact column91_0_r1_8_eq k
  · exact column91_0_r1_9_eq k
  · exact column91_0_r1_10_eq k
  · exact column91_0_r1_11_eq k
  · exact column91_0_r1_12_eq k
  · exact column91_0_r1_13_eq k
  · exact column91_0_r1_14_eq k
  · exact column91_0_r1_15_eq k
lemma column91_0_r2_0_eq : ∀ k : Fin 16, column91_0Expr 2 0 k = column91_0_r2_0 k := by decide +kernel
lemma column91_0_r2_1_eq : ∀ k : Fin 16, column91_0Expr 2 1 k = column91_0_r2_1 k := by decide +kernel
lemma column91_0_r2_2_eq : ∀ k : Fin 16, column91_0Expr 2 2 k = column91_0_r2_2 k := by decide +kernel
lemma column91_0_r2_3_eq : ∀ k : Fin 16, column91_0Expr 2 3 k = column91_0_r2_3 k := by decide +kernel
lemma column91_0_r2_4_eq : ∀ k : Fin 16, column91_0Expr 2 4 k = column91_0_r2_4 k := by decide +kernel
lemma column91_0_r2_5_eq : ∀ k : Fin 16, column91_0Expr 2 5 k = column91_0_r2_5 k := by decide +kernel
lemma column91_0_r2_6_eq : ∀ k : Fin 16, column91_0Expr 2 6 k = column91_0_r2_6 k := by decide +kernel
lemma column91_0_r2_7_eq : ∀ k : Fin 16, column91_0Expr 2 7 k = column91_0_r2_7 k := by decide +kernel
lemma column91_0_r2_8_eq : ∀ k : Fin 16, column91_0Expr 2 8 k = column91_0_r2_8 k := by decide +kernel
lemma column91_0_r2_9_eq : ∀ k : Fin 16, column91_0Expr 2 9 k = column91_0_r2_9 k := by decide +kernel
lemma column91_0_r2_10_eq : ∀ k : Fin 16, column91_0Expr 2 10 k = column91_0_r2_10 k := by decide +kernel
lemma column91_0_r2_11_eq : ∀ k : Fin 16, column91_0Expr 2 11 k = column91_0_r2_11 k := by decide +kernel
lemma column91_0_r2_12_eq : ∀ k : Fin 16, column91_0Expr 2 12 k = column91_0_r2_12 k := by decide +kernel
lemma column91_0_r2_13_eq : ∀ k : Fin 16, column91_0Expr 2 13 k = column91_0_r2_13 k := by decide +kernel
lemma column91_0_r2_14_eq : ∀ k : Fin 16, column91_0Expr 2 14 k = column91_0_r2_14 k := by decide +kernel
lemma column91_0_r2_15_eq : ∀ k : Fin 16, column91_0Expr 2 15 k = column91_0_r2_15 k := by decide +kernel
lemma column91_0_r2_eq (i k : Fin 16) : column91_0Expr 2 i k = column91_0_r2 i k := by
  fin_cases i
  · exact column91_0_r2_0_eq k
  · exact column91_0_r2_1_eq k
  · exact column91_0_r2_2_eq k
  · exact column91_0_r2_3_eq k
  · exact column91_0_r2_4_eq k
  · exact column91_0_r2_5_eq k
  · exact column91_0_r2_6_eq k
  · exact column91_0_r2_7_eq k
  · exact column91_0_r2_8_eq k
  · exact column91_0_r2_9_eq k
  · exact column91_0_r2_10_eq k
  · exact column91_0_r2_11_eq k
  · exact column91_0_r2_12_eq k
  · exact column91_0_r2_13_eq k
  · exact column91_0_r2_14_eq k
  · exact column91_0_r2_15_eq k
lemma column91_0_r3_0_eq : ∀ k : Fin 16, column91_0Expr 3 0 k = column91_0_r3_0 k := by decide +kernel
lemma column91_0_r3_1_eq : ∀ k : Fin 16, column91_0Expr 3 1 k = column91_0_r3_1 k := by decide +kernel
lemma column91_0_r3_2_eq : ∀ k : Fin 16, column91_0Expr 3 2 k = column91_0_r3_2 k := by decide +kernel
lemma column91_0_r3_3_eq : ∀ k : Fin 16, column91_0Expr 3 3 k = column91_0_r3_3 k := by decide +kernel
lemma column91_0_r3_4_eq : ∀ k : Fin 16, column91_0Expr 3 4 k = column91_0_r3_4 k := by decide +kernel
lemma column91_0_r3_5_eq : ∀ k : Fin 16, column91_0Expr 3 5 k = column91_0_r3_5 k := by decide +kernel
lemma column91_0_r3_6_eq : ∀ k : Fin 16, column91_0Expr 3 6 k = column91_0_r3_6 k := by decide +kernel
lemma column91_0_r3_7_eq : ∀ k : Fin 16, column91_0Expr 3 7 k = column91_0_r3_7 k := by decide +kernel
lemma column91_0_r3_8_eq : ∀ k : Fin 16, column91_0Expr 3 8 k = column91_0_r3_8 k := by decide +kernel
lemma column91_0_r3_9_eq : ∀ k : Fin 16, column91_0Expr 3 9 k = column91_0_r3_9 k := by decide +kernel
lemma column91_0_r3_10_eq : ∀ k : Fin 16, column91_0Expr 3 10 k = column91_0_r3_10 k := by decide +kernel
lemma column91_0_r3_11_eq : ∀ k : Fin 16, column91_0Expr 3 11 k = column91_0_r3_11 k := by decide +kernel
lemma column91_0_r3_12_eq : ∀ k : Fin 16, column91_0Expr 3 12 k = column91_0_r3_12 k := by decide +kernel
lemma column91_0_r3_13_eq : ∀ k : Fin 16, column91_0Expr 3 13 k = column91_0_r3_13 k := by decide +kernel
lemma column91_0_r3_14_eq : ∀ k : Fin 16, column91_0Expr 3 14 k = column91_0_r3_14 k := by decide +kernel
lemma column91_0_r3_15_eq : ∀ k : Fin 16, column91_0Expr 3 15 k = column91_0_r3_15 k := by decide +kernel
lemma column91_0_r3_eq (i k : Fin 16) : column91_0Expr 3 i k = column91_0_r3 i k := by
  fin_cases i
  · exact column91_0_r3_0_eq k
  · exact column91_0_r3_1_eq k
  · exact column91_0_r3_2_eq k
  · exact column91_0_r3_3_eq k
  · exact column91_0_r3_4_eq k
  · exact column91_0_r3_5_eq k
  · exact column91_0_r3_6_eq k
  · exact column91_0_r3_7_eq k
  · exact column91_0_r3_8_eq k
  · exact column91_0_r3_9_eq k
  · exact column91_0_r3_10_eq k
  · exact column91_0_r3_11_eq k
  · exact column91_0_r3_12_eq k
  · exact column91_0_r3_13_eq k
  · exact column91_0_r3_14_eq k
  · exact column91_0_r3_15_eq k
lemma column91_0_r4_0_eq : ∀ k : Fin 16, column91_0Expr 4 0 k = column91_0_r4_0 k := by decide +kernel
lemma column91_0_r4_1_eq : ∀ k : Fin 16, column91_0Expr 4 1 k = column91_0_r4_1 k := by decide +kernel
lemma column91_0_r4_2_eq : ∀ k : Fin 16, column91_0Expr 4 2 k = column91_0_r4_2 k := by decide +kernel
lemma column91_0_r4_3_eq : ∀ k : Fin 16, column91_0Expr 4 3 k = column91_0_r4_3 k := by decide +kernel
lemma column91_0_r4_4_eq : ∀ k : Fin 16, column91_0Expr 4 4 k = column91_0_r4_4 k := by decide +kernel
lemma column91_0_r4_5_eq : ∀ k : Fin 16, column91_0Expr 4 5 k = column91_0_r4_5 k := by decide +kernel
lemma column91_0_r4_6_eq : ∀ k : Fin 16, column91_0Expr 4 6 k = column91_0_r4_6 k := by decide +kernel
lemma column91_0_r4_7_eq : ∀ k : Fin 16, column91_0Expr 4 7 k = column91_0_r4_7 k := by decide +kernel
lemma column91_0_r4_8_eq : ∀ k : Fin 16, column91_0Expr 4 8 k = column91_0_r4_8 k := by decide +kernel
lemma column91_0_r4_9_eq : ∀ k : Fin 16, column91_0Expr 4 9 k = column91_0_r4_9 k := by decide +kernel
lemma column91_0_r4_10_eq : ∀ k : Fin 16, column91_0Expr 4 10 k = column91_0_r4_10 k := by decide +kernel
lemma column91_0_r4_11_eq : ∀ k : Fin 16, column91_0Expr 4 11 k = column91_0_r4_11 k := by decide +kernel
lemma column91_0_r4_12_eq : ∀ k : Fin 16, column91_0Expr 4 12 k = column91_0_r4_12 k := by decide +kernel
lemma column91_0_r4_13_eq : ∀ k : Fin 16, column91_0Expr 4 13 k = column91_0_r4_13 k := by decide +kernel
lemma column91_0_r4_14_eq : ∀ k : Fin 16, column91_0Expr 4 14 k = column91_0_r4_14 k := by decide +kernel
lemma column91_0_r4_15_eq : ∀ k : Fin 16, column91_0Expr 4 15 k = column91_0_r4_15 k := by decide +kernel
lemma column91_0_r4_eq (i k : Fin 16) : column91_0Expr 4 i k = column91_0_r4 i k := by
  fin_cases i
  · exact column91_0_r4_0_eq k
  · exact column91_0_r4_1_eq k
  · exact column91_0_r4_2_eq k
  · exact column91_0_r4_3_eq k
  · exact column91_0_r4_4_eq k
  · exact column91_0_r4_5_eq k
  · exact column91_0_r4_6_eq k
  · exact column91_0_r4_7_eq k
  · exact column91_0_r4_8_eq k
  · exact column91_0_r4_9_eq k
  · exact column91_0_r4_10_eq k
  · exact column91_0_r4_11_eq k
  · exact column91_0_r4_12_eq k
  · exact column91_0_r4_13_eq k
  · exact column91_0_r4_14_eq k
  · exact column91_0_r4_15_eq k
lemma column91_0_r5_0_eq : ∀ k : Fin 16, column91_0Expr 5 0 k = column91_0_r5_0 k := by decide +kernel
lemma column91_0_r5_1_eq : ∀ k : Fin 16, column91_0Expr 5 1 k = column91_0_r5_1 k := by decide +kernel
lemma column91_0_r5_2_eq : ∀ k : Fin 16, column91_0Expr 5 2 k = column91_0_r5_2 k := by decide +kernel
lemma column91_0_r5_3_eq : ∀ k : Fin 16, column91_0Expr 5 3 k = column91_0_r5_3 k := by decide +kernel
lemma column91_0_r5_4_eq : ∀ k : Fin 16, column91_0Expr 5 4 k = column91_0_r5_4 k := by decide +kernel
lemma column91_0_r5_5_eq : ∀ k : Fin 16, column91_0Expr 5 5 k = column91_0_r5_5 k := by decide +kernel
lemma column91_0_r5_6_eq : ∀ k : Fin 16, column91_0Expr 5 6 k = column91_0_r5_6 k := by decide +kernel
lemma column91_0_r5_7_eq : ∀ k : Fin 16, column91_0Expr 5 7 k = column91_0_r5_7 k := by decide +kernel
lemma column91_0_r5_8_eq : ∀ k : Fin 16, column91_0Expr 5 8 k = column91_0_r5_8 k := by decide +kernel
lemma column91_0_r5_9_eq : ∀ k : Fin 16, column91_0Expr 5 9 k = column91_0_r5_9 k := by decide +kernel
lemma column91_0_r5_10_eq : ∀ k : Fin 16, column91_0Expr 5 10 k = column91_0_r5_10 k := by decide +kernel
lemma column91_0_r5_11_eq : ∀ k : Fin 16, column91_0Expr 5 11 k = column91_0_r5_11 k := by decide +kernel
lemma column91_0_r5_12_eq : ∀ k : Fin 16, column91_0Expr 5 12 k = column91_0_r5_12 k := by decide +kernel
lemma column91_0_r5_13_eq : ∀ k : Fin 16, column91_0Expr 5 13 k = column91_0_r5_13 k := by decide +kernel
lemma column91_0_r5_14_eq : ∀ k : Fin 16, column91_0Expr 5 14 k = column91_0_r5_14 k := by decide +kernel
lemma column91_0_r5_15_eq : ∀ k : Fin 16, column91_0Expr 5 15 k = column91_0_r5_15 k := by decide +kernel
lemma column91_0_r5_eq (i k : Fin 16) : column91_0Expr 5 i k = column91_0_r5 i k := by
  fin_cases i
  · exact column91_0_r5_0_eq k
  · exact column91_0_r5_1_eq k
  · exact column91_0_r5_2_eq k
  · exact column91_0_r5_3_eq k
  · exact column91_0_r5_4_eq k
  · exact column91_0_r5_5_eq k
  · exact column91_0_r5_6_eq k
  · exact column91_0_r5_7_eq k
  · exact column91_0_r5_8_eq k
  · exact column91_0_r5_9_eq k
  · exact column91_0_r5_10_eq k
  · exact column91_0_r5_11_eq k
  · exact column91_0_r5_12_eq k
  · exact column91_0_r5_13_eq k
  · exact column91_0_r5_14_eq k
  · exact column91_0_r5_15_eq k
lemma column91_0_eq (j : Fin 6) (i k : Fin 16) : column91_0Expr j i k = column91_0 j i k := by
  fin_cases j
  · exact column91_0_r0_eq i k
  · exact column91_0_r1_eq i k
  · exact column91_0_r2_eq i k
  · exact column91_0_r3_eq i k
  · exact column91_0_r4_eq i k
  · exact column91_0_r5_eq i k
noncomputable def column97_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power97 j i k)
lemma column97_0_r0_0_eq : ∀ k : Fin 16, column97_0Expr 0 0 k = column97_0_r0_0 k := by decide +kernel
lemma column97_0_r0_1_eq : ∀ k : Fin 16, column97_0Expr 0 1 k = column97_0_r0_1 k := by decide +kernel
lemma column97_0_r0_2_eq : ∀ k : Fin 16, column97_0Expr 0 2 k = column97_0_r0_2 k := by decide +kernel
lemma column97_0_r0_3_eq : ∀ k : Fin 16, column97_0Expr 0 3 k = column97_0_r0_3 k := by decide +kernel
lemma column97_0_r0_4_eq : ∀ k : Fin 16, column97_0Expr 0 4 k = column97_0_r0_4 k := by decide +kernel
lemma column97_0_r0_5_eq : ∀ k : Fin 16, column97_0Expr 0 5 k = column97_0_r0_5 k := by decide +kernel
lemma column97_0_r0_6_eq : ∀ k : Fin 16, column97_0Expr 0 6 k = column97_0_r0_6 k := by decide +kernel
lemma column97_0_r0_7_eq : ∀ k : Fin 16, column97_0Expr 0 7 k = column97_0_r0_7 k := by decide +kernel
lemma column97_0_r0_8_eq : ∀ k : Fin 16, column97_0Expr 0 8 k = column97_0_r0_8 k := by decide +kernel
lemma column97_0_r0_9_eq : ∀ k : Fin 16, column97_0Expr 0 9 k = column97_0_r0_9 k := by decide +kernel
lemma column97_0_r0_10_eq : ∀ k : Fin 16, column97_0Expr 0 10 k = column97_0_r0_10 k := by decide +kernel
lemma column97_0_r0_11_eq : ∀ k : Fin 16, column97_0Expr 0 11 k = column97_0_r0_11 k := by decide +kernel
lemma column97_0_r0_12_eq : ∀ k : Fin 16, column97_0Expr 0 12 k = column97_0_r0_12 k := by decide +kernel
lemma column97_0_r0_13_eq : ∀ k : Fin 16, column97_0Expr 0 13 k = column97_0_r0_13 k := by decide +kernel
lemma column97_0_r0_14_eq : ∀ k : Fin 16, column97_0Expr 0 14 k = column97_0_r0_14 k := by decide +kernel
lemma column97_0_r0_15_eq : ∀ k : Fin 16, column97_0Expr 0 15 k = column97_0_r0_15 k := by decide +kernel
lemma column97_0_r0_eq (i k : Fin 16) : column97_0Expr 0 i k = column97_0_r0 i k := by
  fin_cases i
  · exact column97_0_r0_0_eq k
  · exact column97_0_r0_1_eq k
  · exact column97_0_r0_2_eq k
  · exact column97_0_r0_3_eq k
  · exact column97_0_r0_4_eq k
  · exact column97_0_r0_5_eq k
  · exact column97_0_r0_6_eq k
  · exact column97_0_r0_7_eq k
  · exact column97_0_r0_8_eq k
  · exact column97_0_r0_9_eq k
  · exact column97_0_r0_10_eq k
  · exact column97_0_r0_11_eq k
  · exact column97_0_r0_12_eq k
  · exact column97_0_r0_13_eq k
  · exact column97_0_r0_14_eq k
  · exact column97_0_r0_15_eq k
lemma column97_0_r1_0_eq : ∀ k : Fin 16, column97_0Expr 1 0 k = column97_0_r1_0 k := by decide +kernel
lemma column97_0_r1_1_eq : ∀ k : Fin 16, column97_0Expr 1 1 k = column97_0_r1_1 k := by decide +kernel
lemma column97_0_r1_2_eq : ∀ k : Fin 16, column97_0Expr 1 2 k = column97_0_r1_2 k := by decide +kernel
lemma column97_0_r1_3_eq : ∀ k : Fin 16, column97_0Expr 1 3 k = column97_0_r1_3 k := by decide +kernel
lemma column97_0_r1_4_eq : ∀ k : Fin 16, column97_0Expr 1 4 k = column97_0_r1_4 k := by decide +kernel
lemma column97_0_r1_5_eq : ∀ k : Fin 16, column97_0Expr 1 5 k = column97_0_r1_5 k := by decide +kernel
lemma column97_0_r1_6_eq : ∀ k : Fin 16, column97_0Expr 1 6 k = column97_0_r1_6 k := by decide +kernel
lemma column97_0_r1_7_eq : ∀ k : Fin 16, column97_0Expr 1 7 k = column97_0_r1_7 k := by decide +kernel
lemma column97_0_r1_8_eq : ∀ k : Fin 16, column97_0Expr 1 8 k = column97_0_r1_8 k := by decide +kernel
lemma column97_0_r1_9_eq : ∀ k : Fin 16, column97_0Expr 1 9 k = column97_0_r1_9 k := by decide +kernel
lemma column97_0_r1_10_eq : ∀ k : Fin 16, column97_0Expr 1 10 k = column97_0_r1_10 k := by decide +kernel
lemma column97_0_r1_11_eq : ∀ k : Fin 16, column97_0Expr 1 11 k = column97_0_r1_11 k := by decide +kernel
lemma column97_0_r1_12_eq : ∀ k : Fin 16, column97_0Expr 1 12 k = column97_0_r1_12 k := by decide +kernel
lemma column97_0_r1_13_eq : ∀ k : Fin 16, column97_0Expr 1 13 k = column97_0_r1_13 k := by decide +kernel
lemma column97_0_r1_14_eq : ∀ k : Fin 16, column97_0Expr 1 14 k = column97_0_r1_14 k := by decide +kernel
lemma column97_0_r1_15_eq : ∀ k : Fin 16, column97_0Expr 1 15 k = column97_0_r1_15 k := by decide +kernel
lemma column97_0_r1_eq (i k : Fin 16) : column97_0Expr 1 i k = column97_0_r1 i k := by
  fin_cases i
  · exact column97_0_r1_0_eq k
  · exact column97_0_r1_1_eq k
  · exact column97_0_r1_2_eq k
  · exact column97_0_r1_3_eq k
  · exact column97_0_r1_4_eq k
  · exact column97_0_r1_5_eq k
  · exact column97_0_r1_6_eq k
  · exact column97_0_r1_7_eq k
  · exact column97_0_r1_8_eq k
  · exact column97_0_r1_9_eq k
  · exact column97_0_r1_10_eq k
  · exact column97_0_r1_11_eq k
  · exact column97_0_r1_12_eq k
  · exact column97_0_r1_13_eq k
  · exact column97_0_r1_14_eq k
  · exact column97_0_r1_15_eq k
lemma column97_0_r2_0_eq : ∀ k : Fin 16, column97_0Expr 2 0 k = column97_0_r2_0 k := by decide +kernel
lemma column97_0_r2_1_eq : ∀ k : Fin 16, column97_0Expr 2 1 k = column97_0_r2_1 k := by decide +kernel
lemma column97_0_r2_2_eq : ∀ k : Fin 16, column97_0Expr 2 2 k = column97_0_r2_2 k := by decide +kernel
lemma column97_0_r2_3_eq : ∀ k : Fin 16, column97_0Expr 2 3 k = column97_0_r2_3 k := by decide +kernel
lemma column97_0_r2_4_eq : ∀ k : Fin 16, column97_0Expr 2 4 k = column97_0_r2_4 k := by decide +kernel
lemma column97_0_r2_5_eq : ∀ k : Fin 16, column97_0Expr 2 5 k = column97_0_r2_5 k := by decide +kernel
lemma column97_0_r2_6_eq : ∀ k : Fin 16, column97_0Expr 2 6 k = column97_0_r2_6 k := by decide +kernel
lemma column97_0_r2_7_eq : ∀ k : Fin 16, column97_0Expr 2 7 k = column97_0_r2_7 k := by decide +kernel
lemma column97_0_r2_8_eq : ∀ k : Fin 16, column97_0Expr 2 8 k = column97_0_r2_8 k := by decide +kernel
lemma column97_0_r2_9_eq : ∀ k : Fin 16, column97_0Expr 2 9 k = column97_0_r2_9 k := by decide +kernel
lemma column97_0_r2_10_eq : ∀ k : Fin 16, column97_0Expr 2 10 k = column97_0_r2_10 k := by decide +kernel
lemma column97_0_r2_11_eq : ∀ k : Fin 16, column97_0Expr 2 11 k = column97_0_r2_11 k := by decide +kernel
lemma column97_0_r2_12_eq : ∀ k : Fin 16, column97_0Expr 2 12 k = column97_0_r2_12 k := by decide +kernel
lemma column97_0_r2_13_eq : ∀ k : Fin 16, column97_0Expr 2 13 k = column97_0_r2_13 k := by decide +kernel
lemma column97_0_r2_14_eq : ∀ k : Fin 16, column97_0Expr 2 14 k = column97_0_r2_14 k := by decide +kernel
lemma column97_0_r2_15_eq : ∀ k : Fin 16, column97_0Expr 2 15 k = column97_0_r2_15 k := by decide +kernel
lemma column97_0_r2_eq (i k : Fin 16) : column97_0Expr 2 i k = column97_0_r2 i k := by
  fin_cases i
  · exact column97_0_r2_0_eq k
  · exact column97_0_r2_1_eq k
  · exact column97_0_r2_2_eq k
  · exact column97_0_r2_3_eq k
  · exact column97_0_r2_4_eq k
  · exact column97_0_r2_5_eq k
  · exact column97_0_r2_6_eq k
  · exact column97_0_r2_7_eq k
  · exact column97_0_r2_8_eq k
  · exact column97_0_r2_9_eq k
  · exact column97_0_r2_10_eq k
  · exact column97_0_r2_11_eq k
  · exact column97_0_r2_12_eq k
  · exact column97_0_r2_13_eq k
  · exact column97_0_r2_14_eq k
  · exact column97_0_r2_15_eq k
lemma column97_0_r3_0_eq : ∀ k : Fin 16, column97_0Expr 3 0 k = column97_0_r3_0 k := by decide +kernel
lemma column97_0_r3_1_eq : ∀ k : Fin 16, column97_0Expr 3 1 k = column97_0_r3_1 k := by decide +kernel
lemma column97_0_r3_2_eq : ∀ k : Fin 16, column97_0Expr 3 2 k = column97_0_r3_2 k := by decide +kernel
lemma column97_0_r3_3_eq : ∀ k : Fin 16, column97_0Expr 3 3 k = column97_0_r3_3 k := by decide +kernel
lemma column97_0_r3_4_eq : ∀ k : Fin 16, column97_0Expr 3 4 k = column97_0_r3_4 k := by decide +kernel
lemma column97_0_r3_5_eq : ∀ k : Fin 16, column97_0Expr 3 5 k = column97_0_r3_5 k := by decide +kernel
lemma column97_0_r3_6_eq : ∀ k : Fin 16, column97_0Expr 3 6 k = column97_0_r3_6 k := by decide +kernel
lemma column97_0_r3_7_eq : ∀ k : Fin 16, column97_0Expr 3 7 k = column97_0_r3_7 k := by decide +kernel
lemma column97_0_r3_8_eq : ∀ k : Fin 16, column97_0Expr 3 8 k = column97_0_r3_8 k := by decide +kernel
lemma column97_0_r3_9_eq : ∀ k : Fin 16, column97_0Expr 3 9 k = column97_0_r3_9 k := by decide +kernel
lemma column97_0_r3_10_eq : ∀ k : Fin 16, column97_0Expr 3 10 k = column97_0_r3_10 k := by decide +kernel
lemma column97_0_r3_11_eq : ∀ k : Fin 16, column97_0Expr 3 11 k = column97_0_r3_11 k := by decide +kernel
lemma column97_0_r3_12_eq : ∀ k : Fin 16, column97_0Expr 3 12 k = column97_0_r3_12 k := by decide +kernel
lemma column97_0_r3_13_eq : ∀ k : Fin 16, column97_0Expr 3 13 k = column97_0_r3_13 k := by decide +kernel
lemma column97_0_r3_14_eq : ∀ k : Fin 16, column97_0Expr 3 14 k = column97_0_r3_14 k := by decide +kernel
lemma column97_0_r3_15_eq : ∀ k : Fin 16, column97_0Expr 3 15 k = column97_0_r3_15 k := by decide +kernel
lemma column97_0_r3_eq (i k : Fin 16) : column97_0Expr 3 i k = column97_0_r3 i k := by
  fin_cases i
  · exact column97_0_r3_0_eq k
  · exact column97_0_r3_1_eq k
  · exact column97_0_r3_2_eq k
  · exact column97_0_r3_3_eq k
  · exact column97_0_r3_4_eq k
  · exact column97_0_r3_5_eq k
  · exact column97_0_r3_6_eq k
  · exact column97_0_r3_7_eq k
  · exact column97_0_r3_8_eq k
  · exact column97_0_r3_9_eq k
  · exact column97_0_r3_10_eq k
  · exact column97_0_r3_11_eq k
  · exact column97_0_r3_12_eq k
  · exact column97_0_r3_13_eq k
  · exact column97_0_r3_14_eq k
  · exact column97_0_r3_15_eq k
lemma column97_0_r4_0_eq : ∀ k : Fin 16, column97_0Expr 4 0 k = column97_0_r4_0 k := by decide +kernel
lemma column97_0_r4_10_eq : ∀ k : Fin 16, column97_0Expr 4 10 k = column97_0_r4_10 k := by decide +kernel
lemma column97_0_r4_11_eq : ∀ k : Fin 16, column97_0Expr 4 11 k = column97_0_r4_11 k := by decide +kernel
lemma column97_0_r4_12_eq : ∀ k : Fin 16, column97_0Expr 4 12 k = column97_0_r4_12 k := by decide +kernel
lemma column97_0_r4_13_eq : ∀ k : Fin 16, column97_0Expr 4 13 k = column97_0_r4_13 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns90
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
noncomputable def column81_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power81 j i k)
lemma column81_1_r0_0_eq : ∀ k : Fin 16, column81_1Expr 0 0 k = column81_1_r0_0 k := by decide +kernel
lemma column81_1_r0_1_eq : ∀ k : Fin 16, column81_1Expr 0 1 k = column81_1_r0_1 k := by decide +kernel
lemma column81_1_r0_2_eq : ∀ k : Fin 16, column81_1Expr 0 2 k = column81_1_r0_2 k := by decide +kernel
lemma column81_1_r0_3_eq : ∀ k : Fin 16, column81_1Expr 0 3 k = column81_1_r0_3 k := by decide +kernel
lemma column81_1_r0_4_eq : ∀ k : Fin 16, column81_1Expr 0 4 k = column81_1_r0_4 k := by decide +kernel
lemma column81_1_r0_5_eq : ∀ k : Fin 16, column81_1Expr 0 5 k = column81_1_r0_5 k := by decide +kernel
lemma column81_1_r0_6_eq : ∀ k : Fin 16, column81_1Expr 0 6 k = column81_1_r0_6 k := by decide +kernel
lemma column81_1_r0_7_eq : ∀ k : Fin 16, column81_1Expr 0 7 k = column81_1_r0_7 k := by decide +kernel
lemma column81_1_r0_8_eq : ∀ k : Fin 16, column81_1Expr 0 8 k = column81_1_r0_8 k := by decide +kernel
lemma column81_1_r0_9_eq : ∀ k : Fin 16, column81_1Expr 0 9 k = column81_1_r0_9 k := by decide +kernel
lemma column81_1_r0_10_eq : ∀ k : Fin 16, column81_1Expr 0 10 k = column81_1_r0_10 k := by decide +kernel
lemma column81_1_r0_11_eq : ∀ k : Fin 16, column81_1Expr 0 11 k = column81_1_r0_11 k := by decide +kernel
lemma column81_1_r0_12_eq : ∀ k : Fin 16, column81_1Expr 0 12 k = column81_1_r0_12 k := by decide +kernel
lemma column81_1_r0_13_eq : ∀ k : Fin 16, column81_1Expr 0 13 k = column81_1_r0_13 k := by decide +kernel
lemma column81_1_r0_14_eq : ∀ k : Fin 16, column81_1Expr 0 14 k = column81_1_r0_14 k := by decide +kernel
lemma column81_1_r0_15_eq : ∀ k : Fin 16, column81_1Expr 0 15 k = column81_1_r0_15 k := by decide +kernel
lemma column81_1_r0_eq (i k : Fin 16) : column81_1Expr 0 i k = column81_1_r0 i k := by
  fin_cases i
  · exact column81_1_r0_0_eq k
  · exact column81_1_r0_1_eq k
  · exact column81_1_r0_2_eq k
  · exact column81_1_r0_3_eq k
  · exact column81_1_r0_4_eq k
  · exact column81_1_r0_5_eq k
  · exact column81_1_r0_6_eq k
  · exact column81_1_r0_7_eq k
  · exact column81_1_r0_8_eq k
  · exact column81_1_r0_9_eq k
  · exact column81_1_r0_10_eq k
  · exact column81_1_r0_11_eq k
  · exact column81_1_r0_12_eq k
  · exact column81_1_r0_13_eq k
  · exact column81_1_r0_14_eq k
  · exact column81_1_r0_15_eq k
lemma column81_1_r1_0_eq : ∀ k : Fin 16, column81_1Expr 1 0 k = column81_1_r1_0 k := by decide +kernel
lemma column81_1_r1_1_eq : ∀ k : Fin 16, column81_1Expr 1 1 k = column81_1_r1_1 k := by decide +kernel
lemma column81_1_r1_2_eq : ∀ k : Fin 16, column81_1Expr 1 2 k = column81_1_r1_2 k := by decide +kernel
lemma column81_1_r1_3_eq : ∀ k : Fin 16, column81_1Expr 1 3 k = column81_1_r1_3 k := by decide +kernel
lemma column81_1_r1_4_eq : ∀ k : Fin 16, column81_1Expr 1 4 k = column81_1_r1_4 k := by decide +kernel
lemma column81_1_r1_5_eq : ∀ k : Fin 16, column81_1Expr 1 5 k = column81_1_r1_5 k := by decide +kernel
lemma column81_1_r1_6_eq : ∀ k : Fin 16, column81_1Expr 1 6 k = column81_1_r1_6 k := by decide +kernel
lemma column81_1_r1_7_eq : ∀ k : Fin 16, column81_1Expr 1 7 k = column81_1_r1_7 k := by decide +kernel
lemma column81_1_r1_8_eq : ∀ k : Fin 16, column81_1Expr 1 8 k = column81_1_r1_8 k := by decide +kernel
lemma column81_1_r1_9_eq : ∀ k : Fin 16, column81_1Expr 1 9 k = column81_1_r1_9 k := by decide +kernel
lemma column81_1_r1_10_eq : ∀ k : Fin 16, column81_1Expr 1 10 k = column81_1_r1_10 k := by decide +kernel
lemma column81_1_r1_11_eq : ∀ k : Fin 16, column81_1Expr 1 11 k = column81_1_r1_11 k := by decide +kernel
lemma column81_1_r1_12_eq : ∀ k : Fin 16, column81_1Expr 1 12 k = column81_1_r1_12 k := by decide +kernel
lemma column81_1_r1_13_eq : ∀ k : Fin 16, column81_1Expr 1 13 k = column81_1_r1_13 k := by decide +kernel
lemma column81_1_r1_14_eq : ∀ k : Fin 16, column81_1Expr 1 14 k = column81_1_r1_14 k := by decide +kernel
lemma column81_1_r1_15_eq : ∀ k : Fin 16, column81_1Expr 1 15 k = column81_1_r1_15 k := by decide +kernel
lemma column81_1_r1_eq (i k : Fin 16) : column81_1Expr 1 i k = column81_1_r1 i k := by
  fin_cases i
  · exact column81_1_r1_0_eq k
  · exact column81_1_r1_1_eq k
  · exact column81_1_r1_2_eq k
  · exact column81_1_r1_3_eq k
  · exact column81_1_r1_4_eq k
  · exact column81_1_r1_5_eq k
  · exact column81_1_r1_6_eq k
  · exact column81_1_r1_7_eq k
  · exact column81_1_r1_8_eq k
  · exact column81_1_r1_9_eq k
  · exact column81_1_r1_10_eq k
  · exact column81_1_r1_11_eq k
  · exact column81_1_r1_12_eq k
  · exact column81_1_r1_13_eq k
  · exact column81_1_r1_14_eq k
  · exact column81_1_r1_15_eq k
lemma column81_1_r2_0_eq : ∀ k : Fin 16, column81_1Expr 2 0 k = column81_1_r2_0 k := by decide +kernel
lemma column81_1_r2_1_eq : ∀ k : Fin 16, column81_1Expr 2 1 k = column81_1_r2_1 k := by decide +kernel
lemma column81_1_r2_2_eq : ∀ k : Fin 16, column81_1Expr 2 2 k = column81_1_r2_2 k := by decide +kernel
lemma column81_1_r2_3_eq : ∀ k : Fin 16, column81_1Expr 2 3 k = column81_1_r2_3 k := by decide +kernel
lemma column81_1_r2_4_eq : ∀ k : Fin 16, column81_1Expr 2 4 k = column81_1_r2_4 k := by decide +kernel
lemma column81_1_r2_5_eq : ∀ k : Fin 16, column81_1Expr 2 5 k = column81_1_r2_5 k := by decide +kernel
lemma column81_1_r2_6_eq : ∀ k : Fin 16, column81_1Expr 2 6 k = column81_1_r2_6 k := by decide +kernel
lemma column81_1_r2_7_eq : ∀ k : Fin 16, column81_1Expr 2 7 k = column81_1_r2_7 k := by decide +kernel
lemma column81_1_r2_8_eq : ∀ k : Fin 16, column81_1Expr 2 8 k = column81_1_r2_8 k := by decide +kernel
lemma column81_1_r2_9_eq : ∀ k : Fin 16, column81_1Expr 2 9 k = column81_1_r2_9 k := by decide +kernel
lemma column81_1_r2_10_eq : ∀ k : Fin 16, column81_1Expr 2 10 k = column81_1_r2_10 k := by decide +kernel
lemma column81_1_r2_11_eq : ∀ k : Fin 16, column81_1Expr 2 11 k = column81_1_r2_11 k := by decide +kernel
lemma column81_1_r2_12_eq : ∀ k : Fin 16, column81_1Expr 2 12 k = column81_1_r2_12 k := by decide +kernel
lemma column81_1_r2_13_eq : ∀ k : Fin 16, column81_1Expr 2 13 k = column81_1_r2_13 k := by decide +kernel
lemma column81_1_r2_14_eq : ∀ k : Fin 16, column81_1Expr 2 14 k = column81_1_r2_14 k := by decide +kernel
lemma column81_1_r2_15_eq : ∀ k : Fin 16, column81_1Expr 2 15 k = column81_1_r2_15 k := by decide +kernel
lemma column81_1_r2_eq (i k : Fin 16) : column81_1Expr 2 i k = column81_1_r2 i k := by
  fin_cases i
  · exact column81_1_r2_0_eq k
  · exact column81_1_r2_1_eq k
  · exact column81_1_r2_2_eq k
  · exact column81_1_r2_3_eq k
  · exact column81_1_r2_4_eq k
  · exact column81_1_r2_5_eq k
  · exact column81_1_r2_6_eq k
  · exact column81_1_r2_7_eq k
  · exact column81_1_r2_8_eq k
  · exact column81_1_r2_9_eq k
  · exact column81_1_r2_10_eq k
  · exact column81_1_r2_11_eq k
  · exact column81_1_r2_12_eq k
  · exact column81_1_r2_13_eq k
  · exact column81_1_r2_14_eq k
  · exact column81_1_r2_15_eq k
lemma column81_1_r3_0_eq : ∀ k : Fin 16, column81_1Expr 3 0 k = column81_1_r3_0 k := by decide +kernel
lemma column81_1_r3_1_eq : ∀ k : Fin 16, column81_1Expr 3 1 k = column81_1_r3_1 k := by decide +kernel
lemma column81_1_r3_2_eq : ∀ k : Fin 16, column81_1Expr 3 2 k = column81_1_r3_2 k := by decide +kernel
lemma column81_1_r3_3_eq : ∀ k : Fin 16, column81_1Expr 3 3 k = column81_1_r3_3 k := by decide +kernel
lemma column81_1_r3_4_eq : ∀ k : Fin 16, column81_1Expr 3 4 k = column81_1_r3_4 k := by decide +kernel
lemma column81_1_r3_5_eq : ∀ k : Fin 16, column81_1Expr 3 5 k = column81_1_r3_5 k := by decide +kernel
lemma column81_1_r3_6_eq : ∀ k : Fin 16, column81_1Expr 3 6 k = column81_1_r3_6 k := by decide +kernel
lemma column81_1_r3_7_eq : ∀ k : Fin 16, column81_1Expr 3 7 k = column81_1_r3_7 k := by decide +kernel
lemma column81_1_r3_8_eq : ∀ k : Fin 16, column81_1Expr 3 8 k = column81_1_r3_8 k := by decide +kernel
lemma column81_1_r3_9_eq : ∀ k : Fin 16, column81_1Expr 3 9 k = column81_1_r3_9 k := by decide +kernel
lemma column81_1_r3_10_eq : ∀ k : Fin 16, column81_1Expr 3 10 k = column81_1_r3_10 k := by decide +kernel
lemma column81_1_r3_11_eq : ∀ k : Fin 16, column81_1Expr 3 11 k = column81_1_r3_11 k := by decide +kernel
lemma column81_1_r3_12_eq : ∀ k : Fin 16, column81_1Expr 3 12 k = column81_1_r3_12 k := by decide +kernel
lemma column81_1_r3_13_eq : ∀ k : Fin 16, column81_1Expr 3 13 k = column81_1_r3_13 k := by decide +kernel
lemma column81_1_r3_14_eq : ∀ k : Fin 16, column81_1Expr 3 14 k = column81_1_r3_14 k := by decide +kernel
lemma column81_1_r3_15_eq : ∀ k : Fin 16, column81_1Expr 3 15 k = column81_1_r3_15 k := by decide +kernel
lemma column81_1_r3_eq (i k : Fin 16) : column81_1Expr 3 i k = column81_1_r3 i k := by
  fin_cases i
  · exact column81_1_r3_0_eq k
  · exact column81_1_r3_1_eq k
  · exact column81_1_r3_2_eq k
  · exact column81_1_r3_3_eq k
  · exact column81_1_r3_4_eq k
  · exact column81_1_r3_5_eq k
  · exact column81_1_r3_6_eq k
  · exact column81_1_r3_7_eq k
  · exact column81_1_r3_8_eq k
  · exact column81_1_r3_9_eq k
  · exact column81_1_r3_10_eq k
  · exact column81_1_r3_11_eq k
  · exact column81_1_r3_12_eq k
  · exact column81_1_r3_13_eq k
  · exact column81_1_r3_14_eq k
  · exact column81_1_r3_15_eq k
lemma column81_1_r4_0_eq : ∀ k : Fin 16, column81_1Expr 4 0 k = column81_1_r4_0 k := by decide +kernel
lemma column81_1_r4_1_eq : ∀ k : Fin 16, column81_1Expr 4 1 k = column81_1_r4_1 k := by decide +kernel
lemma column81_1_r4_2_eq : ∀ k : Fin 16, column81_1Expr 4 2 k = column81_1_r4_2 k := by decide +kernel
lemma column81_1_r4_3_eq : ∀ k : Fin 16, column81_1Expr 4 3 k = column81_1_r4_3 k := by decide +kernel
lemma column81_1_r4_4_eq : ∀ k : Fin 16, column81_1Expr 4 4 k = column81_1_r4_4 k := by decide +kernel
lemma column81_1_r4_5_eq : ∀ k : Fin 16, column81_1Expr 4 5 k = column81_1_r4_5 k := by decide +kernel
lemma column81_1_r4_6_eq : ∀ k : Fin 16, column81_1Expr 4 6 k = column81_1_r4_6 k := by decide +kernel
lemma column81_1_r4_7_eq : ∀ k : Fin 16, column81_1Expr 4 7 k = column81_1_r4_7 k := by decide +kernel
lemma column81_1_r4_8_eq : ∀ k : Fin 16, column81_1Expr 4 8 k = column81_1_r4_8 k := by decide +kernel
lemma column81_1_r4_9_eq : ∀ k : Fin 16, column81_1Expr 4 9 k = column81_1_r4_9 k := by decide +kernel
lemma column81_1_r4_10_eq : ∀ k : Fin 16, column81_1Expr 4 10 k = column81_1_r4_10 k := by decide +kernel
lemma column81_1_r4_11_eq : ∀ k : Fin 16, column81_1Expr 4 11 k = column81_1_r4_11 k := by decide +kernel
lemma column81_1_r4_12_eq : ∀ k : Fin 16, column81_1Expr 4 12 k = column81_1_r4_12 k := by decide +kernel
lemma column81_1_r4_13_eq : ∀ k : Fin 16, column81_1Expr 4 13 k = column81_1_r4_13 k := by decide +kernel
lemma column81_1_r4_14_eq : ∀ k : Fin 16, column81_1Expr 4 14 k = column81_1_r4_14 k := by decide +kernel
lemma column81_1_r4_15_eq : ∀ k : Fin 16, column81_1Expr 4 15 k = column81_1_r4_15 k := by decide +kernel
lemma column81_1_r4_eq (i k : Fin 16) : column81_1Expr 4 i k = column81_1_r4 i k := by
  fin_cases i
  · exact column81_1_r4_0_eq k
  · exact column81_1_r4_1_eq k
  · exact column81_1_r4_2_eq k
  · exact column81_1_r4_3_eq k
  · exact column81_1_r4_4_eq k
  · exact column81_1_r4_5_eq k
  · exact column81_1_r4_6_eq k
  · exact column81_1_r4_7_eq k
  · exact column81_1_r4_8_eq k
  · exact column81_1_r4_9_eq k
  · exact column81_1_r4_10_eq k
  · exact column81_1_r4_11_eq k
  · exact column81_1_r4_12_eq k
  · exact column81_1_r4_13_eq k
  · exact column81_1_r4_14_eq k
  · exact column81_1_r4_15_eq k
lemma column81_1_r5_0_eq : ∀ k : Fin 16, column81_1Expr 5 0 k = column81_1_r5_0 k := by decide +kernel
lemma column81_1_r5_1_eq : ∀ k : Fin 16, column81_1Expr 5 1 k = column81_1_r5_1 k := by decide +kernel
lemma column81_1_r5_2_eq : ∀ k : Fin 16, column81_1Expr 5 2 k = column81_1_r5_2 k := by decide +kernel
lemma column81_1_r5_3_eq : ∀ k : Fin 16, column81_1Expr 5 3 k = column81_1_r5_3 k := by decide +kernel
lemma column81_1_r5_4_eq : ∀ k : Fin 16, column81_1Expr 5 4 k = column81_1_r5_4 k := by decide +kernel
lemma column81_1_r5_5_eq : ∀ k : Fin 16, column81_1Expr 5 5 k = column81_1_r5_5 k := by decide +kernel
lemma column81_1_r5_6_eq : ∀ k : Fin 16, column81_1Expr 5 6 k = column81_1_r5_6 k := by decide +kernel
lemma column81_1_r5_7_eq : ∀ k : Fin 16, column81_1Expr 5 7 k = column81_1_r5_7 k := by decide +kernel
lemma column81_1_r5_8_eq : ∀ k : Fin 16, column81_1Expr 5 8 k = column81_1_r5_8 k := by decide +kernel
lemma column81_1_r5_9_eq : ∀ k : Fin 16, column81_1Expr 5 9 k = column81_1_r5_9 k := by decide +kernel
lemma column81_1_r5_10_eq : ∀ k : Fin 16, column81_1Expr 5 10 k = column81_1_r5_10 k := by decide +kernel
lemma column81_1_r5_11_eq : ∀ k : Fin 16, column81_1Expr 5 11 k = column81_1_r5_11 k := by decide +kernel
lemma column81_1_r5_12_eq : ∀ k : Fin 16, column81_1Expr 5 12 k = column81_1_r5_12 k := by decide +kernel
lemma column81_1_r5_13_eq : ∀ k : Fin 16, column81_1Expr 5 13 k = column81_1_r5_13 k := by decide +kernel
lemma column81_1_r5_14_eq : ∀ k : Fin 16, column81_1Expr 5 14 k = column81_1_r5_14 k := by decide +kernel
lemma column81_1_r5_15_eq : ∀ k : Fin 16, column81_1Expr 5 15 k = column81_1_r5_15 k := by decide +kernel
lemma column81_1_r5_eq (i k : Fin 16) : column81_1Expr 5 i k = column81_1_r5 i k := by
  fin_cases i
  · exact column81_1_r5_0_eq k
  · exact column81_1_r5_1_eq k
  · exact column81_1_r5_2_eq k
  · exact column81_1_r5_3_eq k
  · exact column81_1_r5_4_eq k
  · exact column81_1_r5_5_eq k
  · exact column81_1_r5_6_eq k
  · exact column81_1_r5_7_eq k
  · exact column81_1_r5_8_eq k
  · exact column81_1_r5_9_eq k
  · exact column81_1_r5_10_eq k
  · exact column81_1_r5_11_eq k
  · exact column81_1_r5_12_eq k
  · exact column81_1_r5_13_eq k
  · exact column81_1_r5_14_eq k
  · exact column81_1_r5_15_eq k
lemma column81_1_eq (j : Fin 6) (i k : Fin 16) : column81_1Expr j i k = column81_1 j i k := by
  fin_cases j
  · exact column81_1_r0_eq i k
  · exact column81_1_r1_eq i k
  · exact column81_1_r2_eq i k
  · exact column81_1_r3_eq i k
  · exact column81_1_r4_eq i k
  · exact column81_1_r5_eq i k
noncomputable def column84_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power84 j i k)
lemma column84_0_r0_0_eq : ∀ k : Fin 16, column84_0Expr 0 0 k = column84_0_r0_0 k := by decide +kernel
lemma column84_0_r0_1_eq : ∀ k : Fin 16, column84_0Expr 0 1 k = column84_0_r0_1 k := by decide +kernel
lemma column84_0_r0_2_eq : ∀ k : Fin 16, column84_0Expr 0 2 k = column84_0_r0_2 k := by decide +kernel
lemma column84_0_r0_3_eq : ∀ k : Fin 16, column84_0Expr 0 3 k = column84_0_r0_3 k := by decide +kernel
lemma column84_0_r0_4_eq : ∀ k : Fin 16, column84_0Expr 0 4 k = column84_0_r0_4 k := by decide +kernel
lemma column84_0_r0_5_eq : ∀ k : Fin 16, column84_0Expr 0 5 k = column84_0_r0_5 k := by decide +kernel
lemma column84_0_r0_6_eq : ∀ k : Fin 16, column84_0Expr 0 6 k = column84_0_r0_6 k := by decide +kernel
lemma column84_0_r0_7_eq : ∀ k : Fin 16, column84_0Expr 0 7 k = column84_0_r0_7 k := by decide +kernel
lemma column84_0_r0_8_eq : ∀ k : Fin 16, column84_0Expr 0 8 k = column84_0_r0_8 k := by decide +kernel
lemma column84_0_r0_9_eq : ∀ k : Fin 16, column84_0Expr 0 9 k = column84_0_r0_9 k := by decide +kernel
lemma column84_0_r0_10_eq : ∀ k : Fin 16, column84_0Expr 0 10 k = column84_0_r0_10 k := by decide +kernel
lemma column84_0_r0_11_eq : ∀ k : Fin 16, column84_0Expr 0 11 k = column84_0_r0_11 k := by decide +kernel
lemma column84_0_r0_12_eq : ∀ k : Fin 16, column84_0Expr 0 12 k = column84_0_r0_12 k := by decide +kernel
lemma column84_0_r0_13_eq : ∀ k : Fin 16, column84_0Expr 0 13 k = column84_0_r0_13 k := by decide +kernel
lemma column84_0_r0_14_eq : ∀ k : Fin 16, column84_0Expr 0 14 k = column84_0_r0_14 k := by decide +kernel
lemma column84_0_r0_15_eq : ∀ k : Fin 16, column84_0Expr 0 15 k = column84_0_r0_15 k := by decide +kernel
lemma column84_0_r0_eq (i k : Fin 16) : column84_0Expr 0 i k = column84_0_r0 i k := by
  fin_cases i
  · exact column84_0_r0_0_eq k
  · exact column84_0_r0_1_eq k
  · exact column84_0_r0_2_eq k
  · exact column84_0_r0_3_eq k
  · exact column84_0_r0_4_eq k
  · exact column84_0_r0_5_eq k
  · exact column84_0_r0_6_eq k
  · exact column84_0_r0_7_eq k
  · exact column84_0_r0_8_eq k
  · exact column84_0_r0_9_eq k
  · exact column84_0_r0_10_eq k
  · exact column84_0_r0_11_eq k
  · exact column84_0_r0_12_eq k
  · exact column84_0_r0_13_eq k
  · exact column84_0_r0_14_eq k
  · exact column84_0_r0_15_eq k
lemma column84_0_r1_0_eq : ∀ k : Fin 16, column84_0Expr 1 0 k = column84_0_r1_0 k := by decide +kernel
lemma column84_0_r1_1_eq : ∀ k : Fin 16, column84_0Expr 1 1 k = column84_0_r1_1 k := by decide +kernel
lemma column84_0_r1_2_eq : ∀ k : Fin 16, column84_0Expr 1 2 k = column84_0_r1_2 k := by decide +kernel
lemma column84_0_r1_3_eq : ∀ k : Fin 16, column84_0Expr 1 3 k = column84_0_r1_3 k := by decide +kernel
lemma column84_0_r1_4_eq : ∀ k : Fin 16, column84_0Expr 1 4 k = column84_0_r1_4 k := by decide +kernel
lemma column84_0_r1_5_eq : ∀ k : Fin 16, column84_0Expr 1 5 k = column84_0_r1_5 k := by decide +kernel
lemma column84_0_r1_6_eq : ∀ k : Fin 16, column84_0Expr 1 6 k = column84_0_r1_6 k := by decide +kernel
lemma column84_0_r1_7_eq : ∀ k : Fin 16, column84_0Expr 1 7 k = column84_0_r1_7 k := by decide +kernel
lemma column84_0_r1_8_eq : ∀ k : Fin 16, column84_0Expr 1 8 k = column84_0_r1_8 k := by decide +kernel
lemma column84_0_r1_9_eq : ∀ k : Fin 16, column84_0Expr 1 9 k = column84_0_r1_9 k := by decide +kernel
lemma column84_0_r1_10_eq : ∀ k : Fin 16, column84_0Expr 1 10 k = column84_0_r1_10 k := by decide +kernel
lemma column84_0_r1_11_eq : ∀ k : Fin 16, column84_0Expr 1 11 k = column84_0_r1_11 k := by decide +kernel
lemma column84_0_r1_12_eq : ∀ k : Fin 16, column84_0Expr 1 12 k = column84_0_r1_12 k := by decide +kernel
lemma column84_0_r1_13_eq : ∀ k : Fin 16, column84_0Expr 1 13 k = column84_0_r1_13 k := by decide +kernel
lemma column84_0_r1_14_eq : ∀ k : Fin 16, column84_0Expr 1 14 k = column84_0_r1_14 k := by decide +kernel
lemma column84_0_r1_15_eq : ∀ k : Fin 16, column84_0Expr 1 15 k = column84_0_r1_15 k := by decide +kernel
lemma column84_0_r1_eq (i k : Fin 16) : column84_0Expr 1 i k = column84_0_r1 i k := by
  fin_cases i
  · exact column84_0_r1_0_eq k
  · exact column84_0_r1_1_eq k
  · exact column84_0_r1_2_eq k
  · exact column84_0_r1_3_eq k
  · exact column84_0_r1_4_eq k
  · exact column84_0_r1_5_eq k
  · exact column84_0_r1_6_eq k
  · exact column84_0_r1_7_eq k
  · exact column84_0_r1_8_eq k
  · exact column84_0_r1_9_eq k
  · exact column84_0_r1_10_eq k
  · exact column84_0_r1_11_eq k
  · exact column84_0_r1_12_eq k
  · exact column84_0_r1_13_eq k
  · exact column84_0_r1_14_eq k
  · exact column84_0_r1_15_eq k
lemma column84_0_r2_0_eq : ∀ k : Fin 16, column84_0Expr 2 0 k = column84_0_r2_0 k := by decide +kernel
lemma column84_0_r2_1_eq : ∀ k : Fin 16, column84_0Expr 2 1 k = column84_0_r2_1 k := by decide +kernel
lemma column84_0_r2_2_eq : ∀ k : Fin 16, column84_0Expr 2 2 k = column84_0_r2_2 k := by decide +kernel
lemma column84_0_r2_3_eq : ∀ k : Fin 16, column84_0Expr 2 3 k = column84_0_r2_3 k := by decide +kernel
lemma column84_0_r2_4_eq : ∀ k : Fin 16, column84_0Expr 2 4 k = column84_0_r2_4 k := by decide +kernel
lemma column84_0_r2_5_eq : ∀ k : Fin 16, column84_0Expr 2 5 k = column84_0_r2_5 k := by decide +kernel
lemma column84_0_r2_6_eq : ∀ k : Fin 16, column84_0Expr 2 6 k = column84_0_r2_6 k := by decide +kernel
lemma column84_0_r2_7_eq : ∀ k : Fin 16, column84_0Expr 2 7 k = column84_0_r2_7 k := by decide +kernel
lemma column84_0_r2_8_eq : ∀ k : Fin 16, column84_0Expr 2 8 k = column84_0_r2_8 k := by decide +kernel
lemma column84_0_r2_9_eq : ∀ k : Fin 16, column84_0Expr 2 9 k = column84_0_r2_9 k := by decide +kernel
lemma column84_0_r2_10_eq : ∀ k : Fin 16, column84_0Expr 2 10 k = column84_0_r2_10 k := by decide +kernel
lemma column84_0_r2_11_eq : ∀ k : Fin 16, column84_0Expr 2 11 k = column84_0_r2_11 k := by decide +kernel
lemma column84_0_r2_12_eq : ∀ k : Fin 16, column84_0Expr 2 12 k = column84_0_r2_12 k := by decide +kernel
lemma column84_0_r2_13_eq : ∀ k : Fin 16, column84_0Expr 2 13 k = column84_0_r2_13 k := by decide +kernel
lemma column84_0_r2_14_eq : ∀ k : Fin 16, column84_0Expr 2 14 k = column84_0_r2_14 k := by decide +kernel
lemma column84_0_r2_15_eq : ∀ k : Fin 16, column84_0Expr 2 15 k = column84_0_r2_15 k := by decide +kernel
lemma column84_0_r2_eq (i k : Fin 16) : column84_0Expr 2 i k = column84_0_r2 i k := by
  fin_cases i
  · exact column84_0_r2_0_eq k
  · exact column84_0_r2_1_eq k
  · exact column84_0_r2_2_eq k
  · exact column84_0_r2_3_eq k
  · exact column84_0_r2_4_eq k
  · exact column84_0_r2_5_eq k
  · exact column84_0_r2_6_eq k
  · exact column84_0_r2_7_eq k
  · exact column84_0_r2_8_eq k
  · exact column84_0_r2_9_eq k
  · exact column84_0_r2_10_eq k
  · exact column84_0_r2_11_eq k
  · exact column84_0_r2_12_eq k
  · exact column84_0_r2_13_eq k
  · exact column84_0_r2_14_eq k
  · exact column84_0_r2_15_eq k
lemma column84_0_r3_0_eq : ∀ k : Fin 16, column84_0Expr 3 0 k = column84_0_r3_0 k := by decide +kernel
lemma column84_0_r3_1_eq : ∀ k : Fin 16, column84_0Expr 3 1 k = column84_0_r3_1 k := by decide +kernel
lemma column84_0_r3_2_eq : ∀ k : Fin 16, column84_0Expr 3 2 k = column84_0_r3_2 k := by decide +kernel
lemma column84_0_r3_3_eq : ∀ k : Fin 16, column84_0Expr 3 3 k = column84_0_r3_3 k := by decide +kernel
lemma column84_0_r3_4_eq : ∀ k : Fin 16, column84_0Expr 3 4 k = column84_0_r3_4 k := by decide +kernel
lemma column84_0_r3_5_eq : ∀ k : Fin 16, column84_0Expr 3 5 k = column84_0_r3_5 k := by decide +kernel
lemma column84_0_r3_6_eq : ∀ k : Fin 16, column84_0Expr 3 6 k = column84_0_r3_6 k := by decide +kernel
lemma column84_0_r3_7_eq : ∀ k : Fin 16, column84_0Expr 3 7 k = column84_0_r3_7 k := by decide +kernel
lemma column84_0_r3_8_eq : ∀ k : Fin 16, column84_0Expr 3 8 k = column84_0_r3_8 k := by decide +kernel
lemma column84_0_r3_9_eq : ∀ k : Fin 16, column84_0Expr 3 9 k = column84_0_r3_9 k := by decide +kernel
lemma column84_0_r3_10_eq : ∀ k : Fin 16, column84_0Expr 3 10 k = column84_0_r3_10 k := by decide +kernel
lemma column84_0_r3_11_eq : ∀ k : Fin 16, column84_0Expr 3 11 k = column84_0_r3_11 k := by decide +kernel
lemma column84_0_r3_12_eq : ∀ k : Fin 16, column84_0Expr 3 12 k = column84_0_r3_12 k := by decide +kernel
lemma column84_0_r3_13_eq : ∀ k : Fin 16, column84_0Expr 3 13 k = column84_0_r3_13 k := by decide +kernel
lemma column84_0_r3_14_eq : ∀ k : Fin 16, column84_0Expr 3 14 k = column84_0_r3_14 k := by decide +kernel
lemma column84_0_r3_15_eq : ∀ k : Fin 16, column84_0Expr 3 15 k = column84_0_r3_15 k := by decide +kernel
lemma column84_0_r3_eq (i k : Fin 16) : column84_0Expr 3 i k = column84_0_r3 i k := by
  fin_cases i
  · exact column84_0_r3_0_eq k
  · exact column84_0_r3_1_eq k
  · exact column84_0_r3_2_eq k
  · exact column84_0_r3_3_eq k
  · exact column84_0_r3_4_eq k
  · exact column84_0_r3_5_eq k
  · exact column84_0_r3_6_eq k
  · exact column84_0_r3_7_eq k
  · exact column84_0_r3_8_eq k
  · exact column84_0_r3_9_eq k
  · exact column84_0_r3_10_eq k
  · exact column84_0_r3_11_eq k
  · exact column84_0_r3_12_eq k
  · exact column84_0_r3_13_eq k
  · exact column84_0_r3_14_eq k
  · exact column84_0_r3_15_eq k
lemma column84_0_r4_0_eq : ∀ k : Fin 16, column84_0Expr 4 0 k = column84_0_r4_0 k := by decide +kernel
lemma column84_0_r4_1_eq : ∀ k : Fin 16, column84_0Expr 4 1 k = column84_0_r4_1 k := by decide +kernel
lemma column84_0_r4_2_eq : ∀ k : Fin 16, column84_0Expr 4 2 k = column84_0_r4_2 k := by decide +kernel
lemma column84_0_r4_3_eq : ∀ k : Fin 16, column84_0Expr 4 3 k = column84_0_r4_3 k := by decide +kernel
lemma column84_0_r4_4_eq : ∀ k : Fin 16, column84_0Expr 4 4 k = column84_0_r4_4 k := by decide +kernel
lemma column84_0_r4_5_eq : ∀ k : Fin 16, column84_0Expr 4 5 k = column84_0_r4_5 k := by decide +kernel
lemma column84_0_r4_6_eq : ∀ k : Fin 16, column84_0Expr 4 6 k = column84_0_r4_6 k := by decide +kernel
lemma column84_0_r4_7_eq : ∀ k : Fin 16, column84_0Expr 4 7 k = column84_0_r4_7 k := by decide +kernel
lemma column84_0_r4_8_eq : ∀ k : Fin 16, column84_0Expr 4 8 k = column84_0_r4_8 k := by decide +kernel
lemma column84_0_r4_9_eq : ∀ k : Fin 16, column84_0Expr 4 9 k = column84_0_r4_9 k := by decide +kernel
lemma column84_0_r4_10_eq : ∀ k : Fin 16, column84_0Expr 4 10 k = column84_0_r4_10 k := by decide +kernel
lemma column84_0_r4_11_eq : ∀ k : Fin 16, column84_0Expr 4 11 k = column84_0_r4_11 k := by decide +kernel
lemma column84_0_r4_12_eq : ∀ k : Fin 16, column84_0Expr 4 12 k = column84_0_r4_12 k := by decide +kernel
lemma column84_0_r4_13_eq : ∀ k : Fin 16, column84_0Expr 4 13 k = column84_0_r4_13 k := by decide +kernel
lemma column84_0_r4_14_eq : ∀ k : Fin 16, column84_0Expr 4 14 k = column84_0_r4_14 k := by decide +kernel
lemma column84_0_r4_15_eq : ∀ k : Fin 16, column84_0Expr 4 15 k = column84_0_r4_15 k := by decide +kernel
lemma column84_0_r4_eq (i k : Fin 16) : column84_0Expr 4 i k = column84_0_r4 i k := by
  fin_cases i
  · exact column84_0_r4_0_eq k
  · exact column84_0_r4_1_eq k
  · exact column84_0_r4_2_eq k
  · exact column84_0_r4_3_eq k
  · exact column84_0_r4_4_eq k
  · exact column84_0_r4_5_eq k
  · exact column84_0_r4_6_eq k
  · exact column84_0_r4_7_eq k
  · exact column84_0_r4_8_eq k
  · exact column84_0_r4_9_eq k
  · exact column84_0_r4_10_eq k
  · exact column84_0_r4_11_eq k
  · exact column84_0_r4_12_eq k
  · exact column84_0_r4_13_eq k
  · exact column84_0_r4_14_eq k
  · exact column84_0_r4_15_eq k
lemma column84_0_r5_0_eq : ∀ k : Fin 16, column84_0Expr 5 0 k = column84_0_r5_0 k := by decide +kernel
lemma column84_0_r5_1_eq : ∀ k : Fin 16, column84_0Expr 5 1 k = column84_0_r5_1 k := by decide +kernel
lemma column84_0_r5_2_eq : ∀ k : Fin 16, column84_0Expr 5 2 k = column84_0_r5_2 k := by decide +kernel
lemma column84_0_r5_3_eq : ∀ k : Fin 16, column84_0Expr 5 3 k = column84_0_r5_3 k := by decide +kernel
lemma column84_0_r5_4_eq : ∀ k : Fin 16, column84_0Expr 5 4 k = column84_0_r5_4 k := by decide +kernel
lemma column84_0_r5_5_eq : ∀ k : Fin 16, column84_0Expr 5 5 k = column84_0_r5_5 k := by decide +kernel
lemma column84_0_r5_6_eq : ∀ k : Fin 16, column84_0Expr 5 6 k = column84_0_r5_6 k := by decide +kernel
lemma column84_0_r5_7_eq : ∀ k : Fin 16, column84_0Expr 5 7 k = column84_0_r5_7 k := by decide +kernel
lemma column84_0_r5_8_eq : ∀ k : Fin 16, column84_0Expr 5 8 k = column84_0_r5_8 k := by decide +kernel
lemma column84_0_r5_9_eq : ∀ k : Fin 16, column84_0Expr 5 9 k = column84_0_r5_9 k := by decide +kernel
lemma column84_0_r5_10_eq : ∀ k : Fin 16, column84_0Expr 5 10 k = column84_0_r5_10 k := by decide +kernel
lemma column84_0_r5_11_eq : ∀ k : Fin 16, column84_0Expr 5 11 k = column84_0_r5_11 k := by decide +kernel
lemma column84_0_r5_12_eq : ∀ k : Fin 16, column84_0Expr 5 12 k = column84_0_r5_12 k := by decide +kernel
lemma column84_0_r5_13_eq : ∀ k : Fin 16, column84_0Expr 5 13 k = column84_0_r5_13 k := by decide +kernel
lemma column84_0_r5_14_eq : ∀ k : Fin 16, column84_0Expr 5 14 k = column84_0_r5_14 k := by decide +kernel
lemma column84_0_r5_15_eq : ∀ k : Fin 16, column84_0Expr 5 15 k = column84_0_r5_15 k := by decide +kernel
noncomputable def column84_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power84 j i k)
lemma column84_1_r0_0_eq : ∀ k : Fin 16, column84_1Expr 0 0 k = column84_1_r0_0 k := by decide +kernel
lemma column84_1_r0_1_eq : ∀ k : Fin 16, column84_1Expr 0 1 k = column84_1_r0_1 k := by decide +kernel
lemma column84_1_r0_2_eq : ∀ k : Fin 16, column84_1Expr 0 2 k = column84_1_r0_2 k := by decide +kernel
lemma column84_1_r0_3_eq : ∀ k : Fin 16, column84_1Expr 0 3 k = column84_1_r0_3 k := by decide +kernel
lemma column84_1_r0_4_eq : ∀ k : Fin 16, column84_1Expr 0 4 k = column84_1_r0_4 k := by decide +kernel
lemma column84_1_r0_5_eq : ∀ k : Fin 16, column84_1Expr 0 5 k = column84_1_r0_5 k := by decide +kernel
lemma column84_1_r0_6_eq : ∀ k : Fin 16, column84_1Expr 0 6 k = column84_1_r0_6 k := by decide +kernel
lemma column84_1_r0_7_eq : ∀ k : Fin 16, column84_1Expr 0 7 k = column84_1_r0_7 k := by decide +kernel
lemma column84_1_r0_8_eq : ∀ k : Fin 16, column84_1Expr 0 8 k = column84_1_r0_8 k := by decide +kernel
lemma column84_1_r0_9_eq : ∀ k : Fin 16, column84_1Expr 0 9 k = column84_1_r0_9 k := by decide +kernel
lemma column84_1_r0_10_eq : ∀ k : Fin 16, column84_1Expr 0 10 k = column84_1_r0_10 k := by decide +kernel
lemma column84_1_r0_11_eq : ∀ k : Fin 16, column84_1Expr 0 11 k = column84_1_r0_11 k := by decide +kernel
lemma column84_1_r0_12_eq : ∀ k : Fin 16, column84_1Expr 0 12 k = column84_1_r0_12 k := by decide +kernel
lemma column84_1_r0_13_eq : ∀ k : Fin 16, column84_1Expr 0 13 k = column84_1_r0_13 k := by decide +kernel
lemma column84_1_r0_14_eq : ∀ k : Fin 16, column84_1Expr 0 14 k = column84_1_r0_14 k := by decide +kernel
lemma column84_1_r0_15_eq : ∀ k : Fin 16, column84_1Expr 0 15 k = column84_1_r0_15 k := by decide +kernel
lemma column84_1_r0_eq (i k : Fin 16) : column84_1Expr 0 i k = column84_1_r0 i k := by
  fin_cases i
  · exact column84_1_r0_0_eq k
  · exact column84_1_r0_1_eq k
  · exact column84_1_r0_2_eq k
  · exact column84_1_r0_3_eq k
  · exact column84_1_r0_4_eq k
  · exact column84_1_r0_5_eq k
  · exact column84_1_r0_6_eq k
  · exact column84_1_r0_7_eq k
  · exact column84_1_r0_8_eq k
  · exact column84_1_r0_9_eq k
  · exact column84_1_r0_10_eq k
  · exact column84_1_r0_11_eq k
  · exact column84_1_r0_12_eq k
  · exact column84_1_r0_13_eq k
  · exact column84_1_r0_14_eq k
  · exact column84_1_r0_15_eq k
lemma column84_1_r1_0_eq : ∀ k : Fin 16, column84_1Expr 1 0 k = column84_1_r1_0 k := by decide +kernel
lemma column84_1_r1_1_eq : ∀ k : Fin 16, column84_1Expr 1 1 k = column84_1_r1_1 k := by decide +kernel
lemma column84_1_r1_2_eq : ∀ k : Fin 16, column84_1Expr 1 2 k = column84_1_r1_2 k := by decide +kernel
lemma column84_1_r1_3_eq : ∀ k : Fin 16, column84_1Expr 1 3 k = column84_1_r1_3 k := by decide +kernel
lemma column84_1_r1_4_eq : ∀ k : Fin 16, column84_1Expr 1 4 k = column84_1_r1_4 k := by decide +kernel
lemma column84_1_r1_5_eq : ∀ k : Fin 16, column84_1Expr 1 5 k = column84_1_r1_5 k := by decide +kernel
lemma column84_1_r1_6_eq : ∀ k : Fin 16, column84_1Expr 1 6 k = column84_1_r1_6 k := by decide +kernel
lemma column84_1_r1_7_eq : ∀ k : Fin 16, column84_1Expr 1 7 k = column84_1_r1_7 k := by decide +kernel
lemma column84_1_r1_8_eq : ∀ k : Fin 16, column84_1Expr 1 8 k = column84_1_r1_8 k := by decide +kernel
lemma column84_1_r1_9_eq : ∀ k : Fin 16, column84_1Expr 1 9 k = column84_1_r1_9 k := by decide +kernel
lemma column84_1_r1_10_eq : ∀ k : Fin 16, column84_1Expr 1 10 k = column84_1_r1_10 k := by decide +kernel
lemma column84_1_r1_11_eq : ∀ k : Fin 16, column84_1Expr 1 11 k = column84_1_r1_11 k := by decide +kernel
lemma column84_1_r1_12_eq : ∀ k : Fin 16, column84_1Expr 1 12 k = column84_1_r1_12 k := by decide +kernel
lemma column84_1_r1_13_eq : ∀ k : Fin 16, column84_1Expr 1 13 k = column84_1_r1_13 k := by decide +kernel
lemma column84_1_r1_14_eq : ∀ k : Fin 16, column84_1Expr 1 14 k = column84_1_r1_14 k := by decide +kernel
lemma column84_1_r1_15_eq : ∀ k : Fin 16, column84_1Expr 1 15 k = column84_1_r1_15 k := by decide +kernel
lemma column84_1_r1_eq (i k : Fin 16) : column84_1Expr 1 i k = column84_1_r1 i k := by
  fin_cases i
  · exact column84_1_r1_0_eq k
  · exact column84_1_r1_1_eq k
  · exact column84_1_r1_2_eq k
  · exact column84_1_r1_3_eq k
  · exact column84_1_r1_4_eq k
  · exact column84_1_r1_5_eq k
  · exact column84_1_r1_6_eq k
  · exact column84_1_r1_7_eq k
  · exact column84_1_r1_8_eq k
  · exact column84_1_r1_9_eq k
  · exact column84_1_r1_10_eq k
  · exact column84_1_r1_11_eq k
  · exact column84_1_r1_12_eq k
  · exact column84_1_r1_13_eq k
  · exact column84_1_r1_14_eq k
  · exact column84_1_r1_15_eq k
lemma column84_1_r2_0_eq : ∀ k : Fin 16, column84_1Expr 2 0 k = column84_1_r2_0 k := by decide +kernel
lemma column84_1_r2_1_eq : ∀ k : Fin 16, column84_1Expr 2 1 k = column84_1_r2_1 k := by decide +kernel
lemma column84_1_r2_2_eq : ∀ k : Fin 16, column84_1Expr 2 2 k = column84_1_r2_2 k := by decide +kernel
lemma column84_1_r2_3_eq : ∀ k : Fin 16, column84_1Expr 2 3 k = column84_1_r2_3 k := by decide +kernel
lemma column84_1_r2_4_eq : ∀ k : Fin 16, column84_1Expr 2 4 k = column84_1_r2_4 k := by decide +kernel
lemma column84_1_r2_5_eq : ∀ k : Fin 16, column84_1Expr 2 5 k = column84_1_r2_5 k := by decide +kernel
lemma column84_1_r2_6_eq : ∀ k : Fin 16, column84_1Expr 2 6 k = column84_1_r2_6 k := by decide +kernel
lemma column84_1_r2_7_eq : ∀ k : Fin 16, column84_1Expr 2 7 k = column84_1_r2_7 k := by decide +kernel
lemma column84_1_r2_8_eq : ∀ k : Fin 16, column84_1Expr 2 8 k = column84_1_r2_8 k := by decide +kernel
lemma column84_1_r2_9_eq : ∀ k : Fin 16, column84_1Expr 2 9 k = column84_1_r2_9 k := by decide +kernel
lemma column84_1_r2_10_eq : ∀ k : Fin 16, column84_1Expr 2 10 k = column84_1_r2_10 k := by decide +kernel
lemma column84_1_r2_11_eq : ∀ k : Fin 16, column84_1Expr 2 11 k = column84_1_r2_11 k := by decide +kernel
lemma column84_1_r2_12_eq : ∀ k : Fin 16, column84_1Expr 2 12 k = column84_1_r2_12 k := by decide +kernel
lemma column84_1_r2_13_eq : ∀ k : Fin 16, column84_1Expr 2 13 k = column84_1_r2_13 k := by decide +kernel
lemma column84_1_r2_14_eq : ∀ k : Fin 16, column84_1Expr 2 14 k = column84_1_r2_14 k := by decide +kernel
lemma column84_1_r2_15_eq : ∀ k : Fin 16, column84_1Expr 2 15 k = column84_1_r2_15 k := by decide +kernel
lemma column84_1_r2_eq (i k : Fin 16) : column84_1Expr 2 i k = column84_1_r2 i k := by
  fin_cases i
  · exact column84_1_r2_0_eq k
  · exact column84_1_r2_1_eq k
  · exact column84_1_r2_2_eq k
  · exact column84_1_r2_3_eq k
  · exact column84_1_r2_4_eq k
  · exact column84_1_r2_5_eq k
  · exact column84_1_r2_6_eq k
  · exact column84_1_r2_7_eq k
  · exact column84_1_r2_8_eq k
  · exact column84_1_r2_9_eq k
  · exact column84_1_r2_10_eq k
  · exact column84_1_r2_11_eq k
  · exact column84_1_r2_12_eq k
  · exact column84_1_r2_13_eq k
  · exact column84_1_r2_14_eq k
  · exact column84_1_r2_15_eq k
lemma column84_1_r3_0_eq : ∀ k : Fin 16, column84_1Expr 3 0 k = column84_1_r3_0 k := by decide +kernel
lemma column84_1_r3_1_eq : ∀ k : Fin 16, column84_1Expr 3 1 k = column84_1_r3_1 k := by decide +kernel
lemma column84_1_r3_2_eq : ∀ k : Fin 16, column84_1Expr 3 2 k = column84_1_r3_2 k := by decide +kernel
lemma column84_1_r3_3_eq : ∀ k : Fin 16, column84_1Expr 3 3 k = column84_1_r3_3 k := by decide +kernel
lemma column84_1_r3_4_eq : ∀ k : Fin 16, column84_1Expr 3 4 k = column84_1_r3_4 k := by decide +kernel
lemma column84_1_r3_5_eq : ∀ k : Fin 16, column84_1Expr 3 5 k = column84_1_r3_5 k := by decide +kernel
lemma column84_1_r3_6_eq : ∀ k : Fin 16, column84_1Expr 3 6 k = column84_1_r3_6 k := by decide +kernel
lemma column84_1_r3_7_eq : ∀ k : Fin 16, column84_1Expr 3 7 k = column84_1_r3_7 k := by decide +kernel
lemma column84_1_r3_8_eq : ∀ k : Fin 16, column84_1Expr 3 8 k = column84_1_r3_8 k := by decide +kernel
lemma column84_1_r3_9_eq : ∀ k : Fin 16, column84_1Expr 3 9 k = column84_1_r3_9 k := by decide +kernel
lemma column84_1_r3_10_eq : ∀ k : Fin 16, column84_1Expr 3 10 k = column84_1_r3_10 k := by decide +kernel
lemma column84_1_r3_11_eq : ∀ k : Fin 16, column84_1Expr 3 11 k = column84_1_r3_11 k := by decide +kernel
lemma column84_1_r3_12_eq : ∀ k : Fin 16, column84_1Expr 3 12 k = column84_1_r3_12 k := by decide +kernel
lemma column84_1_r3_13_eq : ∀ k : Fin 16, column84_1Expr 3 13 k = column84_1_r3_13 k := by decide +kernel
lemma column84_1_r3_14_eq : ∀ k : Fin 16, column84_1Expr 3 14 k = column84_1_r3_14 k := by decide +kernel
lemma column84_1_r3_15_eq : ∀ k : Fin 16, column84_1Expr 3 15 k = column84_1_r3_15 k := by decide +kernel
lemma column84_1_r3_eq (i k : Fin 16) : column84_1Expr 3 i k = column84_1_r3 i k := by
  fin_cases i
  · exact column84_1_r3_0_eq k
  · exact column84_1_r3_1_eq k
  · exact column84_1_r3_2_eq k
  · exact column84_1_r3_3_eq k
  · exact column84_1_r3_4_eq k
  · exact column84_1_r3_5_eq k
  · exact column84_1_r3_6_eq k
  · exact column84_1_r3_7_eq k
  · exact column84_1_r3_8_eq k
  · exact column84_1_r3_9_eq k
  · exact column84_1_r3_10_eq k
  · exact column84_1_r3_11_eq k
  · exact column84_1_r3_12_eq k
  · exact column84_1_r3_13_eq k
  · exact column84_1_r3_14_eq k
  · exact column84_1_r3_15_eq k
lemma column84_1_r4_0_eq : ∀ k : Fin 16, column84_1Expr 4 0 k = column84_1_r4_0 k := by decide +kernel
lemma column84_1_r4_1_eq : ∀ k : Fin 16, column84_1Expr 4 1 k = column84_1_r4_1 k := by decide +kernel
lemma column84_1_r4_2_eq : ∀ k : Fin 16, column84_1Expr 4 2 k = column84_1_r4_2 k := by decide +kernel
lemma column84_1_r4_3_eq : ∀ k : Fin 16, column84_1Expr 4 3 k = column84_1_r4_3 k := by decide +kernel
lemma column84_1_r4_4_eq : ∀ k : Fin 16, column84_1Expr 4 4 k = column84_1_r4_4 k := by decide +kernel
lemma column84_1_r4_5_eq : ∀ k : Fin 16, column84_1Expr 4 5 k = column84_1_r4_5 k := by decide +kernel
lemma column84_1_r4_6_eq : ∀ k : Fin 16, column84_1Expr 4 6 k = column84_1_r4_6 k := by decide +kernel
lemma column84_1_r4_7_eq : ∀ k : Fin 16, column84_1Expr 4 7 k = column84_1_r4_7 k := by decide +kernel
lemma column84_1_r4_8_eq : ∀ k : Fin 16, column84_1Expr 4 8 k = column84_1_r4_8 k := by decide +kernel
lemma column84_1_r4_9_eq : ∀ k : Fin 16, column84_1Expr 4 9 k = column84_1_r4_9 k := by decide +kernel
lemma column84_1_r4_10_eq : ∀ k : Fin 16, column84_1Expr 4 10 k = column84_1_r4_10 k := by decide +kernel
lemma column84_1_r4_11_eq : ∀ k : Fin 16, column84_1Expr 4 11 k = column84_1_r4_11 k := by decide +kernel
lemma column84_1_r4_12_eq : ∀ k : Fin 16, column84_1Expr 4 12 k = column84_1_r4_12 k := by decide +kernel
lemma column84_1_r4_13_eq : ∀ k : Fin 16, column84_1Expr 4 13 k = column84_1_r4_13 k := by decide +kernel
lemma column84_1_r4_14_eq : ∀ k : Fin 16, column84_1Expr 4 14 k = column84_1_r4_14 k := by decide +kernel
lemma column84_1_r4_15_eq : ∀ k : Fin 16, column84_1Expr 4 15 k = column84_1_r4_15 k := by decide +kernel
lemma column84_1_r4_eq (i k : Fin 16) : column84_1Expr 4 i k = column84_1_r4 i k := by
  fin_cases i
  · exact column84_1_r4_0_eq k
  · exact column84_1_r4_1_eq k
  · exact column84_1_r4_2_eq k
  · exact column84_1_r4_3_eq k
  · exact column84_1_r4_4_eq k
  · exact column84_1_r4_5_eq k
  · exact column84_1_r4_6_eq k
  · exact column84_1_r4_7_eq k
  · exact column84_1_r4_8_eq k
  · exact column84_1_r4_9_eq k
  · exact column84_1_r4_10_eq k
  · exact column84_1_r4_11_eq k
  · exact column84_1_r4_12_eq k
  · exact column84_1_r4_13_eq k
  · exact column84_1_r4_14_eq k
  · exact column84_1_r4_15_eq k
lemma column84_1_r5_0_eq : ∀ k : Fin 16, column84_1Expr 5 0 k = column84_1_r5_0 k := by decide +kernel
lemma column84_1_r5_1_eq : ∀ k : Fin 16, column84_1Expr 5 1 k = column84_1_r5_1 k := by decide +kernel
lemma column84_1_r5_2_eq : ∀ k : Fin 16, column84_1Expr 5 2 k = column84_1_r5_2 k := by decide +kernel
lemma column84_1_r5_3_eq : ∀ k : Fin 16, column84_1Expr 5 3 k = column84_1_r5_3 k := by decide +kernel
lemma column84_1_r5_4_eq : ∀ k : Fin 16, column84_1Expr 5 4 k = column84_1_r5_4 k := by decide +kernel
lemma column84_1_r5_5_eq : ∀ k : Fin 16, column84_1Expr 5 5 k = column84_1_r5_5 k := by decide +kernel
lemma column84_1_r5_6_eq : ∀ k : Fin 16, column84_1Expr 5 6 k = column84_1_r5_6 k := by decide +kernel
lemma column84_1_r5_7_eq : ∀ k : Fin 16, column84_1Expr 5 7 k = column84_1_r5_7 k := by decide +kernel
lemma column84_1_r5_8_eq : ∀ k : Fin 16, column84_1Expr 5 8 k = column84_1_r5_8 k := by decide +kernel
lemma column84_1_r5_9_eq : ∀ k : Fin 16, column84_1Expr 5 9 k = column84_1_r5_9 k := by decide +kernel
lemma column84_1_r5_10_eq : ∀ k : Fin 16, column84_1Expr 5 10 k = column84_1_r5_10 k := by decide +kernel
lemma column84_1_r5_11_eq : ∀ k : Fin 16, column84_1Expr 5 11 k = column84_1_r5_11 k := by decide +kernel
lemma column84_1_r5_12_eq : ∀ k : Fin 16, column84_1Expr 5 12 k = column84_1_r5_12 k := by decide +kernel
lemma column84_1_r5_13_eq : ∀ k : Fin 16, column84_1Expr 5 13 k = column84_1_r5_13 k := by decide +kernel
lemma column84_1_r5_14_eq : ∀ k : Fin 16, column84_1Expr 5 14 k = column84_1_r5_14 k := by decide +kernel
lemma column84_1_r5_15_eq : ∀ k : Fin 16, column84_1Expr 5 15 k = column84_1_r5_15 k := by decide +kernel
lemma column84_1_r5_eq (i k : Fin 16) : column84_1Expr 5 i k = column84_1_r5 i k := by
  fin_cases i
  · exact column84_1_r5_0_eq k
  · exact column84_1_r5_1_eq k
  · exact column84_1_r5_2_eq k
  · exact column84_1_r5_3_eq k
  · exact column84_1_r5_4_eq k
  · exact column84_1_r5_5_eq k
  · exact column84_1_r5_6_eq k
  · exact column84_1_r5_7_eq k
  · exact column84_1_r5_8_eq k
  · exact column84_1_r5_9_eq k
  · exact column84_1_r5_10_eq k
  · exact column84_1_r5_11_eq k
  · exact column84_1_r5_12_eq k
  · exact column84_1_r5_13_eq k
  · exact column84_1_r5_14_eq k
  · exact column84_1_r5_15_eq k
lemma column84_1_eq (j : Fin 6) (i k : Fin 16) : column84_1Expr j i k = column84_1 j i k := by
  fin_cases j
  · exact column84_1_r0_eq i k
  · exact column84_1_r1_eq i k
  · exact column84_1_r2_eq i k
  · exact column84_1_r3_eq i k
  · exact column84_1_r4_eq i k
  · exact column84_1_r5_eq i k
noncomputable def column87_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power87 j i k)
lemma column87_0_r0_0_eq : ∀ k : Fin 16, column87_0Expr 0 0 k = column87_0_r0_0 k := by decide +kernel
lemma column87_0_r0_1_eq : ∀ k : Fin 16, column87_0Expr 0 1 k = column87_0_r0_1 k := by decide +kernel
lemma column87_0_r0_2_eq : ∀ k : Fin 16, column87_0Expr 0 2 k = column87_0_r0_2 k := by decide +kernel
lemma column87_0_r0_3_eq : ∀ k : Fin 16, column87_0Expr 0 3 k = column87_0_r0_3 k := by decide +kernel
lemma column87_0_r0_4_eq : ∀ k : Fin 16, column87_0Expr 0 4 k = column87_0_r0_4 k := by decide +kernel
lemma column87_0_r0_5_eq : ∀ k : Fin 16, column87_0Expr 0 5 k = column87_0_r0_5 k := by decide +kernel
lemma column87_0_r0_6_eq : ∀ k : Fin 16, column87_0Expr 0 6 k = column87_0_r0_6 k := by decide +kernel
lemma column87_0_r0_7_eq : ∀ k : Fin 16, column87_0Expr 0 7 k = column87_0_r0_7 k := by decide +kernel
lemma column87_0_r0_8_eq : ∀ k : Fin 16, column87_0Expr 0 8 k = column87_0_r0_8 k := by decide +kernel
lemma column87_0_r0_9_eq : ∀ k : Fin 16, column87_0Expr 0 9 k = column87_0_r0_9 k := by decide +kernel
lemma column87_0_r0_10_eq : ∀ k : Fin 16, column87_0Expr 0 10 k = column87_0_r0_10 k := by decide +kernel
lemma column87_0_r0_11_eq : ∀ k : Fin 16, column87_0Expr 0 11 k = column87_0_r0_11 k := by decide +kernel
lemma column87_0_r0_12_eq : ∀ k : Fin 16, column87_0Expr 0 12 k = column87_0_r0_12 k := by decide +kernel
lemma column87_0_r0_13_eq : ∀ k : Fin 16, column87_0Expr 0 13 k = column87_0_r0_13 k := by decide +kernel
lemma column87_0_r0_14_eq : ∀ k : Fin 16, column87_0Expr 0 14 k = column87_0_r0_14 k := by decide +kernel
lemma column87_0_r0_15_eq : ∀ k : Fin 16, column87_0Expr 0 15 k = column87_0_r0_15 k := by decide +kernel
lemma column87_0_r0_eq (i k : Fin 16) : column87_0Expr 0 i k = column87_0_r0 i k := by
  fin_cases i
  · exact column87_0_r0_0_eq k
  · exact column87_0_r0_1_eq k
  · exact column87_0_r0_2_eq k
  · exact column87_0_r0_3_eq k
  · exact column87_0_r0_4_eq k
  · exact column87_0_r0_5_eq k
  · exact column87_0_r0_6_eq k
  · exact column87_0_r0_7_eq k
  · exact column87_0_r0_8_eq k
  · exact column87_0_r0_9_eq k
  · exact column87_0_r0_10_eq k
  · exact column87_0_r0_11_eq k
  · exact column87_0_r0_12_eq k
  · exact column87_0_r0_13_eq k
  · exact column87_0_r0_14_eq k
  · exact column87_0_r0_15_eq k
lemma column87_0_r1_0_eq : ∀ k : Fin 16, column87_0Expr 1 0 k = column87_0_r1_0 k := by decide +kernel
lemma column87_0_r1_1_eq : ∀ k : Fin 16, column87_0Expr 1 1 k = column87_0_r1_1 k := by decide +kernel
lemma column87_0_r1_2_eq : ∀ k : Fin 16, column87_0Expr 1 2 k = column87_0_r1_2 k := by decide +kernel
lemma column87_0_r1_3_eq : ∀ k : Fin 16, column87_0Expr 1 3 k = column87_0_r1_3 k := by decide +kernel
lemma column87_0_r1_4_eq : ∀ k : Fin 16, column87_0Expr 1 4 k = column87_0_r1_4 k := by decide +kernel
lemma column87_0_r1_5_eq : ∀ k : Fin 16, column87_0Expr 1 5 k = column87_0_r1_5 k := by decide +kernel
lemma column87_0_r1_6_eq : ∀ k : Fin 16, column87_0Expr 1 6 k = column87_0_r1_6 k := by decide +kernel
lemma column87_0_r1_7_eq : ∀ k : Fin 16, column87_0Expr 1 7 k = column87_0_r1_7 k := by decide +kernel
lemma column87_0_r1_8_eq : ∀ k : Fin 16, column87_0Expr 1 8 k = column87_0_r1_8 k := by decide +kernel
lemma column87_0_r1_9_eq : ∀ k : Fin 16, column87_0Expr 1 9 k = column87_0_r1_9 k := by decide +kernel
lemma column87_0_r1_10_eq : ∀ k : Fin 16, column87_0Expr 1 10 k = column87_0_r1_10 k := by decide +kernel
lemma column87_0_r1_11_eq : ∀ k : Fin 16, column87_0Expr 1 11 k = column87_0_r1_11 k := by decide +kernel
lemma column87_0_r1_12_eq : ∀ k : Fin 16, column87_0Expr 1 12 k = column87_0_r1_12 k := by decide +kernel
lemma column87_0_r1_13_eq : ∀ k : Fin 16, column87_0Expr 1 13 k = column87_0_r1_13 k := by decide +kernel
lemma column87_0_r1_14_eq : ∀ k : Fin 16, column87_0Expr 1 14 k = column87_0_r1_14 k := by decide +kernel
lemma column87_0_r1_15_eq : ∀ k : Fin 16, column87_0Expr 1 15 k = column87_0_r1_15 k := by decide +kernel
lemma column87_0_r1_eq (i k : Fin 16) : column87_0Expr 1 i k = column87_0_r1 i k := by
  fin_cases i
  · exact column87_0_r1_0_eq k
  · exact column87_0_r1_1_eq k
  · exact column87_0_r1_2_eq k
  · exact column87_0_r1_3_eq k
  · exact column87_0_r1_4_eq k
  · exact column87_0_r1_5_eq k
  · exact column87_0_r1_6_eq k
  · exact column87_0_r1_7_eq k
  · exact column87_0_r1_8_eq k
  · exact column87_0_r1_9_eq k
  · exact column87_0_r1_10_eq k
  · exact column87_0_r1_11_eq k
  · exact column87_0_r1_12_eq k
  · exact column87_0_r1_13_eq k
  · exact column87_0_r1_14_eq k
  · exact column87_0_r1_15_eq k
lemma column87_0_r2_0_eq : ∀ k : Fin 16, column87_0Expr 2 0 k = column87_0_r2_0 k := by decide +kernel
lemma column87_0_r2_1_eq : ∀ k : Fin 16, column87_0Expr 2 1 k = column87_0_r2_1 k := by decide +kernel
lemma column87_0_r2_2_eq : ∀ k : Fin 16, column87_0Expr 2 2 k = column87_0_r2_2 k := by decide +kernel
lemma column87_0_r2_3_eq : ∀ k : Fin 16, column87_0Expr 2 3 k = column87_0_r2_3 k := by decide +kernel
lemma column87_0_r2_4_eq : ∀ k : Fin 16, column87_0Expr 2 4 k = column87_0_r2_4 k := by decide +kernel
lemma column87_0_r2_5_eq : ∀ k : Fin 16, column87_0Expr 2 5 k = column87_0_r2_5 k := by decide +kernel
lemma column87_0_r2_6_eq : ∀ k : Fin 16, column87_0Expr 2 6 k = column87_0_r2_6 k := by decide +kernel
lemma column87_0_r2_7_eq : ∀ k : Fin 16, column87_0Expr 2 7 k = column87_0_r2_7 k := by decide +kernel
lemma column87_0_r2_8_eq : ∀ k : Fin 16, column87_0Expr 2 8 k = column87_0_r2_8 k := by decide +kernel
lemma column87_0_r2_9_eq : ∀ k : Fin 16, column87_0Expr 2 9 k = column87_0_r2_9 k := by decide +kernel
lemma column87_0_r2_10_eq : ∀ k : Fin 16, column87_0Expr 2 10 k = column87_0_r2_10 k := by decide +kernel
lemma column87_0_r2_11_eq : ∀ k : Fin 16, column87_0Expr 2 11 k = column87_0_r2_11 k := by decide +kernel
lemma column87_0_r2_12_eq : ∀ k : Fin 16, column87_0Expr 2 12 k = column87_0_r2_12 k := by decide +kernel
lemma column87_0_r2_13_eq : ∀ k : Fin 16, column87_0Expr 2 13 k = column87_0_r2_13 k := by decide +kernel
lemma column87_0_r2_14_eq : ∀ k : Fin 16, column87_0Expr 2 14 k = column87_0_r2_14 k := by decide +kernel
lemma column87_0_r2_15_eq : ∀ k : Fin 16, column87_0Expr 2 15 k = column87_0_r2_15 k := by decide +kernel
lemma column87_0_r2_eq (i k : Fin 16) : column87_0Expr 2 i k = column87_0_r2 i k := by
  fin_cases i
  · exact column87_0_r2_0_eq k
  · exact column87_0_r2_1_eq k
  · exact column87_0_r2_2_eq k
  · exact column87_0_r2_3_eq k
  · exact column87_0_r2_4_eq k
  · exact column87_0_r2_5_eq k
  · exact column87_0_r2_6_eq k
  · exact column87_0_r2_7_eq k
  · exact column87_0_r2_8_eq k
  · exact column87_0_r2_9_eq k
  · exact column87_0_r2_10_eq k
  · exact column87_0_r2_11_eq k
  · exact column87_0_r2_12_eq k
  · exact column87_0_r2_13_eq k
  · exact column87_0_r2_14_eq k
  · exact column87_0_r2_15_eq k
lemma column87_0_r3_0_eq : ∀ k : Fin 16, column87_0Expr 3 0 k = column87_0_r3_0 k := by decide +kernel
lemma column87_0_r3_1_eq : ∀ k : Fin 16, column87_0Expr 3 1 k = column87_0_r3_1 k := by decide +kernel
lemma column87_0_r3_2_eq : ∀ k : Fin 16, column87_0Expr 3 2 k = column87_0_r3_2 k := by decide +kernel
lemma column87_0_r3_3_eq : ∀ k : Fin 16, column87_0Expr 3 3 k = column87_0_r3_3 k := by decide +kernel
lemma column87_0_r3_4_eq : ∀ k : Fin 16, column87_0Expr 3 4 k = column87_0_r3_4 k := by decide +kernel
lemma column87_0_r3_5_eq : ∀ k : Fin 16, column87_0Expr 3 5 k = column87_0_r3_5 k := by decide +kernel
lemma column87_0_r3_6_eq : ∀ k : Fin 16, column87_0Expr 3 6 k = column87_0_r3_6 k := by decide +kernel
lemma column87_0_r3_7_eq : ∀ k : Fin 16, column87_0Expr 3 7 k = column87_0_r3_7 k := by decide +kernel
lemma column87_0_r3_8_eq : ∀ k : Fin 16, column87_0Expr 3 8 k = column87_0_r3_8 k := by decide +kernel
lemma column87_0_r3_9_eq : ∀ k : Fin 16, column87_0Expr 3 9 k = column87_0_r3_9 k := by decide +kernel
lemma column87_0_r3_10_eq : ∀ k : Fin 16, column87_0Expr 3 10 k = column87_0_r3_10 k := by decide +kernel
lemma column87_0_r3_11_eq : ∀ k : Fin 16, column87_0Expr 3 11 k = column87_0_r3_11 k := by decide +kernel
lemma column87_0_r3_12_eq : ∀ k : Fin 16, column87_0Expr 3 12 k = column87_0_r3_12 k := by decide +kernel
lemma column87_0_r3_13_eq : ∀ k : Fin 16, column87_0Expr 3 13 k = column87_0_r3_13 k := by decide +kernel
lemma column87_0_r3_14_eq : ∀ k : Fin 16, column87_0Expr 3 14 k = column87_0_r3_14 k := by decide +kernel
lemma column87_0_r3_15_eq : ∀ k : Fin 16, column87_0Expr 3 15 k = column87_0_r3_15 k := by decide +kernel
lemma column87_0_r3_eq (i k : Fin 16) : column87_0Expr 3 i k = column87_0_r3 i k := by
  fin_cases i
  · exact column87_0_r3_0_eq k
  · exact column87_0_r3_1_eq k
  · exact column87_0_r3_2_eq k
  · exact column87_0_r3_3_eq k
  · exact column87_0_r3_4_eq k
  · exact column87_0_r3_5_eq k
  · exact column87_0_r3_6_eq k
  · exact column87_0_r3_7_eq k
  · exact column87_0_r3_8_eq k
  · exact column87_0_r3_9_eq k
  · exact column87_0_r3_10_eq k
  · exact column87_0_r3_11_eq k
  · exact column87_0_r3_12_eq k
  · exact column87_0_r3_13_eq k
  · exact column87_0_r3_14_eq k
  · exact column87_0_r3_15_eq k
lemma column87_0_r4_0_eq : ∀ k : Fin 16, column87_0Expr 4 0 k = column87_0_r4_0 k := by decide +kernel
lemma column87_0_r4_1_eq : ∀ k : Fin 16, column87_0Expr 4 1 k = column87_0_r4_1 k := by decide +kernel
lemma column87_0_r4_2_eq : ∀ k : Fin 16, column87_0Expr 4 2 k = column87_0_r4_2 k := by decide +kernel
lemma column87_0_r4_3_eq : ∀ k : Fin 16, column87_0Expr 4 3 k = column87_0_r4_3 k := by decide +kernel
lemma column87_0_r4_4_eq : ∀ k : Fin 16, column87_0Expr 4 4 k = column87_0_r4_4 k := by decide +kernel
lemma column87_0_r4_5_eq : ∀ k : Fin 16, column87_0Expr 4 5 k = column87_0_r4_5 k := by decide +kernel
lemma column87_0_r4_6_eq : ∀ k : Fin 16, column87_0Expr 4 6 k = column87_0_r4_6 k := by decide +kernel
lemma column87_0_r4_7_eq : ∀ k : Fin 16, column87_0Expr 4 7 k = column87_0_r4_7 k := by decide +kernel
lemma column87_0_r4_8_eq : ∀ k : Fin 16, column87_0Expr 4 8 k = column87_0_r4_8 k := by decide +kernel
lemma column87_0_r4_9_eq : ∀ k : Fin 16, column87_0Expr 4 9 k = column87_0_r4_9 k := by decide +kernel
lemma column87_0_r4_10_eq : ∀ k : Fin 16, column87_0Expr 4 10 k = column87_0_r4_10 k := by decide +kernel
lemma column87_0_r4_11_eq : ∀ k : Fin 16, column87_0Expr 4 11 k = column87_0_r4_11 k := by decide +kernel
lemma column87_0_r4_12_eq : ∀ k : Fin 16, column87_0Expr 4 12 k = column87_0_r4_12 k := by decide +kernel
lemma column87_0_r4_13_eq : ∀ k : Fin 16, column87_0Expr 4 13 k = column87_0_r4_13 k := by decide +kernel
lemma column87_0_r4_14_eq : ∀ k : Fin 16, column87_0Expr 4 14 k = column87_0_r4_14 k := by decide +kernel
lemma column87_0_r4_15_eq : ∀ k : Fin 16, column87_0Expr 4 15 k = column87_0_r4_15 k := by decide +kernel
lemma column87_0_r4_eq (i k : Fin 16) : column87_0Expr 4 i k = column87_0_r4 i k := by
  fin_cases i
  · exact column87_0_r4_0_eq k
  · exact column87_0_r4_1_eq k
  · exact column87_0_r4_2_eq k
  · exact column87_0_r4_3_eq k
  · exact column87_0_r4_4_eq k
  · exact column87_0_r4_5_eq k
  · exact column87_0_r4_6_eq k
  · exact column87_0_r4_7_eq k
  · exact column87_0_r4_8_eq k
  · exact column87_0_r4_9_eq k
  · exact column87_0_r4_10_eq k
  · exact column87_0_r4_11_eq k
  · exact column87_0_r4_12_eq k
  · exact column87_0_r4_13_eq k
  · exact column87_0_r4_14_eq k
  · exact column87_0_r4_15_eq k
lemma column87_0_r5_0_eq : ∀ k : Fin 16, column87_0Expr 5 0 k = column87_0_r5_0 k := by decide +kernel
lemma column87_0_r5_1_eq : ∀ k : Fin 16, column87_0Expr 5 1 k = column87_0_r5_1 k := by decide +kernel
lemma column87_0_r5_2_eq : ∀ k : Fin 16, column87_0Expr 5 2 k = column87_0_r5_2 k := by decide +kernel
lemma column87_0_r5_3_eq : ∀ k : Fin 16, column87_0Expr 5 3 k = column87_0_r5_3 k := by decide +kernel
lemma column87_0_r5_4_eq : ∀ k : Fin 16, column87_0Expr 5 4 k = column87_0_r5_4 k := by decide +kernel
lemma column87_0_r5_5_eq : ∀ k : Fin 16, column87_0Expr 5 5 k = column87_0_r5_5 k := by decide +kernel
lemma column87_0_r5_6_eq : ∀ k : Fin 16, column87_0Expr 5 6 k = column87_0_r5_6 k := by decide +kernel
lemma column87_0_r5_7_eq : ∀ k : Fin 16, column87_0Expr 5 7 k = column87_0_r5_7 k := by decide +kernel
lemma column87_0_r5_8_eq : ∀ k : Fin 16, column87_0Expr 5 8 k = column87_0_r5_8 k := by decide +kernel
lemma column87_0_r5_9_eq : ∀ k : Fin 16, column87_0Expr 5 9 k = column87_0_r5_9 k := by decide +kernel
lemma column87_0_r5_10_eq : ∀ k : Fin 16, column87_0Expr 5 10 k = column87_0_r5_10 k := by decide +kernel
lemma column87_0_r5_11_eq : ∀ k : Fin 16, column87_0Expr 5 11 k = column87_0_r5_11 k := by decide +kernel
lemma column87_0_r5_12_eq : ∀ k : Fin 16, column87_0Expr 5 12 k = column87_0_r5_12 k := by decide +kernel
lemma column87_0_r5_13_eq : ∀ k : Fin 16, column87_0Expr 5 13 k = column87_0_r5_13 k := by decide +kernel
lemma column87_0_r5_14_eq : ∀ k : Fin 16, column87_0Expr 5 14 k = column87_0_r5_14 k := by decide +kernel
lemma column87_0_r5_15_eq : ∀ k : Fin 16, column87_0Expr 5 15 k = column87_0_r5_15 k := by decide +kernel
lemma column87_0_r5_eq (i k : Fin 16) : column87_0Expr 5 i k = column87_0_r5 i k := by
  fin_cases i
  · exact column87_0_r5_0_eq k
  · exact column87_0_r5_1_eq k
  · exact column87_0_r5_2_eq k
  · exact column87_0_r5_3_eq k
  · exact column87_0_r5_4_eq k
  · exact column87_0_r5_5_eq k
  · exact column87_0_r5_6_eq k
  · exact column87_0_r5_7_eq k
  · exact column87_0_r5_8_eq k
  · exact column87_0_r5_9_eq k
  · exact column87_0_r5_10_eq k
  · exact column87_0_r5_11_eq k
  · exact column87_0_r5_12_eq k
  · exact column87_0_r5_13_eq k
  · exact column87_0_r5_14_eq k
  · exact column87_0_r5_15_eq k
lemma column87_0_eq (j : Fin 6) (i k : Fin 16) : column87_0Expr j i k = column87_0 j i k := by
  fin_cases j
  · exact column87_0_r0_eq i k
  · exact column87_0_r1_eq i k
  · exact column87_0_r2_eq i k
  · exact column87_0_r3_eq i k
  · exact column87_0_r4_eq i k
  · exact column87_0_r5_eq i k
noncomputable def column87_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power87 j i k)
lemma column87_1_r0_0_eq : ∀ k : Fin 16, column87_1Expr 0 0 k = column87_1_r0_0 k := by decide +kernel
lemma column87_1_r0_1_eq : ∀ k : Fin 16, column87_1Expr 0 1 k = column87_1_r0_1 k := by decide +kernel
lemma column87_1_r0_2_eq : ∀ k : Fin 16, column87_1Expr 0 2 k = column87_1_r0_2 k := by decide +kernel
lemma column87_1_r0_3_eq : ∀ k : Fin 16, column87_1Expr 0 3 k = column87_1_r0_3 k := by decide +kernel
lemma column87_1_r0_4_eq : ∀ k : Fin 16, column87_1Expr 0 4 k = column87_1_r0_4 k := by decide +kernel
lemma column87_1_r0_5_eq : ∀ k : Fin 16, column87_1Expr 0 5 k = column87_1_r0_5 k := by decide +kernel
lemma column87_1_r0_6_eq : ∀ k : Fin 16, column87_1Expr 0 6 k = column87_1_r0_6 k := by decide +kernel
lemma column87_1_r0_7_eq : ∀ k : Fin 16, column87_1Expr 0 7 k = column87_1_r0_7 k := by decide +kernel
lemma column87_1_r0_8_eq : ∀ k : Fin 16, column87_1Expr 0 8 k = column87_1_r0_8 k := by decide +kernel
lemma column87_1_r0_9_eq : ∀ k : Fin 16, column87_1Expr 0 9 k = column87_1_r0_9 k := by decide +kernel
lemma column87_1_r0_10_eq : ∀ k : Fin 16, column87_1Expr 0 10 k = column87_1_r0_10 k := by decide +kernel
lemma column87_1_r0_11_eq : ∀ k : Fin 16, column87_1Expr 0 11 k = column87_1_r0_11 k := by decide +kernel
lemma column87_1_r0_12_eq : ∀ k : Fin 16, column87_1Expr 0 12 k = column87_1_r0_12 k := by decide +kernel
lemma column87_1_r0_13_eq : ∀ k : Fin 16, column87_1Expr 0 13 k = column87_1_r0_13 k := by decide +kernel
lemma column87_1_r0_14_eq : ∀ k : Fin 16, column87_1Expr 0 14 k = column87_1_r0_14 k := by decide +kernel
lemma column87_1_r0_15_eq : ∀ k : Fin 16, column87_1Expr 0 15 k = column87_1_r0_15 k := by decide +kernel
lemma column87_1_r0_eq (i k : Fin 16) : column87_1Expr 0 i k = column87_1_r0 i k := by
  fin_cases i
  · exact column87_1_r0_0_eq k
  · exact column87_1_r0_1_eq k
  · exact column87_1_r0_2_eq k
  · exact column87_1_r0_3_eq k
  · exact column87_1_r0_4_eq k
  · exact column87_1_r0_5_eq k
  · exact column87_1_r0_6_eq k
  · exact column87_1_r0_7_eq k
  · exact column87_1_r0_8_eq k
  · exact column87_1_r0_9_eq k
  · exact column87_1_r0_10_eq k
  · exact column87_1_r0_11_eq k
  · exact column87_1_r0_12_eq k
  · exact column87_1_r0_13_eq k
  · exact column87_1_r0_14_eq k
  · exact column87_1_r0_15_eq k
lemma column87_1_r1_0_eq : ∀ k : Fin 16, column87_1Expr 1 0 k = column87_1_r1_0 k := by decide +kernel
lemma column87_1_r1_1_eq : ∀ k : Fin 16, column87_1Expr 1 1 k = column87_1_r1_1 k := by decide +kernel
lemma column87_1_r1_2_eq : ∀ k : Fin 16, column87_1Expr 1 2 k = column87_1_r1_2 k := by decide +kernel
lemma column87_1_r1_3_eq : ∀ k : Fin 16, column87_1Expr 1 3 k = column87_1_r1_3 k := by decide +kernel
lemma column87_1_r1_4_eq : ∀ k : Fin 16, column87_1Expr 1 4 k = column87_1_r1_4 k := by decide +kernel
lemma column87_1_r1_5_eq : ∀ k : Fin 16, column87_1Expr 1 5 k = column87_1_r1_5 k := by decide +kernel
lemma column87_1_r1_6_eq : ∀ k : Fin 16, column87_1Expr 1 6 k = column87_1_r1_6 k := by decide +kernel
lemma column87_1_r1_7_eq : ∀ k : Fin 16, column87_1Expr 1 7 k = column87_1_r1_7 k := by decide +kernel
lemma column87_1_r1_8_eq : ∀ k : Fin 16, column87_1Expr 1 8 k = column87_1_r1_8 k := by decide +kernel
lemma column87_1_r1_9_eq : ∀ k : Fin 16, column87_1Expr 1 9 k = column87_1_r1_9 k := by decide +kernel
lemma column87_1_r1_10_eq : ∀ k : Fin 16, column87_1Expr 1 10 k = column87_1_r1_10 k := by decide +kernel
lemma column87_1_r1_11_eq : ∀ k : Fin 16, column87_1Expr 1 11 k = column87_1_r1_11 k := by decide +kernel
lemma column87_1_r1_12_eq : ∀ k : Fin 16, column87_1Expr 1 12 k = column87_1_r1_12 k := by decide +kernel
lemma column87_1_r1_13_eq : ∀ k : Fin 16, column87_1Expr 1 13 k = column87_1_r1_13 k := by decide +kernel
lemma column87_1_r1_14_eq : ∀ k : Fin 16, column87_1Expr 1 14 k = column87_1_r1_14 k := by decide +kernel
lemma column87_1_r1_15_eq : ∀ k : Fin 16, column87_1Expr 1 15 k = column87_1_r1_15 k := by decide +kernel
lemma column87_1_r1_eq (i k : Fin 16) : column87_1Expr 1 i k = column87_1_r1 i k := by
  fin_cases i
  · exact column87_1_r1_0_eq k
  · exact column87_1_r1_1_eq k
  · exact column87_1_r1_2_eq k
  · exact column87_1_r1_3_eq k
  · exact column87_1_r1_4_eq k
  · exact column87_1_r1_5_eq k
  · exact column87_1_r1_6_eq k
  · exact column87_1_r1_7_eq k
  · exact column87_1_r1_8_eq k
  · exact column87_1_r1_9_eq k
  · exact column87_1_r1_10_eq k
  · exact column87_1_r1_11_eq k
  · exact column87_1_r1_12_eq k
  · exact column87_1_r1_13_eq k
  · exact column87_1_r1_14_eq k
  · exact column87_1_r1_15_eq k
lemma column87_1_r2_0_eq : ∀ k : Fin 16, column87_1Expr 2 0 k = column87_1_r2_0 k := by decide +kernel
lemma column87_1_r2_1_eq : ∀ k : Fin 16, column87_1Expr 2 1 k = column87_1_r2_1 k := by decide +kernel
lemma column87_1_r2_2_eq : ∀ k : Fin 16, column87_1Expr 2 2 k = column87_1_r2_2 k := by decide +kernel
lemma column87_1_r2_3_eq : ∀ k : Fin 16, column87_1Expr 2 3 k = column87_1_r2_3 k := by decide +kernel
lemma column87_1_r2_4_eq : ∀ k : Fin 16, column87_1Expr 2 4 k = column87_1_r2_4 k := by decide +kernel
lemma column87_1_r2_5_eq : ∀ k : Fin 16, column87_1Expr 2 5 k = column87_1_r2_5 k := by decide +kernel
lemma column87_1_r2_6_eq : ∀ k : Fin 16, column87_1Expr 2 6 k = column87_1_r2_6 k := by decide +kernel
lemma column87_1_r2_7_eq : ∀ k : Fin 16, column87_1Expr 2 7 k = column87_1_r2_7 k := by decide +kernel
lemma column87_1_r2_8_eq : ∀ k : Fin 16, column87_1Expr 2 8 k = column87_1_r2_8 k := by decide +kernel
lemma column87_1_r2_9_eq : ∀ k : Fin 16, column87_1Expr 2 9 k = column87_1_r2_9 k := by decide +kernel
lemma column87_1_r2_10_eq : ∀ k : Fin 16, column87_1Expr 2 10 k = column87_1_r2_10 k := by decide +kernel
lemma column87_1_r2_11_eq : ∀ k : Fin 16, column87_1Expr 2 11 k = column87_1_r2_11 k := by decide +kernel
lemma column87_1_r2_12_eq : ∀ k : Fin 16, column87_1Expr 2 12 k = column87_1_r2_12 k := by decide +kernel
lemma column87_1_r2_13_eq : ∀ k : Fin 16, column87_1Expr 2 13 k = column87_1_r2_13 k := by decide +kernel
lemma column87_1_r2_14_eq : ∀ k : Fin 16, column87_1Expr 2 14 k = column87_1_r2_14 k := by decide +kernel
lemma column87_1_r2_15_eq : ∀ k : Fin 16, column87_1Expr 2 15 k = column87_1_r2_15 k := by decide +kernel
lemma column87_1_r2_eq (i k : Fin 16) : column87_1Expr 2 i k = column87_1_r2 i k := by
  fin_cases i
  · exact column87_1_r2_0_eq k
  · exact column87_1_r2_1_eq k
  · exact column87_1_r2_2_eq k
  · exact column87_1_r2_3_eq k
  · exact column87_1_r2_4_eq k
  · exact column87_1_r2_5_eq k
  · exact column87_1_r2_6_eq k
  · exact column87_1_r2_7_eq k
  · exact column87_1_r2_8_eq k
  · exact column87_1_r2_9_eq k
  · exact column87_1_r2_10_eq k
  · exact column87_1_r2_11_eq k
  · exact column87_1_r2_12_eq k
  · exact column87_1_r2_13_eq k
  · exact column87_1_r2_14_eq k
  · exact column87_1_r2_15_eq k
lemma column87_1_r3_0_eq : ∀ k : Fin 16, column87_1Expr 3 0 k = column87_1_r3_0 k := by decide +kernel
lemma column87_1_r3_1_eq : ∀ k : Fin 16, column87_1Expr 3 1 k = column87_1_r3_1 k := by decide +kernel
lemma column87_1_r3_2_eq : ∀ k : Fin 16, column87_1Expr 3 2 k = column87_1_r3_2 k := by decide +kernel
lemma column87_1_r3_3_eq : ∀ k : Fin 16, column87_1Expr 3 3 k = column87_1_r3_3 k := by decide +kernel
lemma column87_1_r3_4_eq : ∀ k : Fin 16, column87_1Expr 3 4 k = column87_1_r3_4 k := by decide +kernel
lemma column87_1_r3_5_eq : ∀ k : Fin 16, column87_1Expr 3 5 k = column87_1_r3_5 k := by decide +kernel
lemma column87_1_r3_6_eq : ∀ k : Fin 16, column87_1Expr 3 6 k = column87_1_r3_6 k := by decide +kernel
lemma column87_1_r3_7_eq : ∀ k : Fin 16, column87_1Expr 3 7 k = column87_1_r3_7 k := by decide +kernel
lemma column87_1_r3_8_eq : ∀ k : Fin 16, column87_1Expr 3 8 k = column87_1_r3_8 k := by decide +kernel
lemma column87_1_r3_9_eq : ∀ k : Fin 16, column87_1Expr 3 9 k = column87_1_r3_9 k := by decide +kernel
lemma column87_1_r3_10_eq : ∀ k : Fin 16, column87_1Expr 3 10 k = column87_1_r3_10 k := by decide +kernel
lemma column87_1_r3_11_eq : ∀ k : Fin 16, column87_1Expr 3 11 k = column87_1_r3_11 k := by decide +kernel
lemma column87_1_r3_12_eq : ∀ k : Fin 16, column87_1Expr 3 12 k = column87_1_r3_12 k := by decide +kernel
lemma column87_1_r3_13_eq : ∀ k : Fin 16, column87_1Expr 3 13 k = column87_1_r3_13 k := by decide +kernel
lemma column87_1_r3_14_eq : ∀ k : Fin 16, column87_1Expr 3 14 k = column87_1_r3_14 k := by decide +kernel
lemma column87_1_r3_15_eq : ∀ k : Fin 16, column87_1Expr 3 15 k = column87_1_r3_15 k := by decide +kernel
lemma column87_1_r3_eq (i k : Fin 16) : column87_1Expr 3 i k = column87_1_r3 i k := by
  fin_cases i
  · exact column87_1_r3_0_eq k
  · exact column87_1_r3_1_eq k
  · exact column87_1_r3_2_eq k
  · exact column87_1_r3_3_eq k
  · exact column87_1_r3_4_eq k
  · exact column87_1_r3_5_eq k
  · exact column87_1_r3_6_eq k
  · exact column87_1_r3_7_eq k
  · exact column87_1_r3_8_eq k
  · exact column87_1_r3_9_eq k
  · exact column87_1_r3_10_eq k
  · exact column87_1_r3_11_eq k
  · exact column87_1_r3_12_eq k
  · exact column87_1_r3_13_eq k
  · exact column87_1_r3_14_eq k
  · exact column87_1_r3_15_eq k
lemma column87_1_r4_0_eq : ∀ k : Fin 16, column87_1Expr 4 0 k = column87_1_r4_0 k := by decide +kernel
lemma column87_1_r4_1_eq : ∀ k : Fin 16, column87_1Expr 4 1 k = column87_1_r4_1 k := by decide +kernel
lemma column87_1_r4_2_eq : ∀ k : Fin 16, column87_1Expr 4 2 k = column87_1_r4_2 k := by decide +kernel
lemma column87_1_r4_3_eq : ∀ k : Fin 16, column87_1Expr 4 3 k = column87_1_r4_3 k := by decide +kernel
lemma column87_1_r4_4_eq : ∀ k : Fin 16, column87_1Expr 4 4 k = column87_1_r4_4 k := by decide +kernel
lemma column87_1_r4_5_eq : ∀ k : Fin 16, column87_1Expr 4 5 k = column87_1_r4_5 k := by decide +kernel
lemma column87_1_r4_6_eq : ∀ k : Fin 16, column87_1Expr 4 6 k = column87_1_r4_6 k := by decide +kernel
lemma column87_1_r4_7_eq : ∀ k : Fin 16, column87_1Expr 4 7 k = column87_1_r4_7 k := by decide +kernel
lemma column87_1_r4_8_eq : ∀ k : Fin 16, column87_1Expr 4 8 k = column87_1_r4_8 k := by decide +kernel
lemma column87_1_r4_9_eq : ∀ k : Fin 16, column87_1Expr 4 9 k = column87_1_r4_9 k := by decide +kernel
lemma column87_1_r4_10_eq : ∀ k : Fin 16, column87_1Expr 4 10 k = column87_1_r4_10 k := by decide +kernel
lemma column87_1_r4_11_eq : ∀ k : Fin 16, column87_1Expr 4 11 k = column87_1_r4_11 k := by decide +kernel
lemma column87_1_r4_12_eq : ∀ k : Fin 16, column87_1Expr 4 12 k = column87_1_r4_12 k := by decide +kernel
lemma column87_1_r4_13_eq : ∀ k : Fin 16, column87_1Expr 4 13 k = column87_1_r4_13 k := by decide +kernel
lemma column87_1_r4_14_eq : ∀ k : Fin 16, column87_1Expr 4 14 k = column87_1_r4_14 k := by decide +kernel
lemma column87_1_r4_15_eq : ∀ k : Fin 16, column87_1Expr 4 15 k = column87_1_r4_15 k := by decide +kernel
lemma column87_1_r4_eq (i k : Fin 16) : column87_1Expr 4 i k = column87_1_r4 i k := by
  fin_cases i
  · exact column87_1_r4_0_eq k
  · exact column87_1_r4_1_eq k
  · exact column87_1_r4_2_eq k
  · exact column87_1_r4_3_eq k
  · exact column87_1_r4_4_eq k
  · exact column87_1_r4_5_eq k
  · exact column87_1_r4_6_eq k
  · exact column87_1_r4_7_eq k
  · exact column87_1_r4_8_eq k
  · exact column87_1_r4_9_eq k
  · exact column87_1_r4_10_eq k
  · exact column87_1_r4_11_eq k
  · exact column87_1_r4_12_eq k
  · exact column87_1_r4_13_eq k
  · exact column87_1_r4_14_eq k
  · exact column87_1_r4_15_eq k
lemma column87_1_r5_0_eq : ∀ k : Fin 16, column87_1Expr 5 0 k = column87_1_r5_0 k := by decide +kernel
lemma column87_1_r5_1_eq : ∀ k : Fin 16, column87_1Expr 5 1 k = column87_1_r5_1 k := by decide +kernel
lemma column87_1_r5_2_eq : ∀ k : Fin 16, column87_1Expr 5 2 k = column87_1_r5_2 k := by decide +kernel
lemma column87_1_r5_3_eq : ∀ k : Fin 16, column87_1Expr 5 3 k = column87_1_r5_3 k := by decide +kernel
lemma column87_1_r5_4_eq : ∀ k : Fin 16, column87_1Expr 5 4 k = column87_1_r5_4 k := by decide +kernel
lemma column87_1_r5_5_eq : ∀ k : Fin 16, column87_1Expr 5 5 k = column87_1_r5_5 k := by decide +kernel
lemma column87_1_r5_6_eq : ∀ k : Fin 16, column87_1Expr 5 6 k = column87_1_r5_6 k := by decide +kernel
lemma column87_1_r5_7_eq : ∀ k : Fin 16, column87_1Expr 5 7 k = column87_1_r5_7 k := by decide +kernel
lemma column87_1_r5_8_eq : ∀ k : Fin 16, column87_1Expr 5 8 k = column87_1_r5_8 k := by decide +kernel
lemma column87_1_r5_9_eq : ∀ k : Fin 16, column87_1Expr 5 9 k = column87_1_r5_9 k := by decide +kernel
lemma column87_1_r5_10_eq : ∀ k : Fin 16, column87_1Expr 5 10 k = column87_1_r5_10 k := by decide +kernel
lemma column87_1_r5_11_eq : ∀ k : Fin 16, column87_1Expr 5 11 k = column87_1_r5_11 k := by decide +kernel
lemma column87_1_r5_12_eq : ∀ k : Fin 16, column87_1Expr 5 12 k = column87_1_r5_12 k := by decide +kernel
lemma column87_1_r5_13_eq : ∀ k : Fin 16, column87_1Expr 5 13 k = column87_1_r5_13 k := by decide +kernel
lemma column87_1_r5_14_eq : ∀ k : Fin 16, column87_1Expr 5 14 k = column87_1_r5_14 k := by decide +kernel
lemma column87_1_r5_15_eq : ∀ k : Fin 16, column87_1Expr 5 15 k = column87_1_r5_15 k := by decide +kernel
lemma column87_1_r5_eq (i k : Fin 16) : column87_1Expr 5 i k = column87_1_r5 i k := by
  fin_cases i
  · exact column87_1_r5_0_eq k
  · exact column87_1_r5_1_eq k
  · exact column87_1_r5_2_eq k
  · exact column87_1_r5_3_eq k
  · exact column87_1_r5_4_eq k
  · exact column87_1_r5_5_eq k
  · exact column87_1_r5_6_eq k
  · exact column87_1_r5_7_eq k
  · exact column87_1_r5_8_eq k
  · exact column87_1_r5_9_eq k
  · exact column87_1_r5_10_eq k
  · exact column87_1_r5_11_eq k
  · exact column87_1_r5_12_eq k
  · exact column87_1_r5_13_eq k
  · exact column87_1_r5_14_eq k
  · exact column87_1_r5_15_eq k
lemma column87_1_eq (j : Fin 6) (i k : Fin 16) : column87_1Expr j i k = column87_1 j i k := by
  fin_cases j
  · exact column87_1_r0_eq i k
  · exact column87_1_r1_eq i k
  · exact column87_1_r2_eq i k
  · exact column87_1_r3_eq i k
  · exact column87_1_r4_eq i k
  · exact column87_1_r5_eq i k
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def mpower0_0 (_j : Fin 6) (_i _k : Fin 16) : CBox := CBox.rat 1 1 0 1
noncomputable def mpower1_0 (_j : Fin 6) (_i _k : Fin 16) : CBox := CBox.rat 1 1 0 1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments84
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
namespace cm84_4_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm84_4_0_1
namespace cm84_4_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm84_4_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments87
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
namespace cm87_1_1_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm87_1_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments88
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
namespace cm88_3_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm88_3_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments93
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
namespace cm93_1_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm93_1_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments96
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
namespace cm96_4_1_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm96_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments99
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
namespace cm99_4_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
end cm99_4_0_0
end SharpPlanar.CachedData

end OAI
end


