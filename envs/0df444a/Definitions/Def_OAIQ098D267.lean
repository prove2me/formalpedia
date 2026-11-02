-- Prove2me | Definitions.Def_OAIQ098D267
-- name    : OAIQ098D267
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:35:41.275963+00:00
-- url     : https://prove2.me/theorems/36be1a08-a996-4bea-a14f-6a733be77614
-- title:
--   Definitions bundle OAIQ098D267 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 733 declarations of OpenAI's Lean: 37 definitions and 696 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.cm45_3_1_0.s0`, `OAI.SharpPlanar.CachedData.cm45_3_1_0.s1`, `OAI.SharpPlanar.CachedData.cm45_3_1_0.s2`, `OAI.SharpPlanar.CachedData.cm45_3_1_0.s3`, `OAI.SharpPlanar.CachedData.cm45_3_1_0.sums`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.s0`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.s1`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.s2`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.s3`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.s4`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.s5`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.sums`, `OAI.SharpPlanar.CachedData.cm4_16_0_1.s0`, `OAI.SharpPlanar.CachedData.cm4_16_0_1.sums`, `OAI.SharpPlanar.CachedData.cm4_9_1_0.s0`, `OAI.SharpPlanar.CachedData.cm4_9_1_0.s1`, `OAI.SharpPlanar.CachedData.cm4_9_1_0.s2`, `OAI.SharpPlanar.CachedData.cm4_9_1_0.s3`, `OAI.SharpPlanar.CachedData.cm4_9_1_0.sums`, `OAI.SharpPlanar.CachedData.cm4_9_1_1.s0`, `OAI.SharpPlanar.CachedData.cm4_9_1_1.sums`, `OAI.SharpPlanar.CachedData.cm52_3_1_0.s0`, `OAI.SharpPlanar.CachedData.cm52_3_1_0.s1`, `OAI.SharpPlanar.CachedData.cm52_3_1_0.s2`, `OAI.SharpPlanar.CachedData.cm52_3_1_0.sums`, `OAI.SharpPlanar.CachedData.column45_1Expr`, `OAI.SharpPlanar.CachedData.column48_0Expr`, `OAI.SharpPlanar.CachedData.column48_1Expr`, `OAI.SharpPlanar.CachedData.column51_0Expr`, `OAI.SharpPlanar.CachedData.column51_1Expr`, `OAI.SharpPlanar.CachedData.column52_1Expr`, `OAI.SharpPlanar.CachedData.column55_0Expr`, `OAI.SharpPlanar.CachedData.column61_0Expr`, `OAI.SharpPlanar.CachedData.column64_1Expr`, `OAI.SharpPlanar.CachedData.column67_0Expr`, `OAI.SharpPlanar.CachedData.column69_0Expr`, `OAI.SharpPlanar.CachedData.column69_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns50.lean), [`PlanarPacking_Certificate_Columns60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns60.lean), [`PlanarPacking_Certificate_Columns70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns70.lean), [`PlanarPacking_Certificate_LMoments16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments16.lean), [`PlanarPacking_Certificate_LMoments9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments9.lean), [`PlanarPacking_Certificate_UMoments45`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments45.lean), [`PlanarPacking_Certificate_UMoments49`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments49.lean), [`PlanarPacking_Certificate_UMoments52`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments52.lean).
--
--   **Imports.** It imports the bundles `OAIQ098D020`, `OAIQ098D021`, `OAIQ098D022`, `OAIQ098D023`, `OAIQ098D024`, `OAIQ098D041`, `OAIQ098D042`, `OAIQ098D043`, `OAIQ098D044`, `OAIQ098D045`, `OAIQ098D057`, `OAIQ098D058`, `OAIQ098D059`, `OAIQ098D060`, `OAIQ098D062`, `OAIQ098D063`, `OAIQ098D064`, `OAIQ098D065`, `OAIQ098D066`, `OAIQ098D103`, `OAIQ098D104`, `OAIQ098D105`, `OAIQ098D106`, `OAIQ098D107` and `OAIQ098D108` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D297`, `OAIQ098D311`, `OAIQ098D318`, `OAIQ098D320`, `OAIQ098D321`, `OAIQ098D325`, `OAIQ098D328`, `OAIQ098D329` and `OAIQ098D331`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D020
import Definitions.Def_OAIQ098D021
import Definitions.Def_OAIQ098D022
import Definitions.Def_OAIQ098D023
import Definitions.Def_OAIQ098D024
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D042
import Definitions.Def_OAIQ098D043
import Definitions.Def_OAIQ098D044
import Definitions.Def_OAIQ098D045
import Definitions.Def_OAIQ098D057
import Definitions.Def_OAIQ098D058
import Definitions.Def_OAIQ098D059
import Definitions.Def_OAIQ098D060
import Definitions.Def_OAIQ098D062
import Definitions.Def_OAIQ098D063
import Definitions.Def_OAIQ098D064
import Definitions.Def_OAIQ098D065
import Definitions.Def_OAIQ098D066
import Definitions.Def_OAIQ098D103
import Definitions.Def_OAIQ098D104
import Definitions.Def_OAIQ098D105
import Definitions.Def_OAIQ098D106
import Definitions.Def_OAIQ098D107
import Definitions.Def_OAIQ098D108

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns50
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
noncomputable def column45_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power45 j i k)
lemma column45_1_r0_0_eq : ∀ k : Fin 16, column45_1Expr 0 0 k = column45_1_r0_0 k := by decide +kernel
lemma column45_1_r0_1_eq : ∀ k : Fin 16, column45_1Expr 0 1 k = column45_1_r0_1 k := by decide +kernel
lemma column45_1_r0_2_eq : ∀ k : Fin 16, column45_1Expr 0 2 k = column45_1_r0_2 k := by decide +kernel
lemma column45_1_r0_3_eq : ∀ k : Fin 16, column45_1Expr 0 3 k = column45_1_r0_3 k := by decide +kernel
lemma column45_1_r0_4_eq : ∀ k : Fin 16, column45_1Expr 0 4 k = column45_1_r0_4 k := by decide +kernel
lemma column45_1_r0_5_eq : ∀ k : Fin 16, column45_1Expr 0 5 k = column45_1_r0_5 k := by decide +kernel
lemma column45_1_r0_6_eq : ∀ k : Fin 16, column45_1Expr 0 6 k = column45_1_r0_6 k := by decide +kernel
lemma column45_1_r0_7_eq : ∀ k : Fin 16, column45_1Expr 0 7 k = column45_1_r0_7 k := by decide +kernel
lemma column45_1_r0_8_eq : ∀ k : Fin 16, column45_1Expr 0 8 k = column45_1_r0_8 k := by decide +kernel
lemma column45_1_r0_9_eq : ∀ k : Fin 16, column45_1Expr 0 9 k = column45_1_r0_9 k := by decide +kernel
lemma column45_1_r0_10_eq : ∀ k : Fin 16, column45_1Expr 0 10 k = column45_1_r0_10 k := by decide +kernel
lemma column45_1_r0_11_eq : ∀ k : Fin 16, column45_1Expr 0 11 k = column45_1_r0_11 k := by decide +kernel
lemma column45_1_r0_12_eq : ∀ k : Fin 16, column45_1Expr 0 12 k = column45_1_r0_12 k := by decide +kernel
lemma column45_1_r0_13_eq : ∀ k : Fin 16, column45_1Expr 0 13 k = column45_1_r0_13 k := by decide +kernel
lemma column45_1_r0_14_eq : ∀ k : Fin 16, column45_1Expr 0 14 k = column45_1_r0_14 k := by decide +kernel
lemma column45_1_r0_15_eq : ∀ k : Fin 16, column45_1Expr 0 15 k = column45_1_r0_15 k := by decide +kernel
lemma column45_1_r0_eq (i k : Fin 16) : column45_1Expr 0 i k = column45_1_r0 i k := by
  fin_cases i
  · exact column45_1_r0_0_eq k
  · exact column45_1_r0_1_eq k
  · exact column45_1_r0_2_eq k
  · exact column45_1_r0_3_eq k
  · exact column45_1_r0_4_eq k
  · exact column45_1_r0_5_eq k
  · exact column45_1_r0_6_eq k
  · exact column45_1_r0_7_eq k
  · exact column45_1_r0_8_eq k
  · exact column45_1_r0_9_eq k
  · exact column45_1_r0_10_eq k
  · exact column45_1_r0_11_eq k
  · exact column45_1_r0_12_eq k
  · exact column45_1_r0_13_eq k
  · exact column45_1_r0_14_eq k
  · exact column45_1_r0_15_eq k
lemma column45_1_r1_0_eq : ∀ k : Fin 16, column45_1Expr 1 0 k = column45_1_r1_0 k := by decide +kernel
lemma column45_1_r1_1_eq : ∀ k : Fin 16, column45_1Expr 1 1 k = column45_1_r1_1 k := by decide +kernel
lemma column45_1_r1_2_eq : ∀ k : Fin 16, column45_1Expr 1 2 k = column45_1_r1_2 k := by decide +kernel
lemma column45_1_r1_3_eq : ∀ k : Fin 16, column45_1Expr 1 3 k = column45_1_r1_3 k := by decide +kernel
lemma column45_1_r1_4_eq : ∀ k : Fin 16, column45_1Expr 1 4 k = column45_1_r1_4 k := by decide +kernel
lemma column45_1_r1_5_eq : ∀ k : Fin 16, column45_1Expr 1 5 k = column45_1_r1_5 k := by decide +kernel
lemma column45_1_r1_6_eq : ∀ k : Fin 16, column45_1Expr 1 6 k = column45_1_r1_6 k := by decide +kernel
lemma column45_1_r1_7_eq : ∀ k : Fin 16, column45_1Expr 1 7 k = column45_1_r1_7 k := by decide +kernel
lemma column45_1_r1_8_eq : ∀ k : Fin 16, column45_1Expr 1 8 k = column45_1_r1_8 k := by decide +kernel
lemma column45_1_r1_9_eq : ∀ k : Fin 16, column45_1Expr 1 9 k = column45_1_r1_9 k := by decide +kernel
lemma column45_1_r1_10_eq : ∀ k : Fin 16, column45_1Expr 1 10 k = column45_1_r1_10 k := by decide +kernel
lemma column45_1_r1_11_eq : ∀ k : Fin 16, column45_1Expr 1 11 k = column45_1_r1_11 k := by decide +kernel
lemma column45_1_r1_12_eq : ∀ k : Fin 16, column45_1Expr 1 12 k = column45_1_r1_12 k := by decide +kernel
lemma column45_1_r1_13_eq : ∀ k : Fin 16, column45_1Expr 1 13 k = column45_1_r1_13 k := by decide +kernel
lemma column45_1_r1_14_eq : ∀ k : Fin 16, column45_1Expr 1 14 k = column45_1_r1_14 k := by decide +kernel
lemma column45_1_r1_15_eq : ∀ k : Fin 16, column45_1Expr 1 15 k = column45_1_r1_15 k := by decide +kernel
lemma column45_1_r1_eq (i k : Fin 16) : column45_1Expr 1 i k = column45_1_r1 i k := by
  fin_cases i
  · exact column45_1_r1_0_eq k
  · exact column45_1_r1_1_eq k
  · exact column45_1_r1_2_eq k
  · exact column45_1_r1_3_eq k
  · exact column45_1_r1_4_eq k
  · exact column45_1_r1_5_eq k
  · exact column45_1_r1_6_eq k
  · exact column45_1_r1_7_eq k
  · exact column45_1_r1_8_eq k
  · exact column45_1_r1_9_eq k
  · exact column45_1_r1_10_eq k
  · exact column45_1_r1_11_eq k
  · exact column45_1_r1_12_eq k
  · exact column45_1_r1_13_eq k
  · exact column45_1_r1_14_eq k
  · exact column45_1_r1_15_eq k
lemma column45_1_r2_0_eq : ∀ k : Fin 16, column45_1Expr 2 0 k = column45_1_r2_0 k := by decide +kernel
lemma column45_1_r2_1_eq : ∀ k : Fin 16, column45_1Expr 2 1 k = column45_1_r2_1 k := by decide +kernel
lemma column45_1_r2_2_eq : ∀ k : Fin 16, column45_1Expr 2 2 k = column45_1_r2_2 k := by decide +kernel
lemma column45_1_r2_3_eq : ∀ k : Fin 16, column45_1Expr 2 3 k = column45_1_r2_3 k := by decide +kernel
lemma column45_1_r2_4_eq : ∀ k : Fin 16, column45_1Expr 2 4 k = column45_1_r2_4 k := by decide +kernel
lemma column45_1_r2_5_eq : ∀ k : Fin 16, column45_1Expr 2 5 k = column45_1_r2_5 k := by decide +kernel
lemma column45_1_r2_6_eq : ∀ k : Fin 16, column45_1Expr 2 6 k = column45_1_r2_6 k := by decide +kernel
lemma column45_1_r2_7_eq : ∀ k : Fin 16, column45_1Expr 2 7 k = column45_1_r2_7 k := by decide +kernel
lemma column45_1_r2_8_eq : ∀ k : Fin 16, column45_1Expr 2 8 k = column45_1_r2_8 k := by decide +kernel
lemma column45_1_r2_9_eq : ∀ k : Fin 16, column45_1Expr 2 9 k = column45_1_r2_9 k := by decide +kernel
lemma column45_1_r2_10_eq : ∀ k : Fin 16, column45_1Expr 2 10 k = column45_1_r2_10 k := by decide +kernel
lemma column45_1_r2_11_eq : ∀ k : Fin 16, column45_1Expr 2 11 k = column45_1_r2_11 k := by decide +kernel
lemma column45_1_r2_12_eq : ∀ k : Fin 16, column45_1Expr 2 12 k = column45_1_r2_12 k := by decide +kernel
lemma column45_1_r2_13_eq : ∀ k : Fin 16, column45_1Expr 2 13 k = column45_1_r2_13 k := by decide +kernel
lemma column45_1_r2_14_eq : ∀ k : Fin 16, column45_1Expr 2 14 k = column45_1_r2_14 k := by decide +kernel
lemma column45_1_r2_15_eq : ∀ k : Fin 16, column45_1Expr 2 15 k = column45_1_r2_15 k := by decide +kernel
lemma column45_1_r2_eq (i k : Fin 16) : column45_1Expr 2 i k = column45_1_r2 i k := by
  fin_cases i
  · exact column45_1_r2_0_eq k
  · exact column45_1_r2_1_eq k
  · exact column45_1_r2_2_eq k
  · exact column45_1_r2_3_eq k
  · exact column45_1_r2_4_eq k
  · exact column45_1_r2_5_eq k
  · exact column45_1_r2_6_eq k
  · exact column45_1_r2_7_eq k
  · exact column45_1_r2_8_eq k
  · exact column45_1_r2_9_eq k
  · exact column45_1_r2_10_eq k
  · exact column45_1_r2_11_eq k
  · exact column45_1_r2_12_eq k
  · exact column45_1_r2_13_eq k
  · exact column45_1_r2_14_eq k
  · exact column45_1_r2_15_eq k
lemma column45_1_r3_0_eq : ∀ k : Fin 16, column45_1Expr 3 0 k = column45_1_r3_0 k := by decide +kernel
lemma column45_1_r3_1_eq : ∀ k : Fin 16, column45_1Expr 3 1 k = column45_1_r3_1 k := by decide +kernel
lemma column45_1_r3_2_eq : ∀ k : Fin 16, column45_1Expr 3 2 k = column45_1_r3_2 k := by decide +kernel
lemma column45_1_r3_3_eq : ∀ k : Fin 16, column45_1Expr 3 3 k = column45_1_r3_3 k := by decide +kernel
lemma column45_1_r3_4_eq : ∀ k : Fin 16, column45_1Expr 3 4 k = column45_1_r3_4 k := by decide +kernel
lemma column45_1_r3_5_eq : ∀ k : Fin 16, column45_1Expr 3 5 k = column45_1_r3_5 k := by decide +kernel
lemma column45_1_r3_6_eq : ∀ k : Fin 16, column45_1Expr 3 6 k = column45_1_r3_6 k := by decide +kernel
lemma column45_1_r3_7_eq : ∀ k : Fin 16, column45_1Expr 3 7 k = column45_1_r3_7 k := by decide +kernel
lemma column45_1_r3_8_eq : ∀ k : Fin 16, column45_1Expr 3 8 k = column45_1_r3_8 k := by decide +kernel
lemma column45_1_r3_9_eq : ∀ k : Fin 16, column45_1Expr 3 9 k = column45_1_r3_9 k := by decide +kernel
lemma column45_1_r3_10_eq : ∀ k : Fin 16, column45_1Expr 3 10 k = column45_1_r3_10 k := by decide +kernel
lemma column45_1_r3_11_eq : ∀ k : Fin 16, column45_1Expr 3 11 k = column45_1_r3_11 k := by decide +kernel
lemma column45_1_r3_12_eq : ∀ k : Fin 16, column45_1Expr 3 12 k = column45_1_r3_12 k := by decide +kernel
lemma column45_1_r3_13_eq : ∀ k : Fin 16, column45_1Expr 3 13 k = column45_1_r3_13 k := by decide +kernel
lemma column45_1_r3_14_eq : ∀ k : Fin 16, column45_1Expr 3 14 k = column45_1_r3_14 k := by decide +kernel
lemma column45_1_r3_15_eq : ∀ k : Fin 16, column45_1Expr 3 15 k = column45_1_r3_15 k := by decide +kernel
lemma column45_1_r3_eq (i k : Fin 16) : column45_1Expr 3 i k = column45_1_r3 i k := by
  fin_cases i
  · exact column45_1_r3_0_eq k
  · exact column45_1_r3_1_eq k
  · exact column45_1_r3_2_eq k
  · exact column45_1_r3_3_eq k
  · exact column45_1_r3_4_eq k
  · exact column45_1_r3_5_eq k
  · exact column45_1_r3_6_eq k
  · exact column45_1_r3_7_eq k
  · exact column45_1_r3_8_eq k
  · exact column45_1_r3_9_eq k
  · exact column45_1_r3_10_eq k
  · exact column45_1_r3_11_eq k
  · exact column45_1_r3_12_eq k
  · exact column45_1_r3_13_eq k
  · exact column45_1_r3_14_eq k
  · exact column45_1_r3_15_eq k
lemma column45_1_r4_0_eq : ∀ k : Fin 16, column45_1Expr 4 0 k = column45_1_r4_0 k := by decide +kernel
lemma column45_1_r4_1_eq : ∀ k : Fin 16, column45_1Expr 4 1 k = column45_1_r4_1 k := by decide +kernel
lemma column45_1_r4_2_eq : ∀ k : Fin 16, column45_1Expr 4 2 k = column45_1_r4_2 k := by decide +kernel
lemma column45_1_r4_3_eq : ∀ k : Fin 16, column45_1Expr 4 3 k = column45_1_r4_3 k := by decide +kernel
lemma column45_1_r4_4_eq : ∀ k : Fin 16, column45_1Expr 4 4 k = column45_1_r4_4 k := by decide +kernel
lemma column45_1_r4_5_eq : ∀ k : Fin 16, column45_1Expr 4 5 k = column45_1_r4_5 k := by decide +kernel
lemma column45_1_r4_6_eq : ∀ k : Fin 16, column45_1Expr 4 6 k = column45_1_r4_6 k := by decide +kernel
lemma column45_1_r4_7_eq : ∀ k : Fin 16, column45_1Expr 4 7 k = column45_1_r4_7 k := by decide +kernel
lemma column45_1_r4_8_eq : ∀ k : Fin 16, column45_1Expr 4 8 k = column45_1_r4_8 k := by decide +kernel
lemma column45_1_r4_9_eq : ∀ k : Fin 16, column45_1Expr 4 9 k = column45_1_r4_9 k := by decide +kernel
lemma column45_1_r4_10_eq : ∀ k : Fin 16, column45_1Expr 4 10 k = column45_1_r4_10 k := by decide +kernel
lemma column45_1_r4_11_eq : ∀ k : Fin 16, column45_1Expr 4 11 k = column45_1_r4_11 k := by decide +kernel
lemma column45_1_r4_12_eq : ∀ k : Fin 16, column45_1Expr 4 12 k = column45_1_r4_12 k := by decide +kernel
lemma column45_1_r4_13_eq : ∀ k : Fin 16, column45_1Expr 4 13 k = column45_1_r4_13 k := by decide +kernel
lemma column45_1_r4_14_eq : ∀ k : Fin 16, column45_1Expr 4 14 k = column45_1_r4_14 k := by decide +kernel
lemma column45_1_r4_15_eq : ∀ k : Fin 16, column45_1Expr 4 15 k = column45_1_r4_15 k := by decide +kernel
lemma column45_1_r4_eq (i k : Fin 16) : column45_1Expr 4 i k = column45_1_r4 i k := by
  fin_cases i
  · exact column45_1_r4_0_eq k
  · exact column45_1_r4_1_eq k
  · exact column45_1_r4_2_eq k
  · exact column45_1_r4_3_eq k
  · exact column45_1_r4_4_eq k
  · exact column45_1_r4_5_eq k
  · exact column45_1_r4_6_eq k
  · exact column45_1_r4_7_eq k
  · exact column45_1_r4_8_eq k
  · exact column45_1_r4_9_eq k
  · exact column45_1_r4_10_eq k
  · exact column45_1_r4_11_eq k
  · exact column45_1_r4_12_eq k
  · exact column45_1_r4_13_eq k
  · exact column45_1_r4_14_eq k
  · exact column45_1_r4_15_eq k
lemma column45_1_r5_0_eq : ∀ k : Fin 16, column45_1Expr 5 0 k = column45_1_r5_0 k := by decide +kernel
lemma column45_1_r5_1_eq : ∀ k : Fin 16, column45_1Expr 5 1 k = column45_1_r5_1 k := by decide +kernel
lemma column45_1_r5_2_eq : ∀ k : Fin 16, column45_1Expr 5 2 k = column45_1_r5_2 k := by decide +kernel
lemma column45_1_r5_3_eq : ∀ k : Fin 16, column45_1Expr 5 3 k = column45_1_r5_3 k := by decide +kernel
lemma column45_1_r5_4_eq : ∀ k : Fin 16, column45_1Expr 5 4 k = column45_1_r5_4 k := by decide +kernel
lemma column45_1_r5_5_eq : ∀ k : Fin 16, column45_1Expr 5 5 k = column45_1_r5_5 k := by decide +kernel
lemma column45_1_r5_6_eq : ∀ k : Fin 16, column45_1Expr 5 6 k = column45_1_r5_6 k := by decide +kernel
lemma column45_1_r5_7_eq : ∀ k : Fin 16, column45_1Expr 5 7 k = column45_1_r5_7 k := by decide +kernel
lemma column45_1_r5_8_eq : ∀ k : Fin 16, column45_1Expr 5 8 k = column45_1_r5_8 k := by decide +kernel
lemma column45_1_r5_9_eq : ∀ k : Fin 16, column45_1Expr 5 9 k = column45_1_r5_9 k := by decide +kernel
lemma column45_1_r5_10_eq : ∀ k : Fin 16, column45_1Expr 5 10 k = column45_1_r5_10 k := by decide +kernel
lemma column45_1_r5_11_eq : ∀ k : Fin 16, column45_1Expr 5 11 k = column45_1_r5_11 k := by decide +kernel
lemma column45_1_r5_12_eq : ∀ k : Fin 16, column45_1Expr 5 12 k = column45_1_r5_12 k := by decide +kernel
lemma column45_1_r5_13_eq : ∀ k : Fin 16, column45_1Expr 5 13 k = column45_1_r5_13 k := by decide +kernel
lemma column45_1_r5_14_eq : ∀ k : Fin 16, column45_1Expr 5 14 k = column45_1_r5_14 k := by decide +kernel
lemma column45_1_r5_15_eq : ∀ k : Fin 16, column45_1Expr 5 15 k = column45_1_r5_15 k := by decide +kernel
lemma column45_1_r5_eq (i k : Fin 16) : column45_1Expr 5 i k = column45_1_r5 i k := by
  fin_cases i
  · exact column45_1_r5_0_eq k
  · exact column45_1_r5_1_eq k
  · exact column45_1_r5_2_eq k
  · exact column45_1_r5_3_eq k
  · exact column45_1_r5_4_eq k
  · exact column45_1_r5_5_eq k
  · exact column45_1_r5_6_eq k
  · exact column45_1_r5_7_eq k
  · exact column45_1_r5_8_eq k
  · exact column45_1_r5_9_eq k
  · exact column45_1_r5_10_eq k
  · exact column45_1_r5_11_eq k
  · exact column45_1_r5_12_eq k
  · exact column45_1_r5_13_eq k
  · exact column45_1_r5_14_eq k
  · exact column45_1_r5_15_eq k
lemma column45_1_eq (j : Fin 6) (i k : Fin 16) : column45_1Expr j i k = column45_1 j i k := by
  fin_cases j
  · exact column45_1_r0_eq i k
  · exact column45_1_r1_eq i k
  · exact column45_1_r2_eq i k
  · exact column45_1_r3_eq i k
  · exact column45_1_r4_eq i k
  · exact column45_1_r5_eq i k
noncomputable def column48_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power48 j i k)
lemma column48_0_r0_0_eq : ∀ k : Fin 16, column48_0Expr 0 0 k = column48_0_r0_0 k := by decide +kernel
lemma column48_0_r0_1_eq : ∀ k : Fin 16, column48_0Expr 0 1 k = column48_0_r0_1 k := by decide +kernel
lemma column48_0_r0_2_eq : ∀ k : Fin 16, column48_0Expr 0 2 k = column48_0_r0_2 k := by decide +kernel
lemma column48_0_r0_3_eq : ∀ k : Fin 16, column48_0Expr 0 3 k = column48_0_r0_3 k := by decide +kernel
lemma column48_0_r0_4_eq : ∀ k : Fin 16, column48_0Expr 0 4 k = column48_0_r0_4 k := by decide +kernel
lemma column48_0_r0_5_eq : ∀ k : Fin 16, column48_0Expr 0 5 k = column48_0_r0_5 k := by decide +kernel
lemma column48_0_r0_6_eq : ∀ k : Fin 16, column48_0Expr 0 6 k = column48_0_r0_6 k := by decide +kernel
lemma column48_0_r0_7_eq : ∀ k : Fin 16, column48_0Expr 0 7 k = column48_0_r0_7 k := by decide +kernel
lemma column48_0_r0_8_eq : ∀ k : Fin 16, column48_0Expr 0 8 k = column48_0_r0_8 k := by decide +kernel
lemma column48_0_r0_9_eq : ∀ k : Fin 16, column48_0Expr 0 9 k = column48_0_r0_9 k := by decide +kernel
lemma column48_0_r0_10_eq : ∀ k : Fin 16, column48_0Expr 0 10 k = column48_0_r0_10 k := by decide +kernel
lemma column48_0_r0_11_eq : ∀ k : Fin 16, column48_0Expr 0 11 k = column48_0_r0_11 k := by decide +kernel
lemma column48_0_r0_12_eq : ∀ k : Fin 16, column48_0Expr 0 12 k = column48_0_r0_12 k := by decide +kernel
lemma column48_0_r0_13_eq : ∀ k : Fin 16, column48_0Expr 0 13 k = column48_0_r0_13 k := by decide +kernel
lemma column48_0_r0_14_eq : ∀ k : Fin 16, column48_0Expr 0 14 k = column48_0_r0_14 k := by decide +kernel
lemma column48_0_r0_15_eq : ∀ k : Fin 16, column48_0Expr 0 15 k = column48_0_r0_15 k := by decide +kernel
lemma column48_0_r0_eq (i k : Fin 16) : column48_0Expr 0 i k = column48_0_r0 i k := by
  fin_cases i
  · exact column48_0_r0_0_eq k
  · exact column48_0_r0_1_eq k
  · exact column48_0_r0_2_eq k
  · exact column48_0_r0_3_eq k
  · exact column48_0_r0_4_eq k
  · exact column48_0_r0_5_eq k
  · exact column48_0_r0_6_eq k
  · exact column48_0_r0_7_eq k
  · exact column48_0_r0_8_eq k
  · exact column48_0_r0_9_eq k
  · exact column48_0_r0_10_eq k
  · exact column48_0_r0_11_eq k
  · exact column48_0_r0_12_eq k
  · exact column48_0_r0_13_eq k
  · exact column48_0_r0_14_eq k
  · exact column48_0_r0_15_eq k
lemma column48_0_r1_0_eq : ∀ k : Fin 16, column48_0Expr 1 0 k = column48_0_r1_0 k := by decide +kernel
lemma column48_0_r1_1_eq : ∀ k : Fin 16, column48_0Expr 1 1 k = column48_0_r1_1 k := by decide +kernel
lemma column48_0_r1_2_eq : ∀ k : Fin 16, column48_0Expr 1 2 k = column48_0_r1_2 k := by decide +kernel
lemma column48_0_r1_3_eq : ∀ k : Fin 16, column48_0Expr 1 3 k = column48_0_r1_3 k := by decide +kernel
lemma column48_0_r1_4_eq : ∀ k : Fin 16, column48_0Expr 1 4 k = column48_0_r1_4 k := by decide +kernel
lemma column48_0_r1_5_eq : ∀ k : Fin 16, column48_0Expr 1 5 k = column48_0_r1_5 k := by decide +kernel
lemma column48_0_r1_6_eq : ∀ k : Fin 16, column48_0Expr 1 6 k = column48_0_r1_6 k := by decide +kernel
lemma column48_0_r1_7_eq : ∀ k : Fin 16, column48_0Expr 1 7 k = column48_0_r1_7 k := by decide +kernel
lemma column48_0_r1_8_eq : ∀ k : Fin 16, column48_0Expr 1 8 k = column48_0_r1_8 k := by decide +kernel
lemma column48_0_r1_9_eq : ∀ k : Fin 16, column48_0Expr 1 9 k = column48_0_r1_9 k := by decide +kernel
lemma column48_0_r1_10_eq : ∀ k : Fin 16, column48_0Expr 1 10 k = column48_0_r1_10 k := by decide +kernel
lemma column48_0_r1_11_eq : ∀ k : Fin 16, column48_0Expr 1 11 k = column48_0_r1_11 k := by decide +kernel
lemma column48_0_r1_12_eq : ∀ k : Fin 16, column48_0Expr 1 12 k = column48_0_r1_12 k := by decide +kernel
lemma column48_0_r1_13_eq : ∀ k : Fin 16, column48_0Expr 1 13 k = column48_0_r1_13 k := by decide +kernel
lemma column48_0_r1_14_eq : ∀ k : Fin 16, column48_0Expr 1 14 k = column48_0_r1_14 k := by decide +kernel
lemma column48_0_r1_15_eq : ∀ k : Fin 16, column48_0Expr 1 15 k = column48_0_r1_15 k := by decide +kernel
lemma column48_0_r1_eq (i k : Fin 16) : column48_0Expr 1 i k = column48_0_r1 i k := by
  fin_cases i
  · exact column48_0_r1_0_eq k
  · exact column48_0_r1_1_eq k
  · exact column48_0_r1_2_eq k
  · exact column48_0_r1_3_eq k
  · exact column48_0_r1_4_eq k
  · exact column48_0_r1_5_eq k
  · exact column48_0_r1_6_eq k
  · exact column48_0_r1_7_eq k
  · exact column48_0_r1_8_eq k
  · exact column48_0_r1_9_eq k
  · exact column48_0_r1_10_eq k
  · exact column48_0_r1_11_eq k
  · exact column48_0_r1_12_eq k
  · exact column48_0_r1_13_eq k
  · exact column48_0_r1_14_eq k
  · exact column48_0_r1_15_eq k
lemma column48_0_r2_0_eq : ∀ k : Fin 16, column48_0Expr 2 0 k = column48_0_r2_0 k := by decide +kernel
lemma column48_0_r2_1_eq : ∀ k : Fin 16, column48_0Expr 2 1 k = column48_0_r2_1 k := by decide +kernel
lemma column48_0_r2_2_eq : ∀ k : Fin 16, column48_0Expr 2 2 k = column48_0_r2_2 k := by decide +kernel
lemma column48_0_r2_3_eq : ∀ k : Fin 16, column48_0Expr 2 3 k = column48_0_r2_3 k := by decide +kernel
lemma column48_0_r2_4_eq : ∀ k : Fin 16, column48_0Expr 2 4 k = column48_0_r2_4 k := by decide +kernel
lemma column48_0_r2_5_eq : ∀ k : Fin 16, column48_0Expr 2 5 k = column48_0_r2_5 k := by decide +kernel
lemma column48_0_r2_6_eq : ∀ k : Fin 16, column48_0Expr 2 6 k = column48_0_r2_6 k := by decide +kernel
lemma column48_0_r2_7_eq : ∀ k : Fin 16, column48_0Expr 2 7 k = column48_0_r2_7 k := by decide +kernel
lemma column48_0_r2_8_eq : ∀ k : Fin 16, column48_0Expr 2 8 k = column48_0_r2_8 k := by decide +kernel
lemma column48_0_r2_9_eq : ∀ k : Fin 16, column48_0Expr 2 9 k = column48_0_r2_9 k := by decide +kernel
lemma column48_0_r2_10_eq : ∀ k : Fin 16, column48_0Expr 2 10 k = column48_0_r2_10 k := by decide +kernel
lemma column48_0_r2_11_eq : ∀ k : Fin 16, column48_0Expr 2 11 k = column48_0_r2_11 k := by decide +kernel
lemma column48_0_r2_12_eq : ∀ k : Fin 16, column48_0Expr 2 12 k = column48_0_r2_12 k := by decide +kernel
lemma column48_0_r2_13_eq : ∀ k : Fin 16, column48_0Expr 2 13 k = column48_0_r2_13 k := by decide +kernel
lemma column48_0_r2_14_eq : ∀ k : Fin 16, column48_0Expr 2 14 k = column48_0_r2_14 k := by decide +kernel
lemma column48_0_r2_15_eq : ∀ k : Fin 16, column48_0Expr 2 15 k = column48_0_r2_15 k := by decide +kernel
lemma column48_0_r2_eq (i k : Fin 16) : column48_0Expr 2 i k = column48_0_r2 i k := by
  fin_cases i
  · exact column48_0_r2_0_eq k
  · exact column48_0_r2_1_eq k
  · exact column48_0_r2_2_eq k
  · exact column48_0_r2_3_eq k
  · exact column48_0_r2_4_eq k
  · exact column48_0_r2_5_eq k
  · exact column48_0_r2_6_eq k
  · exact column48_0_r2_7_eq k
  · exact column48_0_r2_8_eq k
  · exact column48_0_r2_9_eq k
  · exact column48_0_r2_10_eq k
  · exact column48_0_r2_11_eq k
  · exact column48_0_r2_12_eq k
  · exact column48_0_r2_13_eq k
  · exact column48_0_r2_14_eq k
  · exact column48_0_r2_15_eq k
lemma column48_0_r3_0_eq : ∀ k : Fin 16, column48_0Expr 3 0 k = column48_0_r3_0 k := by decide +kernel
lemma column48_0_r3_1_eq : ∀ k : Fin 16, column48_0Expr 3 1 k = column48_0_r3_1 k := by decide +kernel
lemma column48_0_r3_2_eq : ∀ k : Fin 16, column48_0Expr 3 2 k = column48_0_r3_2 k := by decide +kernel
lemma column48_0_r3_3_eq : ∀ k : Fin 16, column48_0Expr 3 3 k = column48_0_r3_3 k := by decide +kernel
lemma column48_0_r3_4_eq : ∀ k : Fin 16, column48_0Expr 3 4 k = column48_0_r3_4 k := by decide +kernel
lemma column48_0_r3_5_eq : ∀ k : Fin 16, column48_0Expr 3 5 k = column48_0_r3_5 k := by decide +kernel
lemma column48_0_r3_6_eq : ∀ k : Fin 16, column48_0Expr 3 6 k = column48_0_r3_6 k := by decide +kernel
lemma column48_0_r3_7_eq : ∀ k : Fin 16, column48_0Expr 3 7 k = column48_0_r3_7 k := by decide +kernel
lemma column48_0_r3_8_eq : ∀ k : Fin 16, column48_0Expr 3 8 k = column48_0_r3_8 k := by decide +kernel
lemma column48_0_r3_9_eq : ∀ k : Fin 16, column48_0Expr 3 9 k = column48_0_r3_9 k := by decide +kernel
lemma column48_0_r3_10_eq : ∀ k : Fin 16, column48_0Expr 3 10 k = column48_0_r3_10 k := by decide +kernel
lemma column48_0_r3_11_eq : ∀ k : Fin 16, column48_0Expr 3 11 k = column48_0_r3_11 k := by decide +kernel
lemma column48_0_r3_12_eq : ∀ k : Fin 16, column48_0Expr 3 12 k = column48_0_r3_12 k := by decide +kernel
lemma column48_0_r3_13_eq : ∀ k : Fin 16, column48_0Expr 3 13 k = column48_0_r3_13 k := by decide +kernel
lemma column48_0_r3_14_eq : ∀ k : Fin 16, column48_0Expr 3 14 k = column48_0_r3_14 k := by decide +kernel
lemma column48_0_r3_15_eq : ∀ k : Fin 16, column48_0Expr 3 15 k = column48_0_r3_15 k := by decide +kernel
lemma column48_0_r3_eq (i k : Fin 16) : column48_0Expr 3 i k = column48_0_r3 i k := by
  fin_cases i
  · exact column48_0_r3_0_eq k
  · exact column48_0_r3_1_eq k
  · exact column48_0_r3_2_eq k
  · exact column48_0_r3_3_eq k
  · exact column48_0_r3_4_eq k
  · exact column48_0_r3_5_eq k
  · exact column48_0_r3_6_eq k
  · exact column48_0_r3_7_eq k
  · exact column48_0_r3_8_eq k
  · exact column48_0_r3_9_eq k
  · exact column48_0_r3_10_eq k
  · exact column48_0_r3_11_eq k
  · exact column48_0_r3_12_eq k
  · exact column48_0_r3_13_eq k
  · exact column48_0_r3_14_eq k
  · exact column48_0_r3_15_eq k
lemma column48_0_r4_0_eq : ∀ k : Fin 16, column48_0Expr 4 0 k = column48_0_r4_0 k := by decide +kernel
lemma column48_0_r4_1_eq : ∀ k : Fin 16, column48_0Expr 4 1 k = column48_0_r4_1 k := by decide +kernel
lemma column48_0_r4_2_eq : ∀ k : Fin 16, column48_0Expr 4 2 k = column48_0_r4_2 k := by decide +kernel
lemma column48_0_r4_3_eq : ∀ k : Fin 16, column48_0Expr 4 3 k = column48_0_r4_3 k := by decide +kernel
lemma column48_0_r4_4_eq : ∀ k : Fin 16, column48_0Expr 4 4 k = column48_0_r4_4 k := by decide +kernel
lemma column48_0_r4_5_eq : ∀ k : Fin 16, column48_0Expr 4 5 k = column48_0_r4_5 k := by decide +kernel
lemma column48_0_r4_6_eq : ∀ k : Fin 16, column48_0Expr 4 6 k = column48_0_r4_6 k := by decide +kernel
lemma column48_0_r4_7_eq : ∀ k : Fin 16, column48_0Expr 4 7 k = column48_0_r4_7 k := by decide +kernel
lemma column48_0_r4_8_eq : ∀ k : Fin 16, column48_0Expr 4 8 k = column48_0_r4_8 k := by decide +kernel
lemma column48_0_r4_9_eq : ∀ k : Fin 16, column48_0Expr 4 9 k = column48_0_r4_9 k := by decide +kernel
lemma column48_0_r4_10_eq : ∀ k : Fin 16, column48_0Expr 4 10 k = column48_0_r4_10 k := by decide +kernel
lemma column48_0_r4_11_eq : ∀ k : Fin 16, column48_0Expr 4 11 k = column48_0_r4_11 k := by decide +kernel
lemma column48_0_r4_12_eq : ∀ k : Fin 16, column48_0Expr 4 12 k = column48_0_r4_12 k := by decide +kernel
lemma column48_0_r4_13_eq : ∀ k : Fin 16, column48_0Expr 4 13 k = column48_0_r4_13 k := by decide +kernel
lemma column48_0_r4_14_eq : ∀ k : Fin 16, column48_0Expr 4 14 k = column48_0_r4_14 k := by decide +kernel
lemma column48_0_r4_15_eq : ∀ k : Fin 16, column48_0Expr 4 15 k = column48_0_r4_15 k := by decide +kernel
lemma column48_0_r4_eq (i k : Fin 16) : column48_0Expr 4 i k = column48_0_r4 i k := by
  fin_cases i
  · exact column48_0_r4_0_eq k
  · exact column48_0_r4_1_eq k
  · exact column48_0_r4_2_eq k
  · exact column48_0_r4_3_eq k
  · exact column48_0_r4_4_eq k
  · exact column48_0_r4_5_eq k
  · exact column48_0_r4_6_eq k
  · exact column48_0_r4_7_eq k
  · exact column48_0_r4_8_eq k
  · exact column48_0_r4_9_eq k
  · exact column48_0_r4_10_eq k
  · exact column48_0_r4_11_eq k
  · exact column48_0_r4_12_eq k
  · exact column48_0_r4_13_eq k
  · exact column48_0_r4_14_eq k
  · exact column48_0_r4_15_eq k
lemma column48_0_r5_0_eq : ∀ k : Fin 16, column48_0Expr 5 0 k = column48_0_r5_0 k := by decide +kernel
lemma column48_0_r5_1_eq : ∀ k : Fin 16, column48_0Expr 5 1 k = column48_0_r5_1 k := by decide +kernel
lemma column48_0_r5_2_eq : ∀ k : Fin 16, column48_0Expr 5 2 k = column48_0_r5_2 k := by decide +kernel
lemma column48_0_r5_3_eq : ∀ k : Fin 16, column48_0Expr 5 3 k = column48_0_r5_3 k := by decide +kernel
lemma column48_0_r5_4_eq : ∀ k : Fin 16, column48_0Expr 5 4 k = column48_0_r5_4 k := by decide +kernel
lemma column48_0_r5_5_eq : ∀ k : Fin 16, column48_0Expr 5 5 k = column48_0_r5_5 k := by decide +kernel
lemma column48_0_r5_6_eq : ∀ k : Fin 16, column48_0Expr 5 6 k = column48_0_r5_6 k := by decide +kernel
lemma column48_0_r5_7_eq : ∀ k : Fin 16, column48_0Expr 5 7 k = column48_0_r5_7 k := by decide +kernel
lemma column48_0_r5_8_eq : ∀ k : Fin 16, column48_0Expr 5 8 k = column48_0_r5_8 k := by decide +kernel
lemma column48_0_r5_9_eq : ∀ k : Fin 16, column48_0Expr 5 9 k = column48_0_r5_9 k := by decide +kernel
lemma column48_0_r5_10_eq : ∀ k : Fin 16, column48_0Expr 5 10 k = column48_0_r5_10 k := by decide +kernel
lemma column48_0_r5_11_eq : ∀ k : Fin 16, column48_0Expr 5 11 k = column48_0_r5_11 k := by decide +kernel
lemma column48_0_r5_12_eq : ∀ k : Fin 16, column48_0Expr 5 12 k = column48_0_r5_12 k := by decide +kernel
lemma column48_0_r5_13_eq : ∀ k : Fin 16, column48_0Expr 5 13 k = column48_0_r5_13 k := by decide +kernel
lemma column48_0_r5_14_eq : ∀ k : Fin 16, column48_0Expr 5 14 k = column48_0_r5_14 k := by decide +kernel
lemma column48_0_r5_15_eq : ∀ k : Fin 16, column48_0Expr 5 15 k = column48_0_r5_15 k := by decide +kernel
lemma column48_0_r5_eq (i k : Fin 16) : column48_0Expr 5 i k = column48_0_r5 i k := by
  fin_cases i
  · exact column48_0_r5_0_eq k
  · exact column48_0_r5_1_eq k
  · exact column48_0_r5_2_eq k
  · exact column48_0_r5_3_eq k
  · exact column48_0_r5_4_eq k
  · exact column48_0_r5_5_eq k
  · exact column48_0_r5_6_eq k
  · exact column48_0_r5_7_eq k
  · exact column48_0_r5_8_eq k
  · exact column48_0_r5_9_eq k
  · exact column48_0_r5_10_eq k
  · exact column48_0_r5_11_eq k
  · exact column48_0_r5_12_eq k
  · exact column48_0_r5_13_eq k
  · exact column48_0_r5_14_eq k
  · exact column48_0_r5_15_eq k
noncomputable def column48_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power48 j i k)
lemma column48_1_r0_0_eq : ∀ k : Fin 16, column48_1Expr 0 0 k = column48_1_r0_0 k := by decide +kernel
lemma column48_1_r0_1_eq : ∀ k : Fin 16, column48_1Expr 0 1 k = column48_1_r0_1 k := by decide +kernel
lemma column48_1_r0_2_eq : ∀ k : Fin 16, column48_1Expr 0 2 k = column48_1_r0_2 k := by decide +kernel
lemma column48_1_r0_3_eq : ∀ k : Fin 16, column48_1Expr 0 3 k = column48_1_r0_3 k := by decide +kernel
lemma column48_1_r0_4_eq : ∀ k : Fin 16, column48_1Expr 0 4 k = column48_1_r0_4 k := by decide +kernel
lemma column48_1_r0_5_eq : ∀ k : Fin 16, column48_1Expr 0 5 k = column48_1_r0_5 k := by decide +kernel
lemma column48_1_r0_6_eq : ∀ k : Fin 16, column48_1Expr 0 6 k = column48_1_r0_6 k := by decide +kernel
lemma column48_1_r0_7_eq : ∀ k : Fin 16, column48_1Expr 0 7 k = column48_1_r0_7 k := by decide +kernel
lemma column48_1_r0_8_eq : ∀ k : Fin 16, column48_1Expr 0 8 k = column48_1_r0_8 k := by decide +kernel
lemma column48_1_r0_9_eq : ∀ k : Fin 16, column48_1Expr 0 9 k = column48_1_r0_9 k := by decide +kernel
lemma column48_1_r0_10_eq : ∀ k : Fin 16, column48_1Expr 0 10 k = column48_1_r0_10 k := by decide +kernel
lemma column48_1_r0_11_eq : ∀ k : Fin 16, column48_1Expr 0 11 k = column48_1_r0_11 k := by decide +kernel
lemma column48_1_r0_12_eq : ∀ k : Fin 16, column48_1Expr 0 12 k = column48_1_r0_12 k := by decide +kernel
lemma column48_1_r0_13_eq : ∀ k : Fin 16, column48_1Expr 0 13 k = column48_1_r0_13 k := by decide +kernel
lemma column48_1_r0_14_eq : ∀ k : Fin 16, column48_1Expr 0 14 k = column48_1_r0_14 k := by decide +kernel
lemma column48_1_r0_15_eq : ∀ k : Fin 16, column48_1Expr 0 15 k = column48_1_r0_15 k := by decide +kernel
lemma column48_1_r0_eq (i k : Fin 16) : column48_1Expr 0 i k = column48_1_r0 i k := by
  fin_cases i
  · exact column48_1_r0_0_eq k
  · exact column48_1_r0_1_eq k
  · exact column48_1_r0_2_eq k
  · exact column48_1_r0_3_eq k
  · exact column48_1_r0_4_eq k
  · exact column48_1_r0_5_eq k
  · exact column48_1_r0_6_eq k
  · exact column48_1_r0_7_eq k
  · exact column48_1_r0_8_eq k
  · exact column48_1_r0_9_eq k
  · exact column48_1_r0_10_eq k
  · exact column48_1_r0_11_eq k
  · exact column48_1_r0_12_eq k
  · exact column48_1_r0_13_eq k
  · exact column48_1_r0_14_eq k
  · exact column48_1_r0_15_eq k
lemma column48_1_r1_0_eq : ∀ k : Fin 16, column48_1Expr 1 0 k = column48_1_r1_0 k := by decide +kernel
lemma column48_1_r1_1_eq : ∀ k : Fin 16, column48_1Expr 1 1 k = column48_1_r1_1 k := by decide +kernel
lemma column48_1_r1_2_eq : ∀ k : Fin 16, column48_1Expr 1 2 k = column48_1_r1_2 k := by decide +kernel
lemma column48_1_r1_3_eq : ∀ k : Fin 16, column48_1Expr 1 3 k = column48_1_r1_3 k := by decide +kernel
lemma column48_1_r1_4_eq : ∀ k : Fin 16, column48_1Expr 1 4 k = column48_1_r1_4 k := by decide +kernel
lemma column48_1_r1_5_eq : ∀ k : Fin 16, column48_1Expr 1 5 k = column48_1_r1_5 k := by decide +kernel
lemma column48_1_r1_6_eq : ∀ k : Fin 16, column48_1Expr 1 6 k = column48_1_r1_6 k := by decide +kernel
lemma column48_1_r1_7_eq : ∀ k : Fin 16, column48_1Expr 1 7 k = column48_1_r1_7 k := by decide +kernel
lemma column48_1_r1_8_eq : ∀ k : Fin 16, column48_1Expr 1 8 k = column48_1_r1_8 k := by decide +kernel
lemma column48_1_r1_9_eq : ∀ k : Fin 16, column48_1Expr 1 9 k = column48_1_r1_9 k := by decide +kernel
lemma column48_1_r1_10_eq : ∀ k : Fin 16, column48_1Expr 1 10 k = column48_1_r1_10 k := by decide +kernel
lemma column48_1_r1_11_eq : ∀ k : Fin 16, column48_1Expr 1 11 k = column48_1_r1_11 k := by decide +kernel
lemma column48_1_r1_12_eq : ∀ k : Fin 16, column48_1Expr 1 12 k = column48_1_r1_12 k := by decide +kernel
lemma column48_1_r1_13_eq : ∀ k : Fin 16, column48_1Expr 1 13 k = column48_1_r1_13 k := by decide +kernel
lemma column48_1_r1_14_eq : ∀ k : Fin 16, column48_1Expr 1 14 k = column48_1_r1_14 k := by decide +kernel
lemma column48_1_r1_15_eq : ∀ k : Fin 16, column48_1Expr 1 15 k = column48_1_r1_15 k := by decide +kernel
lemma column48_1_r1_eq (i k : Fin 16) : column48_1Expr 1 i k = column48_1_r1 i k := by
  fin_cases i
  · exact column48_1_r1_0_eq k
  · exact column48_1_r1_1_eq k
  · exact column48_1_r1_2_eq k
  · exact column48_1_r1_3_eq k
  · exact column48_1_r1_4_eq k
  · exact column48_1_r1_5_eq k
  · exact column48_1_r1_6_eq k
  · exact column48_1_r1_7_eq k
  · exact column48_1_r1_8_eq k
  · exact column48_1_r1_9_eq k
  · exact column48_1_r1_10_eq k
  · exact column48_1_r1_11_eq k
  · exact column48_1_r1_12_eq k
  · exact column48_1_r1_13_eq k
  · exact column48_1_r1_14_eq k
  · exact column48_1_r1_15_eq k
lemma column48_1_r2_0_eq : ∀ k : Fin 16, column48_1Expr 2 0 k = column48_1_r2_0 k := by decide +kernel
lemma column48_1_r2_1_eq : ∀ k : Fin 16, column48_1Expr 2 1 k = column48_1_r2_1 k := by decide +kernel
lemma column48_1_r2_2_eq : ∀ k : Fin 16, column48_1Expr 2 2 k = column48_1_r2_2 k := by decide +kernel
lemma column48_1_r2_3_eq : ∀ k : Fin 16, column48_1Expr 2 3 k = column48_1_r2_3 k := by decide +kernel
lemma column48_1_r2_4_eq : ∀ k : Fin 16, column48_1Expr 2 4 k = column48_1_r2_4 k := by decide +kernel
lemma column48_1_r2_5_eq : ∀ k : Fin 16, column48_1Expr 2 5 k = column48_1_r2_5 k := by decide +kernel
lemma column48_1_r2_6_eq : ∀ k : Fin 16, column48_1Expr 2 6 k = column48_1_r2_6 k := by decide +kernel
lemma column48_1_r2_7_eq : ∀ k : Fin 16, column48_1Expr 2 7 k = column48_1_r2_7 k := by decide +kernel
lemma column48_1_r2_8_eq : ∀ k : Fin 16, column48_1Expr 2 8 k = column48_1_r2_8 k := by decide +kernel
lemma column48_1_r2_9_eq : ∀ k : Fin 16, column48_1Expr 2 9 k = column48_1_r2_9 k := by decide +kernel
lemma column48_1_r2_10_eq : ∀ k : Fin 16, column48_1Expr 2 10 k = column48_1_r2_10 k := by decide +kernel
lemma column48_1_r2_11_eq : ∀ k : Fin 16, column48_1Expr 2 11 k = column48_1_r2_11 k := by decide +kernel
lemma column48_1_r2_12_eq : ∀ k : Fin 16, column48_1Expr 2 12 k = column48_1_r2_12 k := by decide +kernel
lemma column48_1_r2_13_eq : ∀ k : Fin 16, column48_1Expr 2 13 k = column48_1_r2_13 k := by decide +kernel
lemma column48_1_r2_14_eq : ∀ k : Fin 16, column48_1Expr 2 14 k = column48_1_r2_14 k := by decide +kernel
lemma column48_1_r2_15_eq : ∀ k : Fin 16, column48_1Expr 2 15 k = column48_1_r2_15 k := by decide +kernel
lemma column48_1_r2_eq (i k : Fin 16) : column48_1Expr 2 i k = column48_1_r2 i k := by
  fin_cases i
  · exact column48_1_r2_0_eq k
  · exact column48_1_r2_1_eq k
  · exact column48_1_r2_2_eq k
  · exact column48_1_r2_3_eq k
  · exact column48_1_r2_4_eq k
  · exact column48_1_r2_5_eq k
  · exact column48_1_r2_6_eq k
  · exact column48_1_r2_7_eq k
  · exact column48_1_r2_8_eq k
  · exact column48_1_r2_9_eq k
  · exact column48_1_r2_10_eq k
  · exact column48_1_r2_11_eq k
  · exact column48_1_r2_12_eq k
  · exact column48_1_r2_13_eq k
  · exact column48_1_r2_14_eq k
  · exact column48_1_r2_15_eq k
lemma column48_1_r3_0_eq : ∀ k : Fin 16, column48_1Expr 3 0 k = column48_1_r3_0 k := by decide +kernel
lemma column48_1_r3_1_eq : ∀ k : Fin 16, column48_1Expr 3 1 k = column48_1_r3_1 k := by decide +kernel
lemma column48_1_r3_2_eq : ∀ k : Fin 16, column48_1Expr 3 2 k = column48_1_r3_2 k := by decide +kernel
lemma column48_1_r3_3_eq : ∀ k : Fin 16, column48_1Expr 3 3 k = column48_1_r3_3 k := by decide +kernel
lemma column48_1_r3_4_eq : ∀ k : Fin 16, column48_1Expr 3 4 k = column48_1_r3_4 k := by decide +kernel
lemma column48_1_r3_5_eq : ∀ k : Fin 16, column48_1Expr 3 5 k = column48_1_r3_5 k := by decide +kernel
lemma column48_1_r3_6_eq : ∀ k : Fin 16, column48_1Expr 3 6 k = column48_1_r3_6 k := by decide +kernel
lemma column48_1_r3_7_eq : ∀ k : Fin 16, column48_1Expr 3 7 k = column48_1_r3_7 k := by decide +kernel
lemma column48_1_r3_8_eq : ∀ k : Fin 16, column48_1Expr 3 8 k = column48_1_r3_8 k := by decide +kernel
lemma column48_1_r3_9_eq : ∀ k : Fin 16, column48_1Expr 3 9 k = column48_1_r3_9 k := by decide +kernel
lemma column48_1_r3_10_eq : ∀ k : Fin 16, column48_1Expr 3 10 k = column48_1_r3_10 k := by decide +kernel
lemma column48_1_r3_11_eq : ∀ k : Fin 16, column48_1Expr 3 11 k = column48_1_r3_11 k := by decide +kernel
lemma column48_1_r3_12_eq : ∀ k : Fin 16, column48_1Expr 3 12 k = column48_1_r3_12 k := by decide +kernel
lemma column48_1_r3_13_eq : ∀ k : Fin 16, column48_1Expr 3 13 k = column48_1_r3_13 k := by decide +kernel
lemma column48_1_r3_14_eq : ∀ k : Fin 16, column48_1Expr 3 14 k = column48_1_r3_14 k := by decide +kernel
lemma column48_1_r3_15_eq : ∀ k : Fin 16, column48_1Expr 3 15 k = column48_1_r3_15 k := by decide +kernel
lemma column48_1_r3_eq (i k : Fin 16) : column48_1Expr 3 i k = column48_1_r3 i k := by
  fin_cases i
  · exact column48_1_r3_0_eq k
  · exact column48_1_r3_1_eq k
  · exact column48_1_r3_2_eq k
  · exact column48_1_r3_3_eq k
  · exact column48_1_r3_4_eq k
  · exact column48_1_r3_5_eq k
  · exact column48_1_r3_6_eq k
  · exact column48_1_r3_7_eq k
  · exact column48_1_r3_8_eq k
  · exact column48_1_r3_9_eq k
  · exact column48_1_r3_10_eq k
  · exact column48_1_r3_11_eq k
  · exact column48_1_r3_12_eq k
  · exact column48_1_r3_13_eq k
  · exact column48_1_r3_14_eq k
  · exact column48_1_r3_15_eq k
lemma column48_1_r4_0_eq : ∀ k : Fin 16, column48_1Expr 4 0 k = column48_1_r4_0 k := by decide +kernel
lemma column48_1_r4_1_eq : ∀ k : Fin 16, column48_1Expr 4 1 k = column48_1_r4_1 k := by decide +kernel
lemma column48_1_r4_2_eq : ∀ k : Fin 16, column48_1Expr 4 2 k = column48_1_r4_2 k := by decide +kernel
lemma column48_1_r4_3_eq : ∀ k : Fin 16, column48_1Expr 4 3 k = column48_1_r4_3 k := by decide +kernel
lemma column48_1_r4_4_eq : ∀ k : Fin 16, column48_1Expr 4 4 k = column48_1_r4_4 k := by decide +kernel
lemma column48_1_r4_5_eq : ∀ k : Fin 16, column48_1Expr 4 5 k = column48_1_r4_5 k := by decide +kernel
lemma column48_1_r4_6_eq : ∀ k : Fin 16, column48_1Expr 4 6 k = column48_1_r4_6 k := by decide +kernel
lemma column48_1_r4_7_eq : ∀ k : Fin 16, column48_1Expr 4 7 k = column48_1_r4_7 k := by decide +kernel
lemma column48_1_r4_8_eq : ∀ k : Fin 16, column48_1Expr 4 8 k = column48_1_r4_8 k := by decide +kernel
lemma column48_1_r4_9_eq : ∀ k : Fin 16, column48_1Expr 4 9 k = column48_1_r4_9 k := by decide +kernel
lemma column48_1_r4_10_eq : ∀ k : Fin 16, column48_1Expr 4 10 k = column48_1_r4_10 k := by decide +kernel
lemma column48_1_r4_11_eq : ∀ k : Fin 16, column48_1Expr 4 11 k = column48_1_r4_11 k := by decide +kernel
lemma column48_1_r4_12_eq : ∀ k : Fin 16, column48_1Expr 4 12 k = column48_1_r4_12 k := by decide +kernel
lemma column48_1_r4_13_eq : ∀ k : Fin 16, column48_1Expr 4 13 k = column48_1_r4_13 k := by decide +kernel
lemma column48_1_r4_14_eq : ∀ k : Fin 16, column48_1Expr 4 14 k = column48_1_r4_14 k := by decide +kernel
lemma column48_1_r4_15_eq : ∀ k : Fin 16, column48_1Expr 4 15 k = column48_1_r4_15 k := by decide +kernel
lemma column48_1_r4_eq (i k : Fin 16) : column48_1Expr 4 i k = column48_1_r4 i k := by
  fin_cases i
  · exact column48_1_r4_0_eq k
  · exact column48_1_r4_1_eq k
  · exact column48_1_r4_2_eq k
  · exact column48_1_r4_3_eq k
  · exact column48_1_r4_4_eq k
  · exact column48_1_r4_5_eq k
  · exact column48_1_r4_6_eq k
  · exact column48_1_r4_7_eq k
  · exact column48_1_r4_8_eq k
  · exact column48_1_r4_9_eq k
  · exact column48_1_r4_10_eq k
  · exact column48_1_r4_11_eq k
  · exact column48_1_r4_12_eq k
  · exact column48_1_r4_13_eq k
  · exact column48_1_r4_14_eq k
  · exact column48_1_r4_15_eq k
lemma column48_1_r5_0_eq : ∀ k : Fin 16, column48_1Expr 5 0 k = column48_1_r5_0 k := by decide +kernel
lemma column48_1_r5_1_eq : ∀ k : Fin 16, column48_1Expr 5 1 k = column48_1_r5_1 k := by decide +kernel
lemma column48_1_r5_2_eq : ∀ k : Fin 16, column48_1Expr 5 2 k = column48_1_r5_2 k := by decide +kernel
lemma column48_1_r5_3_eq : ∀ k : Fin 16, column48_1Expr 5 3 k = column48_1_r5_3 k := by decide +kernel
lemma column48_1_r5_4_eq : ∀ k : Fin 16, column48_1Expr 5 4 k = column48_1_r5_4 k := by decide +kernel
lemma column48_1_r5_5_eq : ∀ k : Fin 16, column48_1Expr 5 5 k = column48_1_r5_5 k := by decide +kernel
lemma column48_1_r5_6_eq : ∀ k : Fin 16, column48_1Expr 5 6 k = column48_1_r5_6 k := by decide +kernel
lemma column48_1_r5_7_eq : ∀ k : Fin 16, column48_1Expr 5 7 k = column48_1_r5_7 k := by decide +kernel
lemma column48_1_r5_8_eq : ∀ k : Fin 16, column48_1Expr 5 8 k = column48_1_r5_8 k := by decide +kernel
lemma column48_1_r5_9_eq : ∀ k : Fin 16, column48_1Expr 5 9 k = column48_1_r5_9 k := by decide +kernel
lemma column48_1_r5_10_eq : ∀ k : Fin 16, column48_1Expr 5 10 k = column48_1_r5_10 k := by decide +kernel
lemma column48_1_r5_11_eq : ∀ k : Fin 16, column48_1Expr 5 11 k = column48_1_r5_11 k := by decide +kernel
lemma column48_1_r5_12_eq : ∀ k : Fin 16, column48_1Expr 5 12 k = column48_1_r5_12 k := by decide +kernel
lemma column48_1_r5_13_eq : ∀ k : Fin 16, column48_1Expr 5 13 k = column48_1_r5_13 k := by decide +kernel
lemma column48_1_r5_14_eq : ∀ k : Fin 16, column48_1Expr 5 14 k = column48_1_r5_14 k := by decide +kernel
lemma column48_1_r5_15_eq : ∀ k : Fin 16, column48_1Expr 5 15 k = column48_1_r5_15 k := by decide +kernel
lemma column48_1_r5_eq (i k : Fin 16) : column48_1Expr 5 i k = column48_1_r5 i k := by
  fin_cases i
  · exact column48_1_r5_0_eq k
  · exact column48_1_r5_1_eq k
  · exact column48_1_r5_2_eq k
  · exact column48_1_r5_3_eq k
  · exact column48_1_r5_4_eq k
  · exact column48_1_r5_5_eq k
  · exact column48_1_r5_6_eq k
  · exact column48_1_r5_7_eq k
  · exact column48_1_r5_8_eq k
  · exact column48_1_r5_9_eq k
  · exact column48_1_r5_10_eq k
  · exact column48_1_r5_11_eq k
  · exact column48_1_r5_12_eq k
  · exact column48_1_r5_13_eq k
  · exact column48_1_r5_14_eq k
  · exact column48_1_r5_15_eq k
lemma column48_1_eq (j : Fin 6) (i k : Fin 16) : column48_1Expr j i k = column48_1 j i k := by
  fin_cases j
  · exact column48_1_r0_eq i k
  · exact column48_1_r1_eq i k
  · exact column48_1_r2_eq i k
  · exact column48_1_r3_eq i k
  · exact column48_1_r4_eq i k
  · exact column48_1_r5_eq i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns60
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
noncomputable def column51_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power51 j i k)
lemma column51_0_r0_0_eq : ∀ k : Fin 16, column51_0Expr 0 0 k = column51_0_r0_0 k := by decide +kernel
lemma column51_0_r0_1_eq : ∀ k : Fin 16, column51_0Expr 0 1 k = column51_0_r0_1 k := by decide +kernel
lemma column51_0_r0_2_eq : ∀ k : Fin 16, column51_0Expr 0 2 k = column51_0_r0_2 k := by decide +kernel
lemma column51_0_r0_3_eq : ∀ k : Fin 16, column51_0Expr 0 3 k = column51_0_r0_3 k := by decide +kernel
lemma column51_0_r0_4_eq : ∀ k : Fin 16, column51_0Expr 0 4 k = column51_0_r0_4 k := by decide +kernel
lemma column51_0_r0_5_eq : ∀ k : Fin 16, column51_0Expr 0 5 k = column51_0_r0_5 k := by decide +kernel
lemma column51_0_r0_6_eq : ∀ k : Fin 16, column51_0Expr 0 6 k = column51_0_r0_6 k := by decide +kernel
lemma column51_0_r0_7_eq : ∀ k : Fin 16, column51_0Expr 0 7 k = column51_0_r0_7 k := by decide +kernel
lemma column51_0_r0_8_eq : ∀ k : Fin 16, column51_0Expr 0 8 k = column51_0_r0_8 k := by decide +kernel
lemma column51_0_r0_9_eq : ∀ k : Fin 16, column51_0Expr 0 9 k = column51_0_r0_9 k := by decide +kernel
lemma column51_0_r0_10_eq : ∀ k : Fin 16, column51_0Expr 0 10 k = column51_0_r0_10 k := by decide +kernel
lemma column51_0_r0_11_eq : ∀ k : Fin 16, column51_0Expr 0 11 k = column51_0_r0_11 k := by decide +kernel
lemma column51_0_r0_12_eq : ∀ k : Fin 16, column51_0Expr 0 12 k = column51_0_r0_12 k := by decide +kernel
lemma column51_0_r0_13_eq : ∀ k : Fin 16, column51_0Expr 0 13 k = column51_0_r0_13 k := by decide +kernel
lemma column51_0_r0_14_eq : ∀ k : Fin 16, column51_0Expr 0 14 k = column51_0_r0_14 k := by decide +kernel
lemma column51_0_r0_15_eq : ∀ k : Fin 16, column51_0Expr 0 15 k = column51_0_r0_15 k := by decide +kernel
lemma column51_0_r0_eq (i k : Fin 16) : column51_0Expr 0 i k = column51_0_r0 i k := by
  fin_cases i
  · exact column51_0_r0_0_eq k
  · exact column51_0_r0_1_eq k
  · exact column51_0_r0_2_eq k
  · exact column51_0_r0_3_eq k
  · exact column51_0_r0_4_eq k
  · exact column51_0_r0_5_eq k
  · exact column51_0_r0_6_eq k
  · exact column51_0_r0_7_eq k
  · exact column51_0_r0_8_eq k
  · exact column51_0_r0_9_eq k
  · exact column51_0_r0_10_eq k
  · exact column51_0_r0_11_eq k
  · exact column51_0_r0_12_eq k
  · exact column51_0_r0_13_eq k
  · exact column51_0_r0_14_eq k
  · exact column51_0_r0_15_eq k
lemma column51_0_r1_0_eq : ∀ k : Fin 16, column51_0Expr 1 0 k = column51_0_r1_0 k := by decide +kernel
lemma column51_0_r1_1_eq : ∀ k : Fin 16, column51_0Expr 1 1 k = column51_0_r1_1 k := by decide +kernel
lemma column51_0_r1_2_eq : ∀ k : Fin 16, column51_0Expr 1 2 k = column51_0_r1_2 k := by decide +kernel
lemma column51_0_r1_3_eq : ∀ k : Fin 16, column51_0Expr 1 3 k = column51_0_r1_3 k := by decide +kernel
lemma column51_0_r1_4_eq : ∀ k : Fin 16, column51_0Expr 1 4 k = column51_0_r1_4 k := by decide +kernel
lemma column51_0_r1_5_eq : ∀ k : Fin 16, column51_0Expr 1 5 k = column51_0_r1_5 k := by decide +kernel
lemma column51_0_r1_6_eq : ∀ k : Fin 16, column51_0Expr 1 6 k = column51_0_r1_6 k := by decide +kernel
lemma column51_0_r1_7_eq : ∀ k : Fin 16, column51_0Expr 1 7 k = column51_0_r1_7 k := by decide +kernel
lemma column51_0_r1_8_eq : ∀ k : Fin 16, column51_0Expr 1 8 k = column51_0_r1_8 k := by decide +kernel
lemma column51_0_r1_9_eq : ∀ k : Fin 16, column51_0Expr 1 9 k = column51_0_r1_9 k := by decide +kernel
lemma column51_0_r1_10_eq : ∀ k : Fin 16, column51_0Expr 1 10 k = column51_0_r1_10 k := by decide +kernel
lemma column51_0_r1_11_eq : ∀ k : Fin 16, column51_0Expr 1 11 k = column51_0_r1_11 k := by decide +kernel
lemma column51_0_r1_12_eq : ∀ k : Fin 16, column51_0Expr 1 12 k = column51_0_r1_12 k := by decide +kernel
lemma column51_0_r1_13_eq : ∀ k : Fin 16, column51_0Expr 1 13 k = column51_0_r1_13 k := by decide +kernel
lemma column51_0_r1_14_eq : ∀ k : Fin 16, column51_0Expr 1 14 k = column51_0_r1_14 k := by decide +kernel
lemma column51_0_r1_15_eq : ∀ k : Fin 16, column51_0Expr 1 15 k = column51_0_r1_15 k := by decide +kernel
lemma column51_0_r1_eq (i k : Fin 16) : column51_0Expr 1 i k = column51_0_r1 i k := by
  fin_cases i
  · exact column51_0_r1_0_eq k
  · exact column51_0_r1_1_eq k
  · exact column51_0_r1_2_eq k
  · exact column51_0_r1_3_eq k
  · exact column51_0_r1_4_eq k
  · exact column51_0_r1_5_eq k
  · exact column51_0_r1_6_eq k
  · exact column51_0_r1_7_eq k
  · exact column51_0_r1_8_eq k
  · exact column51_0_r1_9_eq k
  · exact column51_0_r1_10_eq k
  · exact column51_0_r1_11_eq k
  · exact column51_0_r1_12_eq k
  · exact column51_0_r1_13_eq k
  · exact column51_0_r1_14_eq k
  · exact column51_0_r1_15_eq k
lemma column51_0_r2_0_eq : ∀ k : Fin 16, column51_0Expr 2 0 k = column51_0_r2_0 k := by decide +kernel
lemma column51_0_r2_1_eq : ∀ k : Fin 16, column51_0Expr 2 1 k = column51_0_r2_1 k := by decide +kernel
lemma column51_0_r2_2_eq : ∀ k : Fin 16, column51_0Expr 2 2 k = column51_0_r2_2 k := by decide +kernel
lemma column51_0_r2_3_eq : ∀ k : Fin 16, column51_0Expr 2 3 k = column51_0_r2_3 k := by decide +kernel
lemma column51_0_r2_4_eq : ∀ k : Fin 16, column51_0Expr 2 4 k = column51_0_r2_4 k := by decide +kernel
lemma column51_0_r2_5_eq : ∀ k : Fin 16, column51_0Expr 2 5 k = column51_0_r2_5 k := by decide +kernel
lemma column51_0_r2_6_eq : ∀ k : Fin 16, column51_0Expr 2 6 k = column51_0_r2_6 k := by decide +kernel
lemma column51_0_r2_7_eq : ∀ k : Fin 16, column51_0Expr 2 7 k = column51_0_r2_7 k := by decide +kernel
lemma column51_0_r2_8_eq : ∀ k : Fin 16, column51_0Expr 2 8 k = column51_0_r2_8 k := by decide +kernel
lemma column51_0_r2_9_eq : ∀ k : Fin 16, column51_0Expr 2 9 k = column51_0_r2_9 k := by decide +kernel
lemma column51_0_r2_10_eq : ∀ k : Fin 16, column51_0Expr 2 10 k = column51_0_r2_10 k := by decide +kernel
lemma column51_0_r2_11_eq : ∀ k : Fin 16, column51_0Expr 2 11 k = column51_0_r2_11 k := by decide +kernel
lemma column51_0_r2_12_eq : ∀ k : Fin 16, column51_0Expr 2 12 k = column51_0_r2_12 k := by decide +kernel
lemma column51_0_r2_13_eq : ∀ k : Fin 16, column51_0Expr 2 13 k = column51_0_r2_13 k := by decide +kernel
lemma column51_0_r2_14_eq : ∀ k : Fin 16, column51_0Expr 2 14 k = column51_0_r2_14 k := by decide +kernel
lemma column51_0_r2_15_eq : ∀ k : Fin 16, column51_0Expr 2 15 k = column51_0_r2_15 k := by decide +kernel
lemma column51_0_r2_eq (i k : Fin 16) : column51_0Expr 2 i k = column51_0_r2 i k := by
  fin_cases i
  · exact column51_0_r2_0_eq k
  · exact column51_0_r2_1_eq k
  · exact column51_0_r2_2_eq k
  · exact column51_0_r2_3_eq k
  · exact column51_0_r2_4_eq k
  · exact column51_0_r2_5_eq k
  · exact column51_0_r2_6_eq k
  · exact column51_0_r2_7_eq k
  · exact column51_0_r2_8_eq k
  · exact column51_0_r2_9_eq k
  · exact column51_0_r2_10_eq k
  · exact column51_0_r2_11_eq k
  · exact column51_0_r2_12_eq k
  · exact column51_0_r2_13_eq k
  · exact column51_0_r2_14_eq k
  · exact column51_0_r2_15_eq k
lemma column51_0_r3_0_eq : ∀ k : Fin 16, column51_0Expr 3 0 k = column51_0_r3_0 k := by decide +kernel
lemma column51_0_r3_1_eq : ∀ k : Fin 16, column51_0Expr 3 1 k = column51_0_r3_1 k := by decide +kernel
lemma column51_0_r3_2_eq : ∀ k : Fin 16, column51_0Expr 3 2 k = column51_0_r3_2 k := by decide +kernel
lemma column51_0_r3_3_eq : ∀ k : Fin 16, column51_0Expr 3 3 k = column51_0_r3_3 k := by decide +kernel
lemma column51_0_r3_4_eq : ∀ k : Fin 16, column51_0Expr 3 4 k = column51_0_r3_4 k := by decide +kernel
lemma column51_0_r3_5_eq : ∀ k : Fin 16, column51_0Expr 3 5 k = column51_0_r3_5 k := by decide +kernel
lemma column51_0_r3_6_eq : ∀ k : Fin 16, column51_0Expr 3 6 k = column51_0_r3_6 k := by decide +kernel
lemma column51_0_r3_7_eq : ∀ k : Fin 16, column51_0Expr 3 7 k = column51_0_r3_7 k := by decide +kernel
lemma column51_0_r3_8_eq : ∀ k : Fin 16, column51_0Expr 3 8 k = column51_0_r3_8 k := by decide +kernel
lemma column51_0_r3_9_eq : ∀ k : Fin 16, column51_0Expr 3 9 k = column51_0_r3_9 k := by decide +kernel
lemma column51_0_r3_10_eq : ∀ k : Fin 16, column51_0Expr 3 10 k = column51_0_r3_10 k := by decide +kernel
lemma column51_0_r3_11_eq : ∀ k : Fin 16, column51_0Expr 3 11 k = column51_0_r3_11 k := by decide +kernel
lemma column51_0_r3_12_eq : ∀ k : Fin 16, column51_0Expr 3 12 k = column51_0_r3_12 k := by decide +kernel
lemma column51_0_r3_13_eq : ∀ k : Fin 16, column51_0Expr 3 13 k = column51_0_r3_13 k := by decide +kernel
lemma column51_0_r3_14_eq : ∀ k : Fin 16, column51_0Expr 3 14 k = column51_0_r3_14 k := by decide +kernel
lemma column51_0_r3_15_eq : ∀ k : Fin 16, column51_0Expr 3 15 k = column51_0_r3_15 k := by decide +kernel
lemma column51_0_r4_0_eq : ∀ k : Fin 16, column51_0Expr 4 0 k = column51_0_r4_0 k := by decide +kernel
lemma column51_0_r4_1_eq : ∀ k : Fin 16, column51_0Expr 4 1 k = column51_0_r4_1 k := by decide +kernel
lemma column51_0_r4_2_eq : ∀ k : Fin 16, column51_0Expr 4 2 k = column51_0_r4_2 k := by decide +kernel
lemma column51_0_r4_3_eq : ∀ k : Fin 16, column51_0Expr 4 3 k = column51_0_r4_3 k := by decide +kernel
lemma column51_0_r4_4_eq : ∀ k : Fin 16, column51_0Expr 4 4 k = column51_0_r4_4 k := by decide +kernel
lemma column51_0_r4_5_eq : ∀ k : Fin 16, column51_0Expr 4 5 k = column51_0_r4_5 k := by decide +kernel
lemma column51_0_r4_6_eq : ∀ k : Fin 16, column51_0Expr 4 6 k = column51_0_r4_6 k := by decide +kernel
lemma column51_0_r4_7_eq : ∀ k : Fin 16, column51_0Expr 4 7 k = column51_0_r4_7 k := by decide +kernel
lemma column51_0_r4_8_eq : ∀ k : Fin 16, column51_0Expr 4 8 k = column51_0_r4_8 k := by decide +kernel
lemma column51_0_r4_9_eq : ∀ k : Fin 16, column51_0Expr 4 9 k = column51_0_r4_9 k := by decide +kernel
lemma column51_0_r4_10_eq : ∀ k : Fin 16, column51_0Expr 4 10 k = column51_0_r4_10 k := by decide +kernel
lemma column51_0_r4_11_eq : ∀ k : Fin 16, column51_0Expr 4 11 k = column51_0_r4_11 k := by decide +kernel
lemma column51_0_r4_12_eq : ∀ k : Fin 16, column51_0Expr 4 12 k = column51_0_r4_12 k := by decide +kernel
lemma column51_0_r4_13_eq : ∀ k : Fin 16, column51_0Expr 4 13 k = column51_0_r4_13 k := by decide +kernel
lemma column51_0_r4_14_eq : ∀ k : Fin 16, column51_0Expr 4 14 k = column51_0_r4_14 k := by decide +kernel
lemma column51_0_r4_15_eq : ∀ k : Fin 16, column51_0Expr 4 15 k = column51_0_r4_15 k := by decide +kernel
lemma column51_0_r4_eq (i k : Fin 16) : column51_0Expr 4 i k = column51_0_r4 i k := by
  fin_cases i
  · exact column51_0_r4_0_eq k
  · exact column51_0_r4_1_eq k
  · exact column51_0_r4_2_eq k
  · exact column51_0_r4_3_eq k
  · exact column51_0_r4_4_eq k
  · exact column51_0_r4_5_eq k
  · exact column51_0_r4_6_eq k
  · exact column51_0_r4_7_eq k
  · exact column51_0_r4_8_eq k
  · exact column51_0_r4_9_eq k
  · exact column51_0_r4_10_eq k
  · exact column51_0_r4_11_eq k
  · exact column51_0_r4_12_eq k
  · exact column51_0_r4_13_eq k
  · exact column51_0_r4_14_eq k
  · exact column51_0_r4_15_eq k
lemma column51_0_r5_0_eq : ∀ k : Fin 16, column51_0Expr 5 0 k = column51_0_r5_0 k := by decide +kernel
lemma column51_0_r5_1_eq : ∀ k : Fin 16, column51_0Expr 5 1 k = column51_0_r5_1 k := by decide +kernel
lemma column51_0_r5_2_eq : ∀ k : Fin 16, column51_0Expr 5 2 k = column51_0_r5_2 k := by decide +kernel
lemma column51_0_r5_3_eq : ∀ k : Fin 16, column51_0Expr 5 3 k = column51_0_r5_3 k := by decide +kernel
lemma column51_0_r5_4_eq : ∀ k : Fin 16, column51_0Expr 5 4 k = column51_0_r5_4 k := by decide +kernel
lemma column51_0_r5_5_eq : ∀ k : Fin 16, column51_0Expr 5 5 k = column51_0_r5_5 k := by decide +kernel
lemma column51_0_r5_6_eq : ∀ k : Fin 16, column51_0Expr 5 6 k = column51_0_r5_6 k := by decide +kernel
lemma column51_0_r5_7_eq : ∀ k : Fin 16, column51_0Expr 5 7 k = column51_0_r5_7 k := by decide +kernel
lemma column51_0_r5_8_eq : ∀ k : Fin 16, column51_0Expr 5 8 k = column51_0_r5_8 k := by decide +kernel
lemma column51_0_r5_9_eq : ∀ k : Fin 16, column51_0Expr 5 9 k = column51_0_r5_9 k := by decide +kernel
lemma column51_0_r5_10_eq : ∀ k : Fin 16, column51_0Expr 5 10 k = column51_0_r5_10 k := by decide +kernel
lemma column51_0_r5_11_eq : ∀ k : Fin 16, column51_0Expr 5 11 k = column51_0_r5_11 k := by decide +kernel
lemma column51_0_r5_12_eq : ∀ k : Fin 16, column51_0Expr 5 12 k = column51_0_r5_12 k := by decide +kernel
lemma column51_0_r5_13_eq : ∀ k : Fin 16, column51_0Expr 5 13 k = column51_0_r5_13 k := by decide +kernel
lemma column51_0_r5_14_eq : ∀ k : Fin 16, column51_0Expr 5 14 k = column51_0_r5_14 k := by decide +kernel
lemma column51_0_r5_15_eq : ∀ k : Fin 16, column51_0Expr 5 15 k = column51_0_r5_15 k := by decide +kernel
noncomputable def column51_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power51 j i k)
lemma column51_1_r0_0_eq : ∀ k : Fin 16, column51_1Expr 0 0 k = column51_1_r0_0 k := by decide +kernel
lemma column51_1_r0_1_eq : ∀ k : Fin 16, column51_1Expr 0 1 k = column51_1_r0_1 k := by decide +kernel
lemma column51_1_r0_2_eq : ∀ k : Fin 16, column51_1Expr 0 2 k = column51_1_r0_2 k := by decide +kernel
lemma column51_1_r0_3_eq : ∀ k : Fin 16, column51_1Expr 0 3 k = column51_1_r0_3 k := by decide +kernel
lemma column51_1_r0_4_eq : ∀ k : Fin 16, column51_1Expr 0 4 k = column51_1_r0_4 k := by decide +kernel
lemma column51_1_r0_5_eq : ∀ k : Fin 16, column51_1Expr 0 5 k = column51_1_r0_5 k := by decide +kernel
lemma column51_1_r0_6_eq : ∀ k : Fin 16, column51_1Expr 0 6 k = column51_1_r0_6 k := by decide +kernel
lemma column51_1_r0_7_eq : ∀ k : Fin 16, column51_1Expr 0 7 k = column51_1_r0_7 k := by decide +kernel
lemma column51_1_r0_8_eq : ∀ k : Fin 16, column51_1Expr 0 8 k = column51_1_r0_8 k := by decide +kernel
lemma column51_1_r0_9_eq : ∀ k : Fin 16, column51_1Expr 0 9 k = column51_1_r0_9 k := by decide +kernel
lemma column51_1_r0_10_eq : ∀ k : Fin 16, column51_1Expr 0 10 k = column51_1_r0_10 k := by decide +kernel
lemma column51_1_r0_11_eq : ∀ k : Fin 16, column51_1Expr 0 11 k = column51_1_r0_11 k := by decide +kernel
lemma column51_1_r0_12_eq : ∀ k : Fin 16, column51_1Expr 0 12 k = column51_1_r0_12 k := by decide +kernel
lemma column51_1_r0_13_eq : ∀ k : Fin 16, column51_1Expr 0 13 k = column51_1_r0_13 k := by decide +kernel
lemma column51_1_r0_14_eq : ∀ k : Fin 16, column51_1Expr 0 14 k = column51_1_r0_14 k := by decide +kernel
lemma column51_1_r0_15_eq : ∀ k : Fin 16, column51_1Expr 0 15 k = column51_1_r0_15 k := by decide +kernel
lemma column51_1_r0_eq (i k : Fin 16) : column51_1Expr 0 i k = column51_1_r0 i k := by
  fin_cases i
  · exact column51_1_r0_0_eq k
  · exact column51_1_r0_1_eq k
  · exact column51_1_r0_2_eq k
  · exact column51_1_r0_3_eq k
  · exact column51_1_r0_4_eq k
  · exact column51_1_r0_5_eq k
  · exact column51_1_r0_6_eq k
  · exact column51_1_r0_7_eq k
  · exact column51_1_r0_8_eq k
  · exact column51_1_r0_9_eq k
  · exact column51_1_r0_10_eq k
  · exact column51_1_r0_11_eq k
  · exact column51_1_r0_12_eq k
  · exact column51_1_r0_13_eq k
  · exact column51_1_r0_14_eq k
  · exact column51_1_r0_15_eq k
lemma column51_1_r1_0_eq : ∀ k : Fin 16, column51_1Expr 1 0 k = column51_1_r1_0 k := by decide +kernel
lemma column51_1_r1_1_eq : ∀ k : Fin 16, column51_1Expr 1 1 k = column51_1_r1_1 k := by decide +kernel
lemma column51_1_r1_2_eq : ∀ k : Fin 16, column51_1Expr 1 2 k = column51_1_r1_2 k := by decide +kernel
lemma column51_1_r1_3_eq : ∀ k : Fin 16, column51_1Expr 1 3 k = column51_1_r1_3 k := by decide +kernel
lemma column51_1_r1_4_eq : ∀ k : Fin 16, column51_1Expr 1 4 k = column51_1_r1_4 k := by decide +kernel
lemma column51_1_r1_5_eq : ∀ k : Fin 16, column51_1Expr 1 5 k = column51_1_r1_5 k := by decide +kernel
lemma column51_1_r1_6_eq : ∀ k : Fin 16, column51_1Expr 1 6 k = column51_1_r1_6 k := by decide +kernel
lemma column51_1_r1_7_eq : ∀ k : Fin 16, column51_1Expr 1 7 k = column51_1_r1_7 k := by decide +kernel
lemma column51_1_r1_8_eq : ∀ k : Fin 16, column51_1Expr 1 8 k = column51_1_r1_8 k := by decide +kernel
lemma column51_1_r1_9_eq : ∀ k : Fin 16, column51_1Expr 1 9 k = column51_1_r1_9 k := by decide +kernel
lemma column51_1_r1_10_eq : ∀ k : Fin 16, column51_1Expr 1 10 k = column51_1_r1_10 k := by decide +kernel
lemma column51_1_r1_11_eq : ∀ k : Fin 16, column51_1Expr 1 11 k = column51_1_r1_11 k := by decide +kernel
lemma column51_1_r1_12_eq : ∀ k : Fin 16, column51_1Expr 1 12 k = column51_1_r1_12 k := by decide +kernel
lemma column51_1_r1_13_eq : ∀ k : Fin 16, column51_1Expr 1 13 k = column51_1_r1_13 k := by decide +kernel
lemma column51_1_r1_14_eq : ∀ k : Fin 16, column51_1Expr 1 14 k = column51_1_r1_14 k := by decide +kernel
lemma column51_1_r1_15_eq : ∀ k : Fin 16, column51_1Expr 1 15 k = column51_1_r1_15 k := by decide +kernel
lemma column51_1_r1_eq (i k : Fin 16) : column51_1Expr 1 i k = column51_1_r1 i k := by
  fin_cases i
  · exact column51_1_r1_0_eq k
  · exact column51_1_r1_1_eq k
  · exact column51_1_r1_2_eq k
  · exact column51_1_r1_3_eq k
  · exact column51_1_r1_4_eq k
  · exact column51_1_r1_5_eq k
  · exact column51_1_r1_6_eq k
  · exact column51_1_r1_7_eq k
  · exact column51_1_r1_8_eq k
  · exact column51_1_r1_9_eq k
  · exact column51_1_r1_10_eq k
  · exact column51_1_r1_11_eq k
  · exact column51_1_r1_12_eq k
  · exact column51_1_r1_13_eq k
  · exact column51_1_r1_14_eq k
  · exact column51_1_r1_15_eq k
lemma column51_1_r2_0_eq : ∀ k : Fin 16, column51_1Expr 2 0 k = column51_1_r2_0 k := by decide +kernel
lemma column51_1_r2_1_eq : ∀ k : Fin 16, column51_1Expr 2 1 k = column51_1_r2_1 k := by decide +kernel
lemma column51_1_r2_2_eq : ∀ k : Fin 16, column51_1Expr 2 2 k = column51_1_r2_2 k := by decide +kernel
lemma column51_1_r2_3_eq : ∀ k : Fin 16, column51_1Expr 2 3 k = column51_1_r2_3 k := by decide +kernel
lemma column51_1_r2_4_eq : ∀ k : Fin 16, column51_1Expr 2 4 k = column51_1_r2_4 k := by decide +kernel
lemma column51_1_r2_5_eq : ∀ k : Fin 16, column51_1Expr 2 5 k = column51_1_r2_5 k := by decide +kernel
lemma column51_1_r2_6_eq : ∀ k : Fin 16, column51_1Expr 2 6 k = column51_1_r2_6 k := by decide +kernel
lemma column51_1_r2_7_eq : ∀ k : Fin 16, column51_1Expr 2 7 k = column51_1_r2_7 k := by decide +kernel
lemma column51_1_r2_8_eq : ∀ k : Fin 16, column51_1Expr 2 8 k = column51_1_r2_8 k := by decide +kernel
lemma column51_1_r2_9_eq : ∀ k : Fin 16, column51_1Expr 2 9 k = column51_1_r2_9 k := by decide +kernel
lemma column51_1_r2_10_eq : ∀ k : Fin 16, column51_1Expr 2 10 k = column51_1_r2_10 k := by decide +kernel
lemma column51_1_r2_11_eq : ∀ k : Fin 16, column51_1Expr 2 11 k = column51_1_r2_11 k := by decide +kernel
lemma column51_1_r2_12_eq : ∀ k : Fin 16, column51_1Expr 2 12 k = column51_1_r2_12 k := by decide +kernel
lemma column51_1_r2_13_eq : ∀ k : Fin 16, column51_1Expr 2 13 k = column51_1_r2_13 k := by decide +kernel
lemma column51_1_r2_14_eq : ∀ k : Fin 16, column51_1Expr 2 14 k = column51_1_r2_14 k := by decide +kernel
lemma column51_1_r2_15_eq : ∀ k : Fin 16, column51_1Expr 2 15 k = column51_1_r2_15 k := by decide +kernel
lemma column51_1_r2_eq (i k : Fin 16) : column51_1Expr 2 i k = column51_1_r2 i k := by
  fin_cases i
  · exact column51_1_r2_0_eq k
  · exact column51_1_r2_1_eq k
  · exact column51_1_r2_2_eq k
  · exact column51_1_r2_3_eq k
  · exact column51_1_r2_4_eq k
  · exact column51_1_r2_5_eq k
  · exact column51_1_r2_6_eq k
  · exact column51_1_r2_7_eq k
  · exact column51_1_r2_8_eq k
  · exact column51_1_r2_9_eq k
  · exact column51_1_r2_10_eq k
  · exact column51_1_r2_11_eq k
  · exact column51_1_r2_12_eq k
  · exact column51_1_r2_13_eq k
  · exact column51_1_r2_14_eq k
  · exact column51_1_r2_15_eq k
lemma column51_1_r3_0_eq : ∀ k : Fin 16, column51_1Expr 3 0 k = column51_1_r3_0 k := by decide +kernel
lemma column51_1_r3_1_eq : ∀ k : Fin 16, column51_1Expr 3 1 k = column51_1_r3_1 k := by decide +kernel
lemma column51_1_r3_2_eq : ∀ k : Fin 16, column51_1Expr 3 2 k = column51_1_r3_2 k := by decide +kernel
lemma column51_1_r3_3_eq : ∀ k : Fin 16, column51_1Expr 3 3 k = column51_1_r3_3 k := by decide +kernel
lemma column51_1_r3_4_eq : ∀ k : Fin 16, column51_1Expr 3 4 k = column51_1_r3_4 k := by decide +kernel
lemma column51_1_r3_5_eq : ∀ k : Fin 16, column51_1Expr 3 5 k = column51_1_r3_5 k := by decide +kernel
lemma column51_1_r3_6_eq : ∀ k : Fin 16, column51_1Expr 3 6 k = column51_1_r3_6 k := by decide +kernel
lemma column51_1_r3_7_eq : ∀ k : Fin 16, column51_1Expr 3 7 k = column51_1_r3_7 k := by decide +kernel
lemma column51_1_r3_8_eq : ∀ k : Fin 16, column51_1Expr 3 8 k = column51_1_r3_8 k := by decide +kernel
lemma column51_1_r3_9_eq : ∀ k : Fin 16, column51_1Expr 3 9 k = column51_1_r3_9 k := by decide +kernel
lemma column51_1_r3_10_eq : ∀ k : Fin 16, column51_1Expr 3 10 k = column51_1_r3_10 k := by decide +kernel
lemma column51_1_r3_11_eq : ∀ k : Fin 16, column51_1Expr 3 11 k = column51_1_r3_11 k := by decide +kernel
lemma column51_1_r3_12_eq : ∀ k : Fin 16, column51_1Expr 3 12 k = column51_1_r3_12 k := by decide +kernel
lemma column51_1_r3_13_eq : ∀ k : Fin 16, column51_1Expr 3 13 k = column51_1_r3_13 k := by decide +kernel
lemma column51_1_r3_14_eq : ∀ k : Fin 16, column51_1Expr 3 14 k = column51_1_r3_14 k := by decide +kernel
lemma column51_1_r3_15_eq : ∀ k : Fin 16, column51_1Expr 3 15 k = column51_1_r3_15 k := by decide +kernel
lemma column51_1_r3_eq (i k : Fin 16) : column51_1Expr 3 i k = column51_1_r3 i k := by
  fin_cases i
  · exact column51_1_r3_0_eq k
  · exact column51_1_r3_1_eq k
  · exact column51_1_r3_2_eq k
  · exact column51_1_r3_3_eq k
  · exact column51_1_r3_4_eq k
  · exact column51_1_r3_5_eq k
  · exact column51_1_r3_6_eq k
  · exact column51_1_r3_7_eq k
  · exact column51_1_r3_8_eq k
  · exact column51_1_r3_9_eq k
  · exact column51_1_r3_10_eq k
  · exact column51_1_r3_11_eq k
  · exact column51_1_r3_12_eq k
  · exact column51_1_r3_13_eq k
  · exact column51_1_r3_14_eq k
  · exact column51_1_r3_15_eq k
lemma column51_1_r4_0_eq : ∀ k : Fin 16, column51_1Expr 4 0 k = column51_1_r4_0 k := by decide +kernel
lemma column51_1_r4_1_eq : ∀ k : Fin 16, column51_1Expr 4 1 k = column51_1_r4_1 k := by decide +kernel
lemma column51_1_r4_2_eq : ∀ k : Fin 16, column51_1Expr 4 2 k = column51_1_r4_2 k := by decide +kernel
lemma column51_1_r4_3_eq : ∀ k : Fin 16, column51_1Expr 4 3 k = column51_1_r4_3 k := by decide +kernel
lemma column51_1_r4_4_eq : ∀ k : Fin 16, column51_1Expr 4 4 k = column51_1_r4_4 k := by decide +kernel
lemma column51_1_r4_5_eq : ∀ k : Fin 16, column51_1Expr 4 5 k = column51_1_r4_5 k := by decide +kernel
lemma column51_1_r4_6_eq : ∀ k : Fin 16, column51_1Expr 4 6 k = column51_1_r4_6 k := by decide +kernel
lemma column51_1_r4_7_eq : ∀ k : Fin 16, column51_1Expr 4 7 k = column51_1_r4_7 k := by decide +kernel
lemma column51_1_r4_8_eq : ∀ k : Fin 16, column51_1Expr 4 8 k = column51_1_r4_8 k := by decide +kernel
lemma column51_1_r4_9_eq : ∀ k : Fin 16, column51_1Expr 4 9 k = column51_1_r4_9 k := by decide +kernel
lemma column51_1_r4_10_eq : ∀ k : Fin 16, column51_1Expr 4 10 k = column51_1_r4_10 k := by decide +kernel
lemma column51_1_r4_11_eq : ∀ k : Fin 16, column51_1Expr 4 11 k = column51_1_r4_11 k := by decide +kernel
lemma column51_1_r4_12_eq : ∀ k : Fin 16, column51_1Expr 4 12 k = column51_1_r4_12 k := by decide +kernel
lemma column51_1_r4_13_eq : ∀ k : Fin 16, column51_1Expr 4 13 k = column51_1_r4_13 k := by decide +kernel
lemma column51_1_r4_14_eq : ∀ k : Fin 16, column51_1Expr 4 14 k = column51_1_r4_14 k := by decide +kernel
lemma column51_1_r4_15_eq : ∀ k : Fin 16, column51_1Expr 4 15 k = column51_1_r4_15 k := by decide +kernel
lemma column51_1_r4_eq (i k : Fin 16) : column51_1Expr 4 i k = column51_1_r4 i k := by
  fin_cases i
  · exact column51_1_r4_0_eq k
  · exact column51_1_r4_1_eq k
  · exact column51_1_r4_2_eq k
  · exact column51_1_r4_3_eq k
  · exact column51_1_r4_4_eq k
  · exact column51_1_r4_5_eq k
  · exact column51_1_r4_6_eq k
  · exact column51_1_r4_7_eq k
  · exact column51_1_r4_8_eq k
  · exact column51_1_r4_9_eq k
  · exact column51_1_r4_10_eq k
  · exact column51_1_r4_11_eq k
  · exact column51_1_r4_12_eq k
  · exact column51_1_r4_13_eq k
  · exact column51_1_r4_14_eq k
  · exact column51_1_r4_15_eq k
lemma column51_1_r5_0_eq : ∀ k : Fin 16, column51_1Expr 5 0 k = column51_1_r5_0 k := by decide +kernel
lemma column51_1_r5_1_eq : ∀ k : Fin 16, column51_1Expr 5 1 k = column51_1_r5_1 k := by decide +kernel
lemma column51_1_r5_2_eq : ∀ k : Fin 16, column51_1Expr 5 2 k = column51_1_r5_2 k := by decide +kernel
lemma column51_1_r5_3_eq : ∀ k : Fin 16, column51_1Expr 5 3 k = column51_1_r5_3 k := by decide +kernel
lemma column51_1_r5_4_eq : ∀ k : Fin 16, column51_1Expr 5 4 k = column51_1_r5_4 k := by decide +kernel
lemma column51_1_r5_5_eq : ∀ k : Fin 16, column51_1Expr 5 5 k = column51_1_r5_5 k := by decide +kernel
lemma column51_1_r5_6_eq : ∀ k : Fin 16, column51_1Expr 5 6 k = column51_1_r5_6 k := by decide +kernel
lemma column51_1_r5_7_eq : ∀ k : Fin 16, column51_1Expr 5 7 k = column51_1_r5_7 k := by decide +kernel
lemma column51_1_r5_8_eq : ∀ k : Fin 16, column51_1Expr 5 8 k = column51_1_r5_8 k := by decide +kernel
lemma column51_1_r5_9_eq : ∀ k : Fin 16, column51_1Expr 5 9 k = column51_1_r5_9 k := by decide +kernel
lemma column51_1_r5_10_eq : ∀ k : Fin 16, column51_1Expr 5 10 k = column51_1_r5_10 k := by decide +kernel
lemma column51_1_r5_11_eq : ∀ k : Fin 16, column51_1Expr 5 11 k = column51_1_r5_11 k := by decide +kernel
lemma column51_1_r5_12_eq : ∀ k : Fin 16, column51_1Expr 5 12 k = column51_1_r5_12 k := by decide +kernel
lemma column51_1_r5_13_eq : ∀ k : Fin 16, column51_1Expr 5 13 k = column51_1_r5_13 k := by decide +kernel
lemma column51_1_r5_14_eq : ∀ k : Fin 16, column51_1Expr 5 14 k = column51_1_r5_14 k := by decide +kernel
lemma column51_1_r5_15_eq : ∀ k : Fin 16, column51_1Expr 5 15 k = column51_1_r5_15 k := by decide +kernel
lemma column51_1_r5_eq (i k : Fin 16) : column51_1Expr 5 i k = column51_1_r5 i k := by
  fin_cases i
  · exact column51_1_r5_0_eq k
  · exact column51_1_r5_1_eq k
  · exact column51_1_r5_2_eq k
  · exact column51_1_r5_3_eq k
  · exact column51_1_r5_4_eq k
  · exact column51_1_r5_5_eq k
  · exact column51_1_r5_6_eq k
  · exact column51_1_r5_7_eq k
  · exact column51_1_r5_8_eq k
  · exact column51_1_r5_9_eq k
  · exact column51_1_r5_10_eq k
  · exact column51_1_r5_11_eq k
  · exact column51_1_r5_12_eq k
  · exact column51_1_r5_13_eq k
  · exact column51_1_r5_14_eq k
  · exact column51_1_r5_15_eq k
lemma column51_1_eq (j : Fin 6) (i k : Fin 16) : column51_1Expr j i k = column51_1 j i k := by
  fin_cases j
  · exact column51_1_r0_eq i k
  · exact column51_1_r1_eq i k
  · exact column51_1_r2_eq i k
  · exact column51_1_r3_eq i k
  · exact column51_1_r4_eq i k
  · exact column51_1_r5_eq i k
noncomputable def column52_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power52 j i k)
lemma column52_1_r0_0_eq : ∀ k : Fin 16, column52_1Expr 0 0 k = column52_1_r0_0 k := by decide +kernel
lemma column52_1_r0_1_eq : ∀ k : Fin 16, column52_1Expr 0 1 k = column52_1_r0_1 k := by decide +kernel
lemma column52_1_r0_2_eq : ∀ k : Fin 16, column52_1Expr 0 2 k = column52_1_r0_2 k := by decide +kernel
lemma column52_1_r0_3_eq : ∀ k : Fin 16, column52_1Expr 0 3 k = column52_1_r0_3 k := by decide +kernel
lemma column52_1_r0_4_eq : ∀ k : Fin 16, column52_1Expr 0 4 k = column52_1_r0_4 k := by decide +kernel
lemma column52_1_r0_5_eq : ∀ k : Fin 16, column52_1Expr 0 5 k = column52_1_r0_5 k := by decide +kernel
lemma column52_1_r0_6_eq : ∀ k : Fin 16, column52_1Expr 0 6 k = column52_1_r0_6 k := by decide +kernel
lemma column52_1_r0_7_eq : ∀ k : Fin 16, column52_1Expr 0 7 k = column52_1_r0_7 k := by decide +kernel
lemma column52_1_r0_8_eq : ∀ k : Fin 16, column52_1Expr 0 8 k = column52_1_r0_8 k := by decide +kernel
lemma column52_1_r0_9_eq : ∀ k : Fin 16, column52_1Expr 0 9 k = column52_1_r0_9 k := by decide +kernel
lemma column52_1_r0_10_eq : ∀ k : Fin 16, column52_1Expr 0 10 k = column52_1_r0_10 k := by decide +kernel
lemma column52_1_r0_11_eq : ∀ k : Fin 16, column52_1Expr 0 11 k = column52_1_r0_11 k := by decide +kernel
lemma column52_1_r0_12_eq : ∀ k : Fin 16, column52_1Expr 0 12 k = column52_1_r0_12 k := by decide +kernel
lemma column52_1_r0_13_eq : ∀ k : Fin 16, column52_1Expr 0 13 k = column52_1_r0_13 k := by decide +kernel
lemma column52_1_r0_14_eq : ∀ k : Fin 16, column52_1Expr 0 14 k = column52_1_r0_14 k := by decide +kernel
lemma column52_1_r0_15_eq : ∀ k : Fin 16, column52_1Expr 0 15 k = column52_1_r0_15 k := by decide +kernel
lemma column52_1_r0_eq (i k : Fin 16) : column52_1Expr 0 i k = column52_1_r0 i k := by
  fin_cases i
  · exact column52_1_r0_0_eq k
  · exact column52_1_r0_1_eq k
  · exact column52_1_r0_2_eq k
  · exact column52_1_r0_3_eq k
  · exact column52_1_r0_4_eq k
  · exact column52_1_r0_5_eq k
  · exact column52_1_r0_6_eq k
  · exact column52_1_r0_7_eq k
  · exact column52_1_r0_8_eq k
  · exact column52_1_r0_9_eq k
  · exact column52_1_r0_10_eq k
  · exact column52_1_r0_11_eq k
  · exact column52_1_r0_12_eq k
  · exact column52_1_r0_13_eq k
  · exact column52_1_r0_14_eq k
  · exact column52_1_r0_15_eq k
lemma column52_1_r1_0_eq : ∀ k : Fin 16, column52_1Expr 1 0 k = column52_1_r1_0 k := by decide +kernel
lemma column52_1_r1_1_eq : ∀ k : Fin 16, column52_1Expr 1 1 k = column52_1_r1_1 k := by decide +kernel
lemma column52_1_r1_2_eq : ∀ k : Fin 16, column52_1Expr 1 2 k = column52_1_r1_2 k := by decide +kernel
lemma column52_1_r1_3_eq : ∀ k : Fin 16, column52_1Expr 1 3 k = column52_1_r1_3 k := by decide +kernel
lemma column52_1_r1_4_eq : ∀ k : Fin 16, column52_1Expr 1 4 k = column52_1_r1_4 k := by decide +kernel
lemma column52_1_r1_5_eq : ∀ k : Fin 16, column52_1Expr 1 5 k = column52_1_r1_5 k := by decide +kernel
lemma column52_1_r1_6_eq : ∀ k : Fin 16, column52_1Expr 1 6 k = column52_1_r1_6 k := by decide +kernel
lemma column52_1_r1_7_eq : ∀ k : Fin 16, column52_1Expr 1 7 k = column52_1_r1_7 k := by decide +kernel
lemma column52_1_r1_8_eq : ∀ k : Fin 16, column52_1Expr 1 8 k = column52_1_r1_8 k := by decide +kernel
lemma column52_1_r1_9_eq : ∀ k : Fin 16, column52_1Expr 1 9 k = column52_1_r1_9 k := by decide +kernel
lemma column52_1_r1_10_eq : ∀ k : Fin 16, column52_1Expr 1 10 k = column52_1_r1_10 k := by decide +kernel
lemma column52_1_r1_11_eq : ∀ k : Fin 16, column52_1Expr 1 11 k = column52_1_r1_11 k := by decide +kernel
lemma column52_1_r1_12_eq : ∀ k : Fin 16, column52_1Expr 1 12 k = column52_1_r1_12 k := by decide +kernel
lemma column52_1_r1_13_eq : ∀ k : Fin 16, column52_1Expr 1 13 k = column52_1_r1_13 k := by decide +kernel
lemma column52_1_r1_14_eq : ∀ k : Fin 16, column52_1Expr 1 14 k = column52_1_r1_14 k := by decide +kernel
lemma column52_1_r1_15_eq : ∀ k : Fin 16, column52_1Expr 1 15 k = column52_1_r1_15 k := by decide +kernel
lemma column52_1_r1_eq (i k : Fin 16) : column52_1Expr 1 i k = column52_1_r1 i k := by
  fin_cases i
  · exact column52_1_r1_0_eq k
  · exact column52_1_r1_1_eq k
  · exact column52_1_r1_2_eq k
  · exact column52_1_r1_3_eq k
  · exact column52_1_r1_4_eq k
  · exact column52_1_r1_5_eq k
  · exact column52_1_r1_6_eq k
  · exact column52_1_r1_7_eq k
  · exact column52_1_r1_8_eq k
  · exact column52_1_r1_9_eq k
  · exact column52_1_r1_10_eq k
  · exact column52_1_r1_11_eq k
  · exact column52_1_r1_12_eq k
  · exact column52_1_r1_13_eq k
  · exact column52_1_r1_14_eq k
  · exact column52_1_r1_15_eq k
lemma column52_1_r2_0_eq : ∀ k : Fin 16, column52_1Expr 2 0 k = column52_1_r2_0 k := by decide +kernel
lemma column52_1_r2_1_eq : ∀ k : Fin 16, column52_1Expr 2 1 k = column52_1_r2_1 k := by decide +kernel
lemma column52_1_r2_2_eq : ∀ k : Fin 16, column52_1Expr 2 2 k = column52_1_r2_2 k := by decide +kernel
lemma column52_1_r2_3_eq : ∀ k : Fin 16, column52_1Expr 2 3 k = column52_1_r2_3 k := by decide +kernel
lemma column52_1_r2_4_eq : ∀ k : Fin 16, column52_1Expr 2 4 k = column52_1_r2_4 k := by decide +kernel
lemma column52_1_r2_5_eq : ∀ k : Fin 16, column52_1Expr 2 5 k = column52_1_r2_5 k := by decide +kernel
lemma column52_1_r2_6_eq : ∀ k : Fin 16, column52_1Expr 2 6 k = column52_1_r2_6 k := by decide +kernel
lemma column52_1_r2_7_eq : ∀ k : Fin 16, column52_1Expr 2 7 k = column52_1_r2_7 k := by decide +kernel
lemma column52_1_r2_8_eq : ∀ k : Fin 16, column52_1Expr 2 8 k = column52_1_r2_8 k := by decide +kernel
lemma column52_1_r2_9_eq : ∀ k : Fin 16, column52_1Expr 2 9 k = column52_1_r2_9 k := by decide +kernel
lemma column52_1_r2_10_eq : ∀ k : Fin 16, column52_1Expr 2 10 k = column52_1_r2_10 k := by decide +kernel
lemma column52_1_r2_11_eq : ∀ k : Fin 16, column52_1Expr 2 11 k = column52_1_r2_11 k := by decide +kernel
lemma column52_1_r2_12_eq : ∀ k : Fin 16, column52_1Expr 2 12 k = column52_1_r2_12 k := by decide +kernel
lemma column52_1_r2_13_eq : ∀ k : Fin 16, column52_1Expr 2 13 k = column52_1_r2_13 k := by decide +kernel
lemma column52_1_r2_14_eq : ∀ k : Fin 16, column52_1Expr 2 14 k = column52_1_r2_14 k := by decide +kernel
lemma column52_1_r2_15_eq : ∀ k : Fin 16, column52_1Expr 2 15 k = column52_1_r2_15 k := by decide +kernel
lemma column52_1_r3_0_eq : ∀ k : Fin 16, column52_1Expr 3 0 k = column52_1_r3_0 k := by decide +kernel
lemma column52_1_r3_1_eq : ∀ k : Fin 16, column52_1Expr 3 1 k = column52_1_r3_1 k := by decide +kernel
lemma column52_1_r3_2_eq : ∀ k : Fin 16, column52_1Expr 3 2 k = column52_1_r3_2 k := by decide +kernel
lemma column52_1_r3_3_eq : ∀ k : Fin 16, column52_1Expr 3 3 k = column52_1_r3_3 k := by decide +kernel
lemma column52_1_r3_4_eq : ∀ k : Fin 16, column52_1Expr 3 4 k = column52_1_r3_4 k := by decide +kernel
lemma column52_1_r3_5_eq : ∀ k : Fin 16, column52_1Expr 3 5 k = column52_1_r3_5 k := by decide +kernel
lemma column52_1_r3_6_eq : ∀ k : Fin 16, column52_1Expr 3 6 k = column52_1_r3_6 k := by decide +kernel
lemma column52_1_r3_7_eq : ∀ k : Fin 16, column52_1Expr 3 7 k = column52_1_r3_7 k := by decide +kernel
lemma column52_1_r3_8_eq : ∀ k : Fin 16, column52_1Expr 3 8 k = column52_1_r3_8 k := by decide +kernel
lemma column52_1_r3_9_eq : ∀ k : Fin 16, column52_1Expr 3 9 k = column52_1_r3_9 k := by decide +kernel
lemma column52_1_r3_10_eq : ∀ k : Fin 16, column52_1Expr 3 10 k = column52_1_r3_10 k := by decide +kernel
lemma column52_1_r3_11_eq : ∀ k : Fin 16, column52_1Expr 3 11 k = column52_1_r3_11 k := by decide +kernel
lemma column52_1_r3_12_eq : ∀ k : Fin 16, column52_1Expr 3 12 k = column52_1_r3_12 k := by decide +kernel
lemma column52_1_r3_13_eq : ∀ k : Fin 16, column52_1Expr 3 13 k = column52_1_r3_13 k := by decide +kernel
lemma column52_1_r3_14_eq : ∀ k : Fin 16, column52_1Expr 3 14 k = column52_1_r3_14 k := by decide +kernel
lemma column52_1_r3_15_eq : ∀ k : Fin 16, column52_1Expr 3 15 k = column52_1_r3_15 k := by decide +kernel
lemma column52_1_r3_eq (i k : Fin 16) : column52_1Expr 3 i k = column52_1_r3 i k := by
  fin_cases i
  · exact column52_1_r3_0_eq k
  · exact column52_1_r3_1_eq k
  · exact column52_1_r3_2_eq k
  · exact column52_1_r3_3_eq k
  · exact column52_1_r3_4_eq k
  · exact column52_1_r3_5_eq k
  · exact column52_1_r3_6_eq k
  · exact column52_1_r3_7_eq k
  · exact column52_1_r3_8_eq k
  · exact column52_1_r3_9_eq k
  · exact column52_1_r3_10_eq k
  · exact column52_1_r3_11_eq k
  · exact column52_1_r3_12_eq k
  · exact column52_1_r3_13_eq k
  · exact column52_1_r3_14_eq k
  · exact column52_1_r3_15_eq k
lemma column52_1_r4_0_eq : ∀ k : Fin 16, column52_1Expr 4 0 k = column52_1_r4_0 k := by decide +kernel
lemma column52_1_r4_1_eq : ∀ k : Fin 16, column52_1Expr 4 1 k = column52_1_r4_1 k := by decide +kernel
lemma column52_1_r4_2_eq : ∀ k : Fin 16, column52_1Expr 4 2 k = column52_1_r4_2 k := by decide +kernel
lemma column52_1_r4_3_eq : ∀ k : Fin 16, column52_1Expr 4 3 k = column52_1_r4_3 k := by decide +kernel
lemma column52_1_r4_4_eq : ∀ k : Fin 16, column52_1Expr 4 4 k = column52_1_r4_4 k := by decide +kernel
lemma column52_1_r4_5_eq : ∀ k : Fin 16, column52_1Expr 4 5 k = column52_1_r4_5 k := by decide +kernel
lemma column52_1_r4_6_eq : ∀ k : Fin 16, column52_1Expr 4 6 k = column52_1_r4_6 k := by decide +kernel
lemma column52_1_r4_7_eq : ∀ k : Fin 16, column52_1Expr 4 7 k = column52_1_r4_7 k := by decide +kernel
lemma column52_1_r4_8_eq : ∀ k : Fin 16, column52_1Expr 4 8 k = column52_1_r4_8 k := by decide +kernel
lemma column52_1_r4_9_eq : ∀ k : Fin 16, column52_1Expr 4 9 k = column52_1_r4_9 k := by decide +kernel
lemma column52_1_r4_10_eq : ∀ k : Fin 16, column52_1Expr 4 10 k = column52_1_r4_10 k := by decide +kernel
lemma column52_1_r4_11_eq : ∀ k : Fin 16, column52_1Expr 4 11 k = column52_1_r4_11 k := by decide +kernel
lemma column52_1_r4_12_eq : ∀ k : Fin 16, column52_1Expr 4 12 k = column52_1_r4_12 k := by decide +kernel
lemma column52_1_r4_13_eq : ∀ k : Fin 16, column52_1Expr 4 13 k = column52_1_r4_13 k := by decide +kernel
lemma column52_1_r4_14_eq : ∀ k : Fin 16, column52_1Expr 4 14 k = column52_1_r4_14 k := by decide +kernel
lemma column52_1_r4_15_eq : ∀ k : Fin 16, column52_1Expr 4 15 k = column52_1_r4_15 k := by decide +kernel
lemma column52_1_r4_eq (i k : Fin 16) : column52_1Expr 4 i k = column52_1_r4 i k := by
  fin_cases i
  · exact column52_1_r4_0_eq k
  · exact column52_1_r4_1_eq k
  · exact column52_1_r4_2_eq k
  · exact column52_1_r4_3_eq k
  · exact column52_1_r4_4_eq k
  · exact column52_1_r4_5_eq k
  · exact column52_1_r4_6_eq k
  · exact column52_1_r4_7_eq k
  · exact column52_1_r4_8_eq k
  · exact column52_1_r4_9_eq k
  · exact column52_1_r4_10_eq k
  · exact column52_1_r4_11_eq k
  · exact column52_1_r4_12_eq k
  · exact column52_1_r4_13_eq k
  · exact column52_1_r4_14_eq k
  · exact column52_1_r4_15_eq k
lemma column52_1_r5_0_eq : ∀ k : Fin 16, column52_1Expr 5 0 k = column52_1_r5_0 k := by decide +kernel
lemma column52_1_r5_1_eq : ∀ k : Fin 16, column52_1Expr 5 1 k = column52_1_r5_1 k := by decide +kernel
lemma column52_1_r5_2_eq : ∀ k : Fin 16, column52_1Expr 5 2 k = column52_1_r5_2 k := by decide +kernel
lemma column52_1_r5_3_eq : ∀ k : Fin 16, column52_1Expr 5 3 k = column52_1_r5_3 k := by decide +kernel
lemma column52_1_r5_4_eq : ∀ k : Fin 16, column52_1Expr 5 4 k = column52_1_r5_4 k := by decide +kernel
lemma column52_1_r5_5_eq : ∀ k : Fin 16, column52_1Expr 5 5 k = column52_1_r5_5 k := by decide +kernel
lemma column52_1_r5_6_eq : ∀ k : Fin 16, column52_1Expr 5 6 k = column52_1_r5_6 k := by decide +kernel
lemma column52_1_r5_7_eq : ∀ k : Fin 16, column52_1Expr 5 7 k = column52_1_r5_7 k := by decide +kernel
lemma column52_1_r5_8_eq : ∀ k : Fin 16, column52_1Expr 5 8 k = column52_1_r5_8 k := by decide +kernel
lemma column52_1_r5_9_eq : ∀ k : Fin 16, column52_1Expr 5 9 k = column52_1_r5_9 k := by decide +kernel
lemma column52_1_r5_10_eq : ∀ k : Fin 16, column52_1Expr 5 10 k = column52_1_r5_10 k := by decide +kernel
lemma column52_1_r5_11_eq : ∀ k : Fin 16, column52_1Expr 5 11 k = column52_1_r5_11 k := by decide +kernel
lemma column52_1_r5_12_eq : ∀ k : Fin 16, column52_1Expr 5 12 k = column52_1_r5_12 k := by decide +kernel
lemma column52_1_r5_13_eq : ∀ k : Fin 16, column52_1Expr 5 13 k = column52_1_r5_13 k := by decide +kernel
lemma column52_1_r5_14_eq : ∀ k : Fin 16, column52_1Expr 5 14 k = column52_1_r5_14 k := by decide +kernel
lemma column52_1_r5_15_eq : ∀ k : Fin 16, column52_1Expr 5 15 k = column52_1_r5_15 k := by decide +kernel
lemma column52_1_r5_eq (i k : Fin 16) : column52_1Expr 5 i k = column52_1_r5 i k := by
  fin_cases i
  · exact column52_1_r5_0_eq k
  · exact column52_1_r5_1_eq k
  · exact column52_1_r5_2_eq k
  · exact column52_1_r5_3_eq k
  · exact column52_1_r5_4_eq k
  · exact column52_1_r5_5_eq k
  · exact column52_1_r5_6_eq k
  · exact column52_1_r5_7_eq k
  · exact column52_1_r5_8_eq k
  · exact column52_1_r5_9_eq k
  · exact column52_1_r5_10_eq k
  · exact column52_1_r5_11_eq k
  · exact column52_1_r5_12_eq k
  · exact column52_1_r5_13_eq k
  · exact column52_1_r5_14_eq k
  · exact column52_1_r5_15_eq k
noncomputable def column55_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power55 j i k)
lemma column55_0_r0_0_eq : ∀ k : Fin 16, column55_0Expr 0 0 k = column55_0_r0_0 k := by decide +kernel
lemma column55_0_r0_1_eq : ∀ k : Fin 16, column55_0Expr 0 1 k = column55_0_r0_1 k := by decide +kernel
lemma column55_0_r0_2_eq : ∀ k : Fin 16, column55_0Expr 0 2 k = column55_0_r0_2 k := by decide +kernel
lemma column55_0_r0_3_eq : ∀ k : Fin 16, column55_0Expr 0 3 k = column55_0_r0_3 k := by decide +kernel
lemma column55_0_r0_4_eq : ∀ k : Fin 16, column55_0Expr 0 4 k = column55_0_r0_4 k := by decide +kernel
lemma column55_0_r0_5_eq : ∀ k : Fin 16, column55_0Expr 0 5 k = column55_0_r0_5 k := by decide +kernel
lemma column55_0_r0_6_eq : ∀ k : Fin 16, column55_0Expr 0 6 k = column55_0_r0_6 k := by decide +kernel
lemma column55_0_r0_7_eq : ∀ k : Fin 16, column55_0Expr 0 7 k = column55_0_r0_7 k := by decide +kernel
lemma column55_0_r0_8_eq : ∀ k : Fin 16, column55_0Expr 0 8 k = column55_0_r0_8 k := by decide +kernel
lemma column55_0_r0_9_eq : ∀ k : Fin 16, column55_0Expr 0 9 k = column55_0_r0_9 k := by decide +kernel
lemma column55_0_r0_10_eq : ∀ k : Fin 16, column55_0Expr 0 10 k = column55_0_r0_10 k := by decide +kernel
lemma column55_0_r0_11_eq : ∀ k : Fin 16, column55_0Expr 0 11 k = column55_0_r0_11 k := by decide +kernel
lemma column55_0_r0_12_eq : ∀ k : Fin 16, column55_0Expr 0 12 k = column55_0_r0_12 k := by decide +kernel
lemma column55_0_r0_13_eq : ∀ k : Fin 16, column55_0Expr 0 13 k = column55_0_r0_13 k := by decide +kernel
lemma column55_0_r0_14_eq : ∀ k : Fin 16, column55_0Expr 0 14 k = column55_0_r0_14 k := by decide +kernel
lemma column55_0_r0_15_eq : ∀ k : Fin 16, column55_0Expr 0 15 k = column55_0_r0_15 k := by decide +kernel
lemma column55_0_r0_eq (i k : Fin 16) : column55_0Expr 0 i k = column55_0_r0 i k := by
  fin_cases i
  · exact column55_0_r0_0_eq k
  · exact column55_0_r0_1_eq k
  · exact column55_0_r0_2_eq k
  · exact column55_0_r0_3_eq k
  · exact column55_0_r0_4_eq k
  · exact column55_0_r0_5_eq k
  · exact column55_0_r0_6_eq k
  · exact column55_0_r0_7_eq k
  · exact column55_0_r0_8_eq k
  · exact column55_0_r0_9_eq k
  · exact column55_0_r0_10_eq k
  · exact column55_0_r0_11_eq k
  · exact column55_0_r0_12_eq k
  · exact column55_0_r0_13_eq k
  · exact column55_0_r0_14_eq k
  · exact column55_0_r0_15_eq k
lemma column55_0_r1_0_eq : ∀ k : Fin 16, column55_0Expr 1 0 k = column55_0_r1_0 k := by decide +kernel
lemma column55_0_r1_1_eq : ∀ k : Fin 16, column55_0Expr 1 1 k = column55_0_r1_1 k := by decide +kernel
lemma column55_0_r1_2_eq : ∀ k : Fin 16, column55_0Expr 1 2 k = column55_0_r1_2 k := by decide +kernel
lemma column55_0_r1_3_eq : ∀ k : Fin 16, column55_0Expr 1 3 k = column55_0_r1_3 k := by decide +kernel
lemma column55_0_r1_4_eq : ∀ k : Fin 16, column55_0Expr 1 4 k = column55_0_r1_4 k := by decide +kernel
lemma column55_0_r1_5_eq : ∀ k : Fin 16, column55_0Expr 1 5 k = column55_0_r1_5 k := by decide +kernel
lemma column55_0_r1_6_eq : ∀ k : Fin 16, column55_0Expr 1 6 k = column55_0_r1_6 k := by decide +kernel
lemma column55_0_r1_7_eq : ∀ k : Fin 16, column55_0Expr 1 7 k = column55_0_r1_7 k := by decide +kernel
lemma column55_0_r1_8_eq : ∀ k : Fin 16, column55_0Expr 1 8 k = column55_0_r1_8 k := by decide +kernel
lemma column55_0_r1_9_eq : ∀ k : Fin 16, column55_0Expr 1 9 k = column55_0_r1_9 k := by decide +kernel
lemma column55_0_r1_10_eq : ∀ k : Fin 16, column55_0Expr 1 10 k = column55_0_r1_10 k := by decide +kernel
lemma column55_0_r1_11_eq : ∀ k : Fin 16, column55_0Expr 1 11 k = column55_0_r1_11 k := by decide +kernel
lemma column55_0_r1_12_eq : ∀ k : Fin 16, column55_0Expr 1 12 k = column55_0_r1_12 k := by decide +kernel
lemma column55_0_r1_13_eq : ∀ k : Fin 16, column55_0Expr 1 13 k = column55_0_r1_13 k := by decide +kernel
lemma column55_0_r1_14_eq : ∀ k : Fin 16, column55_0Expr 1 14 k = column55_0_r1_14 k := by decide +kernel
lemma column55_0_r1_15_eq : ∀ k : Fin 16, column55_0Expr 1 15 k = column55_0_r1_15 k := by decide +kernel
lemma column55_0_r1_eq (i k : Fin 16) : column55_0Expr 1 i k = column55_0_r1 i k := by
  fin_cases i
  · exact column55_0_r1_0_eq k
  · exact column55_0_r1_1_eq k
  · exact column55_0_r1_2_eq k
  · exact column55_0_r1_3_eq k
  · exact column55_0_r1_4_eq k
  · exact column55_0_r1_5_eq k
  · exact column55_0_r1_6_eq k
  · exact column55_0_r1_7_eq k
  · exact column55_0_r1_8_eq k
  · exact column55_0_r1_9_eq k
  · exact column55_0_r1_10_eq k
  · exact column55_0_r1_11_eq k
  · exact column55_0_r1_12_eq k
  · exact column55_0_r1_13_eq k
  · exact column55_0_r1_14_eq k
  · exact column55_0_r1_15_eq k
lemma column55_0_r2_0_eq : ∀ k : Fin 16, column55_0Expr 2 0 k = column55_0_r2_0 k := by decide +kernel
lemma column55_0_r2_1_eq : ∀ k : Fin 16, column55_0Expr 2 1 k = column55_0_r2_1 k := by decide +kernel
lemma column55_0_r2_2_eq : ∀ k : Fin 16, column55_0Expr 2 2 k = column55_0_r2_2 k := by decide +kernel
lemma column55_0_r2_3_eq : ∀ k : Fin 16, column55_0Expr 2 3 k = column55_0_r2_3 k := by decide +kernel
lemma column55_0_r2_4_eq : ∀ k : Fin 16, column55_0Expr 2 4 k = column55_0_r2_4 k := by decide +kernel
lemma column55_0_r2_5_eq : ∀ k : Fin 16, column55_0Expr 2 5 k = column55_0_r2_5 k := by decide +kernel
lemma column55_0_r2_6_eq : ∀ k : Fin 16, column55_0Expr 2 6 k = column55_0_r2_6 k := by decide +kernel
lemma column55_0_r2_7_eq : ∀ k : Fin 16, column55_0Expr 2 7 k = column55_0_r2_7 k := by decide +kernel
lemma column55_0_r2_8_eq : ∀ k : Fin 16, column55_0Expr 2 8 k = column55_0_r2_8 k := by decide +kernel
lemma column55_0_r2_9_eq : ∀ k : Fin 16, column55_0Expr 2 9 k = column55_0_r2_9 k := by decide +kernel
lemma column55_0_r2_10_eq : ∀ k : Fin 16, column55_0Expr 2 10 k = column55_0_r2_10 k := by decide +kernel
lemma column55_0_r2_11_eq : ∀ k : Fin 16, column55_0Expr 2 11 k = column55_0_r2_11 k := by decide +kernel
lemma column55_0_r2_12_eq : ∀ k : Fin 16, column55_0Expr 2 12 k = column55_0_r2_12 k := by decide +kernel
lemma column55_0_r2_13_eq : ∀ k : Fin 16, column55_0Expr 2 13 k = column55_0_r2_13 k := by decide +kernel
lemma column55_0_r2_14_eq : ∀ k : Fin 16, column55_0Expr 2 14 k = column55_0_r2_14 k := by decide +kernel
lemma column55_0_r2_15_eq : ∀ k : Fin 16, column55_0Expr 2 15 k = column55_0_r2_15 k := by decide +kernel
lemma column55_0_r2_eq (i k : Fin 16) : column55_0Expr 2 i k = column55_0_r2 i k := by
  fin_cases i
  · exact column55_0_r2_0_eq k
  · exact column55_0_r2_1_eq k
  · exact column55_0_r2_2_eq k
  · exact column55_0_r2_3_eq k
  · exact column55_0_r2_4_eq k
  · exact column55_0_r2_5_eq k
  · exact column55_0_r2_6_eq k
  · exact column55_0_r2_7_eq k
  · exact column55_0_r2_8_eq k
  · exact column55_0_r2_9_eq k
  · exact column55_0_r2_10_eq k
  · exact column55_0_r2_11_eq k
  · exact column55_0_r2_12_eq k
  · exact column55_0_r2_13_eq k
  · exact column55_0_r2_14_eq k
  · exact column55_0_r2_15_eq k
lemma column55_0_r3_0_eq : ∀ k : Fin 16, column55_0Expr 3 0 k = column55_0_r3_0 k := by decide +kernel
lemma column55_0_r3_1_eq : ∀ k : Fin 16, column55_0Expr 3 1 k = column55_0_r3_1 k := by decide +kernel
lemma column55_0_r3_2_eq : ∀ k : Fin 16, column55_0Expr 3 2 k = column55_0_r3_2 k := by decide +kernel
lemma column55_0_r3_3_eq : ∀ k : Fin 16, column55_0Expr 3 3 k = column55_0_r3_3 k := by decide +kernel
lemma column55_0_r3_4_eq : ∀ k : Fin 16, column55_0Expr 3 4 k = column55_0_r3_4 k := by decide +kernel
lemma column55_0_r3_5_eq : ∀ k : Fin 16, column55_0Expr 3 5 k = column55_0_r3_5 k := by decide +kernel
lemma column55_0_r3_6_eq : ∀ k : Fin 16, column55_0Expr 3 6 k = column55_0_r3_6 k := by decide +kernel
lemma column55_0_r3_7_eq : ∀ k : Fin 16, column55_0Expr 3 7 k = column55_0_r3_7 k := by decide +kernel
lemma column55_0_r3_8_eq : ∀ k : Fin 16, column55_0Expr 3 8 k = column55_0_r3_8 k := by decide +kernel
lemma column55_0_r3_9_eq : ∀ k : Fin 16, column55_0Expr 3 9 k = column55_0_r3_9 k := by decide +kernel
lemma column55_0_r3_10_eq : ∀ k : Fin 16, column55_0Expr 3 10 k = column55_0_r3_10 k := by decide +kernel
lemma column55_0_r3_11_eq : ∀ k : Fin 16, column55_0Expr 3 11 k = column55_0_r3_11 k := by decide +kernel
lemma column55_0_r3_12_eq : ∀ k : Fin 16, column55_0Expr 3 12 k = column55_0_r3_12 k := by decide +kernel
lemma column55_0_r3_13_eq : ∀ k : Fin 16, column55_0Expr 3 13 k = column55_0_r3_13 k := by decide +kernel
lemma column55_0_r3_14_eq : ∀ k : Fin 16, column55_0Expr 3 14 k = column55_0_r3_14 k := by decide +kernel
lemma column55_0_r3_15_eq : ∀ k : Fin 16, column55_0Expr 3 15 k = column55_0_r3_15 k := by decide +kernel
lemma column55_0_r3_eq (i k : Fin 16) : column55_0Expr 3 i k = column55_0_r3 i k := by
  fin_cases i
  · exact column55_0_r3_0_eq k
  · exact column55_0_r3_1_eq k
  · exact column55_0_r3_2_eq k
  · exact column55_0_r3_3_eq k
  · exact column55_0_r3_4_eq k
  · exact column55_0_r3_5_eq k
  · exact column55_0_r3_6_eq k
  · exact column55_0_r3_7_eq k
  · exact column55_0_r3_8_eq k
  · exact column55_0_r3_9_eq k
  · exact column55_0_r3_10_eq k
  · exact column55_0_r3_11_eq k
  · exact column55_0_r3_12_eq k
  · exact column55_0_r3_13_eq k
  · exact column55_0_r3_14_eq k
  · exact column55_0_r3_15_eq k
lemma column55_0_r4_0_eq : ∀ k : Fin 16, column55_0Expr 4 0 k = column55_0_r4_0 k := by decide +kernel
lemma column55_0_r4_1_eq : ∀ k : Fin 16, column55_0Expr 4 1 k = column55_0_r4_1 k := by decide +kernel
lemma column55_0_r4_2_eq : ∀ k : Fin 16, column55_0Expr 4 2 k = column55_0_r4_2 k := by decide +kernel
lemma column55_0_r4_3_eq : ∀ k : Fin 16, column55_0Expr 4 3 k = column55_0_r4_3 k := by decide +kernel
lemma column55_0_r4_4_eq : ∀ k : Fin 16, column55_0Expr 4 4 k = column55_0_r4_4 k := by decide +kernel
lemma column55_0_r4_5_eq : ∀ k : Fin 16, column55_0Expr 4 5 k = column55_0_r4_5 k := by decide +kernel
lemma column55_0_r4_6_eq : ∀ k : Fin 16, column55_0Expr 4 6 k = column55_0_r4_6 k := by decide +kernel
lemma column55_0_r4_7_eq : ∀ k : Fin 16, column55_0Expr 4 7 k = column55_0_r4_7 k := by decide +kernel
lemma column55_0_r4_8_eq : ∀ k : Fin 16, column55_0Expr 4 8 k = column55_0_r4_8 k := by decide +kernel
lemma column55_0_r4_9_eq : ∀ k : Fin 16, column55_0Expr 4 9 k = column55_0_r4_9 k := by decide +kernel
lemma column55_0_r4_10_eq : ∀ k : Fin 16, column55_0Expr 4 10 k = column55_0_r4_10 k := by decide +kernel
lemma column55_0_r4_11_eq : ∀ k : Fin 16, column55_0Expr 4 11 k = column55_0_r4_11 k := by decide +kernel
lemma column55_0_r4_12_eq : ∀ k : Fin 16, column55_0Expr 4 12 k = column55_0_r4_12 k := by decide +kernel
lemma column55_0_r4_13_eq : ∀ k : Fin 16, column55_0Expr 4 13 k = column55_0_r4_13 k := by decide +kernel
lemma column55_0_r4_14_eq : ∀ k : Fin 16, column55_0Expr 4 14 k = column55_0_r4_14 k := by decide +kernel
lemma column55_0_r4_15_eq : ∀ k : Fin 16, column55_0Expr 4 15 k = column55_0_r4_15 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns70
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
noncomputable def column61_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power61 j i k)
noncomputable def column64_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power64 j i k)
noncomputable def column67_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power67 j i k)
noncomputable def column69_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power69 j i k)
noncomputable def column69_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power69 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments16
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
namespace cm4_16_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm4_16_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments9
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
namespace cm4_9_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm4_9_1_0
namespace cm4_9_1_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm4_9_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments45
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
namespace cm45_3_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm45_3_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments49
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
namespace cm49_1_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm49_1_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments52
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
namespace cm52_3_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm52_3_1_0
end SharpPlanar.CachedData

end OAI
end


