-- Prove2me | Definitions.Def_OAIQ098D265
-- name    : OAIQ098D265
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:33:48.403903+00:00
-- url     : https://prove2.me/theorems/5754bd6c-bf71-4f00-a9f3-bbf9069a4210
-- title:
--   Definitions bundle OAIQ098D265 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 661 declarations of OpenAI's Lean: 70 definitions and 591 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.cm12_3_0_1.s2`, `OAI.SharpPlanar.CachedData.cm12_4_0_0.s0`, `OAI.SharpPlanar.CachedData.cm12_4_0_0.sums`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.s0`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.s1`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.s2`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.s3`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.s4`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.sums`, `OAI.SharpPlanar.CachedData.cm16_4_1_0.s0`, `OAI.SharpPlanar.CachedData.cm16_4_1_0.sums`, `OAI.SharpPlanar.CachedData.cm1_12_0_0.s0`, `OAI.SharpPlanar.CachedData.cm1_12_0_0.sums`, `OAI.SharpPlanar.CachedData.cm1_12_0_1.s0`, `OAI.SharpPlanar.CachedData.cm1_12_0_1.sums`, `OAI.SharpPlanar.CachedData.cm1_12_1_0.s0`, `OAI.SharpPlanar.CachedData.cm1_12_1_0.s1`, `OAI.SharpPlanar.CachedData.cm1_12_1_0.s2`, `OAI.SharpPlanar.CachedData.cm1_12_1_0.sums`, `OAI.SharpPlanar.CachedData.cm1_12_1_1.s0`, `OAI.SharpPlanar.CachedData.cm1_12_1_1.sums`, `OAI.SharpPlanar.CachedData.cm1_13_0_0.s1`, `OAI.SharpPlanar.CachedData.cm1_13_0_0.sums`, `OAI.SharpPlanar.CachedData.cm1_15_0_1.s0`, `OAI.SharpPlanar.CachedData.cm1_15_0_1.sums`, `OAI.SharpPlanar.CachedData.cm1_16_0_1.s0`, `OAI.SharpPlanar.CachedData.cm1_16_0_1.sums`, `OAI.SharpPlanar.CachedData.cm1_7_0_0.s0`, `OAI.SharpPlanar.CachedData.cm1_7_0_0.sums`, `OAI.SharpPlanar.CachedData.cm21_1_0_1.s0`, `OAI.SharpPlanar.CachedData.cm21_1_0_1.sums`, `OAI.SharpPlanar.CachedData.cm21_3_0_0.s0`, `OAI.SharpPlanar.CachedData.cm21_3_0_0.sums`, `OAI.SharpPlanar.CachedData.cm24_4_0_1.s0`, `OAI.SharpPlanar.CachedData.cm24_4_0_1.s1`, `OAI.SharpPlanar.CachedData.cm24_4_0_1.s2`, `OAI.SharpPlanar.CachedData.cm24_4_0_1.s3`, `OAI.SharpPlanar.CachedData.cm24_4_0_1.s4`, `OAI.SharpPlanar.CachedData.cm24_4_0_1.sums`, `OAI.SharpPlanar.CachedData.cm24_4_1_0.s0` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Columns10`, `PlanarPacking_Certificate_Columns20`, `PlanarPacking_Certificate_Columns30`, `PlanarPacking_Certificate_Columns40`, `PlanarPacking_Certificate_KernelValues10`, `PlanarPacking_Certificate_LMoments12`, `PlanarPacking_Certificate_LMoments13`, `PlanarPacking_Certificate_LMoments15`, `PlanarPacking_Certificate_LMoments16`, `PlanarPacking_Certificate_LMoments7`, `PlanarPacking_Certificate_TransformedPowers10`, `PlanarPacking_Certificate_TransformedPowers20`, `PlanarPacking_Certificate_UMoments12`, `PlanarPacking_Certificate_UMoments15`, `PlanarPacking_Certificate_UMoments16`, `PlanarPacking_Certificate_UMoments21`, `PlanarPacking_Certificate_UMoments24`, `PlanarPacking_Certificate_UMoments27`, `PlanarPacking_Certificate_UMoments31`.
--
--   **Imports.** It imports the bundles `OAIQ098D009`, `OAIQ098D010`, `OAIQ098D012`, `OAIQ098D014`, `OAIQ098D041`, `OAIQ098D042`, `OAIQ098D043`, `OAIQ098D044`, `OAIQ098D045`, `OAIQ098D047`, `OAIQ098D054`, `OAIQ098D059`, `OAIQ098D060`, `OAIQ098D061`, `OAIQ098D065`, `OAIQ098D069`, `OAIQ098D070`, `OAIQ098D071`, `OAIQ098D072`, `OAIQ098D073`, `OAIQ098D075`, `OAIQ098D076`, `OAIQ098D079`, `OAIQ098D082`, `OAIQ098D083`, `OAIQ098D085`, `OAIQ098D086`, `OAIQ098D087`, `OAIQ098D088`, `OAIQ098D089`, `OAIQ098D090`, `OAIQ098D091`, `OAIQ098D092`, `OAIQ098D093`, `OAIQ098D094`, `OAIQ098D095`, `OAIQ098D096` and `OAIQ098D097` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D278`, `OAIQ098D279`, `OAIQ098D282`, `OAIQ098D283`, `OAIQ098D284`, `OAIQ098D285`, `OAIQ098D286`, `OAIQ098D287`, `OAIQ098D289`, `OAIQ098D290`, `OAIQ098D292`, `OAIQ098D295`, `OAIQ098D297`, `OAIQ098D298`, `OAIQ098D299`, `OAIQ098D300`, `OAIQ098D307`, `OAIQ098D317`, `OAIQ098D356`, `OAIQ098D391`, `OAIQ098D451`, `OAIQ098D461` and `OAIQ098D475`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D009
import Definitions.Def_OAIQ098D010
import Definitions.Def_OAIQ098D012
import Definitions.Def_OAIQ098D014
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D042
import Definitions.Def_OAIQ098D043
import Definitions.Def_OAIQ098D044
import Definitions.Def_OAIQ098D045
import Definitions.Def_OAIQ098D047
import Definitions.Def_OAIQ098D054
import Definitions.Def_OAIQ098D059
import Definitions.Def_OAIQ098D060
import Definitions.Def_OAIQ098D061
import Definitions.Def_OAIQ098D065
import Definitions.Def_OAIQ098D069
import Definitions.Def_OAIQ098D070
import Definitions.Def_OAIQ098D071
import Definitions.Def_OAIQ098D072
import Definitions.Def_OAIQ098D073
import Definitions.Def_OAIQ098D075
import Definitions.Def_OAIQ098D076
import Definitions.Def_OAIQ098D079
import Definitions.Def_OAIQ098D082
import Definitions.Def_OAIQ098D083
import Definitions.Def_OAIQ098D085
import Definitions.Def_OAIQ098D086
import Definitions.Def_OAIQ098D087
import Definitions.Def_OAIQ098D088
import Definitions.Def_OAIQ098D089
import Definitions.Def_OAIQ098D090
import Definitions.Def_OAIQ098D091
import Definitions.Def_OAIQ098D092
import Definitions.Def_OAIQ098D093
import Definitions.Def_OAIQ098D094
import Definitions.Def_OAIQ098D095
import Definitions.Def_OAIQ098D096
import Definitions.Def_OAIQ098D097

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
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
noncomputable def column1_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power1 j i k)
lemma column1_0_r0_0_eq : ∀ k : Fin 16, column1_0Expr 0 0 k = column1_0_r0_0 k := by decide +kernel
lemma column1_0_r0_1_eq : ∀ k : Fin 16, column1_0Expr 0 1 k = column1_0_r0_1 k := by decide +kernel
lemma column1_0_r0_2_eq : ∀ k : Fin 16, column1_0Expr 0 2 k = column1_0_r0_2 k := by decide +kernel
lemma column1_0_r0_3_eq : ∀ k : Fin 16, column1_0Expr 0 3 k = column1_0_r0_3 k := by decide +kernel
lemma column1_0_r0_4_eq : ∀ k : Fin 16, column1_0Expr 0 4 k = column1_0_r0_4 k := by decide +kernel
lemma column1_0_r0_5_eq : ∀ k : Fin 16, column1_0Expr 0 5 k = column1_0_r0_5 k := by decide +kernel
lemma column1_0_r0_6_eq : ∀ k : Fin 16, column1_0Expr 0 6 k = column1_0_r0_6 k := by decide +kernel
lemma column1_0_r0_7_eq : ∀ k : Fin 16, column1_0Expr 0 7 k = column1_0_r0_7 k := by decide +kernel
lemma column1_0_r0_8_eq : ∀ k : Fin 16, column1_0Expr 0 8 k = column1_0_r0_8 k := by decide +kernel
lemma column1_0_r0_9_eq : ∀ k : Fin 16, column1_0Expr 0 9 k = column1_0_r0_9 k := by decide +kernel
lemma column1_0_r0_10_eq : ∀ k : Fin 16, column1_0Expr 0 10 k = column1_0_r0_10 k := by decide +kernel
lemma column1_0_r0_11_eq : ∀ k : Fin 16, column1_0Expr 0 11 k = column1_0_r0_11 k := by decide +kernel
lemma column1_0_r0_12_eq : ∀ k : Fin 16, column1_0Expr 0 12 k = column1_0_r0_12 k := by decide +kernel
lemma column1_0_r0_13_eq : ∀ k : Fin 16, column1_0Expr 0 13 k = column1_0_r0_13 k := by decide +kernel
lemma column1_0_r0_14_eq : ∀ k : Fin 16, column1_0Expr 0 14 k = column1_0_r0_14 k := by decide +kernel
lemma column1_0_r0_15_eq : ∀ k : Fin 16, column1_0Expr 0 15 k = column1_0_r0_15 k := by decide +kernel
lemma column1_0_r0_eq (i k : Fin 16) : column1_0Expr 0 i k = column1_0_r0 i k := by
  fin_cases i
  · exact column1_0_r0_0_eq k
  · exact column1_0_r0_1_eq k
  · exact column1_0_r0_2_eq k
  · exact column1_0_r0_3_eq k
  · exact column1_0_r0_4_eq k
  · exact column1_0_r0_5_eq k
  · exact column1_0_r0_6_eq k
  · exact column1_0_r0_7_eq k
  · exact column1_0_r0_8_eq k
  · exact column1_0_r0_9_eq k
  · exact column1_0_r0_10_eq k
  · exact column1_0_r0_11_eq k
  · exact column1_0_r0_12_eq k
  · exact column1_0_r0_13_eq k
  · exact column1_0_r0_14_eq k
  · exact column1_0_r0_15_eq k
lemma column1_0_r1_0_eq : ∀ k : Fin 16, column1_0Expr 1 0 k = column1_0_r1_0 k := by decide +kernel
lemma column1_0_r1_1_eq : ∀ k : Fin 16, column1_0Expr 1 1 k = column1_0_r1_1 k := by decide +kernel
lemma column1_0_r1_2_eq : ∀ k : Fin 16, column1_0Expr 1 2 k = column1_0_r1_2 k := by decide +kernel
lemma column1_0_r1_3_eq : ∀ k : Fin 16, column1_0Expr 1 3 k = column1_0_r1_3 k := by decide +kernel
lemma column1_0_r1_4_eq : ∀ k : Fin 16, column1_0Expr 1 4 k = column1_0_r1_4 k := by decide +kernel
lemma column1_0_r1_5_eq : ∀ k : Fin 16, column1_0Expr 1 5 k = column1_0_r1_5 k := by decide +kernel
lemma column1_0_r1_6_eq : ∀ k : Fin 16, column1_0Expr 1 6 k = column1_0_r1_6 k := by decide +kernel
lemma column1_0_r1_7_eq : ∀ k : Fin 16, column1_0Expr 1 7 k = column1_0_r1_7 k := by decide +kernel
lemma column1_0_r1_8_eq : ∀ k : Fin 16, column1_0Expr 1 8 k = column1_0_r1_8 k := by decide +kernel
lemma column1_0_r1_9_eq : ∀ k : Fin 16, column1_0Expr 1 9 k = column1_0_r1_9 k := by decide +kernel
lemma column1_0_r1_10_eq : ∀ k : Fin 16, column1_0Expr 1 10 k = column1_0_r1_10 k := by decide +kernel
lemma column1_0_r1_11_eq : ∀ k : Fin 16, column1_0Expr 1 11 k = column1_0_r1_11 k := by decide +kernel
lemma column1_0_r1_12_eq : ∀ k : Fin 16, column1_0Expr 1 12 k = column1_0_r1_12 k := by decide +kernel
lemma column1_0_r1_13_eq : ∀ k : Fin 16, column1_0Expr 1 13 k = column1_0_r1_13 k := by decide +kernel
lemma column1_0_r1_14_eq : ∀ k : Fin 16, column1_0Expr 1 14 k = column1_0_r1_14 k := by decide +kernel
lemma column1_0_r1_15_eq : ∀ k : Fin 16, column1_0Expr 1 15 k = column1_0_r1_15 k := by decide +kernel
lemma column1_0_r1_eq (i k : Fin 16) : column1_0Expr 1 i k = column1_0_r1 i k := by
  fin_cases i
  · exact column1_0_r1_0_eq k
  · exact column1_0_r1_1_eq k
  · exact column1_0_r1_2_eq k
  · exact column1_0_r1_3_eq k
  · exact column1_0_r1_4_eq k
  · exact column1_0_r1_5_eq k
  · exact column1_0_r1_6_eq k
  · exact column1_0_r1_7_eq k
  · exact column1_0_r1_8_eq k
  · exact column1_0_r1_9_eq k
  · exact column1_0_r1_10_eq k
  · exact column1_0_r1_11_eq k
  · exact column1_0_r1_12_eq k
  · exact column1_0_r1_13_eq k
  · exact column1_0_r1_14_eq k
  · exact column1_0_r1_15_eq k
lemma column1_0_r2_0_eq : ∀ k : Fin 16, column1_0Expr 2 0 k = column1_0_r2_0 k := by decide +kernel
lemma column1_0_r2_1_eq : ∀ k : Fin 16, column1_0Expr 2 1 k = column1_0_r2_1 k := by decide +kernel
lemma column1_0_r2_2_eq : ∀ k : Fin 16, column1_0Expr 2 2 k = column1_0_r2_2 k := by decide +kernel
lemma column1_0_r2_3_eq : ∀ k : Fin 16, column1_0Expr 2 3 k = column1_0_r2_3 k := by decide +kernel
lemma column1_0_r2_4_eq : ∀ k : Fin 16, column1_0Expr 2 4 k = column1_0_r2_4 k := by decide +kernel
lemma column1_0_r2_5_eq : ∀ k : Fin 16, column1_0Expr 2 5 k = column1_0_r2_5 k := by decide +kernel
lemma column1_0_r2_6_eq : ∀ k : Fin 16, column1_0Expr 2 6 k = column1_0_r2_6 k := by decide +kernel
lemma column1_0_r2_7_eq : ∀ k : Fin 16, column1_0Expr 2 7 k = column1_0_r2_7 k := by decide +kernel
lemma column1_0_r2_8_eq : ∀ k : Fin 16, column1_0Expr 2 8 k = column1_0_r2_8 k := by decide +kernel
lemma column1_0_r2_9_eq : ∀ k : Fin 16, column1_0Expr 2 9 k = column1_0_r2_9 k := by decide +kernel
lemma column1_0_r2_10_eq : ∀ k : Fin 16, column1_0Expr 2 10 k = column1_0_r2_10 k := by decide +kernel
lemma column1_0_r2_11_eq : ∀ k : Fin 16, column1_0Expr 2 11 k = column1_0_r2_11 k := by decide +kernel
lemma column1_0_r2_12_eq : ∀ k : Fin 16, column1_0Expr 2 12 k = column1_0_r2_12 k := by decide +kernel
lemma column1_0_r2_13_eq : ∀ k : Fin 16, column1_0Expr 2 13 k = column1_0_r2_13 k := by decide +kernel
lemma column1_0_r2_14_eq : ∀ k : Fin 16, column1_0Expr 2 14 k = column1_0_r2_14 k := by decide +kernel
lemma column1_0_r2_15_eq : ∀ k : Fin 16, column1_0Expr 2 15 k = column1_0_r2_15 k := by decide +kernel
lemma column1_0_r2_eq (i k : Fin 16) : column1_0Expr 2 i k = column1_0_r2 i k := by
  fin_cases i
  · exact column1_0_r2_0_eq k
  · exact column1_0_r2_1_eq k
  · exact column1_0_r2_2_eq k
  · exact column1_0_r2_3_eq k
  · exact column1_0_r2_4_eq k
  · exact column1_0_r2_5_eq k
  · exact column1_0_r2_6_eq k
  · exact column1_0_r2_7_eq k
  · exact column1_0_r2_8_eq k
  · exact column1_0_r2_9_eq k
  · exact column1_0_r2_10_eq k
  · exact column1_0_r2_11_eq k
  · exact column1_0_r2_12_eq k
  · exact column1_0_r2_13_eq k
  · exact column1_0_r2_14_eq k
  · exact column1_0_r2_15_eq k
lemma column1_0_r3_0_eq : ∀ k : Fin 16, column1_0Expr 3 0 k = column1_0_r3_0 k := by decide +kernel
lemma column1_0_r3_1_eq : ∀ k : Fin 16, column1_0Expr 3 1 k = column1_0_r3_1 k := by decide +kernel
lemma column1_0_r3_2_eq : ∀ k : Fin 16, column1_0Expr 3 2 k = column1_0_r3_2 k := by decide +kernel
lemma column1_0_r3_3_eq : ∀ k : Fin 16, column1_0Expr 3 3 k = column1_0_r3_3 k := by decide +kernel
lemma column1_0_r3_4_eq : ∀ k : Fin 16, column1_0Expr 3 4 k = column1_0_r3_4 k := by decide +kernel
lemma column1_0_r3_5_eq : ∀ k : Fin 16, column1_0Expr 3 5 k = column1_0_r3_5 k := by decide +kernel
lemma column1_0_r3_6_eq : ∀ k : Fin 16, column1_0Expr 3 6 k = column1_0_r3_6 k := by decide +kernel
lemma column1_0_r3_7_eq : ∀ k : Fin 16, column1_0Expr 3 7 k = column1_0_r3_7 k := by decide +kernel
lemma column1_0_r3_8_eq : ∀ k : Fin 16, column1_0Expr 3 8 k = column1_0_r3_8 k := by decide +kernel
lemma column1_0_r3_9_eq : ∀ k : Fin 16, column1_0Expr 3 9 k = column1_0_r3_9 k := by decide +kernel
lemma column1_0_r3_10_eq : ∀ k : Fin 16, column1_0Expr 3 10 k = column1_0_r3_10 k := by decide +kernel
lemma column1_0_r3_11_eq : ∀ k : Fin 16, column1_0Expr 3 11 k = column1_0_r3_11 k := by decide +kernel
lemma column1_0_r3_12_eq : ∀ k : Fin 16, column1_0Expr 3 12 k = column1_0_r3_12 k := by decide +kernel
lemma column1_0_r3_13_eq : ∀ k : Fin 16, column1_0Expr 3 13 k = column1_0_r3_13 k := by decide +kernel
lemma column1_0_r3_14_eq : ∀ k : Fin 16, column1_0Expr 3 14 k = column1_0_r3_14 k := by decide +kernel
lemma column1_0_r3_15_eq : ∀ k : Fin 16, column1_0Expr 3 15 k = column1_0_r3_15 k := by decide +kernel
lemma column1_0_r3_eq (i k : Fin 16) : column1_0Expr 3 i k = column1_0_r3 i k := by
  fin_cases i
  · exact column1_0_r3_0_eq k
  · exact column1_0_r3_1_eq k
  · exact column1_0_r3_2_eq k
  · exact column1_0_r3_3_eq k
  · exact column1_0_r3_4_eq k
  · exact column1_0_r3_5_eq k
  · exact column1_0_r3_6_eq k
  · exact column1_0_r3_7_eq k
  · exact column1_0_r3_8_eq k
  · exact column1_0_r3_9_eq k
  · exact column1_0_r3_10_eq k
  · exact column1_0_r3_11_eq k
  · exact column1_0_r3_12_eq k
  · exact column1_0_r3_13_eq k
  · exact column1_0_r3_14_eq k
  · exact column1_0_r3_15_eq k
lemma column1_0_r4_0_eq : ∀ k : Fin 16, column1_0Expr 4 0 k = column1_0_r4_0 k := by decide +kernel
lemma column1_0_r4_1_eq : ∀ k : Fin 16, column1_0Expr 4 1 k = column1_0_r4_1 k := by decide +kernel
lemma column1_0_r4_2_eq : ∀ k : Fin 16, column1_0Expr 4 2 k = column1_0_r4_2 k := by decide +kernel
lemma column1_0_r4_3_eq : ∀ k : Fin 16, column1_0Expr 4 3 k = column1_0_r4_3 k := by decide +kernel
lemma column1_0_r4_4_eq : ∀ k : Fin 16, column1_0Expr 4 4 k = column1_0_r4_4 k := by decide +kernel
lemma column1_0_r4_5_eq : ∀ k : Fin 16, column1_0Expr 4 5 k = column1_0_r4_5 k := by decide +kernel
lemma column1_0_r4_6_eq : ∀ k : Fin 16, column1_0Expr 4 6 k = column1_0_r4_6 k := by decide +kernel
lemma column1_0_r4_7_eq : ∀ k : Fin 16, column1_0Expr 4 7 k = column1_0_r4_7 k := by decide +kernel
lemma column1_0_r4_8_eq : ∀ k : Fin 16, column1_0Expr 4 8 k = column1_0_r4_8 k := by decide +kernel
lemma column1_0_r4_9_eq : ∀ k : Fin 16, column1_0Expr 4 9 k = column1_0_r4_9 k := by decide +kernel
lemma column1_0_r4_10_eq : ∀ k : Fin 16, column1_0Expr 4 10 k = column1_0_r4_10 k := by decide +kernel
lemma column1_0_r4_11_eq : ∀ k : Fin 16, column1_0Expr 4 11 k = column1_0_r4_11 k := by decide +kernel
lemma column1_0_r4_12_eq : ∀ k : Fin 16, column1_0Expr 4 12 k = column1_0_r4_12 k := by decide +kernel
lemma column1_0_r4_13_eq : ∀ k : Fin 16, column1_0Expr 4 13 k = column1_0_r4_13 k := by decide +kernel
lemma column1_0_r4_14_eq : ∀ k : Fin 16, column1_0Expr 4 14 k = column1_0_r4_14 k := by decide +kernel
lemma column1_0_r4_15_eq : ∀ k : Fin 16, column1_0Expr 4 15 k = column1_0_r4_15 k := by decide +kernel
lemma column1_0_r4_eq (i k : Fin 16) : column1_0Expr 4 i k = column1_0_r4 i k := by
  fin_cases i
  · exact column1_0_r4_0_eq k
  · exact column1_0_r4_1_eq k
  · exact column1_0_r4_2_eq k
  · exact column1_0_r4_3_eq k
  · exact column1_0_r4_4_eq k
  · exact column1_0_r4_5_eq k
  · exact column1_0_r4_6_eq k
  · exact column1_0_r4_7_eq k
  · exact column1_0_r4_8_eq k
  · exact column1_0_r4_9_eq k
  · exact column1_0_r4_10_eq k
  · exact column1_0_r4_11_eq k
  · exact column1_0_r4_12_eq k
  · exact column1_0_r4_13_eq k
  · exact column1_0_r4_14_eq k
  · exact column1_0_r4_15_eq k
lemma column1_0_r5_0_eq : ∀ k : Fin 16, column1_0Expr 5 0 k = column1_0_r5_0 k := by decide +kernel
lemma column1_0_r5_1_eq : ∀ k : Fin 16, column1_0Expr 5 1 k = column1_0_r5_1 k := by decide +kernel
lemma column1_0_r5_2_eq : ∀ k : Fin 16, column1_0Expr 5 2 k = column1_0_r5_2 k := by decide +kernel
lemma column1_0_r5_3_eq : ∀ k : Fin 16, column1_0Expr 5 3 k = column1_0_r5_3 k := by decide +kernel
lemma column1_0_r5_4_eq : ∀ k : Fin 16, column1_0Expr 5 4 k = column1_0_r5_4 k := by decide +kernel
lemma column1_0_r5_5_eq : ∀ k : Fin 16, column1_0Expr 5 5 k = column1_0_r5_5 k := by decide +kernel
lemma column1_0_r5_6_eq : ∀ k : Fin 16, column1_0Expr 5 6 k = column1_0_r5_6 k := by decide +kernel
lemma column1_0_r5_7_eq : ∀ k : Fin 16, column1_0Expr 5 7 k = column1_0_r5_7 k := by decide +kernel
lemma column1_0_r5_8_eq : ∀ k : Fin 16, column1_0Expr 5 8 k = column1_0_r5_8 k := by decide +kernel
lemma column1_0_r5_9_eq : ∀ k : Fin 16, column1_0Expr 5 9 k = column1_0_r5_9 k := by decide +kernel
lemma column1_0_r5_10_eq : ∀ k : Fin 16, column1_0Expr 5 10 k = column1_0_r5_10 k := by decide +kernel
lemma column1_0_r5_11_eq : ∀ k : Fin 16, column1_0Expr 5 11 k = column1_0_r5_11 k := by decide +kernel
lemma column1_0_r5_12_eq : ∀ k : Fin 16, column1_0Expr 5 12 k = column1_0_r5_12 k := by decide +kernel
lemma column1_0_r5_13_eq : ∀ k : Fin 16, column1_0Expr 5 13 k = column1_0_r5_13 k := by decide +kernel
lemma column1_0_r5_14_eq : ∀ k : Fin 16, column1_0Expr 5 14 k = column1_0_r5_14 k := by decide +kernel
lemma column1_0_r5_15_eq : ∀ k : Fin 16, column1_0Expr 5 15 k = column1_0_r5_15 k := by decide +kernel
lemma column1_0_r5_eq (i k : Fin 16) : column1_0Expr 5 i k = column1_0_r5 i k := by
  fin_cases i
  · exact column1_0_r5_0_eq k
  · exact column1_0_r5_1_eq k
  · exact column1_0_r5_2_eq k
  · exact column1_0_r5_3_eq k
  · exact column1_0_r5_4_eq k
  · exact column1_0_r5_5_eq k
  · exact column1_0_r5_6_eq k
  · exact column1_0_r5_7_eq k
  · exact column1_0_r5_8_eq k
  · exact column1_0_r5_9_eq k
  · exact column1_0_r5_10_eq k
  · exact column1_0_r5_11_eq k
  · exact column1_0_r5_12_eq k
  · exact column1_0_r5_13_eq k
  · exact column1_0_r5_14_eq k
  · exact column1_0_r5_15_eq k
lemma column1_0_eq (j : Fin 6) (i k : Fin 16) : column1_0Expr j i k = column1_0 j i k := by
  fin_cases j
  · exact column1_0_r0_eq i k
  · exact column1_0_r1_eq i k
  · exact column1_0_r2_eq i k
  · exact column1_0_r3_eq i k
  · exact column1_0_r4_eq i k
  · exact column1_0_r5_eq i k
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
noncomputable def column16_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power16 j i k)
lemma column16_1_r0_0_eq : ∀ k : Fin 16, column16_1Expr 0 0 k = column16_1_r0_0 k := by decide +kernel
lemma column16_1_r0_1_eq : ∀ k : Fin 16, column16_1Expr 0 1 k = column16_1_r0_1 k := by decide +kernel
lemma column16_1_r0_2_eq : ∀ k : Fin 16, column16_1Expr 0 2 k = column16_1_r0_2 k := by decide +kernel
lemma column16_1_r0_3_eq : ∀ k : Fin 16, column16_1Expr 0 3 k = column16_1_r0_3 k := by decide +kernel
lemma column16_1_r0_4_eq : ∀ k : Fin 16, column16_1Expr 0 4 k = column16_1_r0_4 k := by decide +kernel
lemma column16_1_r0_5_eq : ∀ k : Fin 16, column16_1Expr 0 5 k = column16_1_r0_5 k := by decide +kernel
lemma column16_1_r0_6_eq : ∀ k : Fin 16, column16_1Expr 0 6 k = column16_1_r0_6 k := by decide +kernel
lemma column16_1_r0_7_eq : ∀ k : Fin 16, column16_1Expr 0 7 k = column16_1_r0_7 k := by decide +kernel
lemma column16_1_r0_8_eq : ∀ k : Fin 16, column16_1Expr 0 8 k = column16_1_r0_8 k := by decide +kernel
lemma column16_1_r0_9_eq : ∀ k : Fin 16, column16_1Expr 0 9 k = column16_1_r0_9 k := by decide +kernel
lemma column16_1_r0_10_eq : ∀ k : Fin 16, column16_1Expr 0 10 k = column16_1_r0_10 k := by decide +kernel
lemma column16_1_r0_11_eq : ∀ k : Fin 16, column16_1Expr 0 11 k = column16_1_r0_11 k := by decide +kernel
lemma column16_1_r0_12_eq : ∀ k : Fin 16, column16_1Expr 0 12 k = column16_1_r0_12 k := by decide +kernel
lemma column16_1_r0_13_eq : ∀ k : Fin 16, column16_1Expr 0 13 k = column16_1_r0_13 k := by decide +kernel
lemma column16_1_r0_14_eq : ∀ k : Fin 16, column16_1Expr 0 14 k = column16_1_r0_14 k := by decide +kernel
lemma column16_1_r0_15_eq : ∀ k : Fin 16, column16_1Expr 0 15 k = column16_1_r0_15 k := by decide +kernel
lemma column16_1_r0_eq (i k : Fin 16) : column16_1Expr 0 i k = column16_1_r0 i k := by
  fin_cases i
  · exact column16_1_r0_0_eq k
  · exact column16_1_r0_1_eq k
  · exact column16_1_r0_2_eq k
  · exact column16_1_r0_3_eq k
  · exact column16_1_r0_4_eq k
  · exact column16_1_r0_5_eq k
  · exact column16_1_r0_6_eq k
  · exact column16_1_r0_7_eq k
  · exact column16_1_r0_8_eq k
  · exact column16_1_r0_9_eq k
  · exact column16_1_r0_10_eq k
  · exact column16_1_r0_11_eq k
  · exact column16_1_r0_12_eq k
  · exact column16_1_r0_13_eq k
  · exact column16_1_r0_14_eq k
  · exact column16_1_r0_15_eq k
lemma column16_1_r1_0_eq : ∀ k : Fin 16, column16_1Expr 1 0 k = column16_1_r1_0 k := by decide +kernel
lemma column16_1_r1_1_eq : ∀ k : Fin 16, column16_1Expr 1 1 k = column16_1_r1_1 k := by decide +kernel
lemma column16_1_r1_2_eq : ∀ k : Fin 16, column16_1Expr 1 2 k = column16_1_r1_2 k := by decide +kernel
lemma column16_1_r1_3_eq : ∀ k : Fin 16, column16_1Expr 1 3 k = column16_1_r1_3 k := by decide +kernel
lemma column16_1_r1_4_eq : ∀ k : Fin 16, column16_1Expr 1 4 k = column16_1_r1_4 k := by decide +kernel
lemma column16_1_r1_5_eq : ∀ k : Fin 16, column16_1Expr 1 5 k = column16_1_r1_5 k := by decide +kernel
lemma column16_1_r1_6_eq : ∀ k : Fin 16, column16_1Expr 1 6 k = column16_1_r1_6 k := by decide +kernel
lemma column16_1_r1_7_eq : ∀ k : Fin 16, column16_1Expr 1 7 k = column16_1_r1_7 k := by decide +kernel
lemma column16_1_r1_8_eq : ∀ k : Fin 16, column16_1Expr 1 8 k = column16_1_r1_8 k := by decide +kernel
lemma column16_1_r1_9_eq : ∀ k : Fin 16, column16_1Expr 1 9 k = column16_1_r1_9 k := by decide +kernel
lemma column16_1_r1_10_eq : ∀ k : Fin 16, column16_1Expr 1 10 k = column16_1_r1_10 k := by decide +kernel
lemma column16_1_r1_11_eq : ∀ k : Fin 16, column16_1Expr 1 11 k = column16_1_r1_11 k := by decide +kernel
lemma column16_1_r1_12_eq : ∀ k : Fin 16, column16_1Expr 1 12 k = column16_1_r1_12 k := by decide +kernel
lemma column16_1_r1_13_eq : ∀ k : Fin 16, column16_1Expr 1 13 k = column16_1_r1_13 k := by decide +kernel
lemma column16_1_r1_14_eq : ∀ k : Fin 16, column16_1Expr 1 14 k = column16_1_r1_14 k := by decide +kernel
lemma column16_1_r1_15_eq : ∀ k : Fin 16, column16_1Expr 1 15 k = column16_1_r1_15 k := by decide +kernel
lemma column16_1_r1_eq (i k : Fin 16) : column16_1Expr 1 i k = column16_1_r1 i k := by
  fin_cases i
  · exact column16_1_r1_0_eq k
  · exact column16_1_r1_1_eq k
  · exact column16_1_r1_2_eq k
  · exact column16_1_r1_3_eq k
  · exact column16_1_r1_4_eq k
  · exact column16_1_r1_5_eq k
  · exact column16_1_r1_6_eq k
  · exact column16_1_r1_7_eq k
  · exact column16_1_r1_8_eq k
  · exact column16_1_r1_9_eq k
  · exact column16_1_r1_10_eq k
  · exact column16_1_r1_11_eq k
  · exact column16_1_r1_12_eq k
  · exact column16_1_r1_13_eq k
  · exact column16_1_r1_14_eq k
  · exact column16_1_r1_15_eq k
lemma column16_1_r2_0_eq : ∀ k : Fin 16, column16_1Expr 2 0 k = column16_1_r2_0 k := by decide +kernel
lemma column16_1_r2_1_eq : ∀ k : Fin 16, column16_1Expr 2 1 k = column16_1_r2_1 k := by decide +kernel
lemma column16_1_r2_2_eq : ∀ k : Fin 16, column16_1Expr 2 2 k = column16_1_r2_2 k := by decide +kernel
lemma column16_1_r2_3_eq : ∀ k : Fin 16, column16_1Expr 2 3 k = column16_1_r2_3 k := by decide +kernel
lemma column16_1_r2_4_eq : ∀ k : Fin 16, column16_1Expr 2 4 k = column16_1_r2_4 k := by decide +kernel
lemma column16_1_r2_5_eq : ∀ k : Fin 16, column16_1Expr 2 5 k = column16_1_r2_5 k := by decide +kernel
lemma column16_1_r2_6_eq : ∀ k : Fin 16, column16_1Expr 2 6 k = column16_1_r2_6 k := by decide +kernel
lemma column16_1_r2_7_eq : ∀ k : Fin 16, column16_1Expr 2 7 k = column16_1_r2_7 k := by decide +kernel
lemma column16_1_r2_8_eq : ∀ k : Fin 16, column16_1Expr 2 8 k = column16_1_r2_8 k := by decide +kernel
lemma column16_1_r2_9_eq : ∀ k : Fin 16, column16_1Expr 2 9 k = column16_1_r2_9 k := by decide +kernel
lemma column16_1_r2_10_eq : ∀ k : Fin 16, column16_1Expr 2 10 k = column16_1_r2_10 k := by decide +kernel
lemma column16_1_r2_11_eq : ∀ k : Fin 16, column16_1Expr 2 11 k = column16_1_r2_11 k := by decide +kernel
lemma column16_1_r2_12_eq : ∀ k : Fin 16, column16_1Expr 2 12 k = column16_1_r2_12 k := by decide +kernel
lemma column16_1_r2_13_eq : ∀ k : Fin 16, column16_1Expr 2 13 k = column16_1_r2_13 k := by decide +kernel
lemma column16_1_r2_14_eq : ∀ k : Fin 16, column16_1Expr 2 14 k = column16_1_r2_14 k := by decide +kernel
lemma column16_1_r2_15_eq : ∀ k : Fin 16, column16_1Expr 2 15 k = column16_1_r2_15 k := by decide +kernel
lemma column16_1_r2_eq (i k : Fin 16) : column16_1Expr 2 i k = column16_1_r2 i k := by
  fin_cases i
  · exact column16_1_r2_0_eq k
  · exact column16_1_r2_1_eq k
  · exact column16_1_r2_2_eq k
  · exact column16_1_r2_3_eq k
  · exact column16_1_r2_4_eq k
  · exact column16_1_r2_5_eq k
  · exact column16_1_r2_6_eq k
  · exact column16_1_r2_7_eq k
  · exact column16_1_r2_8_eq k
  · exact column16_1_r2_9_eq k
  · exact column16_1_r2_10_eq k
  · exact column16_1_r2_11_eq k
  · exact column16_1_r2_12_eq k
  · exact column16_1_r2_13_eq k
  · exact column16_1_r2_14_eq k
  · exact column16_1_r2_15_eq k
lemma column16_1_r3_0_eq : ∀ k : Fin 16, column16_1Expr 3 0 k = column16_1_r3_0 k := by decide +kernel
lemma column16_1_r3_1_eq : ∀ k : Fin 16, column16_1Expr 3 1 k = column16_1_r3_1 k := by decide +kernel
lemma column16_1_r3_2_eq : ∀ k : Fin 16, column16_1Expr 3 2 k = column16_1_r3_2 k := by decide +kernel
lemma column16_1_r3_3_eq : ∀ k : Fin 16, column16_1Expr 3 3 k = column16_1_r3_3 k := by decide +kernel
lemma column16_1_r3_4_eq : ∀ k : Fin 16, column16_1Expr 3 4 k = column16_1_r3_4 k := by decide +kernel
lemma column16_1_r3_5_eq : ∀ k : Fin 16, column16_1Expr 3 5 k = column16_1_r3_5 k := by decide +kernel
lemma column16_1_r3_6_eq : ∀ k : Fin 16, column16_1Expr 3 6 k = column16_1_r3_6 k := by decide +kernel
lemma column16_1_r3_7_eq : ∀ k : Fin 16, column16_1Expr 3 7 k = column16_1_r3_7 k := by decide +kernel
lemma column16_1_r3_8_eq : ∀ k : Fin 16, column16_1Expr 3 8 k = column16_1_r3_8 k := by decide +kernel
lemma column16_1_r3_9_eq : ∀ k : Fin 16, column16_1Expr 3 9 k = column16_1_r3_9 k := by decide +kernel
lemma column16_1_r3_10_eq : ∀ k : Fin 16, column16_1Expr 3 10 k = column16_1_r3_10 k := by decide +kernel
lemma column16_1_r3_11_eq : ∀ k : Fin 16, column16_1Expr 3 11 k = column16_1_r3_11 k := by decide +kernel
lemma column16_1_r3_12_eq : ∀ k : Fin 16, column16_1Expr 3 12 k = column16_1_r3_12 k := by decide +kernel
lemma column16_1_r3_13_eq : ∀ k : Fin 16, column16_1Expr 3 13 k = column16_1_r3_13 k := by decide +kernel
lemma column16_1_r3_14_eq : ∀ k : Fin 16, column16_1Expr 3 14 k = column16_1_r3_14 k := by decide +kernel
lemma column16_1_r3_15_eq : ∀ k : Fin 16, column16_1Expr 3 15 k = column16_1_r3_15 k := by decide +kernel
lemma column16_1_r3_eq (i k : Fin 16) : column16_1Expr 3 i k = column16_1_r3 i k := by
  fin_cases i
  · exact column16_1_r3_0_eq k
  · exact column16_1_r3_1_eq k
  · exact column16_1_r3_2_eq k
  · exact column16_1_r3_3_eq k
  · exact column16_1_r3_4_eq k
  · exact column16_1_r3_5_eq k
  · exact column16_1_r3_6_eq k
  · exact column16_1_r3_7_eq k
  · exact column16_1_r3_8_eq k
  · exact column16_1_r3_9_eq k
  · exact column16_1_r3_10_eq k
  · exact column16_1_r3_11_eq k
  · exact column16_1_r3_12_eq k
  · exact column16_1_r3_13_eq k
  · exact column16_1_r3_14_eq k
  · exact column16_1_r3_15_eq k
lemma column16_1_r4_0_eq : ∀ k : Fin 16, column16_1Expr 4 0 k = column16_1_r4_0 k := by decide +kernel
lemma column16_1_r4_1_eq : ∀ k : Fin 16, column16_1Expr 4 1 k = column16_1_r4_1 k := by decide +kernel
lemma column16_1_r4_2_eq : ∀ k : Fin 16, column16_1Expr 4 2 k = column16_1_r4_2 k := by decide +kernel
lemma column16_1_r4_3_eq : ∀ k : Fin 16, column16_1Expr 4 3 k = column16_1_r4_3 k := by decide +kernel
lemma column16_1_r4_4_eq : ∀ k : Fin 16, column16_1Expr 4 4 k = column16_1_r4_4 k := by decide +kernel
lemma column16_1_r4_5_eq : ∀ k : Fin 16, column16_1Expr 4 5 k = column16_1_r4_5 k := by decide +kernel
lemma column16_1_r4_6_eq : ∀ k : Fin 16, column16_1Expr 4 6 k = column16_1_r4_6 k := by decide +kernel
lemma column16_1_r4_7_eq : ∀ k : Fin 16, column16_1Expr 4 7 k = column16_1_r4_7 k := by decide +kernel
lemma column16_1_r4_8_eq : ∀ k : Fin 16, column16_1Expr 4 8 k = column16_1_r4_8 k := by decide +kernel
lemma column16_1_r4_9_eq : ∀ k : Fin 16, column16_1Expr 4 9 k = column16_1_r4_9 k := by decide +kernel
lemma column16_1_r4_10_eq : ∀ k : Fin 16, column16_1Expr 4 10 k = column16_1_r4_10 k := by decide +kernel
lemma column16_1_r4_11_eq : ∀ k : Fin 16, column16_1Expr 4 11 k = column16_1_r4_11 k := by decide +kernel
lemma column16_1_r4_12_eq : ∀ k : Fin 16, column16_1Expr 4 12 k = column16_1_r4_12 k := by decide +kernel
lemma column16_1_r4_13_eq : ∀ k : Fin 16, column16_1Expr 4 13 k = column16_1_r4_13 k := by decide +kernel
lemma column16_1_r4_14_eq : ∀ k : Fin 16, column16_1Expr 4 14 k = column16_1_r4_14 k := by decide +kernel
lemma column16_1_r4_15_eq : ∀ k : Fin 16, column16_1Expr 4 15 k = column16_1_r4_15 k := by decide +kernel
lemma column16_1_r4_eq (i k : Fin 16) : column16_1Expr 4 i k = column16_1_r4 i k := by
  fin_cases i
  · exact column16_1_r4_0_eq k
  · exact column16_1_r4_1_eq k
  · exact column16_1_r4_2_eq k
  · exact column16_1_r4_3_eq k
  · exact column16_1_r4_4_eq k
  · exact column16_1_r4_5_eq k
  · exact column16_1_r4_6_eq k
  · exact column16_1_r4_7_eq k
  · exact column16_1_r4_8_eq k
  · exact column16_1_r4_9_eq k
  · exact column16_1_r4_10_eq k
  · exact column16_1_r4_11_eq k
  · exact column16_1_r4_12_eq k
  · exact column16_1_r4_13_eq k
  · exact column16_1_r4_14_eq k
  · exact column16_1_r4_15_eq k
lemma column16_1_r5_0_eq : ∀ k : Fin 16, column16_1Expr 5 0 k = column16_1_r5_0 k := by decide +kernel
lemma column16_1_r5_1_eq : ∀ k : Fin 16, column16_1Expr 5 1 k = column16_1_r5_1 k := by decide +kernel
lemma column16_1_r5_2_eq : ∀ k : Fin 16, column16_1Expr 5 2 k = column16_1_r5_2 k := by decide +kernel
lemma column16_1_r5_3_eq : ∀ k : Fin 16, column16_1Expr 5 3 k = column16_1_r5_3 k := by decide +kernel
lemma column16_1_r5_4_eq : ∀ k : Fin 16, column16_1Expr 5 4 k = column16_1_r5_4 k := by decide +kernel
lemma column16_1_r5_5_eq : ∀ k : Fin 16, column16_1Expr 5 5 k = column16_1_r5_5 k := by decide +kernel
lemma column16_1_r5_6_eq : ∀ k : Fin 16, column16_1Expr 5 6 k = column16_1_r5_6 k := by decide +kernel
lemma column16_1_r5_7_eq : ∀ k : Fin 16, column16_1Expr 5 7 k = column16_1_r5_7 k := by decide +kernel
lemma column16_1_r5_8_eq : ∀ k : Fin 16, column16_1Expr 5 8 k = column16_1_r5_8 k := by decide +kernel
lemma column16_1_r5_9_eq : ∀ k : Fin 16, column16_1Expr 5 9 k = column16_1_r5_9 k := by decide +kernel
lemma column16_1_r5_10_eq : ∀ k : Fin 16, column16_1Expr 5 10 k = column16_1_r5_10 k := by decide +kernel
lemma column16_1_r5_11_eq : ∀ k : Fin 16, column16_1Expr 5 11 k = column16_1_r5_11 k := by decide +kernel
lemma column16_1_r5_12_eq : ∀ k : Fin 16, column16_1Expr 5 12 k = column16_1_r5_12 k := by decide +kernel
lemma column16_1_r5_13_eq : ∀ k : Fin 16, column16_1Expr 5 13 k = column16_1_r5_13 k := by decide +kernel
lemma column16_1_r5_14_eq : ∀ k : Fin 16, column16_1Expr 5 14 k = column16_1_r5_14 k := by decide +kernel
lemma column16_1_r5_15_eq : ∀ k : Fin 16, column16_1Expr 5 15 k = column16_1_r5_15 k := by decide +kernel
lemma column16_1_r5_eq (i k : Fin 16) : column16_1Expr 5 i k = column16_1_r5 i k := by
  fin_cases i
  · exact column16_1_r5_0_eq k
  · exact column16_1_r5_1_eq k
  · exact column16_1_r5_2_eq k
  · exact column16_1_r5_3_eq k
  · exact column16_1_r5_4_eq k
  · exact column16_1_r5_5_eq k
  · exact column16_1_r5_6_eq k
  · exact column16_1_r5_7_eq k
  · exact column16_1_r5_8_eq k
  · exact column16_1_r5_9_eq k
  · exact column16_1_r5_10_eq k
  · exact column16_1_r5_11_eq k
  · exact column16_1_r5_12_eq k
  · exact column16_1_r5_13_eq k
  · exact column16_1_r5_14_eq k
  · exact column16_1_r5_15_eq k
lemma column16_1_eq (j : Fin 6) (i k : Fin 16) : column16_1Expr j i k = column16_1 j i k := by
  fin_cases j
  · exact column16_1_r0_eq i k
  · exact column16_1_r1_eq i k
  · exact column16_1_r2_eq i k
  · exact column16_1_r3_eq i k
  · exact column16_1_r4_eq i k
  · exact column16_1_r5_eq i k
noncomputable def column19_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power19 j i k)
lemma column19_0_r0_0_eq : ∀ k : Fin 16, column19_0Expr 0 0 k = column19_0_r0_0 k := by decide +kernel
lemma column19_0_r0_1_eq : ∀ k : Fin 16, column19_0Expr 0 1 k = column19_0_r0_1 k := by decide +kernel
lemma column19_0_r0_2_eq : ∀ k : Fin 16, column19_0Expr 0 2 k = column19_0_r0_2 k := by decide +kernel
lemma column19_0_r0_3_eq : ∀ k : Fin 16, column19_0Expr 0 3 k = column19_0_r0_3 k := by decide +kernel
lemma column19_0_r0_4_eq : ∀ k : Fin 16, column19_0Expr 0 4 k = column19_0_r0_4 k := by decide +kernel
lemma column19_0_r0_5_eq : ∀ k : Fin 16, column19_0Expr 0 5 k = column19_0_r0_5 k := by decide +kernel
lemma column19_0_r0_6_eq : ∀ k : Fin 16, column19_0Expr 0 6 k = column19_0_r0_6 k := by decide +kernel
lemma column19_0_r0_7_eq : ∀ k : Fin 16, column19_0Expr 0 7 k = column19_0_r0_7 k := by decide +kernel
lemma column19_0_r0_8_eq : ∀ k : Fin 16, column19_0Expr 0 8 k = column19_0_r0_8 k := by decide +kernel
lemma column19_0_r0_9_eq : ∀ k : Fin 16, column19_0Expr 0 9 k = column19_0_r0_9 k := by decide +kernel
lemma column19_0_r0_10_eq : ∀ k : Fin 16, column19_0Expr 0 10 k = column19_0_r0_10 k := by decide +kernel
lemma column19_0_r0_11_eq : ∀ k : Fin 16, column19_0Expr 0 11 k = column19_0_r0_11 k := by decide +kernel
lemma column19_0_r0_12_eq : ∀ k : Fin 16, column19_0Expr 0 12 k = column19_0_r0_12 k := by decide +kernel
lemma column19_0_r0_13_eq : ∀ k : Fin 16, column19_0Expr 0 13 k = column19_0_r0_13 k := by decide +kernel
lemma column19_0_r0_14_eq : ∀ k : Fin 16, column19_0Expr 0 14 k = column19_0_r0_14 k := by decide +kernel
lemma column19_0_r0_15_eq : ∀ k : Fin 16, column19_0Expr 0 15 k = column19_0_r0_15 k := by decide +kernel
lemma column19_0_r0_eq (i k : Fin 16) : column19_0Expr 0 i k = column19_0_r0 i k := by
  fin_cases i
  · exact column19_0_r0_0_eq k
  · exact column19_0_r0_1_eq k
  · exact column19_0_r0_2_eq k
  · exact column19_0_r0_3_eq k
  · exact column19_0_r0_4_eq k
  · exact column19_0_r0_5_eq k
  · exact column19_0_r0_6_eq k
  · exact column19_0_r0_7_eq k
  · exact column19_0_r0_8_eq k
  · exact column19_0_r0_9_eq k
  · exact column19_0_r0_10_eq k
  · exact column19_0_r0_11_eq k
  · exact column19_0_r0_12_eq k
  · exact column19_0_r0_13_eq k
  · exact column19_0_r0_14_eq k
  · exact column19_0_r0_15_eq k
lemma column19_0_r1_0_eq : ∀ k : Fin 16, column19_0Expr 1 0 k = column19_0_r1_0 k := by decide +kernel
lemma column19_0_r1_1_eq : ∀ k : Fin 16, column19_0Expr 1 1 k = column19_0_r1_1 k := by decide +kernel
lemma column19_0_r1_2_eq : ∀ k : Fin 16, column19_0Expr 1 2 k = column19_0_r1_2 k := by decide +kernel
lemma column19_0_r1_3_eq : ∀ k : Fin 16, column19_0Expr 1 3 k = column19_0_r1_3 k := by decide +kernel
lemma column19_0_r1_4_eq : ∀ k : Fin 16, column19_0Expr 1 4 k = column19_0_r1_4 k := by decide +kernel
lemma column19_0_r1_5_eq : ∀ k : Fin 16, column19_0Expr 1 5 k = column19_0_r1_5 k := by decide +kernel
lemma column19_0_r1_6_eq : ∀ k : Fin 16, column19_0Expr 1 6 k = column19_0_r1_6 k := by decide +kernel
lemma column19_0_r1_7_eq : ∀ k : Fin 16, column19_0Expr 1 7 k = column19_0_r1_7 k := by decide +kernel
lemma column19_0_r1_8_eq : ∀ k : Fin 16, column19_0Expr 1 8 k = column19_0_r1_8 k := by decide +kernel
lemma column19_0_r1_9_eq : ∀ k : Fin 16, column19_0Expr 1 9 k = column19_0_r1_9 k := by decide +kernel
lemma column19_0_r1_10_eq : ∀ k : Fin 16, column19_0Expr 1 10 k = column19_0_r1_10 k := by decide +kernel
lemma column19_0_r1_11_eq : ∀ k : Fin 16, column19_0Expr 1 11 k = column19_0_r1_11 k := by decide +kernel
lemma column19_0_r1_12_eq : ∀ k : Fin 16, column19_0Expr 1 12 k = column19_0_r1_12 k := by decide +kernel
lemma column19_0_r1_13_eq : ∀ k : Fin 16, column19_0Expr 1 13 k = column19_0_r1_13 k := by decide +kernel
lemma column19_0_r1_14_eq : ∀ k : Fin 16, column19_0Expr 1 14 k = column19_0_r1_14 k := by decide +kernel
lemma column19_0_r1_15_eq : ∀ k : Fin 16, column19_0Expr 1 15 k = column19_0_r1_15 k := by decide +kernel
lemma column19_0_r1_eq (i k : Fin 16) : column19_0Expr 1 i k = column19_0_r1 i k := by
  fin_cases i
  · exact column19_0_r1_0_eq k
  · exact column19_0_r1_1_eq k
  · exact column19_0_r1_2_eq k
  · exact column19_0_r1_3_eq k
  · exact column19_0_r1_4_eq k
  · exact column19_0_r1_5_eq k
  · exact column19_0_r1_6_eq k
  · exact column19_0_r1_7_eq k
  · exact column19_0_r1_8_eq k
  · exact column19_0_r1_9_eq k
  · exact column19_0_r1_10_eq k
  · exact column19_0_r1_11_eq k
  · exact column19_0_r1_12_eq k
  · exact column19_0_r1_13_eq k
  · exact column19_0_r1_14_eq k
  · exact column19_0_r1_15_eq k
lemma column19_0_r2_0_eq : ∀ k : Fin 16, column19_0Expr 2 0 k = column19_0_r2_0 k := by decide +kernel
lemma column19_0_r2_1_eq : ∀ k : Fin 16, column19_0Expr 2 1 k = column19_0_r2_1 k := by decide +kernel
lemma column19_0_r2_2_eq : ∀ k : Fin 16, column19_0Expr 2 2 k = column19_0_r2_2 k := by decide +kernel
lemma column19_0_r2_3_eq : ∀ k : Fin 16, column19_0Expr 2 3 k = column19_0_r2_3 k := by decide +kernel
lemma column19_0_r2_4_eq : ∀ k : Fin 16, column19_0Expr 2 4 k = column19_0_r2_4 k := by decide +kernel
lemma column19_0_r2_5_eq : ∀ k : Fin 16, column19_0Expr 2 5 k = column19_0_r2_5 k := by decide +kernel
lemma column19_0_r2_6_eq : ∀ k : Fin 16, column19_0Expr 2 6 k = column19_0_r2_6 k := by decide +kernel
lemma column19_0_r2_7_eq : ∀ k : Fin 16, column19_0Expr 2 7 k = column19_0_r2_7 k := by decide +kernel
lemma column19_0_r2_8_eq : ∀ k : Fin 16, column19_0Expr 2 8 k = column19_0_r2_8 k := by decide +kernel
lemma column19_0_r2_9_eq : ∀ k : Fin 16, column19_0Expr 2 9 k = column19_0_r2_9 k := by decide +kernel
lemma column19_0_r2_10_eq : ∀ k : Fin 16, column19_0Expr 2 10 k = column19_0_r2_10 k := by decide +kernel
lemma column19_0_r2_11_eq : ∀ k : Fin 16, column19_0Expr 2 11 k = column19_0_r2_11 k := by decide +kernel
lemma column19_0_r2_12_eq : ∀ k : Fin 16, column19_0Expr 2 12 k = column19_0_r2_12 k := by decide +kernel
lemma column19_0_r2_13_eq : ∀ k : Fin 16, column19_0Expr 2 13 k = column19_0_r2_13 k := by decide +kernel
lemma column19_0_r2_14_eq : ∀ k : Fin 16, column19_0Expr 2 14 k = column19_0_r2_14 k := by decide +kernel
lemma column19_0_r2_15_eq : ∀ k : Fin 16, column19_0Expr 2 15 k = column19_0_r2_15 k := by decide +kernel
lemma column19_0_r2_eq (i k : Fin 16) : column19_0Expr 2 i k = column19_0_r2 i k := by
  fin_cases i
  · exact column19_0_r2_0_eq k
  · exact column19_0_r2_1_eq k
  · exact column19_0_r2_2_eq k
  · exact column19_0_r2_3_eq k
  · exact column19_0_r2_4_eq k
  · exact column19_0_r2_5_eq k
  · exact column19_0_r2_6_eq k
  · exact column19_0_r2_7_eq k
  · exact column19_0_r2_8_eq k
  · exact column19_0_r2_9_eq k
  · exact column19_0_r2_10_eq k
  · exact column19_0_r2_11_eq k
  · exact column19_0_r2_12_eq k
  · exact column19_0_r2_13_eq k
  · exact column19_0_r2_14_eq k
  · exact column19_0_r2_15_eq k
lemma column19_0_r3_0_eq : ∀ k : Fin 16, column19_0Expr 3 0 k = column19_0_r3_0 k := by decide +kernel
lemma column19_0_r3_1_eq : ∀ k : Fin 16, column19_0Expr 3 1 k = column19_0_r3_1 k := by decide +kernel
lemma column19_0_r3_2_eq : ∀ k : Fin 16, column19_0Expr 3 2 k = column19_0_r3_2 k := by decide +kernel
lemma column19_0_r3_3_eq : ∀ k : Fin 16, column19_0Expr 3 3 k = column19_0_r3_3 k := by decide +kernel
lemma column19_0_r3_4_eq : ∀ k : Fin 16, column19_0Expr 3 4 k = column19_0_r3_4 k := by decide +kernel
lemma column19_0_r3_5_eq : ∀ k : Fin 16, column19_0Expr 3 5 k = column19_0_r3_5 k := by decide +kernel
lemma column19_0_r3_6_eq : ∀ k : Fin 16, column19_0Expr 3 6 k = column19_0_r3_6 k := by decide +kernel
lemma column19_0_r3_7_eq : ∀ k : Fin 16, column19_0Expr 3 7 k = column19_0_r3_7 k := by decide +kernel
lemma column19_0_r3_8_eq : ∀ k : Fin 16, column19_0Expr 3 8 k = column19_0_r3_8 k := by decide +kernel
lemma column19_0_r3_9_eq : ∀ k : Fin 16, column19_0Expr 3 9 k = column19_0_r3_9 k := by decide +kernel
lemma column19_0_r3_10_eq : ∀ k : Fin 16, column19_0Expr 3 10 k = column19_0_r3_10 k := by decide +kernel
lemma column19_0_r3_11_eq : ∀ k : Fin 16, column19_0Expr 3 11 k = column19_0_r3_11 k := by decide +kernel
lemma column19_0_r3_12_eq : ∀ k : Fin 16, column19_0Expr 3 12 k = column19_0_r3_12 k := by decide +kernel
lemma column19_0_r3_13_eq : ∀ k : Fin 16, column19_0Expr 3 13 k = column19_0_r3_13 k := by decide +kernel
lemma column19_0_r3_14_eq : ∀ k : Fin 16, column19_0Expr 3 14 k = column19_0_r3_14 k := by decide +kernel
lemma column19_0_r3_15_eq : ∀ k : Fin 16, column19_0Expr 3 15 k = column19_0_r3_15 k := by decide +kernel
lemma column19_0_r3_eq (i k : Fin 16) : column19_0Expr 3 i k = column19_0_r3 i k := by
  fin_cases i
  · exact column19_0_r3_0_eq k
  · exact column19_0_r3_1_eq k
  · exact column19_0_r3_2_eq k
  · exact column19_0_r3_3_eq k
  · exact column19_0_r3_4_eq k
  · exact column19_0_r3_5_eq k
  · exact column19_0_r3_6_eq k
  · exact column19_0_r3_7_eq k
  · exact column19_0_r3_8_eq k
  · exact column19_0_r3_9_eq k
  · exact column19_0_r3_10_eq k
  · exact column19_0_r3_11_eq k
  · exact column19_0_r3_12_eq k
  · exact column19_0_r3_13_eq k
  · exact column19_0_r3_14_eq k
  · exact column19_0_r3_15_eq k
lemma column19_0_r4_0_eq : ∀ k : Fin 16, column19_0Expr 4 0 k = column19_0_r4_0 k := by decide +kernel
lemma column19_0_r4_1_eq : ∀ k : Fin 16, column19_0Expr 4 1 k = column19_0_r4_1 k := by decide +kernel
lemma column19_0_r4_2_eq : ∀ k : Fin 16, column19_0Expr 4 2 k = column19_0_r4_2 k := by decide +kernel
lemma column19_0_r4_3_eq : ∀ k : Fin 16, column19_0Expr 4 3 k = column19_0_r4_3 k := by decide +kernel
lemma column19_0_r4_4_eq : ∀ k : Fin 16, column19_0Expr 4 4 k = column19_0_r4_4 k := by decide +kernel
lemma column19_0_r4_5_eq : ∀ k : Fin 16, column19_0Expr 4 5 k = column19_0_r4_5 k := by decide +kernel
lemma column19_0_r4_6_eq : ∀ k : Fin 16, column19_0Expr 4 6 k = column19_0_r4_6 k := by decide +kernel
lemma column19_0_r4_7_eq : ∀ k : Fin 16, column19_0Expr 4 7 k = column19_0_r4_7 k := by decide +kernel
lemma column19_0_r4_8_eq : ∀ k : Fin 16, column19_0Expr 4 8 k = column19_0_r4_8 k := by decide +kernel
lemma column19_0_r4_9_eq : ∀ k : Fin 16, column19_0Expr 4 9 k = column19_0_r4_9 k := by decide +kernel
lemma column19_0_r4_10_eq : ∀ k : Fin 16, column19_0Expr 4 10 k = column19_0_r4_10 k := by decide +kernel
lemma column19_0_r4_11_eq : ∀ k : Fin 16, column19_0Expr 4 11 k = column19_0_r4_11 k := by decide +kernel
lemma column19_0_r4_12_eq : ∀ k : Fin 16, column19_0Expr 4 12 k = column19_0_r4_12 k := by decide +kernel
lemma column19_0_r4_13_eq : ∀ k : Fin 16, column19_0Expr 4 13 k = column19_0_r4_13 k := by decide +kernel
lemma column19_0_r4_14_eq : ∀ k : Fin 16, column19_0Expr 4 14 k = column19_0_r4_14 k := by decide +kernel
lemma column19_0_r4_15_eq : ∀ k : Fin 16, column19_0Expr 4 15 k = column19_0_r4_15 k := by decide +kernel
lemma column19_0_r4_eq (i k : Fin 16) : column19_0Expr 4 i k = column19_0_r4 i k := by
  fin_cases i
  · exact column19_0_r4_0_eq k
  · exact column19_0_r4_1_eq k
  · exact column19_0_r4_2_eq k
  · exact column19_0_r4_3_eq k
  · exact column19_0_r4_4_eq k
  · exact column19_0_r4_5_eq k
  · exact column19_0_r4_6_eq k
  · exact column19_0_r4_7_eq k
  · exact column19_0_r4_8_eq k
  · exact column19_0_r4_9_eq k
  · exact column19_0_r4_10_eq k
  · exact column19_0_r4_11_eq k
  · exact column19_0_r4_12_eq k
  · exact column19_0_r4_13_eq k
  · exact column19_0_r4_14_eq k
  · exact column19_0_r4_15_eq k
lemma column19_0_r5_0_eq : ∀ k : Fin 16, column19_0Expr 5 0 k = column19_0_r5_0 k := by decide +kernel
lemma column19_0_r5_1_eq : ∀ k : Fin 16, column19_0Expr 5 1 k = column19_0_r5_1 k := by decide +kernel
lemma column19_0_r5_2_eq : ∀ k : Fin 16, column19_0Expr 5 2 k = column19_0_r5_2 k := by decide +kernel
lemma column19_0_r5_3_eq : ∀ k : Fin 16, column19_0Expr 5 3 k = column19_0_r5_3 k := by decide +kernel
lemma column19_0_r5_4_eq : ∀ k : Fin 16, column19_0Expr 5 4 k = column19_0_r5_4 k := by decide +kernel
lemma column19_0_r5_5_eq : ∀ k : Fin 16, column19_0Expr 5 5 k = column19_0_r5_5 k := by decide +kernel
lemma column19_0_r5_6_eq : ∀ k : Fin 16, column19_0Expr 5 6 k = column19_0_r5_6 k := by decide +kernel
lemma column19_0_r5_7_eq : ∀ k : Fin 16, column19_0Expr 5 7 k = column19_0_r5_7 k := by decide +kernel
lemma column19_0_r5_8_eq : ∀ k : Fin 16, column19_0Expr 5 8 k = column19_0_r5_8 k := by decide +kernel
lemma column19_0_r5_9_eq : ∀ k : Fin 16, column19_0Expr 5 9 k = column19_0_r5_9 k := by decide +kernel
lemma column19_0_r5_10_eq : ∀ k : Fin 16, column19_0Expr 5 10 k = column19_0_r5_10 k := by decide +kernel
lemma column19_0_r5_11_eq : ∀ k : Fin 16, column19_0Expr 5 11 k = column19_0_r5_11 k := by decide +kernel
lemma column19_0_r5_12_eq : ∀ k : Fin 16, column19_0Expr 5 12 k = column19_0_r5_12 k := by decide +kernel
lemma column19_0_r5_13_eq : ∀ k : Fin 16, column19_0Expr 5 13 k = column19_0_r5_13 k := by decide +kernel
lemma column19_0_r5_14_eq : ∀ k : Fin 16, column19_0Expr 5 14 k = column19_0_r5_14 k := by decide +kernel
lemma column19_0_r5_15_eq : ∀ k : Fin 16, column19_0Expr 5 15 k = column19_0_r5_15 k := by decide +kernel
lemma column19_0_r5_eq (i k : Fin 16) : column19_0Expr 5 i k = column19_0_r5 i k := by
  fin_cases i
  · exact column19_0_r5_0_eq k
  · exact column19_0_r5_1_eq k
  · exact column19_0_r5_2_eq k
  · exact column19_0_r5_3_eq k
  · exact column19_0_r5_4_eq k
  · exact column19_0_r5_5_eq k
  · exact column19_0_r5_6_eq k
  · exact column19_0_r5_7_eq k
  · exact column19_0_r5_8_eq k
  · exact column19_0_r5_9_eq k
  · exact column19_0_r5_10_eq k
  · exact column19_0_r5_11_eq k
  · exact column19_0_r5_12_eq k
  · exact column19_0_r5_13_eq k
  · exact column19_0_r5_14_eq k
  · exact column19_0_r5_15_eq k
lemma column19_0_eq (j : Fin 6) (i k : Fin 16) : column19_0Expr j i k = column19_0 j i k := by
  fin_cases j
  · exact column19_0_r0_eq i k
  · exact column19_0_r1_eq i k
  · exact column19_0_r2_eq i k
  · exact column19_0_r3_eq i k
  · exact column19_0_r4_eq i k
  · exact column19_0_r5_eq i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns30
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
noncomputable def column25_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power25 j i k)
lemma column25_0_r0_0_eq : ∀ k : Fin 16, column25_0Expr 0 0 k = column25_0_r0_0 k := by decide +kernel
lemma column25_0_r0_1_eq : ∀ k : Fin 16, column25_0Expr 0 1 k = column25_0_r0_1 k := by decide +kernel
lemma column25_0_r0_2_eq : ∀ k : Fin 16, column25_0Expr 0 2 k = column25_0_r0_2 k := by decide +kernel
lemma column25_0_r0_3_eq : ∀ k : Fin 16, column25_0Expr 0 3 k = column25_0_r0_3 k := by decide +kernel
lemma column25_0_r0_4_eq : ∀ k : Fin 16, column25_0Expr 0 4 k = column25_0_r0_4 k := by decide +kernel
lemma column25_0_r0_5_eq : ∀ k : Fin 16, column25_0Expr 0 5 k = column25_0_r0_5 k := by decide +kernel
lemma column25_0_r0_6_eq : ∀ k : Fin 16, column25_0Expr 0 6 k = column25_0_r0_6 k := by decide +kernel
lemma column25_0_r0_7_eq : ∀ k : Fin 16, column25_0Expr 0 7 k = column25_0_r0_7 k := by decide +kernel
lemma column25_0_r0_8_eq : ∀ k : Fin 16, column25_0Expr 0 8 k = column25_0_r0_8 k := by decide +kernel
lemma column25_0_r0_9_eq : ∀ k : Fin 16, column25_0Expr 0 9 k = column25_0_r0_9 k := by decide +kernel
lemma column25_0_r0_10_eq : ∀ k : Fin 16, column25_0Expr 0 10 k = column25_0_r0_10 k := by decide +kernel
lemma column25_0_r0_11_eq : ∀ k : Fin 16, column25_0Expr 0 11 k = column25_0_r0_11 k := by decide +kernel
lemma column25_0_r0_12_eq : ∀ k : Fin 16, column25_0Expr 0 12 k = column25_0_r0_12 k := by decide +kernel
lemma column25_0_r0_13_eq : ∀ k : Fin 16, column25_0Expr 0 13 k = column25_0_r0_13 k := by decide +kernel
lemma column25_0_r0_14_eq : ∀ k : Fin 16, column25_0Expr 0 14 k = column25_0_r0_14 k := by decide +kernel
lemma column25_0_r0_15_eq : ∀ k : Fin 16, column25_0Expr 0 15 k = column25_0_r0_15 k := by decide +kernel
lemma column25_0_r0_eq (i k : Fin 16) : column25_0Expr 0 i k = column25_0_r0 i k := by
  fin_cases i
  · exact column25_0_r0_0_eq k
  · exact column25_0_r0_1_eq k
  · exact column25_0_r0_2_eq k
  · exact column25_0_r0_3_eq k
  · exact column25_0_r0_4_eq k
  · exact column25_0_r0_5_eq k
  · exact column25_0_r0_6_eq k
  · exact column25_0_r0_7_eq k
  · exact column25_0_r0_8_eq k
  · exact column25_0_r0_9_eq k
  · exact column25_0_r0_10_eq k
  · exact column25_0_r0_11_eq k
  · exact column25_0_r0_12_eq k
  · exact column25_0_r0_13_eq k
  · exact column25_0_r0_14_eq k
  · exact column25_0_r0_15_eq k
lemma column25_0_r1_0_eq : ∀ k : Fin 16, column25_0Expr 1 0 k = column25_0_r1_0 k := by decide +kernel
lemma column25_0_r1_1_eq : ∀ k : Fin 16, column25_0Expr 1 1 k = column25_0_r1_1 k := by decide +kernel
lemma column25_0_r1_2_eq : ∀ k : Fin 16, column25_0Expr 1 2 k = column25_0_r1_2 k := by decide +kernel
lemma column25_0_r1_3_eq : ∀ k : Fin 16, column25_0Expr 1 3 k = column25_0_r1_3 k := by decide +kernel
lemma column25_0_r1_4_eq : ∀ k : Fin 16, column25_0Expr 1 4 k = column25_0_r1_4 k := by decide +kernel
lemma column25_0_r1_5_eq : ∀ k : Fin 16, column25_0Expr 1 5 k = column25_0_r1_5 k := by decide +kernel
lemma column25_0_r1_6_eq : ∀ k : Fin 16, column25_0Expr 1 6 k = column25_0_r1_6 k := by decide +kernel
lemma column25_0_r1_7_eq : ∀ k : Fin 16, column25_0Expr 1 7 k = column25_0_r1_7 k := by decide +kernel
lemma column25_0_r1_8_eq : ∀ k : Fin 16, column25_0Expr 1 8 k = column25_0_r1_8 k := by decide +kernel
lemma column25_0_r1_9_eq : ∀ k : Fin 16, column25_0Expr 1 9 k = column25_0_r1_9 k := by decide +kernel
lemma column25_0_r1_10_eq : ∀ k : Fin 16, column25_0Expr 1 10 k = column25_0_r1_10 k := by decide +kernel
lemma column25_0_r1_11_eq : ∀ k : Fin 16, column25_0Expr 1 11 k = column25_0_r1_11 k := by decide +kernel
lemma column25_0_r1_12_eq : ∀ k : Fin 16, column25_0Expr 1 12 k = column25_0_r1_12 k := by decide +kernel
lemma column25_0_r1_13_eq : ∀ k : Fin 16, column25_0Expr 1 13 k = column25_0_r1_13 k := by decide +kernel
lemma column25_0_r1_14_eq : ∀ k : Fin 16, column25_0Expr 1 14 k = column25_0_r1_14 k := by decide +kernel
lemma column25_0_r1_15_eq : ∀ k : Fin 16, column25_0Expr 1 15 k = column25_0_r1_15 k := by decide +kernel
lemma column25_0_r1_eq (i k : Fin 16) : column25_0Expr 1 i k = column25_0_r1 i k := by
  fin_cases i
  · exact column25_0_r1_0_eq k
  · exact column25_0_r1_1_eq k
  · exact column25_0_r1_2_eq k
  · exact column25_0_r1_3_eq k
  · exact column25_0_r1_4_eq k
  · exact column25_0_r1_5_eq k
  · exact column25_0_r1_6_eq k
  · exact column25_0_r1_7_eq k
  · exact column25_0_r1_8_eq k
  · exact column25_0_r1_9_eq k
  · exact column25_0_r1_10_eq k
  · exact column25_0_r1_11_eq k
  · exact column25_0_r1_12_eq k
  · exact column25_0_r1_13_eq k
  · exact column25_0_r1_14_eq k
  · exact column25_0_r1_15_eq k
lemma column25_0_r2_0_eq : ∀ k : Fin 16, column25_0Expr 2 0 k = column25_0_r2_0 k := by decide +kernel
lemma column25_0_r2_1_eq : ∀ k : Fin 16, column25_0Expr 2 1 k = column25_0_r2_1 k := by decide +kernel
lemma column25_0_r2_2_eq : ∀ k : Fin 16, column25_0Expr 2 2 k = column25_0_r2_2 k := by decide +kernel
lemma column25_0_r2_3_eq : ∀ k : Fin 16, column25_0Expr 2 3 k = column25_0_r2_3 k := by decide +kernel
lemma column25_0_r2_4_eq : ∀ k : Fin 16, column25_0Expr 2 4 k = column25_0_r2_4 k := by decide +kernel
lemma column25_0_r2_5_eq : ∀ k : Fin 16, column25_0Expr 2 5 k = column25_0_r2_5 k := by decide +kernel
lemma column25_0_r2_6_eq : ∀ k : Fin 16, column25_0Expr 2 6 k = column25_0_r2_6 k := by decide +kernel
lemma column25_0_r2_7_eq : ∀ k : Fin 16, column25_0Expr 2 7 k = column25_0_r2_7 k := by decide +kernel
lemma column25_0_r2_8_eq : ∀ k : Fin 16, column25_0Expr 2 8 k = column25_0_r2_8 k := by decide +kernel
lemma column25_0_r2_9_eq : ∀ k : Fin 16, column25_0Expr 2 9 k = column25_0_r2_9 k := by decide +kernel
lemma column25_0_r2_10_eq : ∀ k : Fin 16, column25_0Expr 2 10 k = column25_0_r2_10 k := by decide +kernel
lemma column25_0_r2_11_eq : ∀ k : Fin 16, column25_0Expr 2 11 k = column25_0_r2_11 k := by decide +kernel
lemma column25_0_r2_12_eq : ∀ k : Fin 16, column25_0Expr 2 12 k = column25_0_r2_12 k := by decide +kernel
lemma column25_0_r2_13_eq : ∀ k : Fin 16, column25_0Expr 2 13 k = column25_0_r2_13 k := by decide +kernel
lemma column25_0_r2_14_eq : ∀ k : Fin 16, column25_0Expr 2 14 k = column25_0_r2_14 k := by decide +kernel
lemma column25_0_r2_15_eq : ∀ k : Fin 16, column25_0Expr 2 15 k = column25_0_r2_15 k := by decide +kernel
lemma column25_0_r2_eq (i k : Fin 16) : column25_0Expr 2 i k = column25_0_r2 i k := by
  fin_cases i
  · exact column25_0_r2_0_eq k
  · exact column25_0_r2_1_eq k
  · exact column25_0_r2_2_eq k
  · exact column25_0_r2_3_eq k
  · exact column25_0_r2_4_eq k
  · exact column25_0_r2_5_eq k
  · exact column25_0_r2_6_eq k
  · exact column25_0_r2_7_eq k
  · exact column25_0_r2_8_eq k
  · exact column25_0_r2_9_eq k
  · exact column25_0_r2_10_eq k
  · exact column25_0_r2_11_eq k
  · exact column25_0_r2_12_eq k
  · exact column25_0_r2_13_eq k
  · exact column25_0_r2_14_eq k
  · exact column25_0_r2_15_eq k
lemma column25_0_r3_0_eq : ∀ k : Fin 16, column25_0Expr 3 0 k = column25_0_r3_0 k := by decide +kernel
lemma column25_0_r3_1_eq : ∀ k : Fin 16, column25_0Expr 3 1 k = column25_0_r3_1 k := by decide +kernel
lemma column25_0_r3_2_eq : ∀ k : Fin 16, column25_0Expr 3 2 k = column25_0_r3_2 k := by decide +kernel
lemma column25_0_r3_3_eq : ∀ k : Fin 16, column25_0Expr 3 3 k = column25_0_r3_3 k := by decide +kernel
lemma column25_0_r3_4_eq : ∀ k : Fin 16, column25_0Expr 3 4 k = column25_0_r3_4 k := by decide +kernel
lemma column25_0_r3_5_eq : ∀ k : Fin 16, column25_0Expr 3 5 k = column25_0_r3_5 k := by decide +kernel
lemma column25_0_r3_6_eq : ∀ k : Fin 16, column25_0Expr 3 6 k = column25_0_r3_6 k := by decide +kernel
lemma column25_0_r3_7_eq : ∀ k : Fin 16, column25_0Expr 3 7 k = column25_0_r3_7 k := by decide +kernel
lemma column25_0_r3_8_eq : ∀ k : Fin 16, column25_0Expr 3 8 k = column25_0_r3_8 k := by decide +kernel
lemma column25_0_r3_9_eq : ∀ k : Fin 16, column25_0Expr 3 9 k = column25_0_r3_9 k := by decide +kernel
lemma column25_0_r3_10_eq : ∀ k : Fin 16, column25_0Expr 3 10 k = column25_0_r3_10 k := by decide +kernel
lemma column25_0_r3_11_eq : ∀ k : Fin 16, column25_0Expr 3 11 k = column25_0_r3_11 k := by decide +kernel
lemma column25_0_r3_12_eq : ∀ k : Fin 16, column25_0Expr 3 12 k = column25_0_r3_12 k := by decide +kernel
lemma column25_0_r3_13_eq : ∀ k : Fin 16, column25_0Expr 3 13 k = column25_0_r3_13 k := by decide +kernel
lemma column25_0_r3_14_eq : ∀ k : Fin 16, column25_0Expr 3 14 k = column25_0_r3_14 k := by decide +kernel
lemma column25_0_r3_15_eq : ∀ k : Fin 16, column25_0Expr 3 15 k = column25_0_r3_15 k := by decide +kernel
lemma column25_0_r3_eq (i k : Fin 16) : column25_0Expr 3 i k = column25_0_r3 i k := by
  fin_cases i
  · exact column25_0_r3_0_eq k
  · exact column25_0_r3_1_eq k
  · exact column25_0_r3_2_eq k
  · exact column25_0_r3_3_eq k
  · exact column25_0_r3_4_eq k
  · exact column25_0_r3_5_eq k
  · exact column25_0_r3_6_eq k
  · exact column25_0_r3_7_eq k
  · exact column25_0_r3_8_eq k
  · exact column25_0_r3_9_eq k
  · exact column25_0_r3_10_eq k
  · exact column25_0_r3_11_eq k
  · exact column25_0_r3_12_eq k
  · exact column25_0_r3_13_eq k
  · exact column25_0_r3_14_eq k
  · exact column25_0_r3_15_eq k
lemma column25_0_r4_0_eq : ∀ k : Fin 16, column25_0Expr 4 0 k = column25_0_r4_0 k := by decide +kernel
lemma column25_0_r4_1_eq : ∀ k : Fin 16, column25_0Expr 4 1 k = column25_0_r4_1 k := by decide +kernel
lemma column25_0_r4_2_eq : ∀ k : Fin 16, column25_0Expr 4 2 k = column25_0_r4_2 k := by decide +kernel
lemma column25_0_r4_3_eq : ∀ k : Fin 16, column25_0Expr 4 3 k = column25_0_r4_3 k := by decide +kernel
lemma column25_0_r4_4_eq : ∀ k : Fin 16, column25_0Expr 4 4 k = column25_0_r4_4 k := by decide +kernel
lemma column25_0_r4_5_eq : ∀ k : Fin 16, column25_0Expr 4 5 k = column25_0_r4_5 k := by decide +kernel
lemma column25_0_r4_6_eq : ∀ k : Fin 16, column25_0Expr 4 6 k = column25_0_r4_6 k := by decide +kernel
lemma column25_0_r4_7_eq : ∀ k : Fin 16, column25_0Expr 4 7 k = column25_0_r4_7 k := by decide +kernel
lemma column25_0_r4_8_eq : ∀ k : Fin 16, column25_0Expr 4 8 k = column25_0_r4_8 k := by decide +kernel
lemma column25_0_r4_9_eq : ∀ k : Fin 16, column25_0Expr 4 9 k = column25_0_r4_9 k := by decide +kernel
lemma column25_0_r4_10_eq : ∀ k : Fin 16, column25_0Expr 4 10 k = column25_0_r4_10 k := by decide +kernel
lemma column25_0_r4_11_eq : ∀ k : Fin 16, column25_0Expr 4 11 k = column25_0_r4_11 k := by decide +kernel
lemma column25_0_r4_12_eq : ∀ k : Fin 16, column25_0Expr 4 12 k = column25_0_r4_12 k := by decide +kernel
lemma column25_0_r4_13_eq : ∀ k : Fin 16, column25_0Expr 4 13 k = column25_0_r4_13 k := by decide +kernel
lemma column25_0_r4_14_eq : ∀ k : Fin 16, column25_0Expr 4 14 k = column25_0_r4_14 k := by decide +kernel
lemma column25_0_r4_15_eq : ∀ k : Fin 16, column25_0Expr 4 15 k = column25_0_r4_15 k := by decide +kernel
lemma column25_0_r4_eq (i k : Fin 16) : column25_0Expr 4 i k = column25_0_r4 i k := by
  fin_cases i
  · exact column25_0_r4_0_eq k
  · exact column25_0_r4_1_eq k
  · exact column25_0_r4_2_eq k
  · exact column25_0_r4_3_eq k
  · exact column25_0_r4_4_eq k
  · exact column25_0_r4_5_eq k
  · exact column25_0_r4_6_eq k
  · exact column25_0_r4_7_eq k
  · exact column25_0_r4_8_eq k
  · exact column25_0_r4_9_eq k
  · exact column25_0_r4_10_eq k
  · exact column25_0_r4_11_eq k
  · exact column25_0_r4_12_eq k
  · exact column25_0_r4_13_eq k
  · exact column25_0_r4_14_eq k
  · exact column25_0_r4_15_eq k
lemma column25_0_r5_0_eq : ∀ k : Fin 16, column25_0Expr 5 0 k = column25_0_r5_0 k := by decide +kernel
lemma column25_0_r5_1_eq : ∀ k : Fin 16, column25_0Expr 5 1 k = column25_0_r5_1 k := by decide +kernel
lemma column25_0_r5_2_eq : ∀ k : Fin 16, column25_0Expr 5 2 k = column25_0_r5_2 k := by decide +kernel
lemma column25_0_r5_3_eq : ∀ k : Fin 16, column25_0Expr 5 3 k = column25_0_r5_3 k := by decide +kernel
lemma column25_0_r5_4_eq : ∀ k : Fin 16, column25_0Expr 5 4 k = column25_0_r5_4 k := by decide +kernel
lemma column25_0_r5_5_eq : ∀ k : Fin 16, column25_0Expr 5 5 k = column25_0_r5_5 k := by decide +kernel
lemma column25_0_r5_6_eq : ∀ k : Fin 16, column25_0Expr 5 6 k = column25_0_r5_6 k := by decide +kernel
lemma column25_0_r5_7_eq : ∀ k : Fin 16, column25_0Expr 5 7 k = column25_0_r5_7 k := by decide +kernel
lemma column25_0_r5_8_eq : ∀ k : Fin 16, column25_0Expr 5 8 k = column25_0_r5_8 k := by decide +kernel
lemma column25_0_r5_9_eq : ∀ k : Fin 16, column25_0Expr 5 9 k = column25_0_r5_9 k := by decide +kernel
lemma column25_0_r5_10_eq : ∀ k : Fin 16, column25_0Expr 5 10 k = column25_0_r5_10 k := by decide +kernel
lemma column25_0_r5_11_eq : ∀ k : Fin 16, column25_0Expr 5 11 k = column25_0_r5_11 k := by decide +kernel
lemma column25_0_r5_12_eq : ∀ k : Fin 16, column25_0Expr 5 12 k = column25_0_r5_12 k := by decide +kernel
lemma column25_0_r5_13_eq : ∀ k : Fin 16, column25_0Expr 5 13 k = column25_0_r5_13 k := by decide +kernel
lemma column25_0_r5_14_eq : ∀ k : Fin 16, column25_0Expr 5 14 k = column25_0_r5_14 k := by decide +kernel
lemma column25_0_r5_15_eq : ∀ k : Fin 16, column25_0Expr 5 15 k = column25_0_r5_15 k := by decide +kernel
lemma column25_0_r5_eq (i k : Fin 16) : column25_0Expr 5 i k = column25_0_r5 i k := by
  fin_cases i
  · exact column25_0_r5_0_eq k
  · exact column25_0_r5_1_eq k
  · exact column25_0_r5_2_eq k
  · exact column25_0_r5_3_eq k
  · exact column25_0_r5_4_eq k
  · exact column25_0_r5_5_eq k
  · exact column25_0_r5_6_eq k
  · exact column25_0_r5_7_eq k
  · exact column25_0_r5_8_eq k
  · exact column25_0_r5_9_eq k
  · exact column25_0_r5_10_eq k
  · exact column25_0_r5_11_eq k
  · exact column25_0_r5_12_eq k
  · exact column25_0_r5_13_eq k
  · exact column25_0_r5_14_eq k
  · exact column25_0_r5_15_eq k
lemma column25_0_eq (j : Fin 6) (i k : Fin 16) : column25_0Expr j i k = column25_0 j i k := by
  fin_cases j
  · exact column25_0_r0_eq i k
  · exact column25_0_r1_eq i k
  · exact column25_0_r2_eq i k
  · exact column25_0_r3_eq i k
  · exact column25_0_r4_eq i k
  · exact column25_0_r5_eq i k
noncomputable def column28_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power28 j i k)
lemma column28_1_r0_0_eq : ∀ k : Fin 16, column28_1Expr 0 0 k = column28_1_r0_0 k := by decide +kernel
lemma column28_1_r0_1_eq : ∀ k : Fin 16, column28_1Expr 0 1 k = column28_1_r0_1 k := by decide +kernel
lemma column28_1_r0_2_eq : ∀ k : Fin 16, column28_1Expr 0 2 k = column28_1_r0_2 k := by decide +kernel
lemma column28_1_r0_3_eq : ∀ k : Fin 16, column28_1Expr 0 3 k = column28_1_r0_3 k := by decide +kernel
lemma column28_1_r0_4_eq : ∀ k : Fin 16, column28_1Expr 0 4 k = column28_1_r0_4 k := by decide +kernel
lemma column28_1_r0_5_eq : ∀ k : Fin 16, column28_1Expr 0 5 k = column28_1_r0_5 k := by decide +kernel
lemma column28_1_r0_6_eq : ∀ k : Fin 16, column28_1Expr 0 6 k = column28_1_r0_6 k := by decide +kernel
lemma column28_1_r0_7_eq : ∀ k : Fin 16, column28_1Expr 0 7 k = column28_1_r0_7 k := by decide +kernel
lemma column28_1_r0_8_eq : ∀ k : Fin 16, column28_1Expr 0 8 k = column28_1_r0_8 k := by decide +kernel
lemma column28_1_r0_9_eq : ∀ k : Fin 16, column28_1Expr 0 9 k = column28_1_r0_9 k := by decide +kernel
lemma column28_1_r0_10_eq : ∀ k : Fin 16, column28_1Expr 0 10 k = column28_1_r0_10 k := by decide +kernel
lemma column28_1_r0_11_eq : ∀ k : Fin 16, column28_1Expr 0 11 k = column28_1_r0_11 k := by decide +kernel
lemma column28_1_r0_12_eq : ∀ k : Fin 16, column28_1Expr 0 12 k = column28_1_r0_12 k := by decide +kernel
lemma column28_1_r0_13_eq : ∀ k : Fin 16, column28_1Expr 0 13 k = column28_1_r0_13 k := by decide +kernel
lemma column28_1_r0_14_eq : ∀ k : Fin 16, column28_1Expr 0 14 k = column28_1_r0_14 k := by decide +kernel
lemma column28_1_r0_15_eq : ∀ k : Fin 16, column28_1Expr 0 15 k = column28_1_r0_15 k := by decide +kernel
lemma column28_1_r0_eq (i k : Fin 16) : column28_1Expr 0 i k = column28_1_r0 i k := by
  fin_cases i
  · exact column28_1_r0_0_eq k
  · exact column28_1_r0_1_eq k
  · exact column28_1_r0_2_eq k
  · exact column28_1_r0_3_eq k
  · exact column28_1_r0_4_eq k
  · exact column28_1_r0_5_eq k
  · exact column28_1_r0_6_eq k
  · exact column28_1_r0_7_eq k
  · exact column28_1_r0_8_eq k
  · exact column28_1_r0_9_eq k
  · exact column28_1_r0_10_eq k
  · exact column28_1_r0_11_eq k
  · exact column28_1_r0_12_eq k
  · exact column28_1_r0_13_eq k
  · exact column28_1_r0_14_eq k
  · exact column28_1_r0_15_eq k
lemma column28_1_r1_0_eq : ∀ k : Fin 16, column28_1Expr 1 0 k = column28_1_r1_0 k := by decide +kernel
lemma column28_1_r1_1_eq : ∀ k : Fin 16, column28_1Expr 1 1 k = column28_1_r1_1 k := by decide +kernel
lemma column28_1_r1_2_eq : ∀ k : Fin 16, column28_1Expr 1 2 k = column28_1_r1_2 k := by decide +kernel
lemma column28_1_r1_3_eq : ∀ k : Fin 16, column28_1Expr 1 3 k = column28_1_r1_3 k := by decide +kernel
lemma column28_1_r1_4_eq : ∀ k : Fin 16, column28_1Expr 1 4 k = column28_1_r1_4 k := by decide +kernel
lemma column28_1_r1_5_eq : ∀ k : Fin 16, column28_1Expr 1 5 k = column28_1_r1_5 k := by decide +kernel
lemma column28_1_r1_6_eq : ∀ k : Fin 16, column28_1Expr 1 6 k = column28_1_r1_6 k := by decide +kernel
lemma column28_1_r1_7_eq : ∀ k : Fin 16, column28_1Expr 1 7 k = column28_1_r1_7 k := by decide +kernel
lemma column28_1_r1_8_eq : ∀ k : Fin 16, column28_1Expr 1 8 k = column28_1_r1_8 k := by decide +kernel
lemma column28_1_r1_9_eq : ∀ k : Fin 16, column28_1Expr 1 9 k = column28_1_r1_9 k := by decide +kernel
lemma column28_1_r1_10_eq : ∀ k : Fin 16, column28_1Expr 1 10 k = column28_1_r1_10 k := by decide +kernel
lemma column28_1_r1_11_eq : ∀ k : Fin 16, column28_1Expr 1 11 k = column28_1_r1_11 k := by decide +kernel
lemma column28_1_r1_12_eq : ∀ k : Fin 16, column28_1Expr 1 12 k = column28_1_r1_12 k := by decide +kernel
lemma column28_1_r1_13_eq : ∀ k : Fin 16, column28_1Expr 1 13 k = column28_1_r1_13 k := by decide +kernel
lemma column28_1_r1_14_eq : ∀ k : Fin 16, column28_1Expr 1 14 k = column28_1_r1_14 k := by decide +kernel
lemma column28_1_r1_15_eq : ∀ k : Fin 16, column28_1Expr 1 15 k = column28_1_r1_15 k := by decide +kernel
lemma column28_1_r1_eq (i k : Fin 16) : column28_1Expr 1 i k = column28_1_r1 i k := by
  fin_cases i
  · exact column28_1_r1_0_eq k
  · exact column28_1_r1_1_eq k
  · exact column28_1_r1_2_eq k
  · exact column28_1_r1_3_eq k
  · exact column28_1_r1_4_eq k
  · exact column28_1_r1_5_eq k
  · exact column28_1_r1_6_eq k
  · exact column28_1_r1_7_eq k
  · exact column28_1_r1_8_eq k
  · exact column28_1_r1_9_eq k
  · exact column28_1_r1_10_eq k
  · exact column28_1_r1_11_eq k
  · exact column28_1_r1_12_eq k
  · exact column28_1_r1_13_eq k
  · exact column28_1_r1_14_eq k
  · exact column28_1_r1_15_eq k
lemma column28_1_r2_0_eq : ∀ k : Fin 16, column28_1Expr 2 0 k = column28_1_r2_0 k := by decide +kernel
lemma column28_1_r2_1_eq : ∀ k : Fin 16, column28_1Expr 2 1 k = column28_1_r2_1 k := by decide +kernel
lemma column28_1_r2_2_eq : ∀ k : Fin 16, column28_1Expr 2 2 k = column28_1_r2_2 k := by decide +kernel
lemma column28_1_r2_3_eq : ∀ k : Fin 16, column28_1Expr 2 3 k = column28_1_r2_3 k := by decide +kernel
lemma column28_1_r2_4_eq : ∀ k : Fin 16, column28_1Expr 2 4 k = column28_1_r2_4 k := by decide +kernel
lemma column28_1_r2_5_eq : ∀ k : Fin 16, column28_1Expr 2 5 k = column28_1_r2_5 k := by decide +kernel
lemma column28_1_r2_6_eq : ∀ k : Fin 16, column28_1Expr 2 6 k = column28_1_r2_6 k := by decide +kernel
lemma column28_1_r2_7_eq : ∀ k : Fin 16, column28_1Expr 2 7 k = column28_1_r2_7 k := by decide +kernel
lemma column28_1_r2_8_eq : ∀ k : Fin 16, column28_1Expr 2 8 k = column28_1_r2_8 k := by decide +kernel
lemma column28_1_r2_9_eq : ∀ k : Fin 16, column28_1Expr 2 9 k = column28_1_r2_9 k := by decide +kernel
lemma column28_1_r2_10_eq : ∀ k : Fin 16, column28_1Expr 2 10 k = column28_1_r2_10 k := by decide +kernel
lemma column28_1_r2_11_eq : ∀ k : Fin 16, column28_1Expr 2 11 k = column28_1_r2_11 k := by decide +kernel
lemma column28_1_r2_12_eq : ∀ k : Fin 16, column28_1Expr 2 12 k = column28_1_r2_12 k := by decide +kernel
lemma column28_1_r2_13_eq : ∀ k : Fin 16, column28_1Expr 2 13 k = column28_1_r2_13 k := by decide +kernel
lemma column28_1_r2_14_eq : ∀ k : Fin 16, column28_1Expr 2 14 k = column28_1_r2_14 k := by decide +kernel
lemma column28_1_r2_15_eq : ∀ k : Fin 16, column28_1Expr 2 15 k = column28_1_r2_15 k := by decide +kernel
lemma column28_1_r2_eq (i k : Fin 16) : column28_1Expr 2 i k = column28_1_r2 i k := by
  fin_cases i
  · exact column28_1_r2_0_eq k
  · exact column28_1_r2_1_eq k
  · exact column28_1_r2_2_eq k
  · exact column28_1_r2_3_eq k
  · exact column28_1_r2_4_eq k
  · exact column28_1_r2_5_eq k
  · exact column28_1_r2_6_eq k
  · exact column28_1_r2_7_eq k
  · exact column28_1_r2_8_eq k
  · exact column28_1_r2_9_eq k
  · exact column28_1_r2_10_eq k
  · exact column28_1_r2_11_eq k
  · exact column28_1_r2_12_eq k
  · exact column28_1_r2_13_eq k
  · exact column28_1_r2_14_eq k
  · exact column28_1_r2_15_eq k
lemma column28_1_r3_0_eq : ∀ k : Fin 16, column28_1Expr 3 0 k = column28_1_r3_0 k := by decide +kernel
lemma column28_1_r3_1_eq : ∀ k : Fin 16, column28_1Expr 3 1 k = column28_1_r3_1 k := by decide +kernel
lemma column28_1_r3_2_eq : ∀ k : Fin 16, column28_1Expr 3 2 k = column28_1_r3_2 k := by decide +kernel
lemma column28_1_r3_3_eq : ∀ k : Fin 16, column28_1Expr 3 3 k = column28_1_r3_3 k := by decide +kernel
lemma column28_1_r3_4_eq : ∀ k : Fin 16, column28_1Expr 3 4 k = column28_1_r3_4 k := by decide +kernel
lemma column28_1_r3_5_eq : ∀ k : Fin 16, column28_1Expr 3 5 k = column28_1_r3_5 k := by decide +kernel
lemma column28_1_r3_6_eq : ∀ k : Fin 16, column28_1Expr 3 6 k = column28_1_r3_6 k := by decide +kernel
lemma column28_1_r3_7_eq : ∀ k : Fin 16, column28_1Expr 3 7 k = column28_1_r3_7 k := by decide +kernel
lemma column28_1_r3_8_eq : ∀ k : Fin 16, column28_1Expr 3 8 k = column28_1_r3_8 k := by decide +kernel
lemma column28_1_r3_9_eq : ∀ k : Fin 16, column28_1Expr 3 9 k = column28_1_r3_9 k := by decide +kernel
lemma column28_1_r3_10_eq : ∀ k : Fin 16, column28_1Expr 3 10 k = column28_1_r3_10 k := by decide +kernel
lemma column28_1_r3_11_eq : ∀ k : Fin 16, column28_1Expr 3 11 k = column28_1_r3_11 k := by decide +kernel
lemma column28_1_r3_12_eq : ∀ k : Fin 16, column28_1Expr 3 12 k = column28_1_r3_12 k := by decide +kernel
lemma column28_1_r3_13_eq : ∀ k : Fin 16, column28_1Expr 3 13 k = column28_1_r3_13 k := by decide +kernel
lemma column28_1_r3_14_eq : ∀ k : Fin 16, column28_1Expr 3 14 k = column28_1_r3_14 k := by decide +kernel
lemma column28_1_r3_15_eq : ∀ k : Fin 16, column28_1Expr 3 15 k = column28_1_r3_15 k := by decide +kernel
lemma column28_1_r3_eq (i k : Fin 16) : column28_1Expr 3 i k = column28_1_r3 i k := by
  fin_cases i
  · exact column28_1_r3_0_eq k
  · exact column28_1_r3_1_eq k
  · exact column28_1_r3_2_eq k
  · exact column28_1_r3_3_eq k
  · exact column28_1_r3_4_eq k
  · exact column28_1_r3_5_eq k
  · exact column28_1_r3_6_eq k
  · exact column28_1_r3_7_eq k
  · exact column28_1_r3_8_eq k
  · exact column28_1_r3_9_eq k
  · exact column28_1_r3_10_eq k
  · exact column28_1_r3_11_eq k
  · exact column28_1_r3_12_eq k
  · exact column28_1_r3_13_eq k
  · exact column28_1_r3_14_eq k
  · exact column28_1_r3_15_eq k
lemma column28_1_r4_0_eq : ∀ k : Fin 16, column28_1Expr 4 0 k = column28_1_r4_0 k := by decide +kernel
lemma column28_1_r4_1_eq : ∀ k : Fin 16, column28_1Expr 4 1 k = column28_1_r4_1 k := by decide +kernel
lemma column28_1_r4_2_eq : ∀ k : Fin 16, column28_1Expr 4 2 k = column28_1_r4_2 k := by decide +kernel
lemma column28_1_r4_3_eq : ∀ k : Fin 16, column28_1Expr 4 3 k = column28_1_r4_3 k := by decide +kernel
lemma column28_1_r4_4_eq : ∀ k : Fin 16, column28_1Expr 4 4 k = column28_1_r4_4 k := by decide +kernel
lemma column28_1_r4_5_eq : ∀ k : Fin 16, column28_1Expr 4 5 k = column28_1_r4_5 k := by decide +kernel
lemma column28_1_r4_6_eq : ∀ k : Fin 16, column28_1Expr 4 6 k = column28_1_r4_6 k := by decide +kernel
lemma column28_1_r4_7_eq : ∀ k : Fin 16, column28_1Expr 4 7 k = column28_1_r4_7 k := by decide +kernel
lemma column28_1_r4_8_eq : ∀ k : Fin 16, column28_1Expr 4 8 k = column28_1_r4_8 k := by decide +kernel
lemma column28_1_r4_9_eq : ∀ k : Fin 16, column28_1Expr 4 9 k = column28_1_r4_9 k := by decide +kernel
lemma column28_1_r4_10_eq : ∀ k : Fin 16, column28_1Expr 4 10 k = column28_1_r4_10 k := by decide +kernel
lemma column28_1_r4_11_eq : ∀ k : Fin 16, column28_1Expr 4 11 k = column28_1_r4_11 k := by decide +kernel
lemma column28_1_r4_12_eq : ∀ k : Fin 16, column28_1Expr 4 12 k = column28_1_r4_12 k := by decide +kernel
lemma column28_1_r4_13_eq : ∀ k : Fin 16, column28_1Expr 4 13 k = column28_1_r4_13 k := by decide +kernel
lemma column28_1_r4_14_eq : ∀ k : Fin 16, column28_1Expr 4 14 k = column28_1_r4_14 k := by decide +kernel
lemma column28_1_r4_15_eq : ∀ k : Fin 16, column28_1Expr 4 15 k = column28_1_r4_15 k := by decide +kernel
lemma column28_1_r4_eq (i k : Fin 16) : column28_1Expr 4 i k = column28_1_r4 i k := by
  fin_cases i
  · exact column28_1_r4_0_eq k
  · exact column28_1_r4_1_eq k
  · exact column28_1_r4_2_eq k
  · exact column28_1_r4_3_eq k
  · exact column28_1_r4_4_eq k
  · exact column28_1_r4_5_eq k
  · exact column28_1_r4_6_eq k
  · exact column28_1_r4_7_eq k
  · exact column28_1_r4_8_eq k
  · exact column28_1_r4_9_eq k
  · exact column28_1_r4_10_eq k
  · exact column28_1_r4_11_eq k
  · exact column28_1_r4_12_eq k
  · exact column28_1_r4_13_eq k
  · exact column28_1_r4_14_eq k
  · exact column28_1_r4_15_eq k
lemma column28_1_r5_0_eq : ∀ k : Fin 16, column28_1Expr 5 0 k = column28_1_r5_0 k := by decide +kernel
lemma column28_1_r5_1_eq : ∀ k : Fin 16, column28_1Expr 5 1 k = column28_1_r5_1 k := by decide +kernel
lemma column28_1_r5_2_eq : ∀ k : Fin 16, column28_1Expr 5 2 k = column28_1_r5_2 k := by decide +kernel
lemma column28_1_r5_3_eq : ∀ k : Fin 16, column28_1Expr 5 3 k = column28_1_r5_3 k := by decide +kernel
lemma column28_1_r5_4_eq : ∀ k : Fin 16, column28_1Expr 5 4 k = column28_1_r5_4 k := by decide +kernel
lemma column28_1_r5_5_eq : ∀ k : Fin 16, column28_1Expr 5 5 k = column28_1_r5_5 k := by decide +kernel
lemma column28_1_r5_6_eq : ∀ k : Fin 16, column28_1Expr 5 6 k = column28_1_r5_6 k := by decide +kernel
lemma column28_1_r5_7_eq : ∀ k : Fin 16, column28_1Expr 5 7 k = column28_1_r5_7 k := by decide +kernel
lemma column28_1_r5_8_eq : ∀ k : Fin 16, column28_1Expr 5 8 k = column28_1_r5_8 k := by decide +kernel
lemma column28_1_r5_9_eq : ∀ k : Fin 16, column28_1Expr 5 9 k = column28_1_r5_9 k := by decide +kernel
lemma column28_1_r5_10_eq : ∀ k : Fin 16, column28_1Expr 5 10 k = column28_1_r5_10 k := by decide +kernel
lemma column28_1_r5_11_eq : ∀ k : Fin 16, column28_1Expr 5 11 k = column28_1_r5_11 k := by decide +kernel
lemma column28_1_r5_12_eq : ∀ k : Fin 16, column28_1Expr 5 12 k = column28_1_r5_12 k := by decide +kernel
lemma column28_1_r5_13_eq : ∀ k : Fin 16, column28_1Expr 5 13 k = column28_1_r5_13 k := by decide +kernel
lemma column28_1_r5_14_eq : ∀ k : Fin 16, column28_1Expr 5 14 k = column28_1_r5_14 k := by decide +kernel
lemma column28_1_r5_15_eq : ∀ k : Fin 16, column28_1Expr 5 15 k = column28_1_r5_15 k := by decide +kernel
lemma column28_1_r5_eq (i k : Fin 16) : column28_1Expr 5 i k = column28_1_r5 i k := by
  fin_cases i
  · exact column28_1_r5_0_eq k
  · exact column28_1_r5_1_eq k
  · exact column28_1_r5_2_eq k
  · exact column28_1_r5_3_eq k
  · exact column28_1_r5_4_eq k
  · exact column28_1_r5_5_eq k
  · exact column28_1_r5_6_eq k
  · exact column28_1_r5_7_eq k
  · exact column28_1_r5_8_eq k
  · exact column28_1_r5_9_eq k
  · exact column28_1_r5_10_eq k
  · exact column28_1_r5_11_eq k
  · exact column28_1_r5_12_eq k
  · exact column28_1_r5_13_eq k
  · exact column28_1_r5_14_eq k
  · exact column28_1_r5_15_eq k
lemma column28_1_eq (j : Fin 6) (i k : Fin 16) : column28_1Expr j i k = column28_1 j i k := by
  fin_cases j
  · exact column28_1_r0_eq i k
  · exact column28_1_r1_eq i k
  · exact column28_1_r2_eq i k
  · exact column28_1_r3_eq i k
  · exact column28_1_r4_eq i k
  · exact column28_1_r5_eq i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns40
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
noncomputable def column31_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power31 j i k)
lemma column31_0_r0_0_eq : ∀ k : Fin 16, column31_0Expr 0 0 k = column31_0_r0_0 k := by decide +kernel
lemma column31_0_r0_1_eq : ∀ k : Fin 16, column31_0Expr 0 1 k = column31_0_r0_1 k := by decide +kernel
lemma column31_0_r0_2_eq : ∀ k : Fin 16, column31_0Expr 0 2 k = column31_0_r0_2 k := by decide +kernel
lemma column31_0_r0_3_eq : ∀ k : Fin 16, column31_0Expr 0 3 k = column31_0_r0_3 k := by decide +kernel
lemma column31_0_r0_4_eq : ∀ k : Fin 16, column31_0Expr 0 4 k = column31_0_r0_4 k := by decide +kernel
lemma column31_0_r0_5_eq : ∀ k : Fin 16, column31_0Expr 0 5 k = column31_0_r0_5 k := by decide +kernel
lemma column31_0_r0_6_eq : ∀ k : Fin 16, column31_0Expr 0 6 k = column31_0_r0_6 k := by decide +kernel
lemma column31_0_r0_7_eq : ∀ k : Fin 16, column31_0Expr 0 7 k = column31_0_r0_7 k := by decide +kernel
lemma column31_0_r0_8_eq : ∀ k : Fin 16, column31_0Expr 0 8 k = column31_0_r0_8 k := by decide +kernel
lemma column31_0_r0_9_eq : ∀ k : Fin 16, column31_0Expr 0 9 k = column31_0_r0_9 k := by decide +kernel
lemma column31_0_r0_10_eq : ∀ k : Fin 16, column31_0Expr 0 10 k = column31_0_r0_10 k := by decide +kernel
lemma column31_0_r0_11_eq : ∀ k : Fin 16, column31_0Expr 0 11 k = column31_0_r0_11 k := by decide +kernel
lemma column31_0_r0_12_eq : ∀ k : Fin 16, column31_0Expr 0 12 k = column31_0_r0_12 k := by decide +kernel
lemma column31_0_r0_13_eq : ∀ k : Fin 16, column31_0Expr 0 13 k = column31_0_r0_13 k := by decide +kernel
lemma column31_0_r0_14_eq : ∀ k : Fin 16, column31_0Expr 0 14 k = column31_0_r0_14 k := by decide +kernel
lemma column31_0_r0_15_eq : ∀ k : Fin 16, column31_0Expr 0 15 k = column31_0_r0_15 k := by decide +kernel
lemma column31_0_r0_eq (i k : Fin 16) : column31_0Expr 0 i k = column31_0_r0 i k := by
  fin_cases i
  · exact column31_0_r0_0_eq k
  · exact column31_0_r0_1_eq k
  · exact column31_0_r0_2_eq k
  · exact column31_0_r0_3_eq k
  · exact column31_0_r0_4_eq k
  · exact column31_0_r0_5_eq k
  · exact column31_0_r0_6_eq k
  · exact column31_0_r0_7_eq k
  · exact column31_0_r0_8_eq k
  · exact column31_0_r0_9_eq k
  · exact column31_0_r0_10_eq k
  · exact column31_0_r0_11_eq k
  · exact column31_0_r0_12_eq k
  · exact column31_0_r0_13_eq k
  · exact column31_0_r0_14_eq k
  · exact column31_0_r0_15_eq k
lemma column31_0_r1_0_eq : ∀ k : Fin 16, column31_0Expr 1 0 k = column31_0_r1_0 k := by decide +kernel
lemma column31_0_r1_1_eq : ∀ k : Fin 16, column31_0Expr 1 1 k = column31_0_r1_1 k := by decide +kernel
lemma column31_0_r1_2_eq : ∀ k : Fin 16, column31_0Expr 1 2 k = column31_0_r1_2 k := by decide +kernel
lemma column31_0_r1_3_eq : ∀ k : Fin 16, column31_0Expr 1 3 k = column31_0_r1_3 k := by decide +kernel
lemma column31_0_r1_4_eq : ∀ k : Fin 16, column31_0Expr 1 4 k = column31_0_r1_4 k := by decide +kernel
lemma column31_0_r1_5_eq : ∀ k : Fin 16, column31_0Expr 1 5 k = column31_0_r1_5 k := by decide +kernel
lemma column31_0_r1_6_eq : ∀ k : Fin 16, column31_0Expr 1 6 k = column31_0_r1_6 k := by decide +kernel
lemma column31_0_r1_7_eq : ∀ k : Fin 16, column31_0Expr 1 7 k = column31_0_r1_7 k := by decide +kernel
lemma column31_0_r1_8_eq : ∀ k : Fin 16, column31_0Expr 1 8 k = column31_0_r1_8 k := by decide +kernel
lemma column31_0_r1_9_eq : ∀ k : Fin 16, column31_0Expr 1 9 k = column31_0_r1_9 k := by decide +kernel
lemma column31_0_r1_10_eq : ∀ k : Fin 16, column31_0Expr 1 10 k = column31_0_r1_10 k := by decide +kernel
lemma column31_0_r1_11_eq : ∀ k : Fin 16, column31_0Expr 1 11 k = column31_0_r1_11 k := by decide +kernel
lemma column31_0_r1_12_eq : ∀ k : Fin 16, column31_0Expr 1 12 k = column31_0_r1_12 k := by decide +kernel
lemma column31_0_r1_13_eq : ∀ k : Fin 16, column31_0Expr 1 13 k = column31_0_r1_13 k := by decide +kernel
lemma column31_0_r1_14_eq : ∀ k : Fin 16, column31_0Expr 1 14 k = column31_0_r1_14 k := by decide +kernel
lemma column31_0_r1_15_eq : ∀ k : Fin 16, column31_0Expr 1 15 k = column31_0_r1_15 k := by decide +kernel
lemma column31_0_r1_eq (i k : Fin 16) : column31_0Expr 1 i k = column31_0_r1 i k := by
  fin_cases i
  · exact column31_0_r1_0_eq k
  · exact column31_0_r1_1_eq k
  · exact column31_0_r1_2_eq k
  · exact column31_0_r1_3_eq k
  · exact column31_0_r1_4_eq k
  · exact column31_0_r1_5_eq k
  · exact column31_0_r1_6_eq k
  · exact column31_0_r1_7_eq k
  · exact column31_0_r1_8_eq k
  · exact column31_0_r1_9_eq k
  · exact column31_0_r1_10_eq k
  · exact column31_0_r1_11_eq k
  · exact column31_0_r1_12_eq k
  · exact column31_0_r1_13_eq k
  · exact column31_0_r1_14_eq k
  · exact column31_0_r1_15_eq k
lemma column31_0_r2_0_eq : ∀ k : Fin 16, column31_0Expr 2 0 k = column31_0_r2_0 k := by decide +kernel
lemma column31_0_r2_1_eq : ∀ k : Fin 16, column31_0Expr 2 1 k = column31_0_r2_1 k := by decide +kernel
lemma column31_0_r2_2_eq : ∀ k : Fin 16, column31_0Expr 2 2 k = column31_0_r2_2 k := by decide +kernel
lemma column31_0_r2_3_eq : ∀ k : Fin 16, column31_0Expr 2 3 k = column31_0_r2_3 k := by decide +kernel
lemma column31_0_r2_4_eq : ∀ k : Fin 16, column31_0Expr 2 4 k = column31_0_r2_4 k := by decide +kernel
lemma column31_0_r2_5_eq : ∀ k : Fin 16, column31_0Expr 2 5 k = column31_0_r2_5 k := by decide +kernel
lemma column31_0_r2_6_eq : ∀ k : Fin 16, column31_0Expr 2 6 k = column31_0_r2_6 k := by decide +kernel
lemma column31_0_r2_7_eq : ∀ k : Fin 16, column31_0Expr 2 7 k = column31_0_r2_7 k := by decide +kernel
lemma column31_0_r2_8_eq : ∀ k : Fin 16, column31_0Expr 2 8 k = column31_0_r2_8 k := by decide +kernel
lemma column31_0_r2_9_eq : ∀ k : Fin 16, column31_0Expr 2 9 k = column31_0_r2_9 k := by decide +kernel
lemma column31_0_r2_10_eq : ∀ k : Fin 16, column31_0Expr 2 10 k = column31_0_r2_10 k := by decide +kernel
lemma column31_0_r2_11_eq : ∀ k : Fin 16, column31_0Expr 2 11 k = column31_0_r2_11 k := by decide +kernel
lemma column31_0_r2_12_eq : ∀ k : Fin 16, column31_0Expr 2 12 k = column31_0_r2_12 k := by decide +kernel
lemma column31_0_r2_13_eq : ∀ k : Fin 16, column31_0Expr 2 13 k = column31_0_r2_13 k := by decide +kernel
lemma column31_0_r2_14_eq : ∀ k : Fin 16, column31_0Expr 2 14 k = column31_0_r2_14 k := by decide +kernel
lemma column31_0_r2_15_eq : ∀ k : Fin 16, column31_0Expr 2 15 k = column31_0_r2_15 k := by decide +kernel
lemma column31_0_r2_eq (i k : Fin 16) : column31_0Expr 2 i k = column31_0_r2 i k := by
  fin_cases i
  · exact column31_0_r2_0_eq k
  · exact column31_0_r2_1_eq k
  · exact column31_0_r2_2_eq k
  · exact column31_0_r2_3_eq k
  · exact column31_0_r2_4_eq k
  · exact column31_0_r2_5_eq k
  · exact column31_0_r2_6_eq k
  · exact column31_0_r2_7_eq k
  · exact column31_0_r2_8_eq k
  · exact column31_0_r2_9_eq k
  · exact column31_0_r2_10_eq k
  · exact column31_0_r2_11_eq k
  · exact column31_0_r2_12_eq k
  · exact column31_0_r2_13_eq k
  · exact column31_0_r2_14_eq k
  · exact column31_0_r2_15_eq k
lemma column31_0_r3_0_eq : ∀ k : Fin 16, column31_0Expr 3 0 k = column31_0_r3_0 k := by decide +kernel
lemma column31_0_r3_1_eq : ∀ k : Fin 16, column31_0Expr 3 1 k = column31_0_r3_1 k := by decide +kernel
lemma column31_0_r3_2_eq : ∀ k : Fin 16, column31_0Expr 3 2 k = column31_0_r3_2 k := by decide +kernel
lemma column31_0_r3_3_eq : ∀ k : Fin 16, column31_0Expr 3 3 k = column31_0_r3_3 k := by decide +kernel
lemma column31_0_r3_4_eq : ∀ k : Fin 16, column31_0Expr 3 4 k = column31_0_r3_4 k := by decide +kernel
lemma column31_0_r3_5_eq : ∀ k : Fin 16, column31_0Expr 3 5 k = column31_0_r3_5 k := by decide +kernel
lemma column31_0_r3_6_eq : ∀ k : Fin 16, column31_0Expr 3 6 k = column31_0_r3_6 k := by decide +kernel
lemma column31_0_r3_7_eq : ∀ k : Fin 16, column31_0Expr 3 7 k = column31_0_r3_7 k := by decide +kernel
lemma column31_0_r3_8_eq : ∀ k : Fin 16, column31_0Expr 3 8 k = column31_0_r3_8 k := by decide +kernel
lemma column31_0_r3_9_eq : ∀ k : Fin 16, column31_0Expr 3 9 k = column31_0_r3_9 k := by decide +kernel
lemma column31_0_r3_10_eq : ∀ k : Fin 16, column31_0Expr 3 10 k = column31_0_r3_10 k := by decide +kernel
lemma column31_0_r3_11_eq : ∀ k : Fin 16, column31_0Expr 3 11 k = column31_0_r3_11 k := by decide +kernel
lemma column31_0_r3_12_eq : ∀ k : Fin 16, column31_0Expr 3 12 k = column31_0_r3_12 k := by decide +kernel
lemma column31_0_r3_13_eq : ∀ k : Fin 16, column31_0Expr 3 13 k = column31_0_r3_13 k := by decide +kernel
lemma column31_0_r3_14_eq : ∀ k : Fin 16, column31_0Expr 3 14 k = column31_0_r3_14 k := by decide +kernel
lemma column31_0_r3_15_eq : ∀ k : Fin 16, column31_0Expr 3 15 k = column31_0_r3_15 k := by decide +kernel
lemma column31_0_r3_eq (i k : Fin 16) : column31_0Expr 3 i k = column31_0_r3 i k := by
  fin_cases i
  · exact column31_0_r3_0_eq k
  · exact column31_0_r3_1_eq k
  · exact column31_0_r3_2_eq k
  · exact column31_0_r3_3_eq k
  · exact column31_0_r3_4_eq k
  · exact column31_0_r3_5_eq k
  · exact column31_0_r3_6_eq k
  · exact column31_0_r3_7_eq k
  · exact column31_0_r3_8_eq k
  · exact column31_0_r3_9_eq k
  · exact column31_0_r3_10_eq k
  · exact column31_0_r3_11_eq k
  · exact column31_0_r3_12_eq k
  · exact column31_0_r3_13_eq k
  · exact column31_0_r3_14_eq k
  · exact column31_0_r3_15_eq k
lemma column31_0_r4_0_eq : ∀ k : Fin 16, column31_0Expr 4 0 k = column31_0_r4_0 k := by decide +kernel
lemma column31_0_r4_1_eq : ∀ k : Fin 16, column31_0Expr 4 1 k = column31_0_r4_1 k := by decide +kernel
lemma column31_0_r4_10_eq : ∀ k : Fin 16, column31_0Expr 4 10 k = column31_0_r4_10 k := by decide +kernel
lemma column31_0_r4_11_eq : ∀ k : Fin 16, column31_0Expr 4 11 k = column31_0_r4_11 k := by decide +kernel
lemma column31_0_r4_12_eq : ∀ k : Fin 16, column31_0Expr 4 12 k = column31_0_r4_12 k := by decide +kernel
lemma column31_0_r4_13_eq : ∀ k : Fin 16, column31_0Expr 4 13 k = column31_0_r4_13 k := by decide +kernel
lemma column31_0_r4_14_eq : ∀ k : Fin 16, column31_0Expr 4 14 k = column31_0_r4_14 k := by decide +kernel
lemma column31_0_r4_15_eq : ∀ k : Fin 16, column31_0Expr 4 15 k = column31_0_r4_15 k := by decide +kernel
noncomputable def column33_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power33 j i k)
noncomputable def column33_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power33 j i k)
noncomputable def column36_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power36 j i k)
noncomputable def column36_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power36 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def trans7_r1 : Fin 16 → Fin 16 → CBox := ![trans7_r1_0,trans7_r1_1,trans7_r1_2,trans7_r1_3,trans7_r1_4,trans7_r1_5,trans7_r1_6,trans7_r1_7,trans7_r1_8,trans7_r1_9,trans7_r1_10,trans7_r1_11,trans7_r1_12,trans7_r1_13,trans7_r1_14,trans7_r1_15]
noncomputable def trans7 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans7_r0,trans7_r1,trans7_r2,trans7_r3,trans7_r4,trans7_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
noncomputable def kernel7_0_r4 : Fin 16 → Fin 16 → CBox := ![kernel7_0_r4_0,kernel7_0_r4_1,kernel7_0_r4_2,kernel7_0_r4_3,kernel7_0_r4_4,kernel7_0_r4_5,kernel7_0_r4_6,kernel7_0_r4_7,kernel7_0_r4_8,kernel7_0_r4_9,kernel7_0_r4_10,kernel7_0_r4_11,kernel7_0_r4_12,kernel7_0_r4_13,kernel7_0_r4_14,kernel7_0_r4_15]
noncomputable def kernel7_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel7_0_r0,kernel7_0_r1,kernel7_0_r2,kernel7_0_r3,kernel7_0_r4,kernel7_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers20
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
noncomputable def trans11_r0 : Fin 16 → Fin 16 → CBox := ![trans11_r0_0,trans11_r0_1,trans11_r0_2,trans11_r0_3,trans11_r0_4,trans11_r0_5,trans11_r0_6,trans11_r0_7,trans11_r0_8,trans11_r0_9,trans11_r0_10,trans11_r0_11,trans11_r0_12,trans11_r0_13,trans11_r0_14,trans11_r0_15]
noncomputable def trans11 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans11_r0,trans11_r1,trans11_r2,trans11_r3,trans11_r4,trans11_r5]
noncomputable def trans12_r5 : Fin 16 → Fin 16 → CBox := ![trans12_r5_0,trans12_r5_1,trans12_r5_2,trans12_r5_3,trans12_r5_4,trans12_r5_5,trans12_r5_6,trans12_r5_7,trans12_r5_8,trans12_r5_9,trans12_r5_10,trans12_r5_11,trans12_r5_12,trans12_r5_13,trans12_r5_14,trans12_r5_15]
noncomputable def trans12 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans12_r0,trans12_r1,trans12_r2,trans12_r3,trans12_r4,trans12_r5]
noncomputable def trans15 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans15_r0,trans15_r1,trans15_r2,trans15_r3,trans15_r4,trans15_r5]
noncomputable def trans16_r5 : Fin 16 → Fin 16 → CBox := ![trans16_r5_0,trans16_r5_1,trans16_r5_2,trans16_r5_3,trans16_r5_4,trans16_r5_5,trans16_r5_6,trans16_r5_7,trans16_r5_8,trans16_r5_9,trans16_r5_10,trans16_r5_11,trans16_r5_12,trans16_r5_13,trans16_r5_14,trans16_r5_15]
noncomputable def trans16 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans16_r0,trans16_r1,trans16_r2,trans16_r3,trans16_r4,trans16_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments12
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
namespace cm1_12_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_12_0_0
namespace cm1_12_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_12_0_1
namespace cm1_12_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_12_1_0
namespace cm1_12_1_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_12_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments13
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
namespace cm1_13_0_0
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_13_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments15
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
namespace cm1_15_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_15_0_1
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
namespace cm1_16_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_16_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments7
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
namespace cm1_7_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_7_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments12
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
namespace cm12_3_0_1
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
end cm12_3_0_1
namespace cm12_4_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm12_4_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments15
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
namespace cm15_1_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm15_1_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments16
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
namespace cm16_4_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm16_4_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments21
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
namespace cm21_1_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm21_1_0_1
namespace cm21_3_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm21_3_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments24
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
namespace cm24_4_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm24_4_0_1
namespace cm24_4_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm24_4_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments27
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
namespace cm27_3_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm27_3_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments31
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
namespace cm31_1_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
end cm31_1_0_1
end SharpPlanar.CachedData

end OAI
end


