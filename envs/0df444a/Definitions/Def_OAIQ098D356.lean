-- Prove2me | Definitions.Def_OAIQ098D356
-- name    : OAIQ098D356
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T21:44:28.470565+00:00
-- url     : https://prove2.me/theorems/f5a8b14f-e912-463f-8142-686aa8d85430
-- title:
--   Definitions bundle OAIQ098D356 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 786 declarations of OpenAI's Lean: 163 definitions and 623 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.hk15_0_6`, `OAI.SharpPlanar.CachedData.hk15_0_7`, `OAI.SharpPlanar.CachedData.hk15_0_8`, `OAI.SharpPlanar.CachedData.hk15_0_9`, `OAI.SharpPlanar.CachedData.hk1_1_1`, `OAI.SharpPlanar.CachedData.hk1_1_10`, `OAI.SharpPlanar.CachedData.hk1_1_11`, `OAI.SharpPlanar.CachedData.hk1_1_12`, `OAI.SharpPlanar.CachedData.hk1_1_13`, `OAI.SharpPlanar.CachedData.hk1_1_14`, `OAI.SharpPlanar.CachedData.hk1_1_15`, `OAI.SharpPlanar.CachedData.hk1_1_16`, `OAI.SharpPlanar.CachedData.hk1_1_17`, `OAI.SharpPlanar.CachedData.hk1_1_18`, `OAI.SharpPlanar.CachedData.hk1_1_19`, `OAI.SharpPlanar.CachedData.hk1_1_2`, `OAI.SharpPlanar.CachedData.hk1_1_20`, `OAI.SharpPlanar.CachedData.hk1_1_21`, `OAI.SharpPlanar.CachedData.hk1_1_22`, `OAI.SharpPlanar.CachedData.hk1_1_23`, `OAI.SharpPlanar.CachedData.hk1_1_24`, `OAI.SharpPlanar.CachedData.hk1_1_25`, `OAI.SharpPlanar.CachedData.hk1_1_26`, `OAI.SharpPlanar.CachedData.hk1_1_27`, `OAI.SharpPlanar.CachedData.hk1_1_28`, `OAI.SharpPlanar.CachedData.hk1_1_29`, `OAI.SharpPlanar.CachedData.hk1_1_3`, `OAI.SharpPlanar.CachedData.hk1_1_30`, `OAI.SharpPlanar.CachedData.hk1_1_4`, `OAI.SharpPlanar.CachedData.hk1_1_5`, `OAI.SharpPlanar.CachedData.hk1_1_6`, `OAI.SharpPlanar.CachedData.hk1_1_7`, `OAI.SharpPlanar.CachedData.hk1_1_8`, `OAI.SharpPlanar.CachedData.hk1_1_9`, `OAI.SharpPlanar.CachedData.hk21_0_10`, `OAI.SharpPlanar.CachedData.hk21_0_11`, `OAI.SharpPlanar.CachedData.hk21_0_12`, `OAI.SharpPlanar.CachedData.hk21_0_13`, `OAI.SharpPlanar.CachedData.hk21_0_2`, `OAI.SharpPlanar.CachedData.hk21_0_3` and 123 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_HighHeaders0`, `PlanarPacking_Certificate_HighHeaders1`, `PlanarPacking_Certificate_HighHeaders12`, `PlanarPacking_Certificate_HighHeaders13`, `PlanarPacking_Certificate_HighHeaders15`, `PlanarPacking_Certificate_HighHeaders16`, `PlanarPacking_Certificate_HighHeaders19`, `PlanarPacking_Certificate_HighHeaders21`, `PlanarPacking_Certificate_HighHeaders24`, `PlanarPacking_Certificate_HighHeaders25`, `PlanarPacking_Certificate_HighHeaders27`, `PlanarPacking_Certificate_HighHeaders28`, `PlanarPacking_Certificate_HighHeaders3`, `PlanarPacking_Certificate_HighHeaders31`, `PlanarPacking_Certificate_HighHeaders33`, `PlanarPacking_Certificate_HighHeaders36`, `PlanarPacking_Certificate_HighHeaders37`, `PlanarPacking_Certificate_HighHeaders39`, `PlanarPacking_Certificate_HighHeaders4`, `PlanarPacking_Certificate_HighHeaders40`, `PlanarPacking_Certificate_HighHeaders7`, `PlanarPacking_Certificate_HighHeaders9`, `PlanarPacking_Certificate_HighMoments0_4`, `PlanarPacking_Certificate_HighMoments0_5`, `PlanarPacking_TableMomentsBase`.
--
--   **Imports.** It imports the bundles `OAIQ098D262`, `OAIQ098D263`, `OAIQ098D264`, `OAIQ098D265` and `OAIQ098D270` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D500`, `OAIQ098D501`, `OAIQ098D502`, `OAIQ098D503`, `OAIQ098D504`, `OAIQ098D505`, `OAIQ098D506`, `OAIQ098D507`, `OAIQ098D508`, `OAIQ098D509`, `OAIQ098D510`, `OAIQ098D512`, `OAIQ098D513`, `OAIQ098D514`, `OAIQ098D515`, `OAIQ098D516`, `OAIQ098D517`, `OAIQ098D518`, `OAIQ098D519`, `OAIQ098D520`, `OAIQ098D521`, `OAIQ098D522`, `OAIQ098D523`, `OAIQ098D524`, `OAIQ098D525`, `OAIQ098D526`, `OAIQ098D527`, `OAIQ098D528`, `OAIQ098D529`, `OAIQ098D530`, `OAIQ098D531`, `OAIQ098D532`, `OAIQ098D533`, `OAIQ098D534`, `OAIQ098D535`, `OAIQ098D536`, `OAIQ098D537`, `OAIQ098D538`, `OAIQ098D539`, `OAIQ098D540`, `OAIQ098D541`, `OAIQ098D542`, `OAIQ098D543`, `OAIQ098D544`, `OAIQ098D545`, `OAIQ098D546`, `OAIQ098D547`, `OAIQ098D548`, `OAIQ098D549`, `OAIQ098D550`, `OAIQ098D551`, `OAIQ098D552`, `OAIQ098D553`, `OAIQ098D554`, `OAIQ098D555`, `OAIQ098D556`, `OAIQ098D557`, `OAIQ098D558`, `OAIQ098D559`, `OAIQ098D560`, `OAIQ098D561`, `OAIQ098D562`, `OAIQ098D563`, `OAIQ098D564`, `OAIQ098D565`, `OAIQ098D566`, `OAIQ098D567`, `OAIQ098D568`, `OAIQ098D569`, `OAIQ098D570`, `OAIQ098D571`, `OAIQ098D572`, `OAIQ098D573`, `OAIQ098D574`, `OAIQ098D575`, `OAIQ098D576`, `OAIQ098D577`, `OAIQ098D578`, `OAIQ098D579`, `OAIQ098D580`, `OAIQ098D581`, `OAIQ098D582`, `OAIQ098D583`, `OAIQ098D584`, `OAIQ098D585`, `OAIQ098D586`, `OAIQ098D587`, `OAIQ098D588`, `OAIQ098D589`, `OAIQ098D590`, `OAIQ098D591`, `OAIQ098D592`, `OAIQ098D593`, `OAIQ098D594`, `OAIQ098D595`, `OAIQ098D596`, `OAIQ098D597`, `OAIQ098D598`, `OAIQ098D599`, `OAIQ098D606`, `OAIQ098D607`, `OAIQ098D608`, `OAIQ098D609` and `OAIQ098D610`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D262
import Definitions.Def_OAIQ098D263
import Definitions.Def_OAIQ098D264
import Definitions.Def_OAIQ098D265
import Definitions.Def_OAIQ098D270

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Certified quadrature and atomic bounds for the Gaussian moments -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
open scoped BigOperators

def tableAtomBox (a : Bool) (kernel : Fin 7 → CBox) : CBox :=
  (finSum (fun j : Fin 7 => ((coefficientBox j.val).scale (if j.val=0 then 1 else 2) 1).mul (kernel j))).scale (if a then 17 else -13) 1000
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders0
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha0_1_7_eq (j : Fin 7) : ha0_1_7 j = ((ha0_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha0_1_8_eq (j : Fin 7) : ha0_1_8 j = ((ha0_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha0_1_9_eq (j : Fin 7) : ha0_1_9 j = ((ha0_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders1
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha1_0_0_eq (j : Fin 7) : ha1_0_0 j = ((atomPoints j).direct.powBin 7 1).conj := by fin_cases j <;> decide +kernel
lemma ha1_0_1_eq (j : Fin 7) : ha1_0_1 j = ((ha1_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha1_0_2_eq (j : Fin 7) : ha1_0_2 j = ((ha1_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha1_0_3_eq (j : Fin 7) : ha1_0_3 j = ((ha1_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha1_0_4_eq (j : Fin 7) : ha1_0_4 j = ((ha1_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha1_0_5_eq (j : Fin 7) : ha1_0_5 j = ((ha1_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha1_0_6_eq (j : Fin 7) : ha1_0_6 j = ((ha1_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha1_0_7_eq (j : Fin 7) : ha1_0_7 j = ((ha1_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha1_0_8_eq (j : Fin 7) : ha1_0_8 j = ((ha1_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha1_0_9_eq (j : Fin 7) : ha1_0_9 j = ((ha1_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha1_0_10_eq (j : Fin 7) : ha1_0_10 j = ((ha1_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha1_0_11_eq (j : Fin 7) : ha1_0_11 j = ((ha1_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha1_0_12_eq (j : Fin 7) : ha1_0_12 j = ((ha1_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha1_0_13_eq (j : Fin 7) : ha1_0_13 j = ((ha1_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha1_0_14_eq (j : Fin 7) : ha1_0_14 j = ((ha1_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha1_0_15_eq (j : Fin 7) : ha1_0_15 j = ((ha1_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha1_0_16_eq (j : Fin 7) : ha1_0_16 j = ((ha1_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha1_0_17_eq (j : Fin 7) : ha1_0_17 j = ((ha1_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha1_0_18_eq (j : Fin 7) : ha1_0_18 j = ((ha1_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha1_0_19_eq (j : Fin 7) : ha1_0_19 j = ((ha1_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha1_0_20_eq (j : Fin 7) : ha1_0_20 j = ((ha1_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha1_0_21_eq (j : Fin 7) : ha1_0_21 j = ((ha1_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha1_0_22_eq (j : Fin 7) : ha1_0_22 j = ((ha1_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha1_0_23_eq (j : Fin 7) : ha1_0_23 j = ((ha1_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha1_0_24_eq (j : Fin 7) : ha1_0_24 j = ((ha1_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha1_0_25_eq (j : Fin 7) : ha1_0_25 j = ((ha1_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha1_0_26_eq (j : Fin 7) : ha1_0_26 j = ((ha1_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha1_0_27_eq (j : Fin 7) : ha1_0_27 j = ((ha1_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha1_0_28_eq (j : Fin 7) : ha1_0_28 j = ((ha1_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha1_0_29_eq (j : Fin 7) : ha1_0_29 j = ((ha1_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha1_0_30_eq (j : Fin 7) : ha1_0_30 j = ((ha1_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_1 j i k)
lemma ha1_1_1_eq (j : Fin 7) : ha1_1_1 j = ((ha1_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_2 j i k)
lemma ha1_1_2_eq (j : Fin 7) : ha1_1_2 j = ((ha1_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_3 j i k)
lemma ha1_1_3_eq (j : Fin 7) : ha1_1_3 j = ((ha1_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_4 j i k)
lemma ha1_1_4_eq (j : Fin 7) : ha1_1_4 j = ((ha1_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_5 j i k)
lemma ha1_1_5_eq (j : Fin 7) : ha1_1_5 j = ((ha1_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_6 j i k)
lemma ha1_1_6_eq (j : Fin 7) : ha1_1_6 j = ((ha1_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_7 j i k)
lemma ha1_1_7_eq (j : Fin 7) : ha1_1_7 j = ((ha1_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_8 j i k)
lemma ha1_1_8_eq (j : Fin 7) : ha1_1_8 j = ((ha1_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_9 j i k)
lemma ha1_1_9_eq (j : Fin 7) : ha1_1_9 j = ((ha1_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_10 j i k)
lemma ha1_1_10_eq (j : Fin 7) : ha1_1_10 j = ((ha1_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_11 j i k)
lemma ha1_1_11_eq (j : Fin 7) : ha1_1_11 j = ((ha1_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_12 j i k)
lemma ha1_1_12_eq (j : Fin 7) : ha1_1_12 j = ((ha1_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_13 j i k)
lemma ha1_1_13_eq (j : Fin 7) : ha1_1_13 j = ((ha1_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_14 j i k)
lemma ha1_1_14_eq (j : Fin 7) : ha1_1_14 j = ((ha1_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_15 j i k)
lemma ha1_1_15_eq (j : Fin 7) : ha1_1_15 j = ((ha1_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_16 j i k)
lemma ha1_1_16_eq (j : Fin 7) : ha1_1_16 j = ((ha1_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_17 j i k)
lemma ha1_1_17_eq (j : Fin 7) : ha1_1_17 j = ((ha1_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_18 j i k)
lemma ha1_1_18_eq (j : Fin 7) : ha1_1_18 j = ((ha1_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_19 j i k)
lemma ha1_1_19_eq (j : Fin 7) : ha1_1_19 j = ((ha1_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_20 j i k)
lemma ha1_1_20_eq (j : Fin 7) : ha1_1_20 j = ((ha1_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_21 j i k)
lemma ha1_1_21_eq (j : Fin 7) : ha1_1_21 j = ((ha1_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_22 j i k)
lemma ha1_1_22_eq (j : Fin 7) : ha1_1_22 j = ((ha1_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_23 j i k)
lemma ha1_1_23_eq (j : Fin 7) : ha1_1_23 j = ((ha1_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_24 j i k)
lemma ha1_1_24_eq (j : Fin 7) : ha1_1_24 j = ((ha1_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_25 j i k)
lemma ha1_1_25_eq (j : Fin 7) : ha1_1_25 j = ((ha1_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_26 j i k)
lemma ha1_1_26_eq (j : Fin 7) : ha1_1_26 j = ((ha1_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_27 j i k)
lemma ha1_1_27_eq (j : Fin 7) : ha1_1_27 j = ((ha1_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_28 j i k)
lemma ha1_1_28_eq (j : Fin 7) : ha1_1_28 j = ((ha1_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_29 j i k)
lemma ha1_1_29_eq (j : Fin 7) : ha1_1_29 j = ((ha1_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
noncomputable def hk1_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_30 j i k)
lemma ha1_1_30_eq (j : Fin 7) : ha1_1_30 j = ((ha1_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders12
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha12_0_0_eq (j : Fin 7) : ha12_0_0 j = ((atomPoints j).direct.powBin 7 12).conj := by fin_cases j <;> decide +kernel
lemma ha12_0_1_eq (j : Fin 7) : ha12_0_1 j = ((ha12_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha12_0_2_eq (j : Fin 7) : ha12_0_2 j = ((ha12_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha12_0_3_eq (j : Fin 7) : ha12_0_3 j = ((ha12_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha12_0_4_eq (j : Fin 7) : ha12_0_4 j = ((ha12_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha12_0_5_eq (j : Fin 7) : ha12_0_5 j = ((ha12_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha12_0_6_eq (j : Fin 7) : ha12_0_6 j = ((ha12_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha12_0_7_eq (j : Fin 7) : ha12_0_7 j = ((ha12_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha12_0_8_eq (j : Fin 7) : ha12_0_8 j = ((ha12_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha12_0_9_eq (j : Fin 7) : ha12_0_9 j = ((ha12_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha12_0_10_eq (j : Fin 7) : ha12_0_10 j = ((ha12_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha12_0_11_eq (j : Fin 7) : ha12_0_11 j = ((ha12_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha12_0_12_eq (j : Fin 7) : ha12_0_12 j = ((ha12_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha12_0_13_eq (j : Fin 7) : ha12_0_13 j = ((ha12_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha12_1_1_eq (j : Fin 7) : ha12_1_1 j = ((ha12_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha12_1_2_eq (j : Fin 7) : ha12_1_2 j = ((ha12_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha12_1_3_eq (j : Fin 7) : ha12_1_3 j = ((ha12_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha12_1_4_eq (j : Fin 7) : ha12_1_4 j = ((ha12_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha12_1_5_eq (j : Fin 7) : ha12_1_5 j = ((ha12_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha12_1_6_eq (j : Fin 7) : ha12_1_6 j = ((ha12_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha12_1_7_eq (j : Fin 7) : ha12_1_7 j = ((ha12_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha12_1_8_eq (j : Fin 7) : ha12_1_8 j = ((ha12_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha12_1_9_eq (j : Fin 7) : ha12_1_9 j = ((ha12_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha12_1_10_eq (j : Fin 7) : ha12_1_10 j = ((ha12_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha12_1_11_eq (j : Fin 7) : ha12_1_11 j = ((ha12_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha12_1_12_eq (j : Fin 7) : ha12_1_12 j = ((ha12_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha12_1_13_eq (j : Fin 7) : ha12_1_13 j = ((ha12_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders13
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha13_0_0_eq (j : Fin 7) : ha13_0_0 j = ((atomPoints j).direct.powBin 7 13).conj := by fin_cases j <;> decide +kernel
lemma ha13_0_1_eq (j : Fin 7) : ha13_0_1 j = ((ha13_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha13_0_2_eq (j : Fin 7) : ha13_0_2 j = ((ha13_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha13_0_3_eq (j : Fin 7) : ha13_0_3 j = ((ha13_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha13_0_4_eq (j : Fin 7) : ha13_0_4 j = ((ha13_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha13_0_5_eq (j : Fin 7) : ha13_0_5 j = ((ha13_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha13_0_6_eq (j : Fin 7) : ha13_0_6 j = ((ha13_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha13_0_7_eq (j : Fin 7) : ha13_0_7 j = ((ha13_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha13_0_8_eq (j : Fin 7) : ha13_0_8 j = ((ha13_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha13_0_9_eq (j : Fin 7) : ha13_0_9 j = ((ha13_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha13_0_10_eq (j : Fin 7) : ha13_0_10 j = ((ha13_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha13_0_11_eq (j : Fin 7) : ha13_0_11 j = ((ha13_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha13_0_12_eq (j : Fin 7) : ha13_0_12 j = ((ha13_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha13_1_1_eq (j : Fin 7) : ha13_1_1 j = ((ha13_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha13_1_2_eq (j : Fin 7) : ha13_1_2 j = ((ha13_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha13_1_3_eq (j : Fin 7) : ha13_1_3 j = ((ha13_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha13_1_4_eq (j : Fin 7) : ha13_1_4 j = ((ha13_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha13_1_5_eq (j : Fin 7) : ha13_1_5 j = ((ha13_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha13_1_6_eq (j : Fin 7) : ha13_1_6 j = ((ha13_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha13_1_7_eq (j : Fin 7) : ha13_1_7 j = ((ha13_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha13_1_8_eq (j : Fin 7) : ha13_1_8 j = ((ha13_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha13_1_9_eq (j : Fin 7) : ha13_1_9 j = ((ha13_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha13_1_10_eq (j : Fin 7) : ha13_1_10 j = ((ha13_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha13_1_11_eq (j : Fin 7) : ha13_1_11 j = ((ha13_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha13_1_12_eq (j : Fin 7) : ha13_1_12 j = ((ha13_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders15
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha15_0_0_eq (j : Fin 7) : ha15_0_0 j = ((atomPoints j).direct.powBin 7 15).conj := by fin_cases j <;> decide +kernel
lemma ha15_0_1_eq (j : Fin 7) : ha15_0_1 j = ((ha15_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha15_0_2_eq (j : Fin 7) : ha15_0_2 j = ((ha15_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha15_0_3_eq (j : Fin 7) : ha15_0_3 j = ((ha15_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha15_0_4_eq (j : Fin 7) : ha15_0_4 j = ((ha15_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha15_0_5_eq (j : Fin 7) : ha15_0_5 j = ((ha15_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk15_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_6 j i k)
lemma ha15_0_6_eq (j : Fin 7) : ha15_0_6 j = ((ha15_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk15_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_7 j i k)
lemma ha15_0_7_eq (j : Fin 7) : ha15_0_7 j = ((ha15_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk15_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_8 j i k)
lemma ha15_0_8_eq (j : Fin 7) : ha15_0_8 j = ((ha15_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk15_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_9 j i k)
lemma ha15_0_9_eq (j : Fin 7) : ha15_0_9 j = ((ha15_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha15_0_10_eq (j : Fin 7) : ha15_0_10 j = ((ha15_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha15_0_11_eq (j : Fin 7) : ha15_0_11 j = ((ha15_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha15_0_12_eq (j : Fin 7) : ha15_0_12 j = ((ha15_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha15_1_1_eq (j : Fin 7) : ha15_1_1 j = ((ha15_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha15_1_2_eq (j : Fin 7) : ha15_1_2 j = ((ha15_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha15_1_3_eq (j : Fin 7) : ha15_1_3 j = ((ha15_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha15_1_4_eq (j : Fin 7) : ha15_1_4 j = ((ha15_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha15_1_5_eq (j : Fin 7) : ha15_1_5 j = ((ha15_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha15_1_6_eq (j : Fin 7) : ha15_1_6 j = ((ha15_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha15_1_7_eq (j : Fin 7) : ha15_1_7 j = ((ha15_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha15_1_8_eq (j : Fin 7) : ha15_1_8 j = ((ha15_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha15_1_9_eq (j : Fin 7) : ha15_1_9 j = ((ha15_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha15_1_10_eq (j : Fin 7) : ha15_1_10 j = ((ha15_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha15_1_11_eq (j : Fin 7) : ha15_1_11 j = ((ha15_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha15_1_12_eq (j : Fin 7) : ha15_1_12 j = ((ha15_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders16
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha16_0_0_eq (j : Fin 7) : ha16_0_0 j = ((atomPoints j).direct.powBin 7 16).conj := by fin_cases j <;> decide +kernel
lemma ha16_0_1_eq (j : Fin 7) : ha16_0_1 j = ((ha16_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha16_0_2_eq (j : Fin 7) : ha16_0_2 j = ((ha16_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha16_0_3_eq (j : Fin 7) : ha16_0_3 j = ((ha16_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha16_0_4_eq (j : Fin 7) : ha16_0_4 j = ((ha16_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha16_0_5_eq (j : Fin 7) : ha16_0_5 j = ((ha16_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha16_0_6_eq (j : Fin 7) : ha16_0_6 j = ((ha16_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha16_0_7_eq (j : Fin 7) : ha16_0_7 j = ((ha16_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha16_0_8_eq (j : Fin 7) : ha16_0_8 j = ((ha16_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha16_0_9_eq (j : Fin 7) : ha16_0_9 j = ((ha16_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha16_0_10_eq (j : Fin 7) : ha16_0_10 j = ((ha16_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha16_0_11_eq (j : Fin 7) : ha16_0_11 j = ((ha16_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha16_0_12_eq (j : Fin 7) : ha16_0_12 j = ((ha16_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha16_0_13_eq (j : Fin 7) : ha16_0_13 j = ((ha16_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha16_1_1_eq (j : Fin 7) : ha16_1_1 j = ((ha16_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha16_1_2_eq (j : Fin 7) : ha16_1_2 j = ((ha16_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha16_1_3_eq (j : Fin 7) : ha16_1_3 j = ((ha16_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha16_1_4_eq (j : Fin 7) : ha16_1_4 j = ((ha16_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha16_1_5_eq (j : Fin 7) : ha16_1_5 j = ((ha16_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha16_1_6_eq (j : Fin 7) : ha16_1_6 j = ((ha16_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha16_1_7_eq (j : Fin 7) : ha16_1_7 j = ((ha16_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha16_1_8_eq (j : Fin 7) : ha16_1_8 j = ((ha16_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha16_1_9_eq (j : Fin 7) : ha16_1_9 j = ((ha16_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha16_1_10_eq (j : Fin 7) : ha16_1_10 j = ((ha16_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha16_1_11_eq (j : Fin 7) : ha16_1_11 j = ((ha16_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha16_1_12_eq (j : Fin 7) : ha16_1_12 j = ((ha16_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha16_1_13_eq (j : Fin 7) : ha16_1_13 j = ((ha16_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders19
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha19_0_0_eq (j : Fin 7) : ha19_0_0 j = ((atomPoints j).direct.powBin 7 19).conj := by fin_cases j <;> decide +kernel
lemma ha19_0_1_eq (j : Fin 7) : ha19_0_1 j = ((ha19_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha19_0_2_eq (j : Fin 7) : ha19_0_2 j = ((ha19_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha19_0_3_eq (j : Fin 7) : ha19_0_3 j = ((ha19_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha19_0_4_eq (j : Fin 7) : ha19_0_4 j = ((ha19_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha19_0_5_eq (j : Fin 7) : ha19_0_5 j = ((ha19_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha19_0_6_eq (j : Fin 7) : ha19_0_6 j = ((ha19_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha19_0_7_eq (j : Fin 7) : ha19_0_7 j = ((ha19_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha19_0_8_eq (j : Fin 7) : ha19_0_8 j = ((ha19_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha19_0_9_eq (j : Fin 7) : ha19_0_9 j = ((ha19_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha19_0_10_eq (j : Fin 7) : ha19_0_10 j = ((ha19_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha19_0_11_eq (j : Fin 7) : ha19_0_11 j = ((ha19_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha19_0_12_eq (j : Fin 7) : ha19_0_12 j = ((ha19_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha19_0_13_eq (j : Fin 7) : ha19_0_13 j = ((ha19_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha19_1_1_eq (j : Fin 7) : ha19_1_1 j = ((ha19_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha19_1_2_eq (j : Fin 7) : ha19_1_2 j = ((ha19_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha19_1_3_eq (j : Fin 7) : ha19_1_3 j = ((ha19_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha19_1_4_eq (j : Fin 7) : ha19_1_4 j = ((ha19_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha19_1_5_eq (j : Fin 7) : ha19_1_5 j = ((ha19_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha19_1_6_eq (j : Fin 7) : ha19_1_6 j = ((ha19_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha19_1_7_eq (j : Fin 7) : ha19_1_7 j = ((ha19_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha19_1_8_eq (j : Fin 7) : ha19_1_8 j = ((ha19_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha19_1_9_eq (j : Fin 7) : ha19_1_9 j = ((ha19_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha19_1_10_eq (j : Fin 7) : ha19_1_10 j = ((ha19_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha19_1_11_eq (j : Fin 7) : ha19_1_11 j = ((ha19_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha19_1_12_eq (j : Fin 7) : ha19_1_12 j = ((ha19_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha19_1_13_eq (j : Fin 7) : ha19_1_13 j = ((ha19_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders21
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha21_0_0_eq (j : Fin 7) : ha21_0_0 j = ((atomPoints j).direct.powBin 7 21).conj := by fin_cases j <;> decide +kernel
lemma ha21_0_1_eq (j : Fin 7) : ha21_0_1 j = ((ha21_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_2 j i k)
lemma ha21_0_2_eq (j : Fin 7) : ha21_0_2 j = ((ha21_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_3 j i k)
lemma ha21_0_3_eq (j : Fin 7) : ha21_0_3 j = ((ha21_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_4 j i k)
lemma ha21_0_4_eq (j : Fin 7) : ha21_0_4 j = ((ha21_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_5 j i k)
lemma ha21_0_5_eq (j : Fin 7) : ha21_0_5 j = ((ha21_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_6 j i k)
lemma ha21_0_6_eq (j : Fin 7) : ha21_0_6 j = ((ha21_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_7 j i k)
lemma ha21_0_7_eq (j : Fin 7) : ha21_0_7 j = ((ha21_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_8 j i k)
lemma ha21_0_8_eq (j : Fin 7) : ha21_0_8 j = ((ha21_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_9 j i k)
lemma ha21_0_9_eq (j : Fin 7) : ha21_0_9 j = ((ha21_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_10 j i k)
lemma ha21_0_10_eq (j : Fin 7) : ha21_0_10 j = ((ha21_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_11 j i k)
lemma ha21_0_11_eq (j : Fin 7) : ha21_0_11 j = ((ha21_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_12 j i k)
lemma ha21_0_12_eq (j : Fin 7) : ha21_0_12 j = ((ha21_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk21_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_13 j i k)
lemma ha21_0_13_eq (j : Fin 7) : ha21_0_13 j = ((ha21_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha21_1_1_eq (j : Fin 7) : ha21_1_1 j = ((ha21_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha21_1_2_eq (j : Fin 7) : ha21_1_2 j = ((ha21_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha21_1_3_eq (j : Fin 7) : ha21_1_3 j = ((ha21_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha21_1_4_eq (j : Fin 7) : ha21_1_4 j = ((ha21_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha21_1_5_eq (j : Fin 7) : ha21_1_5 j = ((ha21_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha21_1_6_eq (j : Fin 7) : ha21_1_6 j = ((ha21_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha21_1_7_eq (j : Fin 7) : ha21_1_7 j = ((ha21_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha21_1_8_eq (j : Fin 7) : ha21_1_8 j = ((ha21_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha21_1_9_eq (j : Fin 7) : ha21_1_9 j = ((ha21_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha21_1_10_eq (j : Fin 7) : ha21_1_10 j = ((ha21_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha21_1_11_eq (j : Fin 7) : ha21_1_11 j = ((ha21_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders24
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha24_0_0_eq (j : Fin 7) : ha24_0_0 j = ((atomPoints j).direct.powBin 7 24).conj := by fin_cases j <;> decide +kernel
lemma ha24_0_1_eq (j : Fin 7) : ha24_0_1 j = ((ha24_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_2 j i k)
lemma ha24_0_2_eq (j : Fin 7) : ha24_0_2 j = ((ha24_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_3 j i k)
lemma ha24_0_3_eq (j : Fin 7) : ha24_0_3 j = ((ha24_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_4 j i k)
lemma ha24_0_4_eq (j : Fin 7) : ha24_0_4 j = ((ha24_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_5 j i k)
lemma ha24_0_5_eq (j : Fin 7) : ha24_0_5 j = ((ha24_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_6 j i k)
lemma ha24_0_6_eq (j : Fin 7) : ha24_0_6 j = ((ha24_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_7 j i k)
lemma ha24_0_7_eq (j : Fin 7) : ha24_0_7 j = ((ha24_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_8 j i k)
lemma ha24_0_8_eq (j : Fin 7) : ha24_0_8 j = ((ha24_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_9 j i k)
lemma ha24_0_9_eq (j : Fin 7) : ha24_0_9 j = ((ha24_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_10 j i k)
lemma ha24_0_10_eq (j : Fin 7) : ha24_0_10 j = ((ha24_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_11 j i k)
lemma ha24_0_11_eq (j : Fin 7) : ha24_0_11 j = ((ha24_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_12 j i k)
lemma ha24_0_12_eq (j : Fin 7) : ha24_0_12 j = ((ha24_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk24_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_13 j i k)
lemma ha24_0_13_eq (j : Fin 7) : ha24_0_13 j = ((ha24_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha24_1_1_eq (j : Fin 7) : ha24_1_1 j = ((ha24_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha24_1_2_eq (j : Fin 7) : ha24_1_2 j = ((ha24_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha24_1_3_eq (j : Fin 7) : ha24_1_3 j = ((ha24_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha24_1_4_eq (j : Fin 7) : ha24_1_4 j = ((ha24_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha24_1_5_eq (j : Fin 7) : ha24_1_5 j = ((ha24_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha24_1_6_eq (j : Fin 7) : ha24_1_6 j = ((ha24_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha24_1_7_eq (j : Fin 7) : ha24_1_7 j = ((ha24_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha24_1_8_eq (j : Fin 7) : ha24_1_8 j = ((ha24_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha24_1_9_eq (j : Fin 7) : ha24_1_9 j = ((ha24_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha24_1_10_eq (j : Fin 7) : ha24_1_10 j = ((ha24_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha24_1_11_eq (j : Fin 7) : ha24_1_11 j = ((ha24_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders25
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha25_0_0_eq (j : Fin 7) : ha25_0_0 j = ((atomPoints j).direct.powBin 7 25).conj := by fin_cases j <;> decide +kernel
lemma ha25_0_1_eq (j : Fin 7) : ha25_0_1 j = ((ha25_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha25_0_2_eq (j : Fin 7) : ha25_0_2 j = ((ha25_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha25_0_3_eq (j : Fin 7) : ha25_0_3 j = ((ha25_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha25_0_4_eq (j : Fin 7) : ha25_0_4 j = ((ha25_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha25_0_5_eq (j : Fin 7) : ha25_0_5 j = ((ha25_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha25_0_6_eq (j : Fin 7) : ha25_0_6 j = ((ha25_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha25_0_7_eq (j : Fin 7) : ha25_0_7 j = ((ha25_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha25_0_8_eq (j : Fin 7) : ha25_0_8 j = ((ha25_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha25_0_9_eq (j : Fin 7) : ha25_0_9 j = ((ha25_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha25_0_10_eq (j : Fin 7) : ha25_0_10 j = ((ha25_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha25_0_11_eq (j : Fin 7) : ha25_0_11 j = ((ha25_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha25_0_12_eq (j : Fin 7) : ha25_0_12 j = ((ha25_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha25_1_1_eq (j : Fin 7) : ha25_1_1 j = ((ha25_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha25_1_2_eq (j : Fin 7) : ha25_1_2 j = ((ha25_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha25_1_3_eq (j : Fin 7) : ha25_1_3 j = ((ha25_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha25_1_4_eq (j : Fin 7) : ha25_1_4 j = ((ha25_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha25_1_5_eq (j : Fin 7) : ha25_1_5 j = ((ha25_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha25_1_6_eq (j : Fin 7) : ha25_1_6 j = ((ha25_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha25_1_7_eq (j : Fin 7) : ha25_1_7 j = ((ha25_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha25_1_8_eq (j : Fin 7) : ha25_1_8 j = ((ha25_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha25_1_9_eq (j : Fin 7) : ha25_1_9 j = ((ha25_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders27
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha27_0_0_eq (j : Fin 7) : ha27_0_0 j = ((atomPoints j).direct.powBin 7 27).conj := by fin_cases j <;> decide +kernel
lemma ha27_0_1_eq (j : Fin 7) : ha27_0_1 j = ((ha27_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_2 j i k)
lemma ha27_0_2_eq (j : Fin 7) : ha27_0_2 j = ((ha27_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_3 j i k)
lemma ha27_0_3_eq (j : Fin 7) : ha27_0_3 j = ((ha27_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_4 j i k)
lemma ha27_0_4_eq (j : Fin 7) : ha27_0_4 j = ((ha27_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_5 j i k)
lemma ha27_0_5_eq (j : Fin 7) : ha27_0_5 j = ((ha27_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_6 j i k)
lemma ha27_0_6_eq (j : Fin 7) : ha27_0_6 j = ((ha27_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_7 j i k)
lemma ha27_0_7_eq (j : Fin 7) : ha27_0_7 j = ((ha27_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_8 j i k)
lemma ha27_0_8_eq (j : Fin 7) : ha27_0_8 j = ((ha27_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_9 j i k)
lemma ha27_0_9_eq (j : Fin 7) : ha27_0_9 j = ((ha27_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_10 j i k)
lemma ha27_0_10_eq (j : Fin 7) : ha27_0_10 j = ((ha27_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_11 j i k)
lemma ha27_0_11_eq (j : Fin 7) : ha27_0_11 j = ((ha27_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk27_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_12 j i k)
lemma ha27_0_12_eq (j : Fin 7) : ha27_0_12 j = ((ha27_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha27_1_1_eq (j : Fin 7) : ha27_1_1 j = ((ha27_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha27_1_2_eq (j : Fin 7) : ha27_1_2 j = ((ha27_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha27_1_3_eq (j : Fin 7) : ha27_1_3 j = ((ha27_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha27_1_4_eq (j : Fin 7) : ha27_1_4 j = ((ha27_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha27_1_5_eq (j : Fin 7) : ha27_1_5 j = ((ha27_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha27_1_6_eq (j : Fin 7) : ha27_1_6 j = ((ha27_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha27_1_7_eq (j : Fin 7) : ha27_1_7 j = ((ha27_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha27_1_8_eq (j : Fin 7) : ha27_1_8 j = ((ha27_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha27_1_9_eq (j : Fin 7) : ha27_1_9 j = ((ha27_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders28
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha28_0_0_eq (j : Fin 7) : ha28_0_0 j = ((atomPoints j).direct.powBin 7 28).conj := by fin_cases j <;> decide +kernel
lemma ha28_0_1_eq (j : Fin 7) : ha28_0_1 j = ((ha28_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha28_0_2_eq (j : Fin 7) : ha28_0_2 j = ((ha28_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha28_0_3_eq (j : Fin 7) : ha28_0_3 j = ((ha28_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha28_0_4_eq (j : Fin 7) : ha28_0_4 j = ((ha28_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha28_0_5_eq (j : Fin 7) : ha28_0_5 j = ((ha28_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha28_0_6_eq (j : Fin 7) : ha28_0_6 j = ((ha28_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_0_7_eq (j : Fin 7) : ha28_0_7 j = ((ha28_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha28_0_8_eq (j : Fin 7) : ha28_0_8 j = ((ha28_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha28_0_9_eq (j : Fin 7) : ha28_0_9 j = ((ha28_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha28_0_10_eq (j : Fin 7) : ha28_0_10 j = ((ha28_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha28_0_11_eq (j : Fin 7) : ha28_0_11 j = ((ha28_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha28_0_12_eq (j : Fin 7) : ha28_0_12 j = ((ha28_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha28_0_13_eq (j : Fin 7) : ha28_0_13 j = ((ha28_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha28_1_1_eq (j : Fin 7) : ha28_1_1 j = ((ha28_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha28_1_2_eq (j : Fin 7) : ha28_1_2 j = ((ha28_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha28_1_3_eq (j : Fin 7) : ha28_1_3 j = ((ha28_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha28_1_4_eq (j : Fin 7) : ha28_1_4 j = ((ha28_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha28_1_5_eq (j : Fin 7) : ha28_1_5 j = ((ha28_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha28_1_6_eq (j : Fin 7) : ha28_1_6 j = ((ha28_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_1_7_eq (j : Fin 7) : ha28_1_7 j = ((ha28_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha28_1_8_eq (j : Fin 7) : ha28_1_8 j = ((ha28_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha28_1_9_eq (j : Fin 7) : ha28_1_9 j = ((ha28_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders3
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha3_0_0_eq (j : Fin 7) : ha3_0_0 j = ((atomPoints j).direct.powBin 7 3).conj := by fin_cases j <;> decide +kernel
lemma ha3_0_1_eq (j : Fin 7) : ha3_0_1 j = ((ha3_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha3_0_2_eq (j : Fin 7) : ha3_0_2 j = ((ha3_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha3_0_3_eq (j : Fin 7) : ha3_0_3 j = ((ha3_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha3_0_4_eq (j : Fin 7) : ha3_0_4 j = ((ha3_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha3_0_5_eq (j : Fin 7) : ha3_0_5 j = ((ha3_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha3_0_6_eq (j : Fin 7) : ha3_0_6 j = ((ha3_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha3_0_7_eq (j : Fin 7) : ha3_0_7 j = ((ha3_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha3_0_8_eq (j : Fin 7) : ha3_0_8 j = ((ha3_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha3_0_9_eq (j : Fin 7) : ha3_0_9 j = ((ha3_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha3_0_10_eq (j : Fin 7) : ha3_0_10 j = ((ha3_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha3_0_11_eq (j : Fin 7) : ha3_0_11 j = ((ha3_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha3_0_12_eq (j : Fin 7) : ha3_0_12 j = ((ha3_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha3_0_13_eq (j : Fin 7) : ha3_0_13 j = ((ha3_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha3_1_1_eq (j : Fin 7) : ha3_1_1 j = ((ha3_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha3_1_2_eq (j : Fin 7) : ha3_1_2 j = ((ha3_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha3_1_3_eq (j : Fin 7) : ha3_1_3 j = ((ha3_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha3_1_4_eq (j : Fin 7) : ha3_1_4 j = ((ha3_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha3_1_5_eq (j : Fin 7) : ha3_1_5 j = ((ha3_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha3_1_6_eq (j : Fin 7) : ha3_1_6 j = ((ha3_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha3_1_7_eq (j : Fin 7) : ha3_1_7 j = ((ha3_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha3_1_8_eq (j : Fin 7) : ha3_1_8 j = ((ha3_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha3_1_9_eq (j : Fin 7) : ha3_1_9 j = ((ha3_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha3_1_10_eq (j : Fin 7) : ha3_1_10 j = ((ha3_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha3_1_11_eq (j : Fin 7) : ha3_1_11 j = ((ha3_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha3_1_12_eq (j : Fin 7) : ha3_1_12 j = ((ha3_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha3_1_13_eq (j : Fin 7) : ha3_1_13 j = ((ha3_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders31
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha31_0_0_eq (j : Fin 7) : ha31_0_0 j = ((atomPoints j).direct.powBin 7 31).conj := by fin_cases j <;> decide +kernel
lemma ha31_0_1_eq (j : Fin 7) : ha31_0_1 j = ((ha31_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha31_0_2_eq (j : Fin 7) : ha31_0_2 j = ((ha31_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha31_0_3_eq (j : Fin 7) : ha31_0_3 j = ((ha31_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_0_4_eq (j : Fin 7) : ha31_0_4 j = ((ha31_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha31_0_5_eq (j : Fin 7) : ha31_0_5 j = ((ha31_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha31_0_6_eq (j : Fin 7) : ha31_0_6 j = ((ha31_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha31_0_7_eq (j : Fin 7) : ha31_0_7 j = ((ha31_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha31_0_8_eq (j : Fin 7) : ha31_0_8 j = ((ha31_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha31_0_9_eq (j : Fin 7) : ha31_0_9 j = ((ha31_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha31_0_10_eq (j : Fin 7) : ha31_0_10 j = ((ha31_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha31_0_11_eq (j : Fin 7) : ha31_0_11 j = ((ha31_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha31_0_12_eq (j : Fin 7) : ha31_0_12 j = ((ha31_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha31_0_13_eq (j : Fin 7) : ha31_0_13 j = ((ha31_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha31_1_1_eq (j : Fin 7) : ha31_1_1 j = ((ha31_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha31_1_2_eq (j : Fin 7) : ha31_1_2 j = ((ha31_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha31_1_3_eq (j : Fin 7) : ha31_1_3 j = ((ha31_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_1_4_eq (j : Fin 7) : ha31_1_4 j = ((ha31_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha31_1_5_eq (j : Fin 7) : ha31_1_5 j = ((ha31_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha31_1_6_eq (j : Fin 7) : ha31_1_6 j = ((ha31_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha31_1_7_eq (j : Fin 7) : ha31_1_7 j = ((ha31_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders33
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha33_0_0_eq (j : Fin 7) : ha33_0_0 j = ((atomPoints j).direct.powBin 7 33).conj := by fin_cases j <;> decide +kernel
lemma ha33_0_1_eq (j : Fin 7) : ha33_0_1 j = ((ha33_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha33_0_2_eq (j : Fin 7) : ha33_0_2 j = ((ha33_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha33_0_3_eq (j : Fin 7) : ha33_0_3 j = ((ha33_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha33_0_4_eq (j : Fin 7) : ha33_0_4 j = ((ha33_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha33_0_5_eq (j : Fin 7) : ha33_0_5 j = ((ha33_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha33_0_6_eq (j : Fin 7) : ha33_0_6 j = ((ha33_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha33_0_7_eq (j : Fin 7) : ha33_0_7 j = ((ha33_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha33_0_8_eq (j : Fin 7) : ha33_0_8 j = ((ha33_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha33_0_9_eq (j : Fin 7) : ha33_0_9 j = ((ha33_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha33_0_10_eq (j : Fin 7) : ha33_0_10 j = ((ha33_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha33_0_11_eq (j : Fin 7) : ha33_0_11 j = ((ha33_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha33_0_12_eq (j : Fin 7) : ha33_0_12 j = ((ha33_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha33_0_13_eq (j : Fin 7) : ha33_0_13 j = ((ha33_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha33_1_1_eq (j : Fin 7) : ha33_1_1 j = ((ha33_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha33_1_2_eq (j : Fin 7) : ha33_1_2 j = ((ha33_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha33_1_3_eq (j : Fin 7) : ha33_1_3 j = ((ha33_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha33_1_4_eq (j : Fin 7) : ha33_1_4 j = ((ha33_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha33_1_5_eq (j : Fin 7) : ha33_1_5 j = ((ha33_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha33_1_6_eq (j : Fin 7) : ha33_1_6 j = ((ha33_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha33_1_7_eq (j : Fin 7) : ha33_1_7 j = ((ha33_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders36
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha36_0_0_eq (j : Fin 7) : ha36_0_0 j = ((atomPoints j).direct.powBin 7 36).conj := by fin_cases j <;> decide +kernel
lemma ha36_0_1_eq (j : Fin 7) : ha36_0_1 j = ((ha36_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha36_0_2_eq (j : Fin 7) : ha36_0_2 j = ((ha36_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha36_0_3_eq (j : Fin 7) : ha36_0_3 j = ((ha36_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha36_0_4_eq (j : Fin 7) : ha36_0_4 j = ((ha36_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha36_0_5_eq (j : Fin 7) : ha36_0_5 j = ((ha36_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha36_0_6_eq (j : Fin 7) : ha36_0_6 j = ((ha36_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha36_0_7_eq (j : Fin 7) : ha36_0_7 j = ((ha36_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha36_0_8_eq (j : Fin 7) : ha36_0_8 j = ((ha36_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha36_0_9_eq (j : Fin 7) : ha36_0_9 j = ((ha36_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha36_0_10_eq (j : Fin 7) : ha36_0_10 j = ((ha36_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha36_0_11_eq (j : Fin 7) : ha36_0_11 j = ((ha36_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha36_0_12_eq (j : Fin 7) : ha36_0_12 j = ((ha36_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha36_0_13_eq (j : Fin 7) : ha36_0_13 j = ((ha36_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha36_1_1_eq (j : Fin 7) : ha36_1_1 j = ((ha36_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha36_1_2_eq (j : Fin 7) : ha36_1_2 j = ((ha36_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha36_1_3_eq (j : Fin 7) : ha36_1_3 j = ((ha36_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha36_1_4_eq (j : Fin 7) : ha36_1_4 j = ((ha36_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha36_1_5_eq (j : Fin 7) : ha36_1_5 j = ((ha36_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders37
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha37_0_0_eq (j : Fin 7) : ha37_0_0 j = ((atomPoints j).direct.powBin 7 37).conj := by fin_cases j <;> decide +kernel
lemma ha37_0_1_eq (j : Fin 7) : ha37_0_1 j = ((ha37_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha37_0_2_eq (j : Fin 7) : ha37_0_2 j = ((ha37_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha37_0_3_eq (j : Fin 7) : ha37_0_3 j = ((ha37_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha37_0_4_eq (j : Fin 7) : ha37_0_4 j = ((ha37_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha37_0_5_eq (j : Fin 7) : ha37_0_5 j = ((ha37_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha37_0_6_eq (j : Fin 7) : ha37_0_6 j = ((ha37_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha37_0_7_eq (j : Fin 7) : ha37_0_7 j = ((ha37_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha37_0_8_eq (j : Fin 7) : ha37_0_8 j = ((ha37_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha37_0_9_eq (j : Fin 7) : ha37_0_9 j = ((ha37_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha37_0_10_eq (j : Fin 7) : ha37_0_10 j = ((ha37_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha37_0_11_eq (j : Fin 7) : ha37_0_11 j = ((ha37_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha37_0_12_eq (j : Fin 7) : ha37_0_12 j = ((ha37_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha37_1_1_eq (j : Fin 7) : ha37_1_1 j = ((ha37_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha37_1_2_eq (j : Fin 7) : ha37_1_2 j = ((ha37_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha37_1_3_eq (j : Fin 7) : ha37_1_3 j = ((ha37_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha37_1_4_eq (j : Fin 7) : ha37_1_4 j = ((ha37_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha37_1_5_eq (j : Fin 7) : ha37_1_5 j = ((ha37_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders39
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha39_0_0_eq (j : Fin 7) : ha39_0_0 j = ((atomPoints j).direct.powBin 7 39).conj := by fin_cases j <;> decide +kernel
lemma ha39_0_1_eq (j : Fin 7) : ha39_0_1 j = ((ha39_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha39_0_2_eq (j : Fin 7) : ha39_0_2 j = ((ha39_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha39_0_3_eq (j : Fin 7) : ha39_0_3 j = ((ha39_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha39_0_4_eq (j : Fin 7) : ha39_0_4 j = ((ha39_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha39_0_5_eq (j : Fin 7) : ha39_0_5 j = ((ha39_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha39_0_6_eq (j : Fin 7) : ha39_0_6 j = ((ha39_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha39_0_7_eq (j : Fin 7) : ha39_0_7 j = ((ha39_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha39_0_8_eq (j : Fin 7) : ha39_0_8 j = ((ha39_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha39_0_9_eq (j : Fin 7) : ha39_0_9 j = ((ha39_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha39_0_10_eq (j : Fin 7) : ha39_0_10 j = ((ha39_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha39_0_11_eq (j : Fin 7) : ha39_0_11 j = ((ha39_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha39_0_12_eq (j : Fin 7) : ha39_0_12 j = ((ha39_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha39_1_1_eq (j : Fin 7) : ha39_1_1 j = ((ha39_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha39_1_2_eq (j : Fin 7) : ha39_1_2 j = ((ha39_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha39_1_3_eq (j : Fin 7) : ha39_1_3 j = ((ha39_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha39_1_4_eq (j : Fin 7) : ha39_1_4 j = ((ha39_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha39_1_5_eq (j : Fin 7) : ha39_1_5 j = ((ha39_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders4
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha4_0_0_eq (j : Fin 7) : ha4_0_0 j = ((atomPoints j).direct.powBin 7 4).conj := by fin_cases j <;> decide +kernel
lemma ha4_0_1_eq (j : Fin 7) : ha4_0_1 j = ((ha4_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_2 j i k)
lemma ha4_0_2_eq (j : Fin 7) : ha4_0_2 j = ((ha4_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_3 j i k)
lemma ha4_0_3_eq (j : Fin 7) : ha4_0_3 j = ((ha4_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_4 j i k)
lemma ha4_0_4_eq (j : Fin 7) : ha4_0_4 j = ((ha4_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_5 j i k)
lemma ha4_0_5_eq (j : Fin 7) : ha4_0_5 j = ((ha4_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_6 j i k)
lemma ha4_0_6_eq (j : Fin 7) : ha4_0_6 j = ((ha4_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_7 j i k)
lemma ha4_0_7_eq (j : Fin 7) : ha4_0_7 j = ((ha4_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_8 j i k)
lemma ha4_0_8_eq (j : Fin 7) : ha4_0_8 j = ((ha4_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_9 j i k)
lemma ha4_0_9_eq (j : Fin 7) : ha4_0_9 j = ((ha4_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_10 j i k)
lemma ha4_0_10_eq (j : Fin 7) : ha4_0_10 j = ((ha4_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_11 j i k)
lemma ha4_0_11_eq (j : Fin 7) : ha4_0_11 j = ((ha4_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_12 j i k)
lemma ha4_0_12_eq (j : Fin 7) : ha4_0_12 j = ((ha4_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_13 j i k)
lemma ha4_0_13_eq (j : Fin 7) : ha4_0_13 j = ((ha4_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_14 j i k)
lemma ha4_0_14_eq (j : Fin 7) : ha4_0_14 j = ((ha4_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_15 j i k)
lemma ha4_0_15_eq (j : Fin 7) : ha4_0_15 j = ((ha4_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_16 j i k)
lemma ha4_0_16_eq (j : Fin 7) : ha4_0_16 j = ((ha4_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_17 j i k)
lemma ha4_0_17_eq (j : Fin 7) : ha4_0_17 j = ((ha4_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_18 j i k)
lemma ha4_0_18_eq (j : Fin 7) : ha4_0_18 j = ((ha4_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
noncomputable def hk4_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_19 j i k)
lemma ha4_0_19_eq (j : Fin 7) : ha4_0_19 j = ((ha4_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha4_1_1_eq (j : Fin 7) : ha4_1_1 j = ((ha4_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_2 j i k)
lemma ha4_1_2_eq (j : Fin 7) : ha4_1_2 j = ((ha4_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_3 j i k)
lemma ha4_1_3_eq (j : Fin 7) : ha4_1_3 j = ((ha4_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_4 j i k)
lemma ha4_1_4_eq (j : Fin 7) : ha4_1_4 j = ((ha4_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_5 j i k)
lemma ha4_1_5_eq (j : Fin 7) : ha4_1_5 j = ((ha4_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_6 j i k)
lemma ha4_1_6_eq (j : Fin 7) : ha4_1_6 j = ((ha4_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_7 j i k)
lemma ha4_1_7_eq (j : Fin 7) : ha4_1_7 j = ((ha4_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_8 j i k)
lemma ha4_1_8_eq (j : Fin 7) : ha4_1_8 j = ((ha4_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_9 j i k)
lemma ha4_1_9_eq (j : Fin 7) : ha4_1_9 j = ((ha4_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_10 j i k)
lemma ha4_1_10_eq (j : Fin 7) : ha4_1_10 j = ((ha4_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_11 j i k)
lemma ha4_1_11_eq (j : Fin 7) : ha4_1_11 j = ((ha4_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_12 j i k)
lemma ha4_1_12_eq (j : Fin 7) : ha4_1_12 j = ((ha4_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_13 j i k)
lemma ha4_1_13_eq (j : Fin 7) : ha4_1_13 j = ((ha4_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_14 j i k)
lemma ha4_1_14_eq (j : Fin 7) : ha4_1_14 j = ((ha4_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_15 j i k)
lemma ha4_1_15_eq (j : Fin 7) : ha4_1_15 j = ((ha4_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_16 j i k)
lemma ha4_1_16_eq (j : Fin 7) : ha4_1_16 j = ((ha4_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_17 j i k)
lemma ha4_1_17_eq (j : Fin 7) : ha4_1_17 j = ((ha4_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_18 j i k)
lemma ha4_1_18_eq (j : Fin 7) : ha4_1_18 j = ((ha4_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
noncomputable def hk4_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_19 j i k)
lemma ha4_1_19_eq (j : Fin 7) : ha4_1_19 j = ((ha4_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders40
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha40_0_0_eq (j : Fin 7) : ha40_0_0 j = ((atomPoints j).direct.powBin 7 40).conj := by fin_cases j <;> decide +kernel
lemma ha40_0_1_eq (j : Fin 7) : ha40_0_1 j = ((ha40_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_2 j i k)
lemma ha40_0_2_eq (j : Fin 7) : ha40_0_2 j = ((ha40_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_3 j i k)
lemma ha40_0_3_eq (j : Fin 7) : ha40_0_3 j = ((ha40_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_4 j i k)
lemma ha40_0_4_eq (j : Fin 7) : ha40_0_4 j = ((ha40_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_5 j i k)
lemma ha40_0_5_eq (j : Fin 7) : ha40_0_5 j = ((ha40_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_6 j i k)
lemma ha40_0_6_eq (j : Fin 7) : ha40_0_6 j = ((ha40_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_7 j i k)
lemma ha40_0_7_eq (j : Fin 7) : ha40_0_7 j = ((ha40_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_8 j i k)
lemma ha40_0_8_eq (j : Fin 7) : ha40_0_8 j = ((ha40_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_9 j i k)
lemma ha40_0_9_eq (j : Fin 7) : ha40_0_9 j = ((ha40_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_10 j i k)
lemma ha40_0_10_eq (j : Fin 7) : ha40_0_10 j = ((ha40_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_11 j i k)
lemma ha40_0_11_eq (j : Fin 7) : ha40_0_11 j = ((ha40_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_12 j i k)
lemma ha40_0_12_eq (j : Fin 7) : ha40_0_12 j = ((ha40_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk40_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_13 j i k)
lemma ha40_0_13_eq (j : Fin 7) : ha40_0_13 j = ((ha40_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha40_1_1_eq (j : Fin 7) : ha40_1_1 j = ((ha40_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha40_1_2_eq (j : Fin 7) : ha40_1_2 j = ((ha40_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha40_1_3_eq (j : Fin 7) : ha40_1_3 j = ((ha40_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders7
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha7_0_0_eq (j : Fin 7) : ha7_0_0 j = ((atomPoints j).direct.powBin 7 7).conj := by fin_cases j <;> decide +kernel
lemma ha7_0_1_eq (j : Fin 7) : ha7_0_1 j = ((ha7_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_2 j i k)
lemma ha7_0_2_eq (j : Fin 7) : ha7_0_2 j = ((ha7_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_3 j i k)
lemma ha7_0_3_eq (j : Fin 7) : ha7_0_3 j = ((ha7_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_4 j i k)
lemma ha7_0_4_eq (j : Fin 7) : ha7_0_4 j = ((ha7_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_5 j i k)
lemma ha7_0_5_eq (j : Fin 7) : ha7_0_5 j = ((ha7_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_6 j i k)
lemma ha7_0_6_eq (j : Fin 7) : ha7_0_6 j = ((ha7_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_7 j i k)
lemma ha7_0_7_eq (j : Fin 7) : ha7_0_7 j = ((ha7_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_8 j i k)
lemma ha7_0_8_eq (j : Fin 7) : ha7_0_8 j = ((ha7_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_9 j i k)
lemma ha7_0_9_eq (j : Fin 7) : ha7_0_9 j = ((ha7_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_10 j i k)
lemma ha7_0_10_eq (j : Fin 7) : ha7_0_10 j = ((ha7_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_11 j i k)
lemma ha7_0_11_eq (j : Fin 7) : ha7_0_11 j = ((ha7_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_12 j i k)
lemma ha7_0_12_eq (j : Fin 7) : ha7_0_12 j = ((ha7_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_13 j i k)
lemma ha7_0_13_eq (j : Fin 7) : ha7_0_13 j = ((ha7_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_14 j i k)
lemma ha7_0_14_eq (j : Fin 7) : ha7_0_14 j = ((ha7_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
noncomputable def hk7_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_15 j i k)
lemma ha7_0_15_eq (j : Fin 7) : ha7_0_15 j = ((ha7_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha7_1_1_eq (j : Fin 7) : ha7_1_1 j = ((ha7_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_2 j i k)
lemma ha7_1_2_eq (j : Fin 7) : ha7_1_2 j = ((ha7_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_3 j i k)
lemma ha7_1_3_eq (j : Fin 7) : ha7_1_3 j = ((ha7_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_4 j i k)
lemma ha7_1_4_eq (j : Fin 7) : ha7_1_4 j = ((ha7_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_5 j i k)
lemma ha7_1_5_eq (j : Fin 7) : ha7_1_5 j = ((ha7_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_6 j i k)
lemma ha7_1_6_eq (j : Fin 7) : ha7_1_6 j = ((ha7_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_7 j i k)
lemma ha7_1_7_eq (j : Fin 7) : ha7_1_7 j = ((ha7_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_8 j i k)
lemma ha7_1_8_eq (j : Fin 7) : ha7_1_8 j = ((ha7_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_9 j i k)
lemma ha7_1_9_eq (j : Fin 7) : ha7_1_9 j = ((ha7_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_10 j i k)
lemma ha7_1_10_eq (j : Fin 7) : ha7_1_10 j = ((ha7_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_11 j i k)
lemma ha7_1_11_eq (j : Fin 7) : ha7_1_11 j = ((ha7_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_12 j i k)
lemma ha7_1_12_eq (j : Fin 7) : ha7_1_12 j = ((ha7_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_13 j i k)
lemma ha7_1_13_eq (j : Fin 7) : ha7_1_13 j = ((ha7_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_14 j i k)
lemma ha7_1_14_eq (j : Fin 7) : ha7_1_14 j = ((ha7_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
noncomputable def hk7_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_15 j i k)
lemma ha7_1_15_eq (j : Fin 7) : ha7_1_15 j = ((ha7_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders9
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha9_0_0_eq (j : Fin 7) : ha9_0_0 j = ((atomPoints j).direct.powBin 7 9).conj := by fin_cases j <;> decide +kernel
lemma ha9_0_1_eq (j : Fin 7) : ha9_0_1 j = ((ha9_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_2 j i k)
lemma ha9_0_2_eq (j : Fin 7) : ha9_0_2 j = ((ha9_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_3 j i k)
lemma ha9_0_3_eq (j : Fin 7) : ha9_0_3 j = ((ha9_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_4 j i k)
lemma ha9_0_4_eq (j : Fin 7) : ha9_0_4 j = ((ha9_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_5 j i k)
lemma ha9_0_5_eq (j : Fin 7) : ha9_0_5 j = ((ha9_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_6 j i k)
lemma ha9_0_6_eq (j : Fin 7) : ha9_0_6 j = ((ha9_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_7 j i k)
lemma ha9_0_7_eq (j : Fin 7) : ha9_0_7 j = ((ha9_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_8 j i k)
lemma ha9_0_8_eq (j : Fin 7) : ha9_0_8 j = ((ha9_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_9 j i k)
lemma ha9_0_9_eq (j : Fin 7) : ha9_0_9 j = ((ha9_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_10 j i k)
lemma ha9_0_10_eq (j : Fin 7) : ha9_0_10 j = ((ha9_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_11 j i k)
lemma ha9_0_11_eq (j : Fin 7) : ha9_0_11 j = ((ha9_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_12 j i k)
lemma ha9_0_12_eq (j : Fin 7) : ha9_0_12 j = ((ha9_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_13 j i k)
lemma ha9_0_13_eq (j : Fin 7) : ha9_0_13 j = ((ha9_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_14 j i k)
lemma ha9_0_14_eq (j : Fin 7) : ha9_0_14 j = ((ha9_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
noncomputable def hk9_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_15 j i k)
lemma ha9_0_15_eq (j : Fin 7) : ha9_0_15 j = ((ha9_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha9_1_1_eq (j : Fin 7) : ha9_1_1 j = ((ha9_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha9_1_2_eq (j : Fin 7) : ha9_1_2 j = ((ha9_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha9_1_3_eq (j : Fin 7) : ha9_1_3 j = ((ha9_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha9_1_4_eq (j : Fin 7) : ha9_1_4 j = ((ha9_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha9_1_5_eq (j : Fin 7) : ha9_1_5 j = ((ha9_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha9_1_6_eq (j : Fin 7) : ha9_1_6 j = ((ha9_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha9_1_7_eq (j : Fin 7) : ha9_1_7 j = ((ha9_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha9_1_8_eq (j : Fin 7) : ha9_1_8 j = ((ha9_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha9_1_9_eq (j : Fin 7) : ha9_1_9 j = ((ha9_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha9_1_10_eq (j : Fin 7) : ha9_1_10 j = ((ha9_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha9_1_11_eq (j : Fin 7) : ha9_1_11 j = ((ha9_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha9_1_12_eq (j : Fin 7) : ha9_1_12 j = ((ha9_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha9_1_13_eq (j : Fin 7) : ha9_1_13 j = ((ha9_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha9_1_14_eq (j : Fin 7) : ha9_1_14 j = ((ha9_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha9_1_15_eq (j : Fin 7) : ha9_1_15 j = ((ha9_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_4
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm0_0_1_0
lemma atomChecked : tableAtomBox false ha0_1_0 = atomAnswer := by decide +kernel
end hm0_0_1_0
namespace hm0_0_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_1_1 j i k))
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma atomChecked : tableAtomBox false ha0_1_1 = atomAnswer := by decide +kernel
end hm0_0_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_5
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm0_0_1_10
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_1_10 j i k))
end hm0_0_1_10
namespace hm0_0_1_11
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_1_11 j i k))
end hm0_0_1_11
end SharpPlanar.CachedData

end OAI
end


