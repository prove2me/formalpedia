-- Prove2me | Definitions.Def_OAIQ098D276
-- name    : OAIQ098D276
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T17:36:31.167248+00:00
-- url     : https://prove2.me/theorems/78057141-4483-4d51-a609-f727f19b3074
-- title:
--   Definitions bundle OAIQ098D276 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1416 declarations of OpenAI's Lean: 10 definitions and 1406 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.amp0_0Expr`, `OAI.SharpPlanar.CachedData.power100Expr`, `OAI.SharpPlanar.IntegerBasis.alphaBox`, `OAI.SharpPlanar.IntegerBasis.betaBox`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficientBox`, `OAI.SharpPlanar.IntegerGrid.gridRows`, `OAI.SharpPlanar.IntegerGrid.row2`, `OAI.SharpPlanar.IntegerGrid.row2_12`, `OAI.SharpPlanar.IntegerGrid.row4`, `OAI.SharpPlanar.IntegerGrid.row4_8`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BasisIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean), [`PlanarPacking_Certificate_Amplitudes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean), [`PlanarPacking_Certificate_Powers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers100.lean), [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean), [`PlanarPacking_Grid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean), [`PlanarPacking_Roots`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Roots.lean).
--
--   **Imports.** It imports the bundles `OAIQ098D261`, `OAIQ098D262` and `OAIQ098D263` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D467`, `OAIQ098D468`, `OAIQ098D469`, `OAIQ098D470`, `OAIQ098D471`, `OAIQ098D472`, `OAIQ098D473`, `OAIQ098D474`, `OAIQ098D475`, `OAIQ098D476`, `OAIQ098D478`, `OAIQ098D479`, `OAIQ098D480`, `OAIQ098D482`, `OAIQ098D483`, `OAIQ098D486`, `OAIQ098D487`, `OAIQ098D491`, `OAIQ098D493`, `OAIQ098D494`, `OAIQ098D496`, `OAIQ098D497`, `OAIQ098D498`, `OAIQ098D500`, `OAIQ098D501`, `OAIQ098D502`, `OAIQ098D503`, `OAIQ098D504`, `OAIQ098D506`, `OAIQ098D507`, `OAIQ098D508`, `OAIQ098D510`, `OAIQ098D511`, `OAIQ098D512`, `OAIQ098D513`, `OAIQ098D515`, `OAIQ098D517`, `OAIQ098D521`, `OAIQ098D525`, `OAIQ098D526`, `OAIQ098D527`, `OAIQ098D529`, `OAIQ098D532`, `OAIQ098D533`, `OAIQ098D535`, `OAIQ098D536`, `OAIQ098D538`, `OAIQ098D539`, `OAIQ098D540`, `OAIQ098D542`, `OAIQ098D543`, `OAIQ098D544`, `OAIQ098D549`, `OAIQ098D553`, `OAIQ098D554`, `OAIQ098D555`, `OAIQ098D556`, `OAIQ098D557`, `OAIQ098D559`, `OAIQ098D560`, `OAIQ098D561`, `OAIQ098D563`, `OAIQ098D565`, `OAIQ098D566`, `OAIQ098D571`, `OAIQ098D574`, `OAIQ098D575`, `OAIQ098D577`, `OAIQ098D580`, `OAIQ098D583`, `OAIQ098D586`, `OAIQ098D587`, `OAIQ098D590`, `OAIQ098D591`, `OAIQ098D592`, `OAIQ098D595`, `OAIQ098D596`, `OAIQ098D597`, `OAIQ098D598`, `OAIQ098D599`, `OAIQ098D600`, `OAIQ098D601`, `OAIQ098D602`, `OAIQ098D603`, `OAIQ098D604`, `OAIQ098D605` and `OAIQ098D619`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D261
import Definitions.Def_OAIQ098D262
import Definitions.Def_OAIQ098D263

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
namespace IntegerRoots
open IntegerIntervals
lemma mid7_contains : mid7.Contains (rootPhase 6) := root6_contains
lemma root7_contains : root7.Contains (rootPhase 7) := by
  have hh := CBox.mul_contains mid7_contains root1_contains (c:=root7) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid9_contains : mid9.Contains (rootPhase 8) := root8_contains
lemma root9_contains : root9.Contains (rootPhase 9) := by
  have hh := CBox.mul_contains mid9_contains root1_contains (c:=root9) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid11_contains : mid11.Contains (rootPhase 10) := root10_contains
lemma root11_contains : root11.Contains (rootPhase 11) := by
  have hh := CBox.mul_contains mid11_contains root1_contains (c:=root11) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid13_contains : mid13.Contains (rootPhase 12) := root12_contains
lemma root13_contains : root13.Contains (rootPhase 13) := by
  have hh := CBox.mul_contains mid13_contains root1_contains (c:=root13) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root14_contains : root14.Contains (rootPhase 14) := by
  have hh := CBox.mul_contains root7_contains root7_contains (c:=root14) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid15_contains : mid15.Contains (rootPhase 14) := root14_contains
lemma root15_contains : root15.Contains (rootPhase 15) := by
  have hh := CBox.mul_contains mid15_contains root1_contains (c:=root15) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid17_contains : mid17.Contains (rootPhase 16) := root16_contains
lemma root17_contains : root17.Contains (rootPhase 17) := by
  have hh := CBox.mul_contains mid17_contains root1_contains (c:=root17) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root18_contains : root18.Contains (rootPhase 18) := by
  have hh := CBox.mul_contains root9_contains root9_contains (c:=root18) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid19_contains : mid19.Contains (rootPhase 18) := root18_contains
lemma root19_contains : root19.Contains (rootPhase 19) := by
  have hh := CBox.mul_contains mid19_contains root1_contains (c:=root19) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid21_contains : mid21.Contains (rootPhase 20) := root20_contains
lemma root21_contains : root21.Contains (rootPhase 21) := by
  have hh := CBox.mul_contains mid21_contains root1_contains (c:=root21) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root22_contains : root22.Contains (rootPhase 22) := by
  have hh := CBox.mul_contains root11_contains root11_contains (c:=root22) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid23_contains : mid23.Contains (rootPhase 22) := root22_contains
lemma root23_contains : root23.Contains (rootPhase 23) := by
  have hh := CBox.mul_contains mid23_contains root1_contains (c:=root23) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid25_contains : mid25.Contains (rootPhase 24) := root24_contains
lemma root25_contains : root25.Contains (rootPhase 25) := by
  have hh := CBox.mul_contains mid25_contains root1_contains (c:=root25) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root26_contains : root26.Contains (rootPhase 26) := by
  have hh := CBox.mul_contains root13_contains root13_contains (c:=root26) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid27_contains : mid27.Contains (rootPhase 26) := root26_contains
lemma root27_contains : root27.Contains (rootPhase 27) := by
  have hh := CBox.mul_contains mid27_contains root1_contains (c:=root27) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root28_contains : root28.Contains (rootPhase 28) := by
  have hh := CBox.mul_contains root14_contains root14_contains (c:=root28) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid29_contains : mid29.Contains (rootPhase 28) := root28_contains
lemma root29_contains : root29.Contains (rootPhase 29) := by
  have hh := CBox.mul_contains mid29_contains root1_contains (c:=root29) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root30_contains : root30.Contains (rootPhase 30) := by
  have hh := CBox.mul_contains root15_contains root15_contains (c:=root30) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid31_contains : mid31.Contains (rootPhase 30) := root30_contains
lemma root31_contains : root31.Contains (rootPhase 31) := by
  have hh := CBox.mul_contains mid31_contains root1_contains (c:=root31) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root34_contains : root34.Contains (rootPhase 34) := by
  have hh := CBox.mul_contains root17_contains root17_contains (c:=root34) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid35_contains : mid35.Contains (rootPhase 34) := root34_contains
lemma root35_contains : root35.Contains (rootPhase 35) := by
  have hh := CBox.mul_contains mid35_contains root1_contains (c:=root35) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root36_contains : root36.Contains (rootPhase 36) := by
  have hh := CBox.mul_contains root18_contains root18_contains (c:=root36) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid37_contains : mid37.Contains (rootPhase 36) := root36_contains
lemma root37_contains : root37.Contains (rootPhase 37) := by
  have hh := CBox.mul_contains mid37_contains root1_contains (c:=root37) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root38_contains : root38.Contains (rootPhase 38) := by
  have hh := CBox.mul_contains root19_contains root19_contains (c:=root38) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid39_contains : mid39.Contains (rootPhase 38) := root38_contains
lemma root39_contains : root39.Contains (rootPhase 39) := by
  have hh := CBox.mul_contains mid39_contains root1_contains (c:=root39) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid41_contains : mid41.Contains (rootPhase 40) := root40_contains
lemma root41_contains : root41.Contains (rootPhase 41) := by
  have hh := CBox.mul_contains mid41_contains root1_contains (c:=root41) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root42_contains : root42.Contains (rootPhase 42) := by
  have hh := CBox.mul_contains root21_contains root21_contains (c:=root42) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid43_contains : mid43.Contains (rootPhase 42) := root42_contains
lemma root43_contains : root43.Contains (rootPhase 43) := by
  have hh := CBox.mul_contains mid43_contains root1_contains (c:=root43) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root44_contains : root44.Contains (rootPhase 44) := by
  have hh := CBox.mul_contains root22_contains root22_contains (c:=root44) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid45_contains : mid45.Contains (rootPhase 44) := root44_contains
lemma root45_contains : root45.Contains (rootPhase 45) := by
  have hh := CBox.mul_contains mid45_contains root1_contains (c:=root45) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root46_contains : root46.Contains (rootPhase 46) := by
  have hh := CBox.mul_contains root23_contains root23_contains (c:=root46) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid47_contains : mid47.Contains (rootPhase 46) := root46_contains
lemma root47_contains : root47.Contains (rootPhase 47) := by
  have hh := CBox.mul_contains mid47_contains root1_contains (c:=root47) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid49_contains : mid49.Contains (rootPhase 48) := root48_contains
lemma root49_contains : root49.Contains (rootPhase 49) := by
  have hh := CBox.mul_contains mid49_contains root1_contains (c:=root49) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root50_contains : root50.Contains (rootPhase 50) := by
  have hh := CBox.mul_contains root25_contains root25_contains (c:=root50) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid51_contains : mid51.Contains (rootPhase 50) := root50_contains
lemma root51_contains : root51.Contains (rootPhase 51) := by
  have hh := CBox.mul_contains mid51_contains root1_contains (c:=root51) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root52_contains : root52.Contains (rootPhase 52) := by
  have hh := CBox.mul_contains root26_contains root26_contains (c:=root52) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid53_contains : mid53.Contains (rootPhase 52) := root52_contains
lemma root53_contains : root53.Contains (rootPhase 53) := by
  have hh := CBox.mul_contains mid53_contains root1_contains (c:=root53) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root54_contains : root54.Contains (rootPhase 54) := by
  have hh := CBox.mul_contains root27_contains root27_contains (c:=root54) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid55_contains : mid55.Contains (rootPhase 54) := root54_contains
lemma root55_contains : root55.Contains (rootPhase 55) := by
  have hh := CBox.mul_contains mid55_contains root1_contains (c:=root55) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root56_contains : root56.Contains (rootPhase 56) := by
  have hh := CBox.mul_contains root28_contains root28_contains (c:=root56) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid57_contains : mid57.Contains (rootPhase 56) := root56_contains
lemma root57_contains : root57.Contains (rootPhase 57) := by
  have hh := CBox.mul_contains mid57_contains root1_contains (c:=root57) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root58_contains : root58.Contains (rootPhase 58) := by
  have hh := CBox.mul_contains root29_contains root29_contains (c:=root58) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid59_contains : mid59.Contains (rootPhase 58) := root58_contains
lemma root59_contains : root59.Contains (rootPhase 59) := by
  have hh := CBox.mul_contains mid59_contains root1_contains (c:=root59) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root60_contains : root60.Contains (rootPhase 60) := by
  have hh := CBox.mul_contains root30_contains root30_contains (c:=root60) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid61_contains : mid61.Contains (rootPhase 60) := root60_contains
lemma root61_contains : root61.Contains (rootPhase 61) := by
  have hh := CBox.mul_contains mid61_contains root1_contains (c:=root61) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root62_contains : root62.Contains (rootPhase 62) := by
  have hh := CBox.mul_contains root31_contains root31_contains (c:=root62) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid63_contains : mid63.Contains (rootPhase 62) := root62_contains
lemma root63_contains : root63.Contains (rootPhase 63) := by
  have hh := CBox.mul_contains mid63_contains root1_contains (c:=root63) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root68_contains : root68.Contains (rootPhase 68) := by
  have hh := CBox.mul_contains root34_contains root34_contains (c:=root68) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid69_contains : mid69.Contains (rootPhase 68) := root68_contains
lemma root69_contains : root69.Contains (rootPhase 69) := by
  have hh := CBox.mul_contains mid69_contains root1_contains (c:=root69) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root70_contains : root70.Contains (rootPhase 70) := by
  have hh := CBox.mul_contains root35_contains root35_contains (c:=root70) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid71_contains : mid71.Contains (rootPhase 70) := root70_contains
lemma root71_contains : root71.Contains (rootPhase 71) := by
  have hh := CBox.mul_contains mid71_contains root1_contains (c:=root71) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root72_contains : root72.Contains (rootPhase 72) := by
  have hh := CBox.mul_contains root36_contains root36_contains (c:=root72) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid73_contains : mid73.Contains (rootPhase 72) := root72_contains
lemma root73_contains : root73.Contains (rootPhase 73) := by
  have hh := CBox.mul_contains mid73_contains root1_contains (c:=root73) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root74_contains : root74.Contains (rootPhase 74) := by
  have hh := CBox.mul_contains root37_contains root37_contains (c:=root74) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid75_contains : mid75.Contains (rootPhase 74) := root74_contains
lemma root75_contains : root75.Contains (rootPhase 75) := by
  have hh := CBox.mul_contains mid75_contains root1_contains (c:=root75) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root76_contains : root76.Contains (rootPhase 76) := by
  have hh := CBox.mul_contains root38_contains root38_contains (c:=root76) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid77_contains : mid77.Contains (rootPhase 76) := root76_contains
lemma root77_contains : root77.Contains (rootPhase 77) := by
  have hh := CBox.mul_contains mid77_contains root1_contains (c:=root77) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root78_contains : root78.Contains (rootPhase 78) := by
  have hh := CBox.mul_contains root39_contains root39_contains (c:=root78) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid79_contains : mid79.Contains (rootPhase 78) := root78_contains
lemma root79_contains : root79.Contains (rootPhase 79) := by
  have hh := CBox.mul_contains mid79_contains root1_contains (c:=root79) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root82_contains : root82.Contains (rootPhase 82) := by
  have hh := CBox.mul_contains root41_contains root41_contains (c:=root82) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid83_contains : mid83.Contains (rootPhase 82) := root82_contains
lemma root83_contains : root83.Contains (rootPhase 83) := by
  have hh := CBox.mul_contains mid83_contains root1_contains (c:=root83) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root84_contains : root84.Contains (rootPhase 84) := by
  have hh := CBox.mul_contains root42_contains root42_contains (c:=root84) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid85_contains : mid85.Contains (rootPhase 84) := root84_contains
lemma root85_contains : root85.Contains (rootPhase 85) := by
  have hh := CBox.mul_contains mid85_contains root1_contains (c:=root85) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root86_contains : root86.Contains (rootPhase 86) := by
  have hh := CBox.mul_contains root43_contains root43_contains (c:=root86) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid87_contains : mid87.Contains (rootPhase 86) := root86_contains
lemma root87_contains : root87.Contains (rootPhase 87) := by
  have hh := CBox.mul_contains mid87_contains root1_contains (c:=root87) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root88_contains : root88.Contains (rootPhase 88) := by
  have hh := CBox.mul_contains root44_contains root44_contains (c:=root88) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid89_contains : mid89.Contains (rootPhase 88) := root88_contains
lemma root89_contains : root89.Contains (rootPhase 89) := by
  have hh := CBox.mul_contains mid89_contains root1_contains (c:=root89) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root90_contains : root90.Contains (rootPhase 90) := by
  have hh := CBox.mul_contains root45_contains root45_contains (c:=root90) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid91_contains : mid91.Contains (rootPhase 90) := root90_contains
lemma root91_contains : root91.Contains (rootPhase 91) := by
  have hh := CBox.mul_contains mid91_contains root1_contains (c:=root91) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root92_contains : root92.Contains (rootPhase 92) := by
  have hh := CBox.mul_contains root46_contains root46_contains (c:=root92) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid93_contains : mid93.Contains (rootPhase 92) := root92_contains
lemma root93_contains : root93.Contains (rootPhase 93) := by
  have hh := CBox.mul_contains mid93_contains root1_contains (c:=root93) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root94_contains : root94.Contains (rootPhase 94) := by
  have hh := CBox.mul_contains root47_contains root47_contains (c:=root94) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid95_contains : mid95.Contains (rootPhase 94) := root94_contains
lemma root95_contains : root95.Contains (rootPhase 95) := by
  have hh := CBox.mul_contains mid95_contains root1_contains (c:=root95) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root98_contains : root98.Contains (rootPhase 98) := by
  have hh := CBox.mul_contains root49_contains root49_contains (c:=root98) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid99_contains : mid99.Contains (rootPhase 98) := root98_contains
lemma root99_contains : root99.Contains (rootPhase 99) := by
  have hh := CBox.mul_contains mid99_contains root1_contains (c:=root99) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root100_contains : root100.Contains (rootPhase 100) := by
  have hh := CBox.mul_contains root50_contains root50_contains (c:=root100) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid101_contains : mid101.Contains (rootPhase 100) := root100_contains
lemma root101_contains : root101.Contains (rootPhase 101) := by
  have hh := CBox.mul_contains mid101_contains root1_contains (c:=root101) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root102_contains : root102.Contains (rootPhase 102) := by
  have hh := CBox.mul_contains root51_contains root51_contains (c:=root102) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid103_contains : mid103.Contains (rootPhase 102) := root102_contains
lemma root103_contains : root103.Contains (rootPhase 103) := by
  have hh := CBox.mul_contains mid103_contains root1_contains (c:=root103) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root104_contains : root104.Contains (rootPhase 104) := by
  have hh := CBox.mul_contains root52_contains root52_contains (c:=root104) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid105_contains : mid105.Contains (rootPhase 104) := root104_contains
lemma root105_contains : root105.Contains (rootPhase 105) := by
  have hh := CBox.mul_contains mid105_contains root1_contains (c:=root105) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root106_contains : root106.Contains (rootPhase 106) := by
  have hh := CBox.mul_contains root53_contains root53_contains (c:=root106) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid107_contains : mid107.Contains (rootPhase 106) := root106_contains
lemma root107_contains : root107.Contains (rootPhase 107) := by
  have hh := CBox.mul_contains mid107_contains root1_contains (c:=root107) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root108_contains : root108.Contains (rootPhase 108) := by
  have hh := CBox.mul_contains root54_contains root54_contains (c:=root108) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid109_contains : mid109.Contains (rootPhase 108) := root108_contains
lemma root109_contains : root109.Contains (rootPhase 109) := by
  have hh := CBox.mul_contains mid109_contains root1_contains (c:=root109) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root110_contains : root110.Contains (rootPhase 110) := by
  have hh := CBox.mul_contains root55_contains root55_contains (c:=root110) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid111_contains : mid111.Contains (rootPhase 110) := root110_contains
lemma root111_contains : root111.Contains (rootPhase 111) := by
  have hh := CBox.mul_contains mid111_contains root1_contains (c:=root111) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root112_contains : root112.Contains (rootPhase 112) := by
  have hh := CBox.mul_contains root56_contains root56_contains (c:=root112) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid113_contains : mid113.Contains (rootPhase 112) := root112_contains
lemma root113_contains : root113.Contains (rootPhase 113) := by
  have hh := CBox.mul_contains mid113_contains root1_contains (c:=root113) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root114_contains : root114.Contains (rootPhase 114) := by
  have hh := CBox.mul_contains root57_contains root57_contains (c:=root114) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid115_contains : mid115.Contains (rootPhase 114) := root114_contains
lemma root115_contains : root115.Contains (rootPhase 115) := by
  have hh := CBox.mul_contains mid115_contains root1_contains (c:=root115) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root116_contains : root116.Contains (rootPhase 116) := by
  have hh := CBox.mul_contains root58_contains root58_contains (c:=root116) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid117_contains : mid117.Contains (rootPhase 116) := root116_contains
lemma root117_contains : root117.Contains (rootPhase 117) := by
  have hh := CBox.mul_contains mid117_contains root1_contains (c:=root117) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root118_contains : root118.Contains (rootPhase 118) := by
  have hh := CBox.mul_contains root59_contains root59_contains (c:=root118) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid119_contains : mid119.Contains (rootPhase 118) := root118_contains
lemma root119_contains : root119.Contains (rootPhase 119) := by
  have hh := CBox.mul_contains mid119_contains root1_contains (c:=root119) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root120_contains : root120.Contains (rootPhase 120) := by
  have hh := CBox.mul_contains root60_contains root60_contains (c:=root120) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid121_contains : mid121.Contains (rootPhase 120) := root120_contains
lemma root121_contains : root121.Contains (rootPhase 121) := by
  have hh := CBox.mul_contains mid121_contains root1_contains (c:=root121) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root122_contains : root122.Contains (rootPhase 122) := by
  have hh := CBox.mul_contains root61_contains root61_contains (c:=root122) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid123_contains : mid123.Contains (rootPhase 122) := root122_contains
lemma root123_contains : root123.Contains (rootPhase 123) := by
  have hh := CBox.mul_contains mid123_contains root1_contains (c:=root123) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root124_contains : root124.Contains (rootPhase 124) := by
  have hh := CBox.mul_contains root62_contains root62_contains (c:=root124) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid125_contains : mid125.Contains (rootPhase 124) := root124_contains
lemma root125_contains : root125.Contains (rootPhase 125) := by
  have hh := CBox.mul_contains mid125_contains root1_contains (c:=root125) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root126_contains : root126.Contains (rootPhase 126) := by
  have hh := CBox.mul_contains root63_contains root63_contains (c:=root126) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid127_contains : mid127.Contains (rootPhase 126) := root126_contains
lemma root127_contains : root127.Contains (rootPhase 127) := by
  have hh := CBox.mul_contains mid127_contains root1_contains (c:=root127) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root136_contains : root136.Contains (rootPhase 136) := by
  have hh := CBox.mul_contains root68_contains root68_contains (c:=root136) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid137_contains : mid137.Contains (rootPhase 136) := root136_contains
lemma root137_contains : root137.Contains (rootPhase 137) := by
  have hh := CBox.mul_contains mid137_contains root1_contains (c:=root137) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root138_contains : root138.Contains (rootPhase 138) := by
  have hh := CBox.mul_contains root69_contains root69_contains (c:=root138) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid139_contains : mid139.Contains (rootPhase 138) := root138_contains
lemma root139_contains : root139.Contains (rootPhase 139) := by
  have hh := CBox.mul_contains mid139_contains root1_contains (c:=root139) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root140_contains : root140.Contains (rootPhase 140) := by
  have hh := CBox.mul_contains root70_contains root70_contains (c:=root140) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid141_contains : mid141.Contains (rootPhase 140) := root140_contains
lemma root141_contains : root141.Contains (rootPhase 141) := by
  have hh := CBox.mul_contains mid141_contains root1_contains (c:=root141) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root142_contains : root142.Contains (rootPhase 142) := by
  have hh := CBox.mul_contains root71_contains root71_contains (c:=root142) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid143_contains : mid143.Contains (rootPhase 142) := root142_contains
lemma root143_contains : root143.Contains (rootPhase 143) := by
  have hh := CBox.mul_contains mid143_contains root1_contains (c:=root143) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root144_contains : root144.Contains (rootPhase 144) := by
  have hh := CBox.mul_contains root72_contains root72_contains (c:=root144) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid145_contains : mid145.Contains (rootPhase 144) := root144_contains
lemma root145_contains : root145.Contains (rootPhase 145) := by
  have hh := CBox.mul_contains mid145_contains root1_contains (c:=root145) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root146_contains : root146.Contains (rootPhase 146) := by
  have hh := CBox.mul_contains root73_contains root73_contains (c:=root146) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid147_contains : mid147.Contains (rootPhase 146) := root146_contains
lemma root147_contains : root147.Contains (rootPhase 147) := by
  have hh := CBox.mul_contains mid147_contains root1_contains (c:=root147) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root148_contains : root148.Contains (rootPhase 148) := by
  have hh := CBox.mul_contains root74_contains root74_contains (c:=root148) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid149_contains : mid149.Contains (rootPhase 148) := root148_contains
lemma root149_contains : root149.Contains (rootPhase 149) := by
  have hh := CBox.mul_contains mid149_contains root1_contains (c:=root149) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root150_contains : root150.Contains (rootPhase 150) := by
  have hh := CBox.mul_contains root75_contains root75_contains (c:=root150) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid151_contains : mid151.Contains (rootPhase 150) := root150_contains
lemma root151_contains : root151.Contains (rootPhase 151) := by
  have hh := CBox.mul_contains mid151_contains root1_contains (c:=root151) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root152_contains : root152.Contains (rootPhase 152) := by
  have hh := CBox.mul_contains root76_contains root76_contains (c:=root152) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid153_contains : mid153.Contains (rootPhase 152) := root152_contains
lemma root153_contains : root153.Contains (rootPhase 153) := by
  have hh := CBox.mul_contains mid153_contains root1_contains (c:=root153) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root154_contains : root154.Contains (rootPhase 154) := by
  have hh := CBox.mul_contains root77_contains root77_contains (c:=root154) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid155_contains : mid155.Contains (rootPhase 154) := root154_contains
lemma root155_contains : root155.Contains (rootPhase 155) := by
  have hh := CBox.mul_contains mid155_contains root1_contains (c:=root155) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root156_contains : root156.Contains (rootPhase 156) := by
  have hh := CBox.mul_contains root78_contains root78_contains (c:=root156) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid157_contains : mid157.Contains (rootPhase 156) := root156_contains
lemma root157_contains : root157.Contains (rootPhase 157) := by
  have hh := CBox.mul_contains mid157_contains root1_contains (c:=root157) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root158_contains : root158.Contains (rootPhase 158) := by
  have hh := CBox.mul_contains root79_contains root79_contains (c:=root158) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid159_contains : mid159.Contains (rootPhase 158) := root158_contains
lemma root159_contains : root159.Contains (rootPhase 159) := by
  have hh := CBox.mul_contains mid159_contains root1_contains (c:=root159) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root164_contains : root164.Contains (rootPhase 164) := by
  have hh := CBox.mul_contains root82_contains root82_contains (c:=root164) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid165_contains : mid165.Contains (rootPhase 164) := root164_contains
lemma root165_contains : root165.Contains (rootPhase 165) := by
  have hh := CBox.mul_contains mid165_contains root1_contains (c:=root165) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root166_contains : root166.Contains (rootPhase 166) := by
  have hh := CBox.mul_contains root83_contains root83_contains (c:=root166) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid167_contains : mid167.Contains (rootPhase 166) := root166_contains
lemma root167_contains : root167.Contains (rootPhase 167) := by
  have hh := CBox.mul_contains mid167_contains root1_contains (c:=root167) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root168_contains : root168.Contains (rootPhase 168) := by
  have hh := CBox.mul_contains root84_contains root84_contains (c:=root168) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid169_contains : mid169.Contains (rootPhase 168) := root168_contains
lemma root169_contains : root169.Contains (rootPhase 169) := by
  have hh := CBox.mul_contains mid169_contains root1_contains (c:=root169) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root170_contains : root170.Contains (rootPhase 170) := by
  have hh := CBox.mul_contains root85_contains root85_contains (c:=root170) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid171_contains : mid171.Contains (rootPhase 170) := root170_contains
lemma root171_contains : root171.Contains (rootPhase 171) := by
  have hh := CBox.mul_contains mid171_contains root1_contains (c:=root171) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root172_contains : root172.Contains (rootPhase 172) := by
  have hh := CBox.mul_contains root86_contains root86_contains (c:=root172) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid173_contains : mid173.Contains (rootPhase 172) := root172_contains
lemma root173_contains : root173.Contains (rootPhase 173) := by
  have hh := CBox.mul_contains mid173_contains root1_contains (c:=root173) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root174_contains : root174.Contains (rootPhase 174) := by
  have hh := CBox.mul_contains root87_contains root87_contains (c:=root174) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid175_contains : mid175.Contains (rootPhase 174) := root174_contains
lemma root175_contains : root175.Contains (rootPhase 175) := by
  have hh := CBox.mul_contains mid175_contains root1_contains (c:=root175) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root176_contains : root176.Contains (rootPhase 176) := by
  have hh := CBox.mul_contains root88_contains root88_contains (c:=root176) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid177_contains : mid177.Contains (rootPhase 176) := root176_contains
lemma root177_contains : root177.Contains (rootPhase 177) := by
  have hh := CBox.mul_contains mid177_contains root1_contains (c:=root177) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root178_contains : root178.Contains (rootPhase 178) := by
  have hh := CBox.mul_contains root89_contains root89_contains (c:=root178) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid179_contains : mid179.Contains (rootPhase 178) := root178_contains
lemma root179_contains : root179.Contains (rootPhase 179) := by
  have hh := CBox.mul_contains mid179_contains root1_contains (c:=root179) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root180_contains : root180.Contains (rootPhase 180) := by
  have hh := CBox.mul_contains root90_contains root90_contains (c:=root180) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid181_contains : mid181.Contains (rootPhase 180) := root180_contains
lemma root181_contains : root181.Contains (rootPhase 181) := by
  have hh := CBox.mul_contains mid181_contains root1_contains (c:=root181) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root182_contains : root182.Contains (rootPhase 182) := by
  have hh := CBox.mul_contains root91_contains root91_contains (c:=root182) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid183_contains : mid183.Contains (rootPhase 182) := root182_contains
lemma root183_contains : root183.Contains (rootPhase 183) := by
  have hh := CBox.mul_contains mid183_contains root1_contains (c:=root183) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root184_contains : root184.Contains (rootPhase 184) := by
  have hh := CBox.mul_contains root92_contains root92_contains (c:=root184) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid185_contains : mid185.Contains (rootPhase 184) := root184_contains
lemma root185_contains : root185.Contains (rootPhase 185) := by
  have hh := CBox.mul_contains mid185_contains root1_contains (c:=root185) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root186_contains : root186.Contains (rootPhase 186) := by
  have hh := CBox.mul_contains root93_contains root93_contains (c:=root186) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid187_contains : mid187.Contains (rootPhase 186) := root186_contains
lemma root187_contains : root187.Contains (rootPhase 187) := by
  have hh := CBox.mul_contains mid187_contains root1_contains (c:=root187) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root188_contains : root188.Contains (rootPhase 188) := by
  have hh := CBox.mul_contains root94_contains root94_contains (c:=root188) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid189_contains : mid189.Contains (rootPhase 188) := root188_contains
lemma root189_contains : root189.Contains (rootPhase 189) := by
  have hh := CBox.mul_contains mid189_contains root1_contains (c:=root189) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root190_contains : root190.Contains (rootPhase 190) := by
  have hh := CBox.mul_contains root95_contains root95_contains (c:=root190) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid191_contains : mid191.Contains (rootPhase 190) := root190_contains
lemma root191_contains : root191.Contains (rootPhase 191) := by
  have hh := CBox.mul_contains mid191_contains root1_contains (c:=root191) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root196_contains : root196.Contains (rootPhase 196) := by
  have hh := CBox.mul_contains root98_contains root98_contains (c:=root196) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid197_contains : mid197.Contains (rootPhase 196) := root196_contains
lemma root197_contains : root197.Contains (rootPhase 197) := by
  have hh := CBox.mul_contains mid197_contains root1_contains (c:=root197) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root198_contains : root198.Contains (rootPhase 198) := by
  have hh := CBox.mul_contains root99_contains root99_contains (c:=root198) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid199_contains : mid199.Contains (rootPhase 198) := root198_contains
lemma root199_contains : root199.Contains (rootPhase 199) := by
  have hh := CBox.mul_contains mid199_contains root1_contains (c:=root199) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root200_contains : root200.Contains (rootPhase 200) := by
  have hh := CBox.mul_contains root100_contains root100_contains (c:=root200) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid201_contains : mid201.Contains (rootPhase 200) := root200_contains
lemma root201_contains : root201.Contains (rootPhase 201) := by
  have hh := CBox.mul_contains mid201_contains root1_contains (c:=root201) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root202_contains : root202.Contains (rootPhase 202) := by
  have hh := CBox.mul_contains root101_contains root101_contains (c:=root202) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid203_contains : mid203.Contains (rootPhase 202) := root202_contains
lemma root203_contains : root203.Contains (rootPhase 203) := by
  have hh := CBox.mul_contains mid203_contains root1_contains (c:=root203) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root204_contains : root204.Contains (rootPhase 204) := by
  have hh := CBox.mul_contains root102_contains root102_contains (c:=root204) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid205_contains : mid205.Contains (rootPhase 204) := root204_contains
lemma root205_contains : root205.Contains (rootPhase 205) := by
  have hh := CBox.mul_contains mid205_contains root1_contains (c:=root205) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root206_contains : root206.Contains (rootPhase 206) := by
  have hh := CBox.mul_contains root103_contains root103_contains (c:=root206) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid207_contains : mid207.Contains (rootPhase 206) := root206_contains
lemma root207_contains : root207.Contains (rootPhase 207) := by
  have hh := CBox.mul_contains mid207_contains root1_contains (c:=root207) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root208_contains : root208.Contains (rootPhase 208) := by
  have hh := CBox.mul_contains root104_contains root104_contains (c:=root208) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid209_contains : mid209.Contains (rootPhase 208) := root208_contains
lemma root209_contains : root209.Contains (rootPhase 209) := by
  have hh := CBox.mul_contains mid209_contains root1_contains (c:=root209) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root210_contains : root210.Contains (rootPhase 210) := by
  have hh := CBox.mul_contains root105_contains root105_contains (c:=root210) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid211_contains : mid211.Contains (rootPhase 210) := root210_contains
lemma root211_contains : root211.Contains (rootPhase 211) := by
  have hh := CBox.mul_contains mid211_contains root1_contains (c:=root211) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root212_contains : root212.Contains (rootPhase 212) := by
  have hh := CBox.mul_contains root106_contains root106_contains (c:=root212) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid213_contains : mid213.Contains (rootPhase 212) := root212_contains
lemma root213_contains : root213.Contains (rootPhase 213) := by
  have hh := CBox.mul_contains mid213_contains root1_contains (c:=root213) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root214_contains : root214.Contains (rootPhase 214) := by
  have hh := CBox.mul_contains root107_contains root107_contains (c:=root214) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid215_contains : mid215.Contains (rootPhase 214) := root214_contains
lemma root215_contains : root215.Contains (rootPhase 215) := by
  have hh := CBox.mul_contains mid215_contains root1_contains (c:=root215) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root216_contains : root216.Contains (rootPhase 216) := by
  have hh := CBox.mul_contains root108_contains root108_contains (c:=root216) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid217_contains : mid217.Contains (rootPhase 216) := root216_contains
lemma root217_contains : root217.Contains (rootPhase 217) := by
  have hh := CBox.mul_contains mid217_contains root1_contains (c:=root217) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root218_contains : root218.Contains (rootPhase 218) := by
  have hh := CBox.mul_contains root109_contains root109_contains (c:=root218) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid219_contains : mid219.Contains (rootPhase 218) := root218_contains
lemma root219_contains : root219.Contains (rootPhase 219) := by
  have hh := CBox.mul_contains mid219_contains root1_contains (c:=root219) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root220_contains : root220.Contains (rootPhase 220) := by
  have hh := CBox.mul_contains root110_contains root110_contains (c:=root220) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid221_contains : mid221.Contains (rootPhase 220) := root220_contains
lemma root221_contains : root221.Contains (rootPhase 221) := by
  have hh := CBox.mul_contains mid221_contains root1_contains (c:=root221) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root222_contains : root222.Contains (rootPhase 222) := by
  have hh := CBox.mul_contains root111_contains root111_contains (c:=root222) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid223_contains : mid223.Contains (rootPhase 222) := root222_contains
lemma root223_contains : root223.Contains (rootPhase 223) := by
  have hh := CBox.mul_contains mid223_contains root1_contains (c:=root223) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root224_contains : root224.Contains (rootPhase 224) := by
  have hh := CBox.mul_contains root112_contains root112_contains (c:=root224) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid225_contains : mid225.Contains (rootPhase 224) := root224_contains
lemma root225_contains : root225.Contains (rootPhase 225) := by
  have hh := CBox.mul_contains mid225_contains root1_contains (c:=root225) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root226_contains : root226.Contains (rootPhase 226) := by
  have hh := CBox.mul_contains root113_contains root113_contains (c:=root226) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid227_contains : mid227.Contains (rootPhase 226) := root226_contains
lemma root227_contains : root227.Contains (rootPhase 227) := by
  have hh := CBox.mul_contains mid227_contains root1_contains (c:=root227) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root228_contains : root228.Contains (rootPhase 228) := by
  have hh := CBox.mul_contains root114_contains root114_contains (c:=root228) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid229_contains : mid229.Contains (rootPhase 228) := root228_contains
lemma root229_contains : root229.Contains (rootPhase 229) := by
  have hh := CBox.mul_contains mid229_contains root1_contains (c:=root229) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root230_contains : root230.Contains (rootPhase 230) := by
  have hh := CBox.mul_contains root115_contains root115_contains (c:=root230) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid231_contains : mid231.Contains (rootPhase 230) := root230_contains
lemma root231_contains : root231.Contains (rootPhase 231) := by
  have hh := CBox.mul_contains mid231_contains root1_contains (c:=root231) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root232_contains : root232.Contains (rootPhase 232) := by
  have hh := CBox.mul_contains root116_contains root116_contains (c:=root232) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid233_contains : mid233.Contains (rootPhase 232) := root232_contains
lemma root233_contains : root233.Contains (rootPhase 233) := by
  have hh := CBox.mul_contains mid233_contains root1_contains (c:=root233) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root234_contains : root234.Contains (rootPhase 234) := by
  have hh := CBox.mul_contains root117_contains root117_contains (c:=root234) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid235_contains : mid235.Contains (rootPhase 234) := root234_contains
lemma root235_contains : root235.Contains (rootPhase 235) := by
  have hh := CBox.mul_contains mid235_contains root1_contains (c:=root235) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root236_contains : root236.Contains (rootPhase 236) := by
  have hh := CBox.mul_contains root118_contains root118_contains (c:=root236) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid237_contains : mid237.Contains (rootPhase 236) := root236_contains
lemma root237_contains : root237.Contains (rootPhase 237) := by
  have hh := CBox.mul_contains mid237_contains root1_contains (c:=root237) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root238_contains : root238.Contains (rootPhase 238) := by
  have hh := CBox.mul_contains root119_contains root119_contains (c:=root238) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid239_contains : mid239.Contains (rootPhase 238) := root238_contains
lemma root239_contains : root239.Contains (rootPhase 239) := by
  have hh := CBox.mul_contains mid239_contains root1_contains (c:=root239) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root240_contains : root240.Contains (rootPhase 240) := by
  have hh := CBox.mul_contains root120_contains root120_contains (c:=root240) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid241_contains : mid241.Contains (rootPhase 240) := root240_contains
lemma root241_contains : root241.Contains (rootPhase 241) := by
  have hh := CBox.mul_contains mid241_contains root1_contains (c:=root241) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root242_contains : root242.Contains (rootPhase 242) := by
  have hh := CBox.mul_contains root121_contains root121_contains (c:=root242) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid243_contains : mid243.Contains (rootPhase 242) := root242_contains
lemma root243_contains : root243.Contains (rootPhase 243) := by
  have hh := CBox.mul_contains mid243_contains root1_contains (c:=root243) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root244_contains : root244.Contains (rootPhase 244) := by
  have hh := CBox.mul_contains root122_contains root122_contains (c:=root244) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid245_contains : mid245.Contains (rootPhase 244) := root244_contains
lemma root245_contains : root245.Contains (rootPhase 245) := by
  have hh := CBox.mul_contains mid245_contains root1_contains (c:=root245) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root246_contains : root246.Contains (rootPhase 246) := by
  have hh := CBox.mul_contains root123_contains root123_contains (c:=root246) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid247_contains : mid247.Contains (rootPhase 246) := root246_contains
lemma root247_contains : root247.Contains (rootPhase 247) := by
  have hh := CBox.mul_contains mid247_contains root1_contains (c:=root247) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root248_contains : root248.Contains (rootPhase 248) := by
  have hh := CBox.mul_contains root124_contains root124_contains (c:=root248) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid249_contains : mid249.Contains (rootPhase 248) := root248_contains
lemma root249_contains : root249.Contains (rootPhase 249) := by
  have hh := CBox.mul_contains mid249_contains root1_contains (c:=root249) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root250_contains : root250.Contains (rootPhase 250) := by
  have hh := CBox.mul_contains root125_contains root125_contains (c:=root250) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid251_contains : mid251.Contains (rootPhase 250) := root250_contains
lemma root251_contains : root251.Contains (rootPhase 251) := by
  have hh := CBox.mul_contains mid251_contains root1_contains (c:=root251) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root252_contains : root252.Contains (rootPhase 252) := by
  have hh := CBox.mul_contains root126_contains root126_contains (c:=root252) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid253_contains : mid253.Contains (rootPhase 252) := root252_contains
lemma root253_contains : root253.Contains (rootPhase 253) := by
  have hh := CBox.mul_contains mid253_contains root1_contains (c:=root253) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root254_contains : root254.Contains (rootPhase 254) := by
  have hh := CBox.mul_contains root127_contains root127_contains (c:=root254) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid255_contains : mid255.Contains (rootPhase 254) := root254_contains
lemma root255_contains : root255.Contains (rootPhase 255) := by
  have hh := CBox.mul_contains mid255_contains root1_contains (c:=root255) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root272_contains : root272.Contains (rootPhase 272) := by
  have hh := CBox.mul_contains root136_contains root136_contains (c:=root272) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid273_contains : mid273.Contains (rootPhase 272) := root272_contains
lemma root273_contains : root273.Contains (rootPhase 273) := by
  have hh := CBox.mul_contains mid273_contains root1_contains (c:=root273) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root274_contains : root274.Contains (rootPhase 274) := by
  have hh := CBox.mul_contains root137_contains root137_contains (c:=root274) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid275_contains : mid275.Contains (rootPhase 274) := root274_contains
lemma root275_contains : root275.Contains (rootPhase 275) := by
  have hh := CBox.mul_contains mid275_contains root1_contains (c:=root275) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root276_contains : root276.Contains (rootPhase 276) := by
  have hh := CBox.mul_contains root138_contains root138_contains (c:=root276) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid277_contains : mid277.Contains (rootPhase 276) := root276_contains
lemma root277_contains : root277.Contains (rootPhase 277) := by
  have hh := CBox.mul_contains mid277_contains root1_contains (c:=root277) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root278_contains : root278.Contains (rootPhase 278) := by
  have hh := CBox.mul_contains root139_contains root139_contains (c:=root278) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid279_contains : mid279.Contains (rootPhase 278) := root278_contains
lemma root279_contains : root279.Contains (rootPhase 279) := by
  have hh := CBox.mul_contains mid279_contains root1_contains (c:=root279) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root280_contains : root280.Contains (rootPhase 280) := by
  have hh := CBox.mul_contains root140_contains root140_contains (c:=root280) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid281_contains : mid281.Contains (rootPhase 280) := root280_contains
lemma root281_contains : root281.Contains (rootPhase 281) := by
  have hh := CBox.mul_contains mid281_contains root1_contains (c:=root281) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root282_contains : root282.Contains (rootPhase 282) := by
  have hh := CBox.mul_contains root141_contains root141_contains (c:=root282) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid283_contains : mid283.Contains (rootPhase 282) := root282_contains
lemma root283_contains : root283.Contains (rootPhase 283) := by
  have hh := CBox.mul_contains mid283_contains root1_contains (c:=root283) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root284_contains : root284.Contains (rootPhase 284) := by
  have hh := CBox.mul_contains root142_contains root142_contains (c:=root284) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid285_contains : mid285.Contains (rootPhase 284) := root284_contains
lemma root285_contains : root285.Contains (rootPhase 285) := by
  have hh := CBox.mul_contains mid285_contains root1_contains (c:=root285) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root286_contains : root286.Contains (rootPhase 286) := by
  have hh := CBox.mul_contains root143_contains root143_contains (c:=root286) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid287_contains : mid287.Contains (rootPhase 286) := root286_contains
lemma root287_contains : root287.Contains (rootPhase 287) := by
  have hh := CBox.mul_contains mid287_contains root1_contains (c:=root287) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root288_contains : root288.Contains (rootPhase 288) := by
  have hh := CBox.mul_contains root144_contains root144_contains (c:=root288) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid289_contains : mid289.Contains (rootPhase 288) := root288_contains
lemma root289_contains : root289.Contains (rootPhase 289) := by
  have hh := CBox.mul_contains mid289_contains root1_contains (c:=root289) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root290_contains : root290.Contains (rootPhase 290) := by
  have hh := CBox.mul_contains root145_contains root145_contains (c:=root290) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid291_contains : mid291.Contains (rootPhase 290) := root290_contains
lemma root291_contains : root291.Contains (rootPhase 291) := by
  have hh := CBox.mul_contains mid291_contains root1_contains (c:=root291) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root292_contains : root292.Contains (rootPhase 292) := by
  have hh := CBox.mul_contains root146_contains root146_contains (c:=root292) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid293_contains : mid293.Contains (rootPhase 292) := root292_contains
lemma root293_contains : root293.Contains (rootPhase 293) := by
  have hh := CBox.mul_contains mid293_contains root1_contains (c:=root293) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root294_contains : root294.Contains (rootPhase 294) := by
  have hh := CBox.mul_contains root147_contains root147_contains (c:=root294) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid295_contains : mid295.Contains (rootPhase 294) := root294_contains
lemma root295_contains : root295.Contains (rootPhase 295) := by
  have hh := CBox.mul_contains mid295_contains root1_contains (c:=root295) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root296_contains : root296.Contains (rootPhase 296) := by
  have hh := CBox.mul_contains root148_contains root148_contains (c:=root296) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid297_contains : mid297.Contains (rootPhase 296) := root296_contains
lemma root297_contains : root297.Contains (rootPhase 297) := by
  have hh := CBox.mul_contains mid297_contains root1_contains (c:=root297) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root298_contains : root298.Contains (rootPhase 298) := by
  have hh := CBox.mul_contains root149_contains root149_contains (c:=root298) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid299_contains : mid299.Contains (rootPhase 298) := root298_contains
lemma root299_contains : root299.Contains (rootPhase 299) := by
  have hh := CBox.mul_contains mid299_contains root1_contains (c:=root299) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root300_contains : root300.Contains (rootPhase 300) := by
  have hh := CBox.mul_contains root150_contains root150_contains (c:=root300) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid301_contains : mid301.Contains (rootPhase 300) := root300_contains
lemma root301_contains : root301.Contains (rootPhase 301) := by
  have hh := CBox.mul_contains mid301_contains root1_contains (c:=root301) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root302_contains : root302.Contains (rootPhase 302) := by
  have hh := CBox.mul_contains root151_contains root151_contains (c:=root302) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid303_contains : mid303.Contains (rootPhase 302) := root302_contains
lemma root303_contains : root303.Contains (rootPhase 303) := by
  have hh := CBox.mul_contains mid303_contains root1_contains (c:=root303) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root304_contains : root304.Contains (rootPhase 304) := by
  have hh := CBox.mul_contains root152_contains root152_contains (c:=root304) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid305_contains : mid305.Contains (rootPhase 304) := root304_contains
lemma root305_contains : root305.Contains (rootPhase 305) := by
  have hh := CBox.mul_contains mid305_contains root1_contains (c:=root305) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root306_contains : root306.Contains (rootPhase 306) := by
  have hh := CBox.mul_contains root153_contains root153_contains (c:=root306) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid307_contains : mid307.Contains (rootPhase 306) := root306_contains
lemma root307_contains : root307.Contains (rootPhase 307) := by
  have hh := CBox.mul_contains mid307_contains root1_contains (c:=root307) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root308_contains : root308.Contains (rootPhase 308) := by
  have hh := CBox.mul_contains root154_contains root154_contains (c:=root308) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid309_contains : mid309.Contains (rootPhase 308) := root308_contains
lemma root309_contains : root309.Contains (rootPhase 309) := by
  have hh := CBox.mul_contains mid309_contains root1_contains (c:=root309) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root310_contains : root310.Contains (rootPhase 310) := by
  have hh := CBox.mul_contains root155_contains root155_contains (c:=root310) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid311_contains : mid311.Contains (rootPhase 310) := root310_contains
lemma root311_contains : root311.Contains (rootPhase 311) := by
  have hh := CBox.mul_contains mid311_contains root1_contains (c:=root311) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root312_contains : root312.Contains (rootPhase 312) := by
  have hh := CBox.mul_contains root156_contains root156_contains (c:=root312) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid313_contains : mid313.Contains (rootPhase 312) := root312_contains
lemma root313_contains : root313.Contains (rootPhase 313) := by
  have hh := CBox.mul_contains mid313_contains root1_contains (c:=root313) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root314_contains : root314.Contains (rootPhase 314) := by
  have hh := CBox.mul_contains root157_contains root157_contains (c:=root314) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid315_contains : mid315.Contains (rootPhase 314) := root314_contains
lemma root315_contains : root315.Contains (rootPhase 315) := by
  have hh := CBox.mul_contains mid315_contains root1_contains (c:=root315) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root316_contains : root316.Contains (rootPhase 316) := by
  have hh := CBox.mul_contains root158_contains root158_contains (c:=root316) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid317_contains : mid317.Contains (rootPhase 316) := root316_contains
lemma root317_contains : root317.Contains (rootPhase 317) := by
  have hh := CBox.mul_contains mid317_contains root1_contains (c:=root317) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root318_contains : root318.Contains (rootPhase 318) := by
  have hh := CBox.mul_contains root159_contains root159_contains (c:=root318) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid319_contains : mid319.Contains (rootPhase 318) := root318_contains
lemma root319_contains : root319.Contains (rootPhase 319) := by
  have hh := CBox.mul_contains mid319_contains root1_contains (c:=root319) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid323_contains : mid323.Contains (rootPhase 322) := root322_contains
lemma root323_contains : root323.Contains (rootPhase 323) := by
  have hh := CBox.mul_contains mid323_contains root1_contains (c:=root323) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid325_contains : mid325.Contains (rootPhase 324) := root324_contains
lemma root325_contains : root325.Contains (rootPhase 325) := by
  have hh := CBox.mul_contains mid325_contains root1_contains (c:=root325) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid327_contains : mid327.Contains (rootPhase 326) := root326_contains
lemma root327_contains : root327.Contains (rootPhase 327) := by
  have hh := CBox.mul_contains mid327_contains root1_contains (c:=root327) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root328_contains : root328.Contains (rootPhase 328) := by
  have hh := CBox.mul_contains root164_contains root164_contains (c:=root328) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid329_contains : mid329.Contains (rootPhase 328) := root328_contains
lemma root329_contains : root329.Contains (rootPhase 329) := by
  have hh := CBox.mul_contains mid329_contains root1_contains (c:=root329) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root330_contains : root330.Contains (rootPhase 330) := by
  have hh := CBox.mul_contains root165_contains root165_contains (c:=root330) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid331_contains : mid331.Contains (rootPhase 330) := root330_contains
lemma root331_contains : root331.Contains (rootPhase 331) := by
  have hh := CBox.mul_contains mid331_contains root1_contains (c:=root331) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root332_contains : root332.Contains (rootPhase 332) := by
  have hh := CBox.mul_contains root166_contains root166_contains (c:=root332) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid333_contains : mid333.Contains (rootPhase 332) := root332_contains
lemma root333_contains : root333.Contains (rootPhase 333) := by
  have hh := CBox.mul_contains mid333_contains root1_contains (c:=root333) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root334_contains : root334.Contains (rootPhase 334) := by
  have hh := CBox.mul_contains root167_contains root167_contains (c:=root334) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid335_contains : mid335.Contains (rootPhase 334) := root334_contains
lemma root335_contains : root335.Contains (rootPhase 335) := by
  have hh := CBox.mul_contains mid335_contains root1_contains (c:=root335) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root336_contains : root336.Contains (rootPhase 336) := by
  have hh := CBox.mul_contains root168_contains root168_contains (c:=root336) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid337_contains : mid337.Contains (rootPhase 336) := root336_contains
lemma root337_contains : root337.Contains (rootPhase 337) := by
  have hh := CBox.mul_contains mid337_contains root1_contains (c:=root337) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root338_contains : root338.Contains (rootPhase 338) := by
  have hh := CBox.mul_contains root169_contains root169_contains (c:=root338) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid339_contains : mid339.Contains (rootPhase 338) := root338_contains
lemma root339_contains : root339.Contains (rootPhase 339) := by
  have hh := CBox.mul_contains mid339_contains root1_contains (c:=root339) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root340_contains : root340.Contains (rootPhase 340) := by
  have hh := CBox.mul_contains root170_contains root170_contains (c:=root340) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid341_contains : mid341.Contains (rootPhase 340) := root340_contains
lemma root341_contains : root341.Contains (rootPhase 341) := by
  have hh := CBox.mul_contains mid341_contains root1_contains (c:=root341) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root342_contains : root342.Contains (rootPhase 342) := by
  have hh := CBox.mul_contains root171_contains root171_contains (c:=root342) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid343_contains : mid343.Contains (rootPhase 342) := root342_contains
lemma root343_contains : root343.Contains (rootPhase 343) := by
  have hh := CBox.mul_contains mid343_contains root1_contains (c:=root343) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root344_contains : root344.Contains (rootPhase 344) := by
  have hh := CBox.mul_contains root172_contains root172_contains (c:=root344) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid345_contains : mid345.Contains (rootPhase 344) := root344_contains
lemma root345_contains : root345.Contains (rootPhase 345) := by
  have hh := CBox.mul_contains mid345_contains root1_contains (c:=root345) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root346_contains : root346.Contains (rootPhase 346) := by
  have hh := CBox.mul_contains root173_contains root173_contains (c:=root346) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid347_contains : mid347.Contains (rootPhase 346) := root346_contains
lemma root347_contains : root347.Contains (rootPhase 347) := by
  have hh := CBox.mul_contains mid347_contains root1_contains (c:=root347) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root348_contains : root348.Contains (rootPhase 348) := by
  have hh := CBox.mul_contains root174_contains root174_contains (c:=root348) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid349_contains : mid349.Contains (rootPhase 348) := root348_contains
lemma root349_contains : root349.Contains (rootPhase 349) := by
  have hh := CBox.mul_contains mid349_contains root1_contains (c:=root349) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root350_contains : root350.Contains (rootPhase 350) := by
  have hh := CBox.mul_contains root175_contains root175_contains (c:=root350) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid351_contains : mid351.Contains (rootPhase 350) := root350_contains
lemma root351_contains : root351.Contains (rootPhase 351) := by
  have hh := CBox.mul_contains mid351_contains root1_contains (c:=root351) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root352_contains : root352.Contains (rootPhase 352) := by
  have hh := CBox.mul_contains root176_contains root176_contains (c:=root352) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid353_contains : mid353.Contains (rootPhase 352) := root352_contains
lemma root353_contains : root353.Contains (rootPhase 353) := by
  have hh := CBox.mul_contains mid353_contains root1_contains (c:=root353) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root354_contains : root354.Contains (rootPhase 354) := by
  have hh := CBox.mul_contains root177_contains root177_contains (c:=root354) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid355_contains : mid355.Contains (rootPhase 354) := root354_contains
lemma root355_contains : root355.Contains (rootPhase 355) := by
  have hh := CBox.mul_contains mid355_contains root1_contains (c:=root355) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root356_contains : root356.Contains (rootPhase 356) := by
  have hh := CBox.mul_contains root178_contains root178_contains (c:=root356) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid357_contains : mid357.Contains (rootPhase 356) := root356_contains
lemma root357_contains : root357.Contains (rootPhase 357) := by
  have hh := CBox.mul_contains mid357_contains root1_contains (c:=root357) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root358_contains : root358.Contains (rootPhase 358) := by
  have hh := CBox.mul_contains root179_contains root179_contains (c:=root358) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid359_contains : mid359.Contains (rootPhase 358) := root358_contains
lemma root359_contains : root359.Contains (rootPhase 359) := by
  have hh := CBox.mul_contains mid359_contains root1_contains (c:=root359) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root360_contains : root360.Contains (rootPhase 360) := by
  have hh := CBox.mul_contains root180_contains root180_contains (c:=root360) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid361_contains : mid361.Contains (rootPhase 360) := root360_contains
lemma root361_contains : root361.Contains (rootPhase 361) := by
  have hh := CBox.mul_contains mid361_contains root1_contains (c:=root361) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root362_contains : root362.Contains (rootPhase 362) := by
  have hh := CBox.mul_contains root181_contains root181_contains (c:=root362) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid363_contains : mid363.Contains (rootPhase 362) := root362_contains
lemma root363_contains : root363.Contains (rootPhase 363) := by
  have hh := CBox.mul_contains mid363_contains root1_contains (c:=root363) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root364_contains : root364.Contains (rootPhase 364) := by
  have hh := CBox.mul_contains root182_contains root182_contains (c:=root364) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid365_contains : mid365.Contains (rootPhase 364) := root364_contains
lemma root365_contains : root365.Contains (rootPhase 365) := by
  have hh := CBox.mul_contains mid365_contains root1_contains (c:=root365) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root366_contains : root366.Contains (rootPhase 366) := by
  have hh := CBox.mul_contains root183_contains root183_contains (c:=root366) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid367_contains : mid367.Contains (rootPhase 366) := root366_contains
lemma root367_contains : root367.Contains (rootPhase 367) := by
  have hh := CBox.mul_contains mid367_contains root1_contains (c:=root367) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root368_contains : root368.Contains (rootPhase 368) := by
  have hh := CBox.mul_contains root184_contains root184_contains (c:=root368) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid369_contains : mid369.Contains (rootPhase 368) := root368_contains
lemma root369_contains : root369.Contains (rootPhase 369) := by
  have hh := CBox.mul_contains mid369_contains root1_contains (c:=root369) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root370_contains : root370.Contains (rootPhase 370) := by
  have hh := CBox.mul_contains root185_contains root185_contains (c:=root370) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid371_contains : mid371.Contains (rootPhase 370) := root370_contains
lemma root371_contains : root371.Contains (rootPhase 371) := by
  have hh := CBox.mul_contains mid371_contains root1_contains (c:=root371) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root372_contains : root372.Contains (rootPhase 372) := by
  have hh := CBox.mul_contains root186_contains root186_contains (c:=root372) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid373_contains : mid373.Contains (rootPhase 372) := root372_contains
lemma root373_contains : root373.Contains (rootPhase 373) := by
  have hh := CBox.mul_contains mid373_contains root1_contains (c:=root373) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root374_contains : root374.Contains (rootPhase 374) := by
  have hh := CBox.mul_contains root187_contains root187_contains (c:=root374) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid375_contains : mid375.Contains (rootPhase 374) := root374_contains
lemma root375_contains : root375.Contains (rootPhase 375) := by
  have hh := CBox.mul_contains mid375_contains root1_contains (c:=root375) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root376_contains : root376.Contains (rootPhase 376) := by
  have hh := CBox.mul_contains root188_contains root188_contains (c:=root376) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid377_contains : mid377.Contains (rootPhase 376) := root376_contains
lemma root377_contains : root377.Contains (rootPhase 377) := by
  have hh := CBox.mul_contains mid377_contains root1_contains (c:=root377) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root378_contains : root378.Contains (rootPhase 378) := by
  have hh := CBox.mul_contains root189_contains root189_contains (c:=root378) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid379_contains : mid379.Contains (rootPhase 378) := root378_contains
lemma root379_contains : root379.Contains (rootPhase 379) := by
  have hh := CBox.mul_contains mid379_contains root1_contains (c:=root379) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root380_contains : root380.Contains (rootPhase 380) := by
  have hh := CBox.mul_contains root190_contains root190_contains (c:=root380) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid381_contains : mid381.Contains (rootPhase 380) := root380_contains
lemma root381_contains : root381.Contains (rootPhase 381) := by
  have hh := CBox.mul_contains mid381_contains root1_contains (c:=root381) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root382_contains : root382.Contains (rootPhase 382) := by
  have hh := CBox.mul_contains root191_contains root191_contains (c:=root382) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid383_contains : mid383.Contains (rootPhase 382) := root382_contains
lemma root383_contains : root383.Contains (rootPhase 383) := by
  have hh := CBox.mul_contains mid383_contains root1_contains (c:=root383) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid385_contains : mid385.Contains (rootPhase 384) := root384_contains
lemma root385_contains : root385.Contains (rootPhase 385) := by
  have hh := CBox.mul_contains mid385_contains root1_contains (c:=root385) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid387_contains : mid387.Contains (rootPhase 386) := root386_contains
lemma root387_contains : root387.Contains (rootPhase 387) := by
  have hh := CBox.mul_contains mid387_contains root1_contains (c:=root387) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid389_contains : mid389.Contains (rootPhase 388) := root388_contains
lemma root389_contains : root389.Contains (rootPhase 389) := by
  have hh := CBox.mul_contains mid389_contains root1_contains (c:=root389) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid391_contains : mid391.Contains (rootPhase 390) := root390_contains
lemma root391_contains : root391.Contains (rootPhase 391) := by
  have hh := CBox.mul_contains mid391_contains root1_contains (c:=root391) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root392_contains : root392.Contains (rootPhase 392) := by
  have hh := CBox.mul_contains root196_contains root196_contains (c:=root392) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid393_contains : mid393.Contains (rootPhase 392) := root392_contains
lemma root393_contains : root393.Contains (rootPhase 393) := by
  have hh := CBox.mul_contains mid393_contains root1_contains (c:=root393) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root394_contains : root394.Contains (rootPhase 394) := by
  have hh := CBox.mul_contains root197_contains root197_contains (c:=root394) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid395_contains : mid395.Contains (rootPhase 394) := root394_contains
lemma root395_contains : root395.Contains (rootPhase 395) := by
  have hh := CBox.mul_contains mid395_contains root1_contains (c:=root395) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root396_contains : root396.Contains (rootPhase 396) := by
  have hh := CBox.mul_contains root198_contains root198_contains (c:=root396) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid397_contains : mid397.Contains (rootPhase 396) := root396_contains
lemma root397_contains : root397.Contains (rootPhase 397) := by
  have hh := CBox.mul_contains mid397_contains root1_contains (c:=root397) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root398_contains : root398.Contains (rootPhase 398) := by
  have hh := CBox.mul_contains root199_contains root199_contains (c:=root398) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid399_contains : mid399.Contains (rootPhase 398) := root398_contains
lemma root399_contains : root399.Contains (rootPhase 399) := by
  have hh := CBox.mul_contains mid399_contains root1_contains (c:=root399) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root400_contains : root400.Contains (rootPhase 400) := by
  have hh := CBox.mul_contains root200_contains root200_contains (c:=root400) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid401_contains : mid401.Contains (rootPhase 400) := root400_contains
lemma root401_contains : root401.Contains (rootPhase 401) := by
  have hh := CBox.mul_contains mid401_contains root1_contains (c:=root401) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root402_contains : root402.Contains (rootPhase 402) := by
  have hh := CBox.mul_contains root201_contains root201_contains (c:=root402) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid403_contains : mid403.Contains (rootPhase 402) := root402_contains
lemma root403_contains : root403.Contains (rootPhase 403) := by
  have hh := CBox.mul_contains mid403_contains root1_contains (c:=root403) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root404_contains : root404.Contains (rootPhase 404) := by
  have hh := CBox.mul_contains root202_contains root202_contains (c:=root404) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid405_contains : mid405.Contains (rootPhase 404) := root404_contains
lemma root405_contains : root405.Contains (rootPhase 405) := by
  have hh := CBox.mul_contains mid405_contains root1_contains (c:=root405) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root406_contains : root406.Contains (rootPhase 406) := by
  have hh := CBox.mul_contains root203_contains root203_contains (c:=root406) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid407_contains : mid407.Contains (rootPhase 406) := root406_contains
lemma root407_contains : root407.Contains (rootPhase 407) := by
  have hh := CBox.mul_contains mid407_contains root1_contains (c:=root407) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root408_contains : root408.Contains (rootPhase 408) := by
  have hh := CBox.mul_contains root204_contains root204_contains (c:=root408) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid409_contains : mid409.Contains (rootPhase 408) := root408_contains
lemma root409_contains : root409.Contains (rootPhase 409) := by
  have hh := CBox.mul_contains mid409_contains root1_contains (c:=root409) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root410_contains : root410.Contains (rootPhase 410) := by
  have hh := CBox.mul_contains root205_contains root205_contains (c:=root410) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid411_contains : mid411.Contains (rootPhase 410) := root410_contains
lemma root411_contains : root411.Contains (rootPhase 411) := by
  have hh := CBox.mul_contains mid411_contains root1_contains (c:=root411) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root412_contains : root412.Contains (rootPhase 412) := by
  have hh := CBox.mul_contains root206_contains root206_contains (c:=root412) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid413_contains : mid413.Contains (rootPhase 412) := root412_contains
lemma root413_contains : root413.Contains (rootPhase 413) := by
  have hh := CBox.mul_contains mid413_contains root1_contains (c:=root413) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root414_contains : root414.Contains (rootPhase 414) := by
  have hh := CBox.mul_contains root207_contains root207_contains (c:=root414) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid415_contains : mid415.Contains (rootPhase 414) := root414_contains
lemma root415_contains : root415.Contains (rootPhase 415) := by
  have hh := CBox.mul_contains mid415_contains root1_contains (c:=root415) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root416_contains : root416.Contains (rootPhase 416) := by
  have hh := CBox.mul_contains root208_contains root208_contains (c:=root416) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid417_contains : mid417.Contains (rootPhase 416) := root416_contains
lemma root417_contains : root417.Contains (rootPhase 417) := by
  have hh := CBox.mul_contains mid417_contains root1_contains (c:=root417) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root418_contains : root418.Contains (rootPhase 418) := by
  have hh := CBox.mul_contains root209_contains root209_contains (c:=root418) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid419_contains : mid419.Contains (rootPhase 418) := root418_contains
lemma root419_contains : root419.Contains (rootPhase 419) := by
  have hh := CBox.mul_contains mid419_contains root1_contains (c:=root419) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root420_contains : root420.Contains (rootPhase 420) := by
  have hh := CBox.mul_contains root210_contains root210_contains (c:=root420) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid421_contains : mid421.Contains (rootPhase 420) := root420_contains
lemma root421_contains : root421.Contains (rootPhase 421) := by
  have hh := CBox.mul_contains mid421_contains root1_contains (c:=root421) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root422_contains : root422.Contains (rootPhase 422) := by
  have hh := CBox.mul_contains root211_contains root211_contains (c:=root422) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid423_contains : mid423.Contains (rootPhase 422) := root422_contains
lemma root423_contains : root423.Contains (rootPhase 423) := by
  have hh := CBox.mul_contains mid423_contains root1_contains (c:=root423) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root424_contains : root424.Contains (rootPhase 424) := by
  have hh := CBox.mul_contains root212_contains root212_contains (c:=root424) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid425_contains : mid425.Contains (rootPhase 424) := root424_contains
lemma root425_contains : root425.Contains (rootPhase 425) := by
  have hh := CBox.mul_contains mid425_contains root1_contains (c:=root425) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root426_contains : root426.Contains (rootPhase 426) := by
  have hh := CBox.mul_contains root213_contains root213_contains (c:=root426) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid427_contains : mid427.Contains (rootPhase 426) := root426_contains
lemma root427_contains : root427.Contains (rootPhase 427) := by
  have hh := CBox.mul_contains mid427_contains root1_contains (c:=root427) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root428_contains : root428.Contains (rootPhase 428) := by
  have hh := CBox.mul_contains root214_contains root214_contains (c:=root428) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid429_contains : mid429.Contains (rootPhase 428) := root428_contains
lemma root429_contains : root429.Contains (rootPhase 429) := by
  have hh := CBox.mul_contains mid429_contains root1_contains (c:=root429) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root430_contains : root430.Contains (rootPhase 430) := by
  have hh := CBox.mul_contains root215_contains root215_contains (c:=root430) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid431_contains : mid431.Contains (rootPhase 430) := root430_contains
lemma root431_contains : root431.Contains (rootPhase 431) := by
  have hh := CBox.mul_contains mid431_contains root1_contains (c:=root431) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root432_contains : root432.Contains (rootPhase 432) := by
  have hh := CBox.mul_contains root216_contains root216_contains (c:=root432) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid433_contains : mid433.Contains (rootPhase 432) := root432_contains
lemma root433_contains : root433.Contains (rootPhase 433) := by
  have hh := CBox.mul_contains mid433_contains root1_contains (c:=root433) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root434_contains : root434.Contains (rootPhase 434) := by
  have hh := CBox.mul_contains root217_contains root217_contains (c:=root434) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid435_contains : mid435.Contains (rootPhase 434) := root434_contains
lemma root435_contains : root435.Contains (rootPhase 435) := by
  have hh := CBox.mul_contains mid435_contains root1_contains (c:=root435) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root436_contains : root436.Contains (rootPhase 436) := by
  have hh := CBox.mul_contains root218_contains root218_contains (c:=root436) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid437_contains : mid437.Contains (rootPhase 436) := root436_contains
lemma root437_contains : root437.Contains (rootPhase 437) := by
  have hh := CBox.mul_contains mid437_contains root1_contains (c:=root437) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root438_contains : root438.Contains (rootPhase 438) := by
  have hh := CBox.mul_contains root219_contains root219_contains (c:=root438) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid439_contains : mid439.Contains (rootPhase 438) := root438_contains
lemma root439_contains : root439.Contains (rootPhase 439) := by
  have hh := CBox.mul_contains mid439_contains root1_contains (c:=root439) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root440_contains : root440.Contains (rootPhase 440) := by
  have hh := CBox.mul_contains root220_contains root220_contains (c:=root440) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid441_contains : mid441.Contains (rootPhase 440) := root440_contains
lemma root441_contains : root441.Contains (rootPhase 441) := by
  have hh := CBox.mul_contains mid441_contains root1_contains (c:=root441) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root442_contains : root442.Contains (rootPhase 442) := by
  have hh := CBox.mul_contains root221_contains root221_contains (c:=root442) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid443_contains : mid443.Contains (rootPhase 442) := root442_contains
lemma root443_contains : root443.Contains (rootPhase 443) := by
  have hh := CBox.mul_contains mid443_contains root1_contains (c:=root443) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root444_contains : root444.Contains (rootPhase 444) := by
  have hh := CBox.mul_contains root222_contains root222_contains (c:=root444) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid445_contains : mid445.Contains (rootPhase 444) := root444_contains
lemma root445_contains : root445.Contains (rootPhase 445) := by
  have hh := CBox.mul_contains mid445_contains root1_contains (c:=root445) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root446_contains : root446.Contains (rootPhase 446) := by
  have hh := CBox.mul_contains root223_contains root223_contains (c:=root446) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid447_contains : mid447.Contains (rootPhase 446) := root446_contains
lemma root447_contains : root447.Contains (rootPhase 447) := by
  have hh := CBox.mul_contains mid447_contains root1_contains (c:=root447) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root448_contains : root448.Contains (rootPhase 448) := by
  have hh := CBox.mul_contains root224_contains root224_contains (c:=root448) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid449_contains : mid449.Contains (rootPhase 448) := root448_contains
lemma root449_contains : root449.Contains (rootPhase 449) := by
  have hh := CBox.mul_contains mid449_contains root1_contains (c:=root449) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root450_contains : root450.Contains (rootPhase 450) := by
  have hh := CBox.mul_contains root225_contains root225_contains (c:=root450) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid451_contains : mid451.Contains (rootPhase 450) := root450_contains
lemma root451_contains : root451.Contains (rootPhase 451) := by
  have hh := CBox.mul_contains mid451_contains root1_contains (c:=root451) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root452_contains : root452.Contains (rootPhase 452) := by
  have hh := CBox.mul_contains root226_contains root226_contains (c:=root452) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid453_contains : mid453.Contains (rootPhase 452) := root452_contains
lemma root453_contains : root453.Contains (rootPhase 453) := by
  have hh := CBox.mul_contains mid453_contains root1_contains (c:=root453) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root454_contains : root454.Contains (rootPhase 454) := by
  have hh := CBox.mul_contains root227_contains root227_contains (c:=root454) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid455_contains : mid455.Contains (rootPhase 454) := root454_contains
lemma root455_contains : root455.Contains (rootPhase 455) := by
  have hh := CBox.mul_contains mid455_contains root1_contains (c:=root455) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root456_contains : root456.Contains (rootPhase 456) := by
  have hh := CBox.mul_contains root228_contains root228_contains (c:=root456) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid457_contains : mid457.Contains (rootPhase 456) := root456_contains
lemma root457_contains : root457.Contains (rootPhase 457) := by
  have hh := CBox.mul_contains mid457_contains root1_contains (c:=root457) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root458_contains : root458.Contains (rootPhase 458) := by
  have hh := CBox.mul_contains root229_contains root229_contains (c:=root458) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid459_contains : mid459.Contains (rootPhase 458) := root458_contains
lemma root459_contains : root459.Contains (rootPhase 459) := by
  have hh := CBox.mul_contains mid459_contains root1_contains (c:=root459) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root460_contains : root460.Contains (rootPhase 460) := by
  have hh := CBox.mul_contains root230_contains root230_contains (c:=root460) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid461_contains : mid461.Contains (rootPhase 460) := root460_contains
lemma root461_contains : root461.Contains (rootPhase 461) := by
  have hh := CBox.mul_contains mid461_contains root1_contains (c:=root461) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root462_contains : root462.Contains (rootPhase 462) := by
  have hh := CBox.mul_contains root231_contains root231_contains (c:=root462) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid463_contains : mid463.Contains (rootPhase 462) := root462_contains
lemma root463_contains : root463.Contains (rootPhase 463) := by
  have hh := CBox.mul_contains mid463_contains root1_contains (c:=root463) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root464_contains : root464.Contains (rootPhase 464) := by
  have hh := CBox.mul_contains root232_contains root232_contains (c:=root464) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid465_contains : mid465.Contains (rootPhase 464) := root464_contains
lemma root465_contains : root465.Contains (rootPhase 465) := by
  have hh := CBox.mul_contains mid465_contains root1_contains (c:=root465) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root466_contains : root466.Contains (rootPhase 466) := by
  have hh := CBox.mul_contains root233_contains root233_contains (c:=root466) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid467_contains : mid467.Contains (rootPhase 466) := root466_contains
lemma root467_contains : root467.Contains (rootPhase 467) := by
  have hh := CBox.mul_contains mid467_contains root1_contains (c:=root467) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root468_contains : root468.Contains (rootPhase 468) := by
  have hh := CBox.mul_contains root234_contains root234_contains (c:=root468) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid469_contains : mid469.Contains (rootPhase 468) := root468_contains
lemma root469_contains : root469.Contains (rootPhase 469) := by
  have hh := CBox.mul_contains mid469_contains root1_contains (c:=root469) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root470_contains : root470.Contains (rootPhase 470) := by
  have hh := CBox.mul_contains root235_contains root235_contains (c:=root470) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid471_contains : mid471.Contains (rootPhase 470) := root470_contains
lemma root471_contains : root471.Contains (rootPhase 471) := by
  have hh := CBox.mul_contains mid471_contains root1_contains (c:=root471) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root472_contains : root472.Contains (rootPhase 472) := by
  have hh := CBox.mul_contains root236_contains root236_contains (c:=root472) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid473_contains : mid473.Contains (rootPhase 472) := root472_contains
lemma root473_contains : root473.Contains (rootPhase 473) := by
  have hh := CBox.mul_contains mid473_contains root1_contains (c:=root473) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root474_contains : root474.Contains (rootPhase 474) := by
  have hh := CBox.mul_contains root237_contains root237_contains (c:=root474) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid475_contains : mid475.Contains (rootPhase 474) := root474_contains
lemma root475_contains : root475.Contains (rootPhase 475) := by
  have hh := CBox.mul_contains mid475_contains root1_contains (c:=root475) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root476_contains : root476.Contains (rootPhase 476) := by
  have hh := CBox.mul_contains root238_contains root238_contains (c:=root476) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid477_contains : mid477.Contains (rootPhase 476) := root476_contains
lemma root477_contains : root477.Contains (rootPhase 477) := by
  have hh := CBox.mul_contains mid477_contains root1_contains (c:=root477) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root478_contains : root478.Contains (rootPhase 478) := by
  have hh := CBox.mul_contains root239_contains root239_contains (c:=root478) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid479_contains : mid479.Contains (rootPhase 478) := root478_contains
lemma root479_contains : root479.Contains (rootPhase 479) := by
  have hh := CBox.mul_contains mid479_contains root1_contains (c:=root479) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root480_contains : root480.Contains (rootPhase 480) := by
  have hh := CBox.mul_contains root240_contains root240_contains (c:=root480) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid481_contains : mid481.Contains (rootPhase 480) := root480_contains
lemma root481_contains : root481.Contains (rootPhase 481) := by
  have hh := CBox.mul_contains mid481_contains root1_contains (c:=root481) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root482_contains : root482.Contains (rootPhase 482) := by
  have hh := CBox.mul_contains root241_contains root241_contains (c:=root482) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid483_contains : mid483.Contains (rootPhase 482) := root482_contains
lemma root483_contains : root483.Contains (rootPhase 483) := by
  have hh := CBox.mul_contains mid483_contains root1_contains (c:=root483) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root484_contains : root484.Contains (rootPhase 484) := by
  have hh := CBox.mul_contains root242_contains root242_contains (c:=root484) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid485_contains : mid485.Contains (rootPhase 484) := root484_contains
lemma root485_contains : root485.Contains (rootPhase 485) := by
  have hh := CBox.mul_contains mid485_contains root1_contains (c:=root485) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root486_contains : root486.Contains (rootPhase 486) := by
  have hh := CBox.mul_contains root243_contains root243_contains (c:=root486) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid487_contains : mid487.Contains (rootPhase 486) := root486_contains
lemma root487_contains : root487.Contains (rootPhase 487) := by
  have hh := CBox.mul_contains mid487_contains root1_contains (c:=root487) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root488_contains : root488.Contains (rootPhase 488) := by
  have hh := CBox.mul_contains root244_contains root244_contains (c:=root488) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid489_contains : mid489.Contains (rootPhase 488) := root488_contains
lemma root489_contains : root489.Contains (rootPhase 489) := by
  have hh := CBox.mul_contains mid489_contains root1_contains (c:=root489) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root490_contains : root490.Contains (rootPhase 490) := by
  have hh := CBox.mul_contains root245_contains root245_contains (c:=root490) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid491_contains : mid491.Contains (rootPhase 490) := root490_contains
lemma root491_contains : root491.Contains (rootPhase 491) := by
  have hh := CBox.mul_contains mid491_contains root1_contains (c:=root491) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root492_contains : root492.Contains (rootPhase 492) := by
  have hh := CBox.mul_contains root246_contains root246_contains (c:=root492) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid493_contains : mid493.Contains (rootPhase 492) := root492_contains
lemma root493_contains : root493.Contains (rootPhase 493) := by
  have hh := CBox.mul_contains mid493_contains root1_contains (c:=root493) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root494_contains : root494.Contains (rootPhase 494) := by
  have hh := CBox.mul_contains root247_contains root247_contains (c:=root494) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid495_contains : mid495.Contains (rootPhase 494) := root494_contains
lemma root495_contains : root495.Contains (rootPhase 495) := by
  have hh := CBox.mul_contains mid495_contains root1_contains (c:=root495) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root496_contains : root496.Contains (rootPhase 496) := by
  have hh := CBox.mul_contains root248_contains root248_contains (c:=root496) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid497_contains : mid497.Contains (rootPhase 496) := root496_contains
lemma root497_contains : root497.Contains (rootPhase 497) := by
  have hh := CBox.mul_contains mid497_contains root1_contains (c:=root497) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root498_contains : root498.Contains (rootPhase 498) := by
  have hh := CBox.mul_contains root249_contains root249_contains (c:=root498) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid499_contains : mid499.Contains (rootPhase 498) := root498_contains
lemma root499_contains : root499.Contains (rootPhase 499) := by
  have hh := CBox.mul_contains mid499_contains root1_contains (c:=root499) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root500_contains : root500.Contains (rootPhase 500) := by
  have hh := CBox.mul_contains root250_contains root250_contains (c:=root500) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid501_contains : mid501.Contains (rootPhase 500) := root500_contains
lemma root501_contains : root501.Contains (rootPhase 501) := by
  have hh := CBox.mul_contains mid501_contains root1_contains (c:=root501) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root502_contains : root502.Contains (rootPhase 502) := by
  have hh := CBox.mul_contains root251_contains root251_contains (c:=root502) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid503_contains : mid503.Contains (rootPhase 502) := root502_contains
lemma root503_contains : root503.Contains (rootPhase 503) := by
  have hh := CBox.mul_contains mid503_contains root1_contains (c:=root503) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root504_contains : root504.Contains (rootPhase 504) := by
  have hh := CBox.mul_contains root252_contains root252_contains (c:=root504) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid505_contains : mid505.Contains (rootPhase 504) := root504_contains
lemma root505_contains : root505.Contains (rootPhase 505) := by
  have hh := CBox.mul_contains mid505_contains root1_contains (c:=root505) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root506_contains : root506.Contains (rootPhase 506) := by
  have hh := CBox.mul_contains root253_contains root253_contains (c:=root506) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid507_contains : mid507.Contains (rootPhase 506) := root506_contains
lemma root507_contains : root507.Contains (rootPhase 507) := by
  have hh := CBox.mul_contains mid507_contains root1_contains (c:=root507) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root508_contains : root508.Contains (rootPhase 508) := by
  have hh := CBox.mul_contains root254_contains root254_contains (c:=root508) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid509_contains : mid509.Contains (rootPhase 508) := root508_contains
lemma root509_contains : root509.Contains (rootPhase 509) := by
  have hh := CBox.mul_contains mid509_contains root1_contains (c:=root509) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root510_contains : root510.Contains (rootPhase 510) := by
  have hh := CBox.mul_contains root255_contains root255_contains (c:=root510) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid511_contains : mid511.Contains (rootPhase 510) := root510_contains
lemma root511_contains : root511.Contains (rootPhase 511) := by
  have hh := CBox.mul_contains mid511_contains root1_contains (c:=root511) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root544_contains : root544.Contains (rootPhase 544) := by
  have hh := CBox.mul_contains root272_contains root272_contains (c:=root544) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid545_contains : mid545.Contains (rootPhase 544) := root544_contains
lemma root545_contains : root545.Contains (rootPhase 545) := by
  have hh := CBox.mul_contains mid545_contains root1_contains (c:=root545) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root546_contains : root546.Contains (rootPhase 546) := by
  have hh := CBox.mul_contains root273_contains root273_contains (c:=root546) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid547_contains : mid547.Contains (rootPhase 546) := root546_contains
lemma root547_contains : root547.Contains (rootPhase 547) := by
  have hh := CBox.mul_contains mid547_contains root1_contains (c:=root547) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root548_contains : root548.Contains (rootPhase 548) := by
  have hh := CBox.mul_contains root274_contains root274_contains (c:=root548) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid549_contains : mid549.Contains (rootPhase 548) := root548_contains
lemma root549_contains : root549.Contains (rootPhase 549) := by
  have hh := CBox.mul_contains mid549_contains root1_contains (c:=root549) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root550_contains : root550.Contains (rootPhase 550) := by
  have hh := CBox.mul_contains root275_contains root275_contains (c:=root550) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid551_contains : mid551.Contains (rootPhase 550) := root550_contains
lemma root551_contains : root551.Contains (rootPhase 551) := by
  have hh := CBox.mul_contains mid551_contains root1_contains (c:=root551) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root552_contains : root552.Contains (rootPhase 552) := by
  have hh := CBox.mul_contains root276_contains root276_contains (c:=root552) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid553_contains : mid553.Contains (rootPhase 552) := root552_contains
lemma root553_contains : root553.Contains (rootPhase 553) := by
  have hh := CBox.mul_contains mid553_contains root1_contains (c:=root553) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root554_contains : root554.Contains (rootPhase 554) := by
  have hh := CBox.mul_contains root277_contains root277_contains (c:=root554) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid555_contains : mid555.Contains (rootPhase 554) := root554_contains
lemma root555_contains : root555.Contains (rootPhase 555) := by
  have hh := CBox.mul_contains mid555_contains root1_contains (c:=root555) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root556_contains : root556.Contains (rootPhase 556) := by
  have hh := CBox.mul_contains root278_contains root278_contains (c:=root556) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid557_contains : mid557.Contains (rootPhase 556) := root556_contains
lemma root557_contains : root557.Contains (rootPhase 557) := by
  have hh := CBox.mul_contains mid557_contains root1_contains (c:=root557) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root558_contains : root558.Contains (rootPhase 558) := by
  have hh := CBox.mul_contains root279_contains root279_contains (c:=root558) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid559_contains : mid559.Contains (rootPhase 558) := root558_contains
lemma root559_contains : root559.Contains (rootPhase 559) := by
  have hh := CBox.mul_contains mid559_contains root1_contains (c:=root559) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root560_contains : root560.Contains (rootPhase 560) := by
  have hh := CBox.mul_contains root280_contains root280_contains (c:=root560) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid561_contains : mid561.Contains (rootPhase 560) := root560_contains
lemma root561_contains : root561.Contains (rootPhase 561) := by
  have hh := CBox.mul_contains mid561_contains root1_contains (c:=root561) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root562_contains : root562.Contains (rootPhase 562) := by
  have hh := CBox.mul_contains root281_contains root281_contains (c:=root562) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid563_contains : mid563.Contains (rootPhase 562) := root562_contains
lemma root563_contains : root563.Contains (rootPhase 563) := by
  have hh := CBox.mul_contains mid563_contains root1_contains (c:=root563) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root564_contains : root564.Contains (rootPhase 564) := by
  have hh := CBox.mul_contains root282_contains root282_contains (c:=root564) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid565_contains : mid565.Contains (rootPhase 564) := root564_contains
lemma root565_contains : root565.Contains (rootPhase 565) := by
  have hh := CBox.mul_contains mid565_contains root1_contains (c:=root565) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root566_contains : root566.Contains (rootPhase 566) := by
  have hh := CBox.mul_contains root283_contains root283_contains (c:=root566) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid567_contains : mid567.Contains (rootPhase 566) := root566_contains
lemma root567_contains : root567.Contains (rootPhase 567) := by
  have hh := CBox.mul_contains mid567_contains root1_contains (c:=root567) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root568_contains : root568.Contains (rootPhase 568) := by
  have hh := CBox.mul_contains root284_contains root284_contains (c:=root568) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid569_contains : mid569.Contains (rootPhase 568) := root568_contains
lemma root569_contains : root569.Contains (rootPhase 569) := by
  have hh := CBox.mul_contains mid569_contains root1_contains (c:=root569) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root570_contains : root570.Contains (rootPhase 570) := by
  have hh := CBox.mul_contains root285_contains root285_contains (c:=root570) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid571_contains : mid571.Contains (rootPhase 570) := root570_contains
lemma root571_contains : root571.Contains (rootPhase 571) := by
  have hh := CBox.mul_contains mid571_contains root1_contains (c:=root571) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root572_contains : root572.Contains (rootPhase 572) := by
  have hh := CBox.mul_contains root286_contains root286_contains (c:=root572) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid573_contains : mid573.Contains (rootPhase 572) := root572_contains
lemma root573_contains : root573.Contains (rootPhase 573) := by
  have hh := CBox.mul_contains mid573_contains root1_contains (c:=root573) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root574_contains : root574.Contains (rootPhase 574) := by
  have hh := CBox.mul_contains root287_contains root287_contains (c:=root574) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid575_contains : mid575.Contains (rootPhase 574) := root574_contains
lemma root575_contains : root575.Contains (rootPhase 575) := by
  have hh := CBox.mul_contains mid575_contains root1_contains (c:=root575) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root576_contains : root576.Contains (rootPhase 576) := by
  have hh := CBox.mul_contains root288_contains root288_contains (c:=root576) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid577_contains : mid577.Contains (rootPhase 576) := root576_contains
lemma root577_contains : root577.Contains (rootPhase 577) := by
  have hh := CBox.mul_contains mid577_contains root1_contains (c:=root577) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root578_contains : root578.Contains (rootPhase 578) := by
  have hh := CBox.mul_contains root289_contains root289_contains (c:=root578) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid579_contains : mid579.Contains (rootPhase 578) := root578_contains
lemma root579_contains : root579.Contains (rootPhase 579) := by
  have hh := CBox.mul_contains mid579_contains root1_contains (c:=root579) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root580_contains : root580.Contains (rootPhase 580) := by
  have hh := CBox.mul_contains root290_contains root290_contains (c:=root580) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid581_contains : mid581.Contains (rootPhase 580) := root580_contains
lemma root581_contains : root581.Contains (rootPhase 581) := by
  have hh := CBox.mul_contains mid581_contains root1_contains (c:=root581) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root582_contains : root582.Contains (rootPhase 582) := by
  have hh := CBox.mul_contains root291_contains root291_contains (c:=root582) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid583_contains : mid583.Contains (rootPhase 582) := root582_contains
lemma root583_contains : root583.Contains (rootPhase 583) := by
  have hh := CBox.mul_contains mid583_contains root1_contains (c:=root583) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root584_contains : root584.Contains (rootPhase 584) := by
  have hh := CBox.mul_contains root292_contains root292_contains (c:=root584) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid585_contains : mid585.Contains (rootPhase 584) := root584_contains
lemma root585_contains : root585.Contains (rootPhase 585) := by
  have hh := CBox.mul_contains mid585_contains root1_contains (c:=root585) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root586_contains : root586.Contains (rootPhase 586) := by
  have hh := CBox.mul_contains root293_contains root293_contains (c:=root586) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid587_contains : mid587.Contains (rootPhase 586) := root586_contains
lemma root587_contains : root587.Contains (rootPhase 587) := by
  have hh := CBox.mul_contains mid587_contains root1_contains (c:=root587) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root588_contains : root588.Contains (rootPhase 588) := by
  have hh := CBox.mul_contains root294_contains root294_contains (c:=root588) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid589_contains : mid589.Contains (rootPhase 588) := root588_contains
lemma root589_contains : root589.Contains (rootPhase 589) := by
  have hh := CBox.mul_contains mid589_contains root1_contains (c:=root589) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root590_contains : root590.Contains (rootPhase 590) := by
  have hh := CBox.mul_contains root295_contains root295_contains (c:=root590) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid591_contains : mid591.Contains (rootPhase 590) := root590_contains
lemma root591_contains : root591.Contains (rootPhase 591) := by
  have hh := CBox.mul_contains mid591_contains root1_contains (c:=root591) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root592_contains : root592.Contains (rootPhase 592) := by
  have hh := CBox.mul_contains root296_contains root296_contains (c:=root592) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid593_contains : mid593.Contains (rootPhase 592) := root592_contains
lemma root593_contains : root593.Contains (rootPhase 593) := by
  have hh := CBox.mul_contains mid593_contains root1_contains (c:=root593) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root594_contains : root594.Contains (rootPhase 594) := by
  have hh := CBox.mul_contains root297_contains root297_contains (c:=root594) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid595_contains : mid595.Contains (rootPhase 594) := root594_contains
lemma root595_contains : root595.Contains (rootPhase 595) := by
  have hh := CBox.mul_contains mid595_contains root1_contains (c:=root595) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root596_contains : root596.Contains (rootPhase 596) := by
  have hh := CBox.mul_contains root298_contains root298_contains (c:=root596) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid597_contains : mid597.Contains (rootPhase 596) := root596_contains
lemma root597_contains : root597.Contains (rootPhase 597) := by
  have hh := CBox.mul_contains mid597_contains root1_contains (c:=root597) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root598_contains : root598.Contains (rootPhase 598) := by
  have hh := CBox.mul_contains root299_contains root299_contains (c:=root598) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid599_contains : mid599.Contains (rootPhase 598) := root598_contains
lemma root599_contains : root599.Contains (rootPhase 599) := by
  have hh := CBox.mul_contains mid599_contains root1_contains (c:=root599) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root600_contains : root600.Contains (rootPhase 600) := by
  have hh := CBox.mul_contains root300_contains root300_contains (c:=root600) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid601_contains : mid601.Contains (rootPhase 600) := root600_contains
lemma root601_contains : root601.Contains (rootPhase 601) := by
  have hh := CBox.mul_contains mid601_contains root1_contains (c:=root601) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root602_contains : root602.Contains (rootPhase 602) := by
  have hh := CBox.mul_contains root301_contains root301_contains (c:=root602) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid603_contains : mid603.Contains (rootPhase 602) := root602_contains
lemma root603_contains : root603.Contains (rootPhase 603) := by
  have hh := CBox.mul_contains mid603_contains root1_contains (c:=root603) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root604_contains : root604.Contains (rootPhase 604) := by
  have hh := CBox.mul_contains root302_contains root302_contains (c:=root604) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid605_contains : mid605.Contains (rootPhase 604) := root604_contains
lemma root605_contains : root605.Contains (rootPhase 605) := by
  have hh := CBox.mul_contains mid605_contains root1_contains (c:=root605) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root606_contains : root606.Contains (rootPhase 606) := by
  have hh := CBox.mul_contains root303_contains root303_contains (c:=root606) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid607_contains : mid607.Contains (rootPhase 606) := root606_contains
lemma root607_contains : root607.Contains (rootPhase 607) := by
  have hh := CBox.mul_contains mid607_contains root1_contains (c:=root607) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root608_contains : root608.Contains (rootPhase 608) := by
  have hh := CBox.mul_contains root304_contains root304_contains (c:=root608) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid609_contains : mid609.Contains (rootPhase 608) := root608_contains
lemma root609_contains : root609.Contains (rootPhase 609) := by
  have hh := CBox.mul_contains mid609_contains root1_contains (c:=root609) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root610_contains : root610.Contains (rootPhase 610) := by
  have hh := CBox.mul_contains root305_contains root305_contains (c:=root610) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid611_contains : mid611.Contains (rootPhase 610) := root610_contains
lemma root611_contains : root611.Contains (rootPhase 611) := by
  have hh := CBox.mul_contains mid611_contains root1_contains (c:=root611) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root612_contains : root612.Contains (rootPhase 612) := by
  have hh := CBox.mul_contains root306_contains root306_contains (c:=root612) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid613_contains : mid613.Contains (rootPhase 612) := root612_contains
lemma root613_contains : root613.Contains (rootPhase 613) := by
  have hh := CBox.mul_contains mid613_contains root1_contains (c:=root613) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root614_contains : root614.Contains (rootPhase 614) := by
  have hh := CBox.mul_contains root307_contains root307_contains (c:=root614) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid615_contains : mid615.Contains (rootPhase 614) := root614_contains
lemma root615_contains : root615.Contains (rootPhase 615) := by
  have hh := CBox.mul_contains mid615_contains root1_contains (c:=root615) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root616_contains : root616.Contains (rootPhase 616) := by
  have hh := CBox.mul_contains root308_contains root308_contains (c:=root616) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid617_contains : mid617.Contains (rootPhase 616) := root616_contains
lemma root617_contains : root617.Contains (rootPhase 617) := by
  have hh := CBox.mul_contains mid617_contains root1_contains (c:=root617) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root618_contains : root618.Contains (rootPhase 618) := by
  have hh := CBox.mul_contains root309_contains root309_contains (c:=root618) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid619_contains : mid619.Contains (rootPhase 618) := root618_contains
lemma root619_contains : root619.Contains (rootPhase 619) := by
  have hh := CBox.mul_contains mid619_contains root1_contains (c:=root619) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root620_contains : root620.Contains (rootPhase 620) := by
  have hh := CBox.mul_contains root310_contains root310_contains (c:=root620) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid621_contains : mid621.Contains (rootPhase 620) := root620_contains
lemma root621_contains : root621.Contains (rootPhase 621) := by
  have hh := CBox.mul_contains mid621_contains root1_contains (c:=root621) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root622_contains : root622.Contains (rootPhase 622) := by
  have hh := CBox.mul_contains root311_contains root311_contains (c:=root622) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid623_contains : mid623.Contains (rootPhase 622) := root622_contains
lemma root623_contains : root623.Contains (rootPhase 623) := by
  have hh := CBox.mul_contains mid623_contains root1_contains (c:=root623) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root624_contains : root624.Contains (rootPhase 624) := by
  have hh := CBox.mul_contains root312_contains root312_contains (c:=root624) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid625_contains : mid625.Contains (rootPhase 624) := root624_contains
lemma root625_contains : root625.Contains (rootPhase 625) := by
  have hh := CBox.mul_contains mid625_contains root1_contains (c:=root625) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root626_contains : root626.Contains (rootPhase 626) := by
  have hh := CBox.mul_contains root313_contains root313_contains (c:=root626) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid627_contains : mid627.Contains (rootPhase 626) := root626_contains
lemma root627_contains : root627.Contains (rootPhase 627) := by
  have hh := CBox.mul_contains mid627_contains root1_contains (c:=root627) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root628_contains : root628.Contains (rootPhase 628) := by
  have hh := CBox.mul_contains root314_contains root314_contains (c:=root628) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid629_contains : mid629.Contains (rootPhase 628) := root628_contains
lemma root629_contains : root629.Contains (rootPhase 629) := by
  have hh := CBox.mul_contains mid629_contains root1_contains (c:=root629) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root630_contains : root630.Contains (rootPhase 630) := by
  have hh := CBox.mul_contains root315_contains root315_contains (c:=root630) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid631_contains : mid631.Contains (rootPhase 630) := root630_contains
lemma root631_contains : root631.Contains (rootPhase 631) := by
  have hh := CBox.mul_contains mid631_contains root1_contains (c:=root631) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root632_contains : root632.Contains (rootPhase 632) := by
  have hh := CBox.mul_contains root316_contains root316_contains (c:=root632) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid633_contains : mid633.Contains (rootPhase 632) := root632_contains
lemma root633_contains : root633.Contains (rootPhase 633) := by
  have hh := CBox.mul_contains mid633_contains root1_contains (c:=root633) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root634_contains : root634.Contains (rootPhase 634) := by
  have hh := CBox.mul_contains root317_contains root317_contains (c:=root634) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid635_contains : mid635.Contains (rootPhase 634) := root634_contains
lemma root635_contains : root635.Contains (rootPhase 635) := by
  have hh := CBox.mul_contains mid635_contains root1_contains (c:=root635) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root636_contains : root636.Contains (rootPhase 636) := by
  have hh := CBox.mul_contains root318_contains root318_contains (c:=root636) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid637_contains : mid637.Contains (rootPhase 636) := root636_contains
lemma root637_contains : root637.Contains (rootPhase 637) := by
  have hh := CBox.mul_contains mid637_contains root1_contains (c:=root637) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root638_contains : root638.Contains (rootPhase 638) := by
  have hh := CBox.mul_contains root319_contains root319_contains (c:=root638) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid639_contains : mid639.Contains (rootPhase 638) := root638_contains
lemma root639_contains : root639.Contains (rootPhase 639) := by
  have hh := CBox.mul_contains mid639_contains root1_contains (c:=root639) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root646_contains : root646.Contains (rootPhase 646) := by
  have hh := CBox.mul_contains root323_contains root323_contains (c:=root646) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid647_contains : mid647.Contains (rootPhase 646) := root646_contains
lemma root647_contains : root647.Contains (rootPhase 647) := by
  have hh := CBox.mul_contains mid647_contains root1_contains (c:=root647) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root650_contains : root650.Contains (rootPhase 650) := by
  have hh := CBox.mul_contains root325_contains root325_contains (c:=root650) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid651_contains : mid651.Contains (rootPhase 650) := root650_contains
lemma root651_contains : root651.Contains (rootPhase 651) := by
  have hh := CBox.mul_contains mid651_contains root1_contains (c:=root651) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root654_contains : root654.Contains (rootPhase 654) := by
  have hh := CBox.mul_contains root327_contains root327_contains (c:=root654) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid655_contains : mid655.Contains (rootPhase 654) := root654_contains
lemma root655_contains : root655.Contains (rootPhase 655) := by
  have hh := CBox.mul_contains mid655_contains root1_contains (c:=root655) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root656_contains : root656.Contains (rootPhase 656) := by
  have hh := CBox.mul_contains root328_contains root328_contains (c:=root656) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid657_contains : mid657.Contains (rootPhase 656) := root656_contains
lemma root657_contains : root657.Contains (rootPhase 657) := by
  have hh := CBox.mul_contains mid657_contains root1_contains (c:=root657) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root658_contains : root658.Contains (rootPhase 658) := by
  have hh := CBox.mul_contains root329_contains root329_contains (c:=root658) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid659_contains : mid659.Contains (rootPhase 658) := root658_contains
lemma root659_contains : root659.Contains (rootPhase 659) := by
  have hh := CBox.mul_contains mid659_contains root1_contains (c:=root659) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root660_contains : root660.Contains (rootPhase 660) := by
  have hh := CBox.mul_contains root330_contains root330_contains (c:=root660) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid661_contains : mid661.Contains (rootPhase 660) := root660_contains
lemma root661_contains : root661.Contains (rootPhase 661) := by
  have hh := CBox.mul_contains mid661_contains root1_contains (c:=root661) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root662_contains : root662.Contains (rootPhase 662) := by
  have hh := CBox.mul_contains root331_contains root331_contains (c:=root662) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid663_contains : mid663.Contains (rootPhase 662) := root662_contains
lemma root663_contains : root663.Contains (rootPhase 663) := by
  have hh := CBox.mul_contains mid663_contains root1_contains (c:=root663) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root664_contains : root664.Contains (rootPhase 664) := by
  have hh := CBox.mul_contains root332_contains root332_contains (c:=root664) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid665_contains : mid665.Contains (rootPhase 664) := root664_contains
lemma root665_contains : root665.Contains (rootPhase 665) := by
  have hh := CBox.mul_contains mid665_contains root1_contains (c:=root665) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root666_contains : root666.Contains (rootPhase 666) := by
  have hh := CBox.mul_contains root333_contains root333_contains (c:=root666) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid667_contains : mid667.Contains (rootPhase 666) := root666_contains
lemma root667_contains : root667.Contains (rootPhase 667) := by
  have hh := CBox.mul_contains mid667_contains root1_contains (c:=root667) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root668_contains : root668.Contains (rootPhase 668) := by
  have hh := CBox.mul_contains root334_contains root334_contains (c:=root668) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid669_contains : mid669.Contains (rootPhase 668) := root668_contains
lemma root669_contains : root669.Contains (rootPhase 669) := by
  have hh := CBox.mul_contains mid669_contains root1_contains (c:=root669) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root670_contains : root670.Contains (rootPhase 670) := by
  have hh := CBox.mul_contains root335_contains root335_contains (c:=root670) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid671_contains : mid671.Contains (rootPhase 670) := root670_contains
lemma root671_contains : root671.Contains (rootPhase 671) := by
  have hh := CBox.mul_contains mid671_contains root1_contains (c:=root671) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root672_contains : root672.Contains (rootPhase 672) := by
  have hh := CBox.mul_contains root336_contains root336_contains (c:=root672) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid673_contains : mid673.Contains (rootPhase 672) := root672_contains
lemma root673_contains : root673.Contains (rootPhase 673) := by
  have hh := CBox.mul_contains mid673_contains root1_contains (c:=root673) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root674_contains : root674.Contains (rootPhase 674) := by
  have hh := CBox.mul_contains root337_contains root337_contains (c:=root674) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid675_contains : mid675.Contains (rootPhase 674) := root674_contains
lemma root675_contains : root675.Contains (rootPhase 675) := by
  have hh := CBox.mul_contains mid675_contains root1_contains (c:=root675) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root676_contains : root676.Contains (rootPhase 676) := by
  have hh := CBox.mul_contains root338_contains root338_contains (c:=root676) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid677_contains : mid677.Contains (rootPhase 676) := root676_contains
lemma root677_contains : root677.Contains (rootPhase 677) := by
  have hh := CBox.mul_contains mid677_contains root1_contains (c:=root677) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root678_contains : root678.Contains (rootPhase 678) := by
  have hh := CBox.mul_contains root339_contains root339_contains (c:=root678) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid679_contains : mid679.Contains (rootPhase 678) := root678_contains
lemma root679_contains : root679.Contains (rootPhase 679) := by
  have hh := CBox.mul_contains mid679_contains root1_contains (c:=root679) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root680_contains : root680.Contains (rootPhase 680) := by
  have hh := CBox.mul_contains root340_contains root340_contains (c:=root680) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid681_contains : mid681.Contains (rootPhase 680) := root680_contains
lemma root681_contains : root681.Contains (rootPhase 681) := by
  have hh := CBox.mul_contains mid681_contains root1_contains (c:=root681) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root682_contains : root682.Contains (rootPhase 682) := by
  have hh := CBox.mul_contains root341_contains root341_contains (c:=root682) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid683_contains : mid683.Contains (rootPhase 682) := root682_contains
lemma root683_contains : root683.Contains (rootPhase 683) := by
  have hh := CBox.mul_contains mid683_contains root1_contains (c:=root683) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root684_contains : root684.Contains (rootPhase 684) := by
  have hh := CBox.mul_contains root342_contains root342_contains (c:=root684) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid685_contains : mid685.Contains (rootPhase 684) := root684_contains
lemma root685_contains : root685.Contains (rootPhase 685) := by
  have hh := CBox.mul_contains mid685_contains root1_contains (c:=root685) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root686_contains : root686.Contains (rootPhase 686) := by
  have hh := CBox.mul_contains root343_contains root343_contains (c:=root686) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid687_contains : mid687.Contains (rootPhase 686) := root686_contains
lemma root687_contains : root687.Contains (rootPhase 687) := by
  have hh := CBox.mul_contains mid687_contains root1_contains (c:=root687) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root688_contains : root688.Contains (rootPhase 688) := by
  have hh := CBox.mul_contains root344_contains root344_contains (c:=root688) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid689_contains : mid689.Contains (rootPhase 688) := root688_contains
lemma root689_contains : root689.Contains (rootPhase 689) := by
  have hh := CBox.mul_contains mid689_contains root1_contains (c:=root689) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root690_contains : root690.Contains (rootPhase 690) := by
  have hh := CBox.mul_contains root345_contains root345_contains (c:=root690) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid691_contains : mid691.Contains (rootPhase 690) := root690_contains
lemma root691_contains : root691.Contains (rootPhase 691) := by
  have hh := CBox.mul_contains mid691_contains root1_contains (c:=root691) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root692_contains : root692.Contains (rootPhase 692) := by
  have hh := CBox.mul_contains root346_contains root346_contains (c:=root692) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid693_contains : mid693.Contains (rootPhase 692) := root692_contains
lemma root693_contains : root693.Contains (rootPhase 693) := by
  have hh := CBox.mul_contains mid693_contains root1_contains (c:=root693) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root694_contains : root694.Contains (rootPhase 694) := by
  have hh := CBox.mul_contains root347_contains root347_contains (c:=root694) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid695_contains : mid695.Contains (rootPhase 694) := root694_contains
lemma root695_contains : root695.Contains (rootPhase 695) := by
  have hh := CBox.mul_contains mid695_contains root1_contains (c:=root695) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root696_contains : root696.Contains (rootPhase 696) := by
  have hh := CBox.mul_contains root348_contains root348_contains (c:=root696) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid697_contains : mid697.Contains (rootPhase 696) := root696_contains
lemma root697_contains : root697.Contains (rootPhase 697) := by
  have hh := CBox.mul_contains mid697_contains root1_contains (c:=root697) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root698_contains : root698.Contains (rootPhase 698) := by
  have hh := CBox.mul_contains root349_contains root349_contains (c:=root698) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid699_contains : mid699.Contains (rootPhase 698) := root698_contains
lemma root699_contains : root699.Contains (rootPhase 699) := by
  have hh := CBox.mul_contains mid699_contains root1_contains (c:=root699) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root700_contains : root700.Contains (rootPhase 700) := by
  have hh := CBox.mul_contains root350_contains root350_contains (c:=root700) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid701_contains : mid701.Contains (rootPhase 700) := root700_contains
lemma root701_contains : root701.Contains (rootPhase 701) := by
  have hh := CBox.mul_contains mid701_contains root1_contains (c:=root701) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root702_contains : root702.Contains (rootPhase 702) := by
  have hh := CBox.mul_contains root351_contains root351_contains (c:=root702) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid703_contains : mid703.Contains (rootPhase 702) := root702_contains
lemma root703_contains : root703.Contains (rootPhase 703) := by
  have hh := CBox.mul_contains mid703_contains root1_contains (c:=root703) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root704_contains : root704.Contains (rootPhase 704) := by
  have hh := CBox.mul_contains root352_contains root352_contains (c:=root704) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid705_contains : mid705.Contains (rootPhase 704) := root704_contains
lemma root705_contains : root705.Contains (rootPhase 705) := by
  have hh := CBox.mul_contains mid705_contains root1_contains (c:=root705) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root706_contains : root706.Contains (rootPhase 706) := by
  have hh := CBox.mul_contains root353_contains root353_contains (c:=root706) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid707_contains : mid707.Contains (rootPhase 706) := root706_contains
lemma root707_contains : root707.Contains (rootPhase 707) := by
  have hh := CBox.mul_contains mid707_contains root1_contains (c:=root707) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root708_contains : root708.Contains (rootPhase 708) := by
  have hh := CBox.mul_contains root354_contains root354_contains (c:=root708) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid709_contains : mid709.Contains (rootPhase 708) := root708_contains
lemma root709_contains : root709.Contains (rootPhase 709) := by
  have hh := CBox.mul_contains mid709_contains root1_contains (c:=root709) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root710_contains : root710.Contains (rootPhase 710) := by
  have hh := CBox.mul_contains root355_contains root355_contains (c:=root710) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid711_contains : mid711.Contains (rootPhase 710) := root710_contains
lemma root711_contains : root711.Contains (rootPhase 711) := by
  have hh := CBox.mul_contains mid711_contains root1_contains (c:=root711) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root712_contains : root712.Contains (rootPhase 712) := by
  have hh := CBox.mul_contains root356_contains root356_contains (c:=root712) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid713_contains : mid713.Contains (rootPhase 712) := root712_contains
lemma root713_contains : root713.Contains (rootPhase 713) := by
  have hh := CBox.mul_contains mid713_contains root1_contains (c:=root713) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root714_contains : root714.Contains (rootPhase 714) := by
  have hh := CBox.mul_contains root357_contains root357_contains (c:=root714) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid715_contains : mid715.Contains (rootPhase 714) := root714_contains
lemma root715_contains : root715.Contains (rootPhase 715) := by
  have hh := CBox.mul_contains mid715_contains root1_contains (c:=root715) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root716_contains : root716.Contains (rootPhase 716) := by
  have hh := CBox.mul_contains root358_contains root358_contains (c:=root716) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid717_contains : mid717.Contains (rootPhase 716) := root716_contains
lemma root717_contains : root717.Contains (rootPhase 717) := by
  have hh := CBox.mul_contains mid717_contains root1_contains (c:=root717) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root718_contains : root718.Contains (rootPhase 718) := by
  have hh := CBox.mul_contains root359_contains root359_contains (c:=root718) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid719_contains : mid719.Contains (rootPhase 718) := root718_contains
lemma root719_contains : root719.Contains (rootPhase 719) := by
  have hh := CBox.mul_contains mid719_contains root1_contains (c:=root719) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root720_contains : root720.Contains (rootPhase 720) := by
  have hh := CBox.mul_contains root360_contains root360_contains (c:=root720) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid721_contains : mid721.Contains (rootPhase 720) := root720_contains
lemma root721_contains : root721.Contains (rootPhase 721) := by
  have hh := CBox.mul_contains mid721_contains root1_contains (c:=root721) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root722_contains : root722.Contains (rootPhase 722) := by
  have hh := CBox.mul_contains root361_contains root361_contains (c:=root722) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid723_contains : mid723.Contains (rootPhase 722) := root722_contains
lemma root723_contains : root723.Contains (rootPhase 723) := by
  have hh := CBox.mul_contains mid723_contains root1_contains (c:=root723) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root724_contains : root724.Contains (rootPhase 724) := by
  have hh := CBox.mul_contains root362_contains root362_contains (c:=root724) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid725_contains : mid725.Contains (rootPhase 724) := root724_contains
lemma root725_contains : root725.Contains (rootPhase 725) := by
  have hh := CBox.mul_contains mid725_contains root1_contains (c:=root725) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root726_contains : root726.Contains (rootPhase 726) := by
  have hh := CBox.mul_contains root363_contains root363_contains (c:=root726) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid727_contains : mid727.Contains (rootPhase 726) := root726_contains
lemma root727_contains : root727.Contains (rootPhase 727) := by
  have hh := CBox.mul_contains mid727_contains root1_contains (c:=root727) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root728_contains : root728.Contains (rootPhase 728) := by
  have hh := CBox.mul_contains root364_contains root364_contains (c:=root728) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid729_contains : mid729.Contains (rootPhase 728) := root728_contains
lemma root729_contains : root729.Contains (rootPhase 729) := by
  have hh := CBox.mul_contains mid729_contains root1_contains (c:=root729) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root730_contains : root730.Contains (rootPhase 730) := by
  have hh := CBox.mul_contains root365_contains root365_contains (c:=root730) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid731_contains : mid731.Contains (rootPhase 730) := root730_contains
lemma root731_contains : root731.Contains (rootPhase 731) := by
  have hh := CBox.mul_contains mid731_contains root1_contains (c:=root731) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root732_contains : root732.Contains (rootPhase 732) := by
  have hh := CBox.mul_contains root366_contains root366_contains (c:=root732) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid733_contains : mid733.Contains (rootPhase 732) := root732_contains
lemma root733_contains : root733.Contains (rootPhase 733) := by
  have hh := CBox.mul_contains mid733_contains root1_contains (c:=root733) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root734_contains : root734.Contains (rootPhase 734) := by
  have hh := CBox.mul_contains root367_contains root367_contains (c:=root734) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid735_contains : mid735.Contains (rootPhase 734) := root734_contains
lemma root735_contains : root735.Contains (rootPhase 735) := by
  have hh := CBox.mul_contains mid735_contains root1_contains (c:=root735) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root736_contains : root736.Contains (rootPhase 736) := by
  have hh := CBox.mul_contains root368_contains root368_contains (c:=root736) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid737_contains : mid737.Contains (rootPhase 736) := root736_contains
lemma root737_contains : root737.Contains (rootPhase 737) := by
  have hh := CBox.mul_contains mid737_contains root1_contains (c:=root737) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root738_contains : root738.Contains (rootPhase 738) := by
  have hh := CBox.mul_contains root369_contains root369_contains (c:=root738) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid739_contains : mid739.Contains (rootPhase 738) := root738_contains
lemma root739_contains : root739.Contains (rootPhase 739) := by
  have hh := CBox.mul_contains mid739_contains root1_contains (c:=root739) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root740_contains : root740.Contains (rootPhase 740) := by
  have hh := CBox.mul_contains root370_contains root370_contains (c:=root740) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid741_contains : mid741.Contains (rootPhase 740) := root740_contains
lemma root741_contains : root741.Contains (rootPhase 741) := by
  have hh := CBox.mul_contains mid741_contains root1_contains (c:=root741) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root742_contains : root742.Contains (rootPhase 742) := by
  have hh := CBox.mul_contains root371_contains root371_contains (c:=root742) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid743_contains : mid743.Contains (rootPhase 742) := root742_contains
lemma root743_contains : root743.Contains (rootPhase 743) := by
  have hh := CBox.mul_contains mid743_contains root1_contains (c:=root743) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root744_contains : root744.Contains (rootPhase 744) := by
  have hh := CBox.mul_contains root372_contains root372_contains (c:=root744) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid745_contains : mid745.Contains (rootPhase 744) := root744_contains
lemma root745_contains : root745.Contains (rootPhase 745) := by
  have hh := CBox.mul_contains mid745_contains root1_contains (c:=root745) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root746_contains : root746.Contains (rootPhase 746) := by
  have hh := CBox.mul_contains root373_contains root373_contains (c:=root746) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid747_contains : mid747.Contains (rootPhase 746) := root746_contains
lemma root747_contains : root747.Contains (rootPhase 747) := by
  have hh := CBox.mul_contains mid747_contains root1_contains (c:=root747) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root748_contains : root748.Contains (rootPhase 748) := by
  have hh := CBox.mul_contains root374_contains root374_contains (c:=root748) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid749_contains : mid749.Contains (rootPhase 748) := root748_contains
lemma root749_contains : root749.Contains (rootPhase 749) := by
  have hh := CBox.mul_contains mid749_contains root1_contains (c:=root749) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root750_contains : root750.Contains (rootPhase 750) := by
  have hh := CBox.mul_contains root375_contains root375_contains (c:=root750) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid751_contains : mid751.Contains (rootPhase 750) := root750_contains
lemma root751_contains : root751.Contains (rootPhase 751) := by
  have hh := CBox.mul_contains mid751_contains root1_contains (c:=root751) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root752_contains : root752.Contains (rootPhase 752) := by
  have hh := CBox.mul_contains root376_contains root376_contains (c:=root752) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid753_contains : mid753.Contains (rootPhase 752) := root752_contains
lemma root753_contains : root753.Contains (rootPhase 753) := by
  have hh := CBox.mul_contains mid753_contains root1_contains (c:=root753) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root754_contains : root754.Contains (rootPhase 754) := by
  have hh := CBox.mul_contains root377_contains root377_contains (c:=root754) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid755_contains : mid755.Contains (rootPhase 754) := root754_contains
lemma root755_contains : root755.Contains (rootPhase 755) := by
  have hh := CBox.mul_contains mid755_contains root1_contains (c:=root755) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root756_contains : root756.Contains (rootPhase 756) := by
  have hh := CBox.mul_contains root378_contains root378_contains (c:=root756) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid757_contains : mid757.Contains (rootPhase 756) := root756_contains
lemma root757_contains : root757.Contains (rootPhase 757) := by
  have hh := CBox.mul_contains mid757_contains root1_contains (c:=root757) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root758_contains : root758.Contains (rootPhase 758) := by
  have hh := CBox.mul_contains root379_contains root379_contains (c:=root758) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid759_contains : mid759.Contains (rootPhase 758) := root758_contains
lemma root759_contains : root759.Contains (rootPhase 759) := by
  have hh := CBox.mul_contains mid759_contains root1_contains (c:=root759) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root760_contains : root760.Contains (rootPhase 760) := by
  have hh := CBox.mul_contains root380_contains root380_contains (c:=root760) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid761_contains : mid761.Contains (rootPhase 760) := root760_contains
lemma root761_contains : root761.Contains (rootPhase 761) := by
  have hh := CBox.mul_contains mid761_contains root1_contains (c:=root761) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root762_contains : root762.Contains (rootPhase 762) := by
  have hh := CBox.mul_contains root381_contains root381_contains (c:=root762) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid763_contains : mid763.Contains (rootPhase 762) := root762_contains
lemma root763_contains : root763.Contains (rootPhase 763) := by
  have hh := CBox.mul_contains mid763_contains root1_contains (c:=root763) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root764_contains : root764.Contains (rootPhase 764) := by
  have hh := CBox.mul_contains root382_contains root382_contains (c:=root764) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid765_contains : mid765.Contains (rootPhase 764) := root764_contains
lemma root765_contains : root765.Contains (rootPhase 765) := by
  have hh := CBox.mul_contains mid765_contains root1_contains (c:=root765) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root766_contains : root766.Contains (rootPhase 766) := by
  have hh := CBox.mul_contains root383_contains root383_contains (c:=root766) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid767_contains : mid767.Contains (rootPhase 766) := root766_contains
lemma root767_contains : root767.Contains (rootPhase 767) := by
  have hh := CBox.mul_contains mid767_contains root1_contains (c:=root767) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root770_contains : root770.Contains (rootPhase 770) := by
  have hh := CBox.mul_contains root385_contains root385_contains (c:=root770) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid771_contains : mid771.Contains (rootPhase 770) := root770_contains
lemma root771_contains : root771.Contains (rootPhase 771) := by
  have hh := CBox.mul_contains mid771_contains root1_contains (c:=root771) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root774_contains : root774.Contains (rootPhase 774) := by
  have hh := CBox.mul_contains root387_contains root387_contains (c:=root774) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid775_contains : mid775.Contains (rootPhase 774) := root774_contains
lemma root775_contains : root775.Contains (rootPhase 775) := by
  have hh := CBox.mul_contains mid775_contains root1_contains (c:=root775) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root778_contains : root778.Contains (rootPhase 778) := by
  have hh := CBox.mul_contains root389_contains root389_contains (c:=root778) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid779_contains : mid779.Contains (rootPhase 778) := root778_contains
lemma root779_contains : root779.Contains (rootPhase 779) := by
  have hh := CBox.mul_contains mid779_contains root1_contains (c:=root779) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root782_contains : root782.Contains (rootPhase 782) := by
  have hh := CBox.mul_contains root391_contains root391_contains (c:=root782) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid783_contains : mid783.Contains (rootPhase 782) := root782_contains
lemma root783_contains : root783.Contains (rootPhase 783) := by
  have hh := CBox.mul_contains mid783_contains root1_contains (c:=root783) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root784_contains : root784.Contains (rootPhase 784) := by
  have hh := CBox.mul_contains root392_contains root392_contains (c:=root784) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid785_contains : mid785.Contains (rootPhase 784) := root784_contains
lemma root785_contains : root785.Contains (rootPhase 785) := by
  have hh := CBox.mul_contains mid785_contains root1_contains (c:=root785) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root786_contains : root786.Contains (rootPhase 786) := by
  have hh := CBox.mul_contains root393_contains root393_contains (c:=root786) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid787_contains : mid787.Contains (rootPhase 786) := root786_contains
lemma root787_contains : root787.Contains (rootPhase 787) := by
  have hh := CBox.mul_contains mid787_contains root1_contains (c:=root787) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root788_contains : root788.Contains (rootPhase 788) := by
  have hh := CBox.mul_contains root394_contains root394_contains (c:=root788) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid789_contains : mid789.Contains (rootPhase 788) := root788_contains
lemma root789_contains : root789.Contains (rootPhase 789) := by
  have hh := CBox.mul_contains mid789_contains root1_contains (c:=root789) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root790_contains : root790.Contains (rootPhase 790) := by
  have hh := CBox.mul_contains root395_contains root395_contains (c:=root790) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid791_contains : mid791.Contains (rootPhase 790) := root790_contains
lemma root791_contains : root791.Contains (rootPhase 791) := by
  have hh := CBox.mul_contains mid791_contains root1_contains (c:=root791) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root792_contains : root792.Contains (rootPhase 792) := by
  have hh := CBox.mul_contains root396_contains root396_contains (c:=root792) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid793_contains : mid793.Contains (rootPhase 792) := root792_contains
lemma root793_contains : root793.Contains (rootPhase 793) := by
  have hh := CBox.mul_contains mid793_contains root1_contains (c:=root793) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root794_contains : root794.Contains (rootPhase 794) := by
  have hh := CBox.mul_contains root397_contains root397_contains (c:=root794) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid795_contains : mid795.Contains (rootPhase 794) := root794_contains
lemma root795_contains : root795.Contains (rootPhase 795) := by
  have hh := CBox.mul_contains mid795_contains root1_contains (c:=root795) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root796_contains : root796.Contains (rootPhase 796) := by
  have hh := CBox.mul_contains root398_contains root398_contains (c:=root796) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid797_contains : mid797.Contains (rootPhase 796) := root796_contains
lemma root797_contains : root797.Contains (rootPhase 797) := by
  have hh := CBox.mul_contains mid797_contains root1_contains (c:=root797) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root798_contains : root798.Contains (rootPhase 798) := by
  have hh := CBox.mul_contains root399_contains root399_contains (c:=root798) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid799_contains : mid799.Contains (rootPhase 798) := root798_contains
lemma root799_contains : root799.Contains (rootPhase 799) := by
  have hh := CBox.mul_contains mid799_contains root1_contains (c:=root799) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root800_contains : root800.Contains (rootPhase 800) := by
  have hh := CBox.mul_contains root400_contains root400_contains (c:=root800) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid801_contains : mid801.Contains (rootPhase 800) := root800_contains
lemma root801_contains : root801.Contains (rootPhase 801) := by
  have hh := CBox.mul_contains mid801_contains root1_contains (c:=root801) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root802_contains : root802.Contains (rootPhase 802) := by
  have hh := CBox.mul_contains root401_contains root401_contains (c:=root802) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid803_contains : mid803.Contains (rootPhase 802) := root802_contains
lemma root803_contains : root803.Contains (rootPhase 803) := by
  have hh := CBox.mul_contains mid803_contains root1_contains (c:=root803) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root804_contains : root804.Contains (rootPhase 804) := by
  have hh := CBox.mul_contains root402_contains root402_contains (c:=root804) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid805_contains : mid805.Contains (rootPhase 804) := root804_contains
lemma root805_contains : root805.Contains (rootPhase 805) := by
  have hh := CBox.mul_contains mid805_contains root1_contains (c:=root805) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root806_contains : root806.Contains (rootPhase 806) := by
  have hh := CBox.mul_contains root403_contains root403_contains (c:=root806) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid807_contains : mid807.Contains (rootPhase 806) := root806_contains
lemma root807_contains : root807.Contains (rootPhase 807) := by
  have hh := CBox.mul_contains mid807_contains root1_contains (c:=root807) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root808_contains : root808.Contains (rootPhase 808) := by
  have hh := CBox.mul_contains root404_contains root404_contains (c:=root808) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid809_contains : mid809.Contains (rootPhase 808) := root808_contains
lemma root809_contains : root809.Contains (rootPhase 809) := by
  have hh := CBox.mul_contains mid809_contains root1_contains (c:=root809) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root810_contains : root810.Contains (rootPhase 810) := by
  have hh := CBox.mul_contains root405_contains root405_contains (c:=root810) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid811_contains : mid811.Contains (rootPhase 810) := root810_contains
lemma root811_contains : root811.Contains (rootPhase 811) := by
  have hh := CBox.mul_contains mid811_contains root1_contains (c:=root811) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root812_contains : root812.Contains (rootPhase 812) := by
  have hh := CBox.mul_contains root406_contains root406_contains (c:=root812) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid813_contains : mid813.Contains (rootPhase 812) := root812_contains
lemma root813_contains : root813.Contains (rootPhase 813) := by
  have hh := CBox.mul_contains mid813_contains root1_contains (c:=root813) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root814_contains : root814.Contains (rootPhase 814) := by
  have hh := CBox.mul_contains root407_contains root407_contains (c:=root814) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid815_contains : mid815.Contains (rootPhase 814) := root814_contains
lemma root815_contains : root815.Contains (rootPhase 815) := by
  have hh := CBox.mul_contains mid815_contains root1_contains (c:=root815) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root816_contains : root816.Contains (rootPhase 816) := by
  have hh := CBox.mul_contains root408_contains root408_contains (c:=root816) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid817_contains : mid817.Contains (rootPhase 816) := root816_contains
lemma root817_contains : root817.Contains (rootPhase 817) := by
  have hh := CBox.mul_contains mid817_contains root1_contains (c:=root817) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root818_contains : root818.Contains (rootPhase 818) := by
  have hh := CBox.mul_contains root409_contains root409_contains (c:=root818) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid819_contains : mid819.Contains (rootPhase 818) := root818_contains
lemma root819_contains : root819.Contains (rootPhase 819) := by
  have hh := CBox.mul_contains mid819_contains root1_contains (c:=root819) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root820_contains : root820.Contains (rootPhase 820) := by
  have hh := CBox.mul_contains root410_contains root410_contains (c:=root820) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid821_contains : mid821.Contains (rootPhase 820) := root820_contains
lemma root821_contains : root821.Contains (rootPhase 821) := by
  have hh := CBox.mul_contains mid821_contains root1_contains (c:=root821) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root822_contains : root822.Contains (rootPhase 822) := by
  have hh := CBox.mul_contains root411_contains root411_contains (c:=root822) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid823_contains : mid823.Contains (rootPhase 822) := root822_contains
lemma root823_contains : root823.Contains (rootPhase 823) := by
  have hh := CBox.mul_contains mid823_contains root1_contains (c:=root823) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root824_contains : root824.Contains (rootPhase 824) := by
  have hh := CBox.mul_contains root412_contains root412_contains (c:=root824) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid825_contains : mid825.Contains (rootPhase 824) := root824_contains
lemma root825_contains : root825.Contains (rootPhase 825) := by
  have hh := CBox.mul_contains mid825_contains root1_contains (c:=root825) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root826_contains : root826.Contains (rootPhase 826) := by
  have hh := CBox.mul_contains root413_contains root413_contains (c:=root826) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid827_contains : mid827.Contains (rootPhase 826) := root826_contains
lemma root827_contains : root827.Contains (rootPhase 827) := by
  have hh := CBox.mul_contains mid827_contains root1_contains (c:=root827) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root828_contains : root828.Contains (rootPhase 828) := by
  have hh := CBox.mul_contains root414_contains root414_contains (c:=root828) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid829_contains : mid829.Contains (rootPhase 828) := root828_contains
lemma root829_contains : root829.Contains (rootPhase 829) := by
  have hh := CBox.mul_contains mid829_contains root1_contains (c:=root829) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root830_contains : root830.Contains (rootPhase 830) := by
  have hh := CBox.mul_contains root415_contains root415_contains (c:=root830) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid831_contains : mid831.Contains (rootPhase 830) := root830_contains
lemma root831_contains : root831.Contains (rootPhase 831) := by
  have hh := CBox.mul_contains mid831_contains root1_contains (c:=root831) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root832_contains : root832.Contains (rootPhase 832) := by
  have hh := CBox.mul_contains root416_contains root416_contains (c:=root832) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid833_contains : mid833.Contains (rootPhase 832) := root832_contains
lemma root833_contains : root833.Contains (rootPhase 833) := by
  have hh := CBox.mul_contains mid833_contains root1_contains (c:=root833) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root834_contains : root834.Contains (rootPhase 834) := by
  have hh := CBox.mul_contains root417_contains root417_contains (c:=root834) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid835_contains : mid835.Contains (rootPhase 834) := root834_contains
lemma root835_contains : root835.Contains (rootPhase 835) := by
  have hh := CBox.mul_contains mid835_contains root1_contains (c:=root835) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root836_contains : root836.Contains (rootPhase 836) := by
  have hh := CBox.mul_contains root418_contains root418_contains (c:=root836) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid837_contains : mid837.Contains (rootPhase 836) := root836_contains
lemma root837_contains : root837.Contains (rootPhase 837) := by
  have hh := CBox.mul_contains mid837_contains root1_contains (c:=root837) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root838_contains : root838.Contains (rootPhase 838) := by
  have hh := CBox.mul_contains root419_contains root419_contains (c:=root838) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid839_contains : mid839.Contains (rootPhase 838) := root838_contains
lemma root839_contains : root839.Contains (rootPhase 839) := by
  have hh := CBox.mul_contains mid839_contains root1_contains (c:=root839) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root840_contains : root840.Contains (rootPhase 840) := by
  have hh := CBox.mul_contains root420_contains root420_contains (c:=root840) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid841_contains : mid841.Contains (rootPhase 840) := root840_contains
lemma root841_contains : root841.Contains (rootPhase 841) := by
  have hh := CBox.mul_contains mid841_contains root1_contains (c:=root841) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root842_contains : root842.Contains (rootPhase 842) := by
  have hh := CBox.mul_contains root421_contains root421_contains (c:=root842) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid843_contains : mid843.Contains (rootPhase 842) := root842_contains
lemma root843_contains : root843.Contains (rootPhase 843) := by
  have hh := CBox.mul_contains mid843_contains root1_contains (c:=root843) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root844_contains : root844.Contains (rootPhase 844) := by
  have hh := CBox.mul_contains root422_contains root422_contains (c:=root844) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid845_contains : mid845.Contains (rootPhase 844) := root844_contains
lemma root845_contains : root845.Contains (rootPhase 845) := by
  have hh := CBox.mul_contains mid845_contains root1_contains (c:=root845) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root846_contains : root846.Contains (rootPhase 846) := by
  have hh := CBox.mul_contains root423_contains root423_contains (c:=root846) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid847_contains : mid847.Contains (rootPhase 846) := root846_contains
lemma root847_contains : root847.Contains (rootPhase 847) := by
  have hh := CBox.mul_contains mid847_contains root1_contains (c:=root847) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root848_contains : root848.Contains (rootPhase 848) := by
  have hh := CBox.mul_contains root424_contains root424_contains (c:=root848) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid849_contains : mid849.Contains (rootPhase 848) := root848_contains
lemma root849_contains : root849.Contains (rootPhase 849) := by
  have hh := CBox.mul_contains mid849_contains root1_contains (c:=root849) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
end IntegerRoots
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma roots0_contains (j : Fin 32) : (roots0 j).Contains (rootPhase (0+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root0_contains
  · exact IntegerRoots.root1_contains
  · exact IntegerRoots.root2_contains
  · exact IntegerRoots.root3_contains
  · exact IntegerRoots.root4_contains
  · exact IntegerRoots.root5_contains
  · exact IntegerRoots.root6_contains
  · exact IntegerRoots.root7_contains
  · exact IntegerRoots.root8_contains
  · exact IntegerRoots.root9_contains
  · exact IntegerRoots.root10_contains
  · exact IntegerRoots.root11_contains
  · exact IntegerRoots.root12_contains
  · exact IntegerRoots.root13_contains
  · exact IntegerRoots.root14_contains
  · exact IntegerRoots.root15_contains
  · exact IntegerRoots.root16_contains
  · exact IntegerRoots.root17_contains
  · exact IntegerRoots.root18_contains
  · exact IntegerRoots.root19_contains
  · exact IntegerRoots.root20_contains
  · exact IntegerRoots.root21_contains
  · exact IntegerRoots.root22_contains
  · exact IntegerRoots.root23_contains
  · exact IntegerRoots.root24_contains
  · exact IntegerRoots.root25_contains
  · exact IntegerRoots.root26_contains
  · exact IntegerRoots.root27_contains
  · exact IntegerRoots.root28_contains
  · exact IntegerRoots.root29_contains
  · exact IntegerRoots.root30_contains
  · exact IntegerRoots.root31_contains
lemma roots1_contains (j : Fin 32) : (roots1 j).Contains (rootPhase (32+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root32_contains
  · exact IntegerRoots.root33_contains
  · exact IntegerRoots.root34_contains
  · exact IntegerRoots.root35_contains
  · exact IntegerRoots.root36_contains
  · exact IntegerRoots.root37_contains
  · exact IntegerRoots.root38_contains
  · exact IntegerRoots.root39_contains
  · exact IntegerRoots.root40_contains
  · exact IntegerRoots.root41_contains
  · exact IntegerRoots.root42_contains
  · exact IntegerRoots.root43_contains
  · exact IntegerRoots.root44_contains
  · exact IntegerRoots.root45_contains
  · exact IntegerRoots.root46_contains
  · exact IntegerRoots.root47_contains
  · exact IntegerRoots.root48_contains
  · exact IntegerRoots.root49_contains
  · exact IntegerRoots.root50_contains
  · exact IntegerRoots.root51_contains
  · exact IntegerRoots.root52_contains
  · exact IntegerRoots.root53_contains
  · exact IntegerRoots.root54_contains
  · exact IntegerRoots.root55_contains
  · exact IntegerRoots.root56_contains
  · exact IntegerRoots.root57_contains
  · exact IntegerRoots.root58_contains
  · exact IntegerRoots.root59_contains
  · exact IntegerRoots.root60_contains
  · exact IntegerRoots.root61_contains
  · exact IntegerRoots.root62_contains
  · exact IntegerRoots.root63_contains
lemma roots10_contains (j : Fin 32) : (roots10 j).Contains (rootPhase (320+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root320_contains
  · exact IntegerRoots.root321_contains
  · exact IntegerRoots.root322_contains
  · exact IntegerRoots.root323_contains
  · exact IntegerRoots.root324_contains
  · exact IntegerRoots.root325_contains
  · exact IntegerRoots.root326_contains
  · exact IntegerRoots.root327_contains
  · exact IntegerRoots.root328_contains
  · exact IntegerRoots.root329_contains
  · exact IntegerRoots.root330_contains
  · exact IntegerRoots.root331_contains
  · exact IntegerRoots.root332_contains
  · exact IntegerRoots.root333_contains
  · exact IntegerRoots.root334_contains
  · exact IntegerRoots.root335_contains
  · exact IntegerRoots.root336_contains
  · exact IntegerRoots.root337_contains
  · exact IntegerRoots.root338_contains
  · exact IntegerRoots.root339_contains
  · exact IntegerRoots.root340_contains
  · exact IntegerRoots.root341_contains
  · exact IntegerRoots.root342_contains
  · exact IntegerRoots.root343_contains
  · exact IntegerRoots.root344_contains
  · exact IntegerRoots.root345_contains
  · exact IntegerRoots.root346_contains
  · exact IntegerRoots.root347_contains
  · exact IntegerRoots.root348_contains
  · exact IntegerRoots.root349_contains
  · exact IntegerRoots.root350_contains
  · exact IntegerRoots.root351_contains
lemma roots11_contains (j : Fin 32) : (roots11 j).Contains (rootPhase (352+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root352_contains
  · exact IntegerRoots.root353_contains
  · exact IntegerRoots.root354_contains
  · exact IntegerRoots.root355_contains
  · exact IntegerRoots.root356_contains
  · exact IntegerRoots.root357_contains
  · exact IntegerRoots.root358_contains
  · exact IntegerRoots.root359_contains
  · exact IntegerRoots.root360_contains
  · exact IntegerRoots.root361_contains
  · exact IntegerRoots.root362_contains
  · exact IntegerRoots.root363_contains
  · exact IntegerRoots.root364_contains
  · exact IntegerRoots.root365_contains
  · exact IntegerRoots.root366_contains
  · exact IntegerRoots.root367_contains
  · exact IntegerRoots.root368_contains
  · exact IntegerRoots.root369_contains
  · exact IntegerRoots.root370_contains
  · exact IntegerRoots.root371_contains
  · exact IntegerRoots.root372_contains
  · exact IntegerRoots.root373_contains
  · exact IntegerRoots.root374_contains
  · exact IntegerRoots.root375_contains
  · exact IntegerRoots.root376_contains
  · exact IntegerRoots.root377_contains
  · exact IntegerRoots.root378_contains
  · exact IntegerRoots.root379_contains
  · exact IntegerRoots.root380_contains
  · exact IntegerRoots.root381_contains
  · exact IntegerRoots.root382_contains
  · exact IntegerRoots.root383_contains
lemma roots12_contains (j : Fin 32) : (roots12 j).Contains (rootPhase (384+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root384_contains
  · exact IntegerRoots.root385_contains
  · exact IntegerRoots.root386_contains
  · exact IntegerRoots.root387_contains
  · exact IntegerRoots.root388_contains
  · exact IntegerRoots.root389_contains
  · exact IntegerRoots.root390_contains
  · exact IntegerRoots.root391_contains
  · exact IntegerRoots.root392_contains
  · exact IntegerRoots.root393_contains
  · exact IntegerRoots.root394_contains
  · exact IntegerRoots.root395_contains
  · exact IntegerRoots.root396_contains
  · exact IntegerRoots.root397_contains
  · exact IntegerRoots.root398_contains
  · exact IntegerRoots.root399_contains
  · exact IntegerRoots.root400_contains
  · exact IntegerRoots.root401_contains
  · exact IntegerRoots.root402_contains
  · exact IntegerRoots.root403_contains
  · exact IntegerRoots.root404_contains
  · exact IntegerRoots.root405_contains
  · exact IntegerRoots.root406_contains
  · exact IntegerRoots.root407_contains
  · exact IntegerRoots.root408_contains
  · exact IntegerRoots.root409_contains
  · exact IntegerRoots.root410_contains
  · exact IntegerRoots.root411_contains
  · exact IntegerRoots.root412_contains
  · exact IntegerRoots.root413_contains
  · exact IntegerRoots.root414_contains
  · exact IntegerRoots.root415_contains
lemma roots13_contains (j : Fin 32) : (roots13 j).Contains (rootPhase (416+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root416_contains
  · exact IntegerRoots.root417_contains
  · exact IntegerRoots.root418_contains
  · exact IntegerRoots.root419_contains
  · exact IntegerRoots.root420_contains
  · exact IntegerRoots.root421_contains
  · exact IntegerRoots.root422_contains
  · exact IntegerRoots.root423_contains
  · exact IntegerRoots.root424_contains
  · exact IntegerRoots.root425_contains
  · exact IntegerRoots.root426_contains
  · exact IntegerRoots.root427_contains
  · exact IntegerRoots.root428_contains
  · exact IntegerRoots.root429_contains
  · exact IntegerRoots.root430_contains
  · exact IntegerRoots.root431_contains
  · exact IntegerRoots.root432_contains
  · exact IntegerRoots.root433_contains
  · exact IntegerRoots.root434_contains
  · exact IntegerRoots.root435_contains
  · exact IntegerRoots.root436_contains
  · exact IntegerRoots.root437_contains
  · exact IntegerRoots.root438_contains
  · exact IntegerRoots.root439_contains
  · exact IntegerRoots.root440_contains
  · exact IntegerRoots.root441_contains
  · exact IntegerRoots.root442_contains
  · exact IntegerRoots.root443_contains
  · exact IntegerRoots.root444_contains
  · exact IntegerRoots.root445_contains
  · exact IntegerRoots.root446_contains
  · exact IntegerRoots.root447_contains
lemma roots14_contains (j : Fin 32) : (roots14 j).Contains (rootPhase (448+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root448_contains
  · exact IntegerRoots.root449_contains
  · exact IntegerRoots.root450_contains
  · exact IntegerRoots.root451_contains
  · exact IntegerRoots.root452_contains
  · exact IntegerRoots.root453_contains
  · exact IntegerRoots.root454_contains
  · exact IntegerRoots.root455_contains
  · exact IntegerRoots.root456_contains
  · exact IntegerRoots.root457_contains
  · exact IntegerRoots.root458_contains
  · exact IntegerRoots.root459_contains
  · exact IntegerRoots.root460_contains
  · exact IntegerRoots.root461_contains
  · exact IntegerRoots.root462_contains
  · exact IntegerRoots.root463_contains
  · exact IntegerRoots.root464_contains
  · exact IntegerRoots.root465_contains
  · exact IntegerRoots.root466_contains
  · exact IntegerRoots.root467_contains
  · exact IntegerRoots.root468_contains
  · exact IntegerRoots.root469_contains
  · exact IntegerRoots.root470_contains
  · exact IntegerRoots.root471_contains
  · exact IntegerRoots.root472_contains
  · exact IntegerRoots.root473_contains
  · exact IntegerRoots.root474_contains
  · exact IntegerRoots.root475_contains
  · exact IntegerRoots.root476_contains
  · exact IntegerRoots.root477_contains
  · exact IntegerRoots.root478_contains
  · exact IntegerRoots.root479_contains
lemma roots15_contains (j : Fin 32) : (roots15 j).Contains (rootPhase (480+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root480_contains
  · exact IntegerRoots.root481_contains
  · exact IntegerRoots.root482_contains
  · exact IntegerRoots.root483_contains
  · exact IntegerRoots.root484_contains
  · exact IntegerRoots.root485_contains
  · exact IntegerRoots.root486_contains
  · exact IntegerRoots.root487_contains
  · exact IntegerRoots.root488_contains
  · exact IntegerRoots.root489_contains
  · exact IntegerRoots.root490_contains
  · exact IntegerRoots.root491_contains
  · exact IntegerRoots.root492_contains
  · exact IntegerRoots.root493_contains
  · exact IntegerRoots.root494_contains
  · exact IntegerRoots.root495_contains
  · exact IntegerRoots.root496_contains
  · exact IntegerRoots.root497_contains
  · exact IntegerRoots.root498_contains
  · exact IntegerRoots.root499_contains
  · exact IntegerRoots.root500_contains
  · exact IntegerRoots.root501_contains
  · exact IntegerRoots.root502_contains
  · exact IntegerRoots.root503_contains
  · exact IntegerRoots.root504_contains
  · exact IntegerRoots.root505_contains
  · exact IntegerRoots.root506_contains
  · exact IntegerRoots.root507_contains
  · exact IntegerRoots.root508_contains
  · exact IntegerRoots.root509_contains
  · exact IntegerRoots.root510_contains
  · exact IntegerRoots.root511_contains
lemma roots17_contains (j : Fin 32) : (roots17 j).Contains (rootPhase (544+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root544_contains
  · exact IntegerRoots.root545_contains
  · exact IntegerRoots.root546_contains
  · exact IntegerRoots.root547_contains
  · exact IntegerRoots.root548_contains
  · exact IntegerRoots.root549_contains
  · exact IntegerRoots.root550_contains
  · exact IntegerRoots.root551_contains
  · exact IntegerRoots.root552_contains
  · exact IntegerRoots.root553_contains
  · exact IntegerRoots.root554_contains
  · exact IntegerRoots.root555_contains
  · exact IntegerRoots.root556_contains
  · exact IntegerRoots.root557_contains
  · exact IntegerRoots.root558_contains
  · exact IntegerRoots.root559_contains
  · exact IntegerRoots.root560_contains
  · exact IntegerRoots.root561_contains
  · exact IntegerRoots.root562_contains
  · exact IntegerRoots.root563_contains
  · exact IntegerRoots.root564_contains
  · exact IntegerRoots.root565_contains
  · exact IntegerRoots.root566_contains
  · exact IntegerRoots.root567_contains
  · exact IntegerRoots.root568_contains
  · exact IntegerRoots.root569_contains
  · exact IntegerRoots.root570_contains
  · exact IntegerRoots.root571_contains
  · exact IntegerRoots.root572_contains
  · exact IntegerRoots.root573_contains
  · exact IntegerRoots.root574_contains
  · exact IntegerRoots.root575_contains
lemma roots18_contains (j : Fin 32) : (roots18 j).Contains (rootPhase (576+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root576_contains
  · exact IntegerRoots.root577_contains
  · exact IntegerRoots.root578_contains
  · exact IntegerRoots.root579_contains
  · exact IntegerRoots.root580_contains
  · exact IntegerRoots.root581_contains
  · exact IntegerRoots.root582_contains
  · exact IntegerRoots.root583_contains
  · exact IntegerRoots.root584_contains
  · exact IntegerRoots.root585_contains
  · exact IntegerRoots.root586_contains
  · exact IntegerRoots.root587_contains
  · exact IntegerRoots.root588_contains
  · exact IntegerRoots.root589_contains
  · exact IntegerRoots.root590_contains
  · exact IntegerRoots.root591_contains
  · exact IntegerRoots.root592_contains
  · exact IntegerRoots.root593_contains
  · exact IntegerRoots.root594_contains
  · exact IntegerRoots.root595_contains
  · exact IntegerRoots.root596_contains
  · exact IntegerRoots.root597_contains
  · exact IntegerRoots.root598_contains
  · exact IntegerRoots.root599_contains
  · exact IntegerRoots.root600_contains
  · exact IntegerRoots.root601_contains
  · exact IntegerRoots.root602_contains
  · exact IntegerRoots.root603_contains
  · exact IntegerRoots.root604_contains
  · exact IntegerRoots.root605_contains
  · exact IntegerRoots.root606_contains
  · exact IntegerRoots.root607_contains
lemma roots19_contains (j : Fin 32) : (roots19 j).Contains (rootPhase (608+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root608_contains
  · exact IntegerRoots.root609_contains
  · exact IntegerRoots.root610_contains
  · exact IntegerRoots.root611_contains
  · exact IntegerRoots.root612_contains
  · exact IntegerRoots.root613_contains
  · exact IntegerRoots.root614_contains
  · exact IntegerRoots.root615_contains
  · exact IntegerRoots.root616_contains
  · exact IntegerRoots.root617_contains
  · exact IntegerRoots.root618_contains
  · exact IntegerRoots.root619_contains
  · exact IntegerRoots.root620_contains
  · exact IntegerRoots.root621_contains
  · exact IntegerRoots.root622_contains
  · exact IntegerRoots.root623_contains
  · exact IntegerRoots.root624_contains
  · exact IntegerRoots.root625_contains
  · exact IntegerRoots.root626_contains
  · exact IntegerRoots.root627_contains
  · exact IntegerRoots.root628_contains
  · exact IntegerRoots.root629_contains
  · exact IntegerRoots.root630_contains
  · exact IntegerRoots.root631_contains
  · exact IntegerRoots.root632_contains
  · exact IntegerRoots.root633_contains
  · exact IntegerRoots.root634_contains
  · exact IntegerRoots.root635_contains
  · exact IntegerRoots.root636_contains
  · exact IntegerRoots.root637_contains
  · exact IntegerRoots.root638_contains
  · exact IntegerRoots.root639_contains
lemma roots20_contains (j : Fin 32) : (roots20 j).Contains (rootPhase (640+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root640_contains
  · exact IntegerRoots.root641_contains
  · exact IntegerRoots.root642_contains
  · exact IntegerRoots.root643_contains
  · exact IntegerRoots.root644_contains
  · exact IntegerRoots.root645_contains
  · exact IntegerRoots.root646_contains
  · exact IntegerRoots.root647_contains
  · exact IntegerRoots.root648_contains
  · exact IntegerRoots.root649_contains
  · exact IntegerRoots.root650_contains
  · exact IntegerRoots.root651_contains
  · exact IntegerRoots.root652_contains
  · exact IntegerRoots.root653_contains
  · exact IntegerRoots.root654_contains
  · exact IntegerRoots.root655_contains
  · exact IntegerRoots.root656_contains
  · exact IntegerRoots.root657_contains
  · exact IntegerRoots.root658_contains
  · exact IntegerRoots.root659_contains
  · exact IntegerRoots.root660_contains
  · exact IntegerRoots.root661_contains
  · exact IntegerRoots.root662_contains
  · exact IntegerRoots.root663_contains
  · exact IntegerRoots.root664_contains
  · exact IntegerRoots.root665_contains
  · exact IntegerRoots.root666_contains
  · exact IntegerRoots.root667_contains
  · exact IntegerRoots.root668_contains
  · exact IntegerRoots.root669_contains
  · exact IntegerRoots.root670_contains
  · exact IntegerRoots.root671_contains
lemma roots21_contains (j : Fin 32) : (roots21 j).Contains (rootPhase (672+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root672_contains
  · exact IntegerRoots.root673_contains
  · exact IntegerRoots.root674_contains
  · exact IntegerRoots.root675_contains
  · exact IntegerRoots.root676_contains
  · exact IntegerRoots.root677_contains
  · exact IntegerRoots.root678_contains
  · exact IntegerRoots.root679_contains
  · exact IntegerRoots.root680_contains
  · exact IntegerRoots.root681_contains
  · exact IntegerRoots.root682_contains
  · exact IntegerRoots.root683_contains
  · exact IntegerRoots.root684_contains
  · exact IntegerRoots.root685_contains
  · exact IntegerRoots.root686_contains
  · exact IntegerRoots.root687_contains
  · exact IntegerRoots.root688_contains
  · exact IntegerRoots.root689_contains
  · exact IntegerRoots.root690_contains
  · exact IntegerRoots.root691_contains
  · exact IntegerRoots.root692_contains
  · exact IntegerRoots.root693_contains
  · exact IntegerRoots.root694_contains
  · exact IntegerRoots.root695_contains
  · exact IntegerRoots.root696_contains
  · exact IntegerRoots.root697_contains
  · exact IntegerRoots.root698_contains
  · exact IntegerRoots.root699_contains
  · exact IntegerRoots.root700_contains
  · exact IntegerRoots.root701_contains
  · exact IntegerRoots.root702_contains
  · exact IntegerRoots.root703_contains
lemma roots22_contains (j : Fin 32) : (roots22 j).Contains (rootPhase (704+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root704_contains
  · exact IntegerRoots.root705_contains
  · exact IntegerRoots.root706_contains
  · exact IntegerRoots.root707_contains
  · exact IntegerRoots.root708_contains
  · exact IntegerRoots.root709_contains
  · exact IntegerRoots.root710_contains
  · exact IntegerRoots.root711_contains
  · exact IntegerRoots.root712_contains
  · exact IntegerRoots.root713_contains
  · exact IntegerRoots.root714_contains
  · exact IntegerRoots.root715_contains
  · exact IntegerRoots.root716_contains
  · exact IntegerRoots.root717_contains
  · exact IntegerRoots.root718_contains
  · exact IntegerRoots.root719_contains
  · exact IntegerRoots.root720_contains
  · exact IntegerRoots.root721_contains
  · exact IntegerRoots.root722_contains
  · exact IntegerRoots.root723_contains
  · exact IntegerRoots.root724_contains
  · exact IntegerRoots.root725_contains
  · exact IntegerRoots.root726_contains
  · exact IntegerRoots.root727_contains
  · exact IntegerRoots.root728_contains
  · exact IntegerRoots.root729_contains
  · exact IntegerRoots.root730_contains
  · exact IntegerRoots.root731_contains
  · exact IntegerRoots.root732_contains
  · exact IntegerRoots.root733_contains
  · exact IntegerRoots.root734_contains
  · exact IntegerRoots.root735_contains
lemma roots23_contains (j : Fin 32) : (roots23 j).Contains (rootPhase (736+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root736_contains
  · exact IntegerRoots.root737_contains
  · exact IntegerRoots.root738_contains
  · exact IntegerRoots.root739_contains
  · exact IntegerRoots.root740_contains
  · exact IntegerRoots.root741_contains
  · exact IntegerRoots.root742_contains
  · exact IntegerRoots.root743_contains
  · exact IntegerRoots.root744_contains
  · exact IntegerRoots.root745_contains
  · exact IntegerRoots.root746_contains
  · exact IntegerRoots.root747_contains
  · exact IntegerRoots.root748_contains
  · exact IntegerRoots.root749_contains
  · exact IntegerRoots.root750_contains
  · exact IntegerRoots.root751_contains
  · exact IntegerRoots.root752_contains
  · exact IntegerRoots.root753_contains
  · exact IntegerRoots.root754_contains
  · exact IntegerRoots.root755_contains
  · exact IntegerRoots.root756_contains
  · exact IntegerRoots.root757_contains
  · exact IntegerRoots.root758_contains
  · exact IntegerRoots.root759_contains
  · exact IntegerRoots.root760_contains
  · exact IntegerRoots.root761_contains
  · exact IntegerRoots.root762_contains
  · exact IntegerRoots.root763_contains
  · exact IntegerRoots.root764_contains
  · exact IntegerRoots.root765_contains
  · exact IntegerRoots.root766_contains
  · exact IntegerRoots.root767_contains
lemma roots24_contains (j : Fin 32) : (roots24 j).Contains (rootPhase (768+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root768_contains
  · exact IntegerRoots.root769_contains
  · exact IntegerRoots.root770_contains
  · exact IntegerRoots.root771_contains
  · exact IntegerRoots.root772_contains
  · exact IntegerRoots.root773_contains
  · exact IntegerRoots.root774_contains
  · exact IntegerRoots.root775_contains
  · exact IntegerRoots.root776_contains
  · exact IntegerRoots.root777_contains
  · exact IntegerRoots.root778_contains
  · exact IntegerRoots.root779_contains
  · exact IntegerRoots.root780_contains
  · exact IntegerRoots.root781_contains
  · exact IntegerRoots.root782_contains
  · exact IntegerRoots.root783_contains
  · exact IntegerRoots.root784_contains
  · exact IntegerRoots.root785_contains
  · exact IntegerRoots.root786_contains
  · exact IntegerRoots.root787_contains
  · exact IntegerRoots.root788_contains
  · exact IntegerRoots.root789_contains
  · exact IntegerRoots.root790_contains
  · exact IntegerRoots.root791_contains
  · exact IntegerRoots.root792_contains
  · exact IntegerRoots.root793_contains
  · exact IntegerRoots.root794_contains
  · exact IntegerRoots.root795_contains
  · exact IntegerRoots.root796_contains
  · exact IntegerRoots.root797_contains
  · exact IntegerRoots.root798_contains
  · exact IntegerRoots.root799_contains
lemma roots25_contains (j : Fin 32) : (roots25 j).Contains (rootPhase (800+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root800_contains
  · exact IntegerRoots.root801_contains
  · exact IntegerRoots.root802_contains
  · exact IntegerRoots.root803_contains
  · exact IntegerRoots.root804_contains
  · exact IntegerRoots.root805_contains
  · exact IntegerRoots.root806_contains
  · exact IntegerRoots.root807_contains
  · exact IntegerRoots.root808_contains
  · exact IntegerRoots.root809_contains
  · exact IntegerRoots.root810_contains
  · exact IntegerRoots.root811_contains
  · exact IntegerRoots.root812_contains
  · exact IntegerRoots.root813_contains
  · exact IntegerRoots.root814_contains
  · exact IntegerRoots.root815_contains
  · exact IntegerRoots.root816_contains
  · exact IntegerRoots.root817_contains
  · exact IntegerRoots.root818_contains
  · exact IntegerRoots.root819_contains
  · exact IntegerRoots.root820_contains
  · exact IntegerRoots.root821_contains
  · exact IntegerRoots.root822_contains
  · exact IntegerRoots.root823_contains
  · exact IntegerRoots.root824_contains
  · exact IntegerRoots.root825_contains
  · exact IntegerRoots.root826_contains
  · exact IntegerRoots.root827_contains
  · exact IntegerRoots.root828_contains
  · exact IntegerRoots.root829_contains
  · exact IntegerRoots.root830_contains
  · exact IntegerRoots.root831_contains
end SharpPlanar.IntegerCompact


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma coefficientBox_contains (n : ℕ) : (coefficientBox n).Contains (Pcoeff n) := by
  have hb : bBounds.Contains b := bBounds_contains
  have hp := RBox.contains_scale hb 2 1 (by norm_num)
  have hm := RBox.contains_scale hb (-2) 1 (by norm_num)
  have h0 (m k : ℤ) (hk : 0 < k) := CBox.contains_rat m k 0 1 hk (by norm_num)
  have hr (m k : ℤ) (hk : 0 < k) := RBox.contains_rat m k hk
  rcases n with _|_|_|_|_|_|_|n
  · simpa [coefficientBox,Pcoeff] using h0 5 1 (by norm_num)
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr (-1) 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hp
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr 1 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hp
  · simpa [coefficientBox,Pcoeff] using h0 (-2) 1 (by norm_num)
  · constructor
    · convert hr (-1) 2 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [coefficientBox,Pcoeff])
    · simpa [coefficientBox,Pcoeff] using hb
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr (-1) 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hm
  · simpa [coefficientBox,Pcoeff] using h0 1 1 (by norm_num)
  · simpa [coefficientBox,Pcoeff] using h0 0 1 (by norm_num)

def spectralCoefficientBox (n l : ℕ) : CBox := (coefficientBox l).mul (phaseBox (l*n))
lemma spectralCoefficientBox_contains (n l : ℕ) :
    (spectralCoefficientBox n l).Contains (spectralCoefficient n l) := by
  have hh := CBox.contains_mul (coefficientBox_contains l) (phaseBox_contains (l*n))
  unfold spectralCoefficientBox
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

lemma boxSum_contains {f : ℕ → CBox} {g : ℕ → ℂ} (N : ℕ)
    (h : ∀ n < N, (f n).Contains (g n)) :
    (boxSum f N).Contains (∑ n ∈ Finset.range N, g n) := by
  induction N with
  | zero => simpa [boxSum] using zeroBox_contains
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact CBox.contains_add (ih (fun n hn => h n (by omega))) (h N (by omega))
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def alphaBox (n j : ℕ) : CBox := boxSum
  (fun l => if j<l then spectralCoefficientBox n l else zeroBox) 7
def betaBox (n j : ℕ) : CBox := boxSum
  (fun l => if j<l then (spectralCoefficientBox n l).scale l 6 else zeroBox) 7
lemma alphaBox_contains (n j : ℕ) : (alphaBox n j).Contains (basisAlpha n j) := by
  have hh (l : ℕ) : (if j<l then spectralCoefficientBox n l else zeroBox).Contains
      (if j<l then spectralCoefficient n l else 0) := by
    split_ifs <;> first | exact spectralCoefficientBox_contains n l | exact zeroBox_contains
  have hs := boxSum_contains 7 (fun l _ => hh l)
  rwa [sum_seven_Icc] at hs
lemma betaBox_contains (n j : ℕ) : (betaBox n j).Contains (basisBeta n j) := by
  have hh (l : ℕ) : (if j<l then (spectralCoefficientBox n l).scale l 6 else zeroBox).Contains
      (if j<l then ((l:ℂ)/6)*spectralCoefficient n l else 0) := by
    split_ifs
    · simpa only [Int.cast_natCast,Int.cast_ofNat] using CBox.contains_scale (spectralCoefficientBox_contains n l) l 6 (by norm_num)
    · exact zeroBox_contains
  have hs := boxSum_contains 7 (fun l _ => hh l)
  rwa [sum_seven_Icc] at hs

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma a0_0_contains : a0_0.Contains (basisAlpha 0 0) := by
  have he : alphaBox 0 0 = a0_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 0
lemma b0_0_contains : b0_0.Contains (basisBeta 0 0) := by
  have he : betaBox 0 0 = b0_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 0
lemma a0_1_contains : a0_1.Contains (basisAlpha 0 1) := by
  have he : alphaBox 0 1 = a0_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 1
lemma b0_1_contains : b0_1.Contains (basisBeta 0 1) := by
  have he : betaBox 0 1 = b0_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 1
lemma a0_2_contains : a0_2.Contains (basisAlpha 0 2) := by
  have he : alphaBox 0 2 = a0_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 2
lemma b0_2_contains : b0_2.Contains (basisBeta 0 2) := by
  have he : betaBox 0 2 = b0_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 2
lemma a0_3_contains : a0_3.Contains (basisAlpha 0 3) := by
  have he : alphaBox 0 3 = a0_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 3
lemma b0_3_contains : b0_3.Contains (basisBeta 0 3) := by
  have he : betaBox 0 3 = b0_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 3
lemma a0_4_contains : a0_4.Contains (basisAlpha 0 4) := by
  have he : alphaBox 0 4 = a0_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 4
lemma b0_4_contains : b0_4.Contains (basisBeta 0 4) := by
  have he : betaBox 0 4 = b0_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 4
lemma a0_5_contains : a0_5.Contains (basisAlpha 0 5) := by
  have he : alphaBox 0 5 = a0_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 5
lemma b0_5_contains : b0_5.Contains (basisBeta 0 5) := by
  have he : betaBox 0 5 = b0_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 5
lemma aRow0_contains (j : Fin 6) : (aRow0 j).Contains (basisAlpha 0 j.val) := by
  fin_cases j
  · exact a0_0_contains
  · exact a0_1_contains
  · exact a0_2_contains
  · exact a0_3_contains
  · exact a0_4_contains
  · exact a0_5_contains
lemma bRow0_contains (j : Fin 6) : (bRow0 j).Contains (basisBeta 0 j.val) := by
  fin_cases j
  · exact b0_0_contains
  · exact b0_1_contains
  · exact b0_2_contains
  · exact b0_3_contains
  · exact b0_4_contains
  · exact b0_5_contains
lemma a1_0_contains : a1_0.Contains (basisAlpha 1 0) := by
  have he : alphaBox 1 0 = a1_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 0
lemma b1_0_contains : b1_0.Contains (basisBeta 1 0) := by
  have he : betaBox 1 0 = b1_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 0
lemma a1_1_contains : a1_1.Contains (basisAlpha 1 1) := by
  have he : alphaBox 1 1 = a1_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 1
lemma b1_1_contains : b1_1.Contains (basisBeta 1 1) := by
  have he : betaBox 1 1 = b1_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 1
lemma a1_2_contains : a1_2.Contains (basisAlpha 1 2) := by
  have he : alphaBox 1 2 = a1_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 2
lemma b1_2_contains : b1_2.Contains (basisBeta 1 2) := by
  have he : betaBox 1 2 = b1_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 2
lemma a1_3_contains : a1_3.Contains (basisAlpha 1 3) := by
  have he : alphaBox 1 3 = a1_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 3
lemma b1_3_contains : b1_3.Contains (basisBeta 1 3) := by
  have he : betaBox 1 3 = b1_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 3
lemma a1_4_contains : a1_4.Contains (basisAlpha 1 4) := by
  have he : alphaBox 1 4 = a1_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 4
lemma b1_4_contains : b1_4.Contains (basisBeta 1 4) := by
  have he : betaBox 1 4 = b1_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 4
lemma a1_5_contains : a1_5.Contains (basisAlpha 1 5) := by
  have he : alphaBox 1 5 = a1_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 5
lemma b1_5_contains : b1_5.Contains (basisBeta 1 5) := by
  have he : betaBox 1 5 = b1_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 5
lemma aRow1_contains (j : Fin 6) : (aRow1 j).Contains (basisAlpha 1 j.val) := by
  fin_cases j
  · exact a1_0_contains
  · exact a1_1_contains
  · exact a1_2_contains
  · exact a1_3_contains
  · exact a1_4_contains
  · exact a1_5_contains
lemma bRow1_contains (j : Fin 6) : (bRow1 j).Contains (basisBeta 1 j.val) := by
  fin_cases j
  · exact b1_0_contains
  · exact b1_1_contains
  · exact b1_2_contains
  · exact b1_3_contains
  · exact b1_4_contains
  · exact b1_5_contains
lemma a2_0_contains : a2_0.Contains (basisAlpha 2 0) := by
  have he : alphaBox 2 0 = a2_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 0
lemma b2_0_contains : b2_0.Contains (basisBeta 2 0) := by
  have he : betaBox 2 0 = b2_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 0
lemma a2_1_contains : a2_1.Contains (basisAlpha 2 1) := by
  have he : alphaBox 2 1 = a2_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 1
lemma b2_1_contains : b2_1.Contains (basisBeta 2 1) := by
  have he : betaBox 2 1 = b2_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 1
lemma a2_2_contains : a2_2.Contains (basisAlpha 2 2) := by
  have he : alphaBox 2 2 = a2_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 2
lemma b2_2_contains : b2_2.Contains (basisBeta 2 2) := by
  have he : betaBox 2 2 = b2_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 2
lemma a2_3_contains : a2_3.Contains (basisAlpha 2 3) := by
  have he : alphaBox 2 3 = a2_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 3
lemma b2_3_contains : b2_3.Contains (basisBeta 2 3) := by
  have he : betaBox 2 3 = b2_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 3
lemma a2_4_contains : a2_4.Contains (basisAlpha 2 4) := by
  have he : alphaBox 2 4 = a2_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 4
lemma b2_4_contains : b2_4.Contains (basisBeta 2 4) := by
  have he : betaBox 2 4 = b2_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 4
lemma a2_5_contains : a2_5.Contains (basisAlpha 2 5) := by
  have he : alphaBox 2 5 = a2_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 5
lemma b2_5_contains : b2_5.Contains (basisBeta 2 5) := by
  have he : betaBox 2 5 = b2_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 5
lemma aRow2_contains (j : Fin 6) : (aRow2 j).Contains (basisAlpha 2 j.val) := by
  fin_cases j
  · exact a2_0_contains
  · exact a2_1_contains
  · exact a2_2_contains
  · exact a2_3_contains
  · exact a2_4_contains
  · exact a2_5_contains
lemma bRow2_contains (j : Fin 6) : (bRow2 j).Contains (basisBeta 2 j.val) := by
  fin_cases j
  · exact b2_0_contains
  · exact b2_1_contains
  · exact b2_2_contains
  · exact b2_3_contains
  · exact b2_4_contains
  · exact b2_5_contains
lemma a3_0_contains : a3_0.Contains (basisAlpha 3 0) := by
  have he : alphaBox 3 0 = a3_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 0
lemma b3_0_contains : b3_0.Contains (basisBeta 3 0) := by
  have he : betaBox 3 0 = b3_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 0
lemma a3_1_contains : a3_1.Contains (basisAlpha 3 1) := by
  have he : alphaBox 3 1 = a3_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 1
lemma b3_1_contains : b3_1.Contains (basisBeta 3 1) := by
  have he : betaBox 3 1 = b3_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 1
lemma a3_2_contains : a3_2.Contains (basisAlpha 3 2) := by
  have he : alphaBox 3 2 = a3_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 2
lemma b3_2_contains : b3_2.Contains (basisBeta 3 2) := by
  have he : betaBox 3 2 = b3_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 2
lemma a3_3_contains : a3_3.Contains (basisAlpha 3 3) := by
  have he : alphaBox 3 3 = a3_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 3
lemma b3_3_contains : b3_3.Contains (basisBeta 3 3) := by
  have he : betaBox 3 3 = b3_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 3
lemma a3_4_contains : a3_4.Contains (basisAlpha 3 4) := by
  have he : alphaBox 3 4 = a3_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 4
lemma b3_4_contains : b3_4.Contains (basisBeta 3 4) := by
  have he : betaBox 3 4 = b3_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 4
lemma a3_5_contains : a3_5.Contains (basisAlpha 3 5) := by
  have he : alphaBox 3 5 = a3_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 5
lemma b3_5_contains : b3_5.Contains (basisBeta 3 5) := by
  have he : betaBox 3 5 = b3_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 5
lemma aRow3_contains (j : Fin 6) : (aRow3 j).Contains (basisAlpha 3 j.val) := by
  fin_cases j
  · exact a3_0_contains
  · exact a3_1_contains
  · exact a3_2_contains
  · exact a3_3_contains
  · exact a3_4_contains
  · exact a3_5_contains
lemma bRow3_contains (j : Fin 6) : (bRow3 j).Contains (basisBeta 3 j.val) := by
  fin_cases j
  · exact b3_0_contains
  · exact b3_1_contains
  · exact b3_2_contains
  · exact b3_3_contains
  · exact b3_4_contains
  · exact b3_5_contains
lemma a4_0_contains : a4_0.Contains (basisAlpha 4 0) := by
  have he : alphaBox 4 0 = a4_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 0
lemma b4_0_contains : b4_0.Contains (basisBeta 4 0) := by
  have he : betaBox 4 0 = b4_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 0
lemma a4_1_contains : a4_1.Contains (basisAlpha 4 1) := by
  have he : alphaBox 4 1 = a4_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 1
lemma b4_1_contains : b4_1.Contains (basisBeta 4 1) := by
  have he : betaBox 4 1 = b4_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 1
lemma a4_2_contains : a4_2.Contains (basisAlpha 4 2) := by
  have he : alphaBox 4 2 = a4_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 2
lemma b4_2_contains : b4_2.Contains (basisBeta 4 2) := by
  have he : betaBox 4 2 = b4_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 2
lemma a4_3_contains : a4_3.Contains (basisAlpha 4 3) := by
  have he : alphaBox 4 3 = a4_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 3
lemma b4_3_contains : b4_3.Contains (basisBeta 4 3) := by
  have he : betaBox 4 3 = b4_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 3
lemma a4_4_contains : a4_4.Contains (basisAlpha 4 4) := by
  have he : alphaBox 4 4 = a4_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 4
lemma b4_4_contains : b4_4.Contains (basisBeta 4 4) := by
  have he : betaBox 4 4 = b4_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 4
lemma a4_5_contains : a4_5.Contains (basisAlpha 4 5) := by
  have he : alphaBox 4 5 = a4_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 5
lemma b4_5_contains : b4_5.Contains (basisBeta 4 5) := by
  have he : betaBox 4 5 = b4_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 5
lemma aRow4_contains (j : Fin 6) : (aRow4 j).Contains (basisAlpha 4 j.val) := by
  fin_cases j
  · exact a4_0_contains
  · exact a4_1_contains
  · exact a4_2_contains
  · exact a4_3_contains
  · exact a4_4_contains
  · exact a4_5_contains
lemma bRow4_contains (j : Fin 6) : (bRow4 j).Contains (basisBeta 4 j.val) := by
  fin_cases j
  · exact b4_0_contains
  · exact b4_1_contains
  · exact b4_2_contains
  · exact b4_3_contains
  · exact b4_4_contains
  · exact b4_5_contains
lemma a5_0_contains : a5_0.Contains (basisAlpha 5 0) := by
  have he : alphaBox 5 0 = a5_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 0
lemma b5_0_contains : b5_0.Contains (basisBeta 5 0) := by
  have he : betaBox 5 0 = b5_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 0
lemma a5_1_contains : a5_1.Contains (basisAlpha 5 1) := by
  have he : alphaBox 5 1 = a5_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 1
lemma b5_1_contains : b5_1.Contains (basisBeta 5 1) := by
  have he : betaBox 5 1 = b5_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 1
lemma a5_2_contains : a5_2.Contains (basisAlpha 5 2) := by
  have he : alphaBox 5 2 = a5_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 2
lemma b5_2_contains : b5_2.Contains (basisBeta 5 2) := by
  have he : betaBox 5 2 = b5_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 2
lemma a5_3_contains : a5_3.Contains (basisAlpha 5 3) := by
  have he : alphaBox 5 3 = a5_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 3
lemma b5_3_contains : b5_3.Contains (basisBeta 5 3) := by
  have he : betaBox 5 3 = b5_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 3
lemma a5_4_contains : a5_4.Contains (basisAlpha 5 4) := by
  have he : alphaBox 5 4 = a5_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 4
lemma b5_4_contains : b5_4.Contains (basisBeta 5 4) := by
  have he : betaBox 5 4 = b5_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 4
lemma a5_5_contains : a5_5.Contains (basisAlpha 5 5) := by
  have he : alphaBox 5 5 = a5_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 5
lemma b5_5_contains : b5_5.Contains (basisBeta 5 5) := by
  have he : betaBox 5 5 = b5_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 5
lemma aRow5_contains (j : Fin 6) : (aRow5 j).Contains (basisAlpha 5 j.val) := by
  fin_cases j
  · exact a5_0_contains
  · exact a5_1_contains
  · exact a5_2_contains
  · exact a5_3_contains
  · exact a5_4_contains
  · exact a5_5_contains
lemma bRow5_contains (j : Fin 6) : (bRow5 j).Contains (basisBeta 5 j.val) := by
  fin_cases j
  · exact b5_0_contains
  · exact b5_1_contains
  · exact b5_2_contains
  · exact b5_3_contains
  · exact b5_4_contains
  · exact b5_5_contains
lemma a6_0_contains : a6_0.Contains (basisAlpha 6 0) := by
  have he : alphaBox 6 0 = a6_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 0
lemma b6_0_contains : b6_0.Contains (basisBeta 6 0) := by
  have he : betaBox 6 0 = b6_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 0
lemma a6_1_contains : a6_1.Contains (basisAlpha 6 1) := by
  have he : alphaBox 6 1 = a6_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 1
lemma b6_1_contains : b6_1.Contains (basisBeta 6 1) := by
  have he : betaBox 6 1 = b6_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 1
lemma a6_2_contains : a6_2.Contains (basisAlpha 6 2) := by
  have he : alphaBox 6 2 = a6_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 2
lemma b6_2_contains : b6_2.Contains (basisBeta 6 2) := by
  have he : betaBox 6 2 = b6_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 2
lemma a6_3_contains : a6_3.Contains (basisAlpha 6 3) := by
  have he : alphaBox 6 3 = a6_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 3
lemma b6_3_contains : b6_3.Contains (basisBeta 6 3) := by
  have he : betaBox 6 3 = b6_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 3
lemma a6_4_contains : a6_4.Contains (basisAlpha 6 4) := by
  have he : alphaBox 6 4 = a6_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 4
lemma b6_4_contains : b6_4.Contains (basisBeta 6 4) := by
  have he : betaBox 6 4 = b6_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 4
lemma a6_5_contains : a6_5.Contains (basisAlpha 6 5) := by
  have he : alphaBox 6 5 = a6_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 5
lemma b6_5_contains : b6_5.Contains (basisBeta 6 5) := by
  have he : betaBox 6 5 = b6_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 5
lemma aRow6_contains (j : Fin 6) : (aRow6 j).Contains (basisAlpha 6 j.val) := by
  fin_cases j
  · exact a6_0_contains
  · exact a6_1_contains
  · exact a6_2_contains
  · exact a6_3_contains
  · exact a6_4_contains
  · exact a6_5_contains
lemma bRow6_contains (j : Fin 6) : (bRow6 j).Contains (basisBeta 6 j.val) := by
  fin_cases j
  · exact b6_0_contains
  · exact b6_1_contains
  · exact b6_2_contains
  · exact b6_3_contains
  · exact b6_4_contains
  · exact b6_5_contains
lemma a7_0_contains : a7_0.Contains (basisAlpha 7 0) := by
  have he : alphaBox 7 0 = a7_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 0
lemma b7_0_contains : b7_0.Contains (basisBeta 7 0) := by
  have he : betaBox 7 0 = b7_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 0
lemma a7_1_contains : a7_1.Contains (basisAlpha 7 1) := by
  have he : alphaBox 7 1 = a7_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 1
lemma b7_1_contains : b7_1.Contains (basisBeta 7 1) := by
  have he : betaBox 7 1 = b7_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 1
lemma a7_2_contains : a7_2.Contains (basisAlpha 7 2) := by
  have he : alphaBox 7 2 = a7_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 2
lemma b7_2_contains : b7_2.Contains (basisBeta 7 2) := by
  have he : betaBox 7 2 = b7_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 2
lemma a7_3_contains : a7_3.Contains (basisAlpha 7 3) := by
  have he : alphaBox 7 3 = a7_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 3
lemma b7_3_contains : b7_3.Contains (basisBeta 7 3) := by
  have he : betaBox 7 3 = b7_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 3
lemma a7_4_contains : a7_4.Contains (basisAlpha 7 4) := by
  have he : alphaBox 7 4 = a7_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 4
lemma b7_4_contains : b7_4.Contains (basisBeta 7 4) := by
  have he : betaBox 7 4 = b7_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 4
lemma a7_5_contains : a7_5.Contains (basisAlpha 7 5) := by
  have he : alphaBox 7 5 = a7_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 5
lemma b7_5_contains : b7_5.Contains (basisBeta 7 5) := by
  have he : betaBox 7 5 = b7_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 5
lemma aRow7_contains (j : Fin 6) : (aRow7 j).Contains (basisAlpha 7 j.val) := by
  fin_cases j
  · exact a7_0_contains
  · exact a7_1_contains
  · exact a7_2_contains
  · exact a7_3_contains
  · exact a7_4_contains
  · exact a7_5_contains
lemma bRow7_contains (j : Fin 6) : (bRow7 j).Contains (basisBeta 7 j.val) := by
  fin_cases j
  · exact b7_0_contains
  · exact b7_1_contains
  · exact b7_2_contains
  · exact b7_3_contains
  · exact b7_4_contains
  · exact b7_5_contains
lemma a8_0_contains : a8_0.Contains (basisAlpha 8 0) := by
  have he : alphaBox 8 0 = a8_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 0
lemma b8_0_contains : b8_0.Contains (basisBeta 8 0) := by
  have he : betaBox 8 0 = b8_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 0
lemma a8_1_contains : a8_1.Contains (basisAlpha 8 1) := by
  have he : alphaBox 8 1 = a8_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 1
lemma b8_1_contains : b8_1.Contains (basisBeta 8 1) := by
  have he : betaBox 8 1 = b8_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 1
lemma a8_2_contains : a8_2.Contains (basisAlpha 8 2) := by
  have he : alphaBox 8 2 = a8_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 2
lemma b8_2_contains : b8_2.Contains (basisBeta 8 2) := by
  have he : betaBox 8 2 = b8_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 2
lemma a8_3_contains : a8_3.Contains (basisAlpha 8 3) := by
  have he : alphaBox 8 3 = a8_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 3
lemma b8_3_contains : b8_3.Contains (basisBeta 8 3) := by
  have he : betaBox 8 3 = b8_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 3
lemma a8_4_contains : a8_4.Contains (basisAlpha 8 4) := by
  have he : alphaBox 8 4 = a8_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 4
lemma b8_4_contains : b8_4.Contains (basisBeta 8 4) := by
  have he : betaBox 8 4 = b8_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 4
lemma a8_5_contains : a8_5.Contains (basisAlpha 8 5) := by
  have he : alphaBox 8 5 = a8_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 5
lemma b8_5_contains : b8_5.Contains (basisBeta 8 5) := by
  have he : betaBox 8 5 = b8_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 5
lemma aRow8_contains (j : Fin 6) : (aRow8 j).Contains (basisAlpha 8 j.val) := by
  fin_cases j
  · exact a8_0_contains
  · exact a8_1_contains
  · exact a8_2_contains
  · exact a8_3_contains
  · exact a8_4_contains
  · exact a8_5_contains
lemma bRow8_contains (j : Fin 6) : (bRow8 j).Contains (basisBeta 8 j.val) := by
  fin_cases j
  · exact b8_0_contains
  · exact b8_1_contains
  · exact b8_2_contains
  · exact b8_3_contains
  · exact b8_4_contains
  · exact b8_5_contains
lemma a9_0_contains : a9_0.Contains (basisAlpha 9 0) := by
  have he : alphaBox 9 0 = a9_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 0
lemma b9_0_contains : b9_0.Contains (basisBeta 9 0) := by
  have he : betaBox 9 0 = b9_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 0
lemma a9_1_contains : a9_1.Contains (basisAlpha 9 1) := by
  have he : alphaBox 9 1 = a9_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 1
lemma b9_1_contains : b9_1.Contains (basisBeta 9 1) := by
  have he : betaBox 9 1 = b9_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 1
lemma a9_2_contains : a9_2.Contains (basisAlpha 9 2) := by
  have he : alphaBox 9 2 = a9_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 2
lemma b9_2_contains : b9_2.Contains (basisBeta 9 2) := by
  have he : betaBox 9 2 = b9_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 2
lemma a9_3_contains : a9_3.Contains (basisAlpha 9 3) := by
  have he : alphaBox 9 3 = a9_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 3
lemma b9_3_contains : b9_3.Contains (basisBeta 9 3) := by
  have he : betaBox 9 3 = b9_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 3
lemma a9_4_contains : a9_4.Contains (basisAlpha 9 4) := by
  have he : alphaBox 9 4 = a9_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 4
lemma b9_4_contains : b9_4.Contains (basisBeta 9 4) := by
  have he : betaBox 9 4 = b9_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 4
lemma a9_5_contains : a9_5.Contains (basisAlpha 9 5) := by
  have he : alphaBox 9 5 = a9_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 5
lemma b9_5_contains : b9_5.Contains (basisBeta 9 5) := by
  have he : betaBox 9 5 = b9_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 5
lemma aRow9_contains (j : Fin 6) : (aRow9 j).Contains (basisAlpha 9 j.val) := by
  fin_cases j
  · exact a9_0_contains
  · exact a9_1_contains
  · exact a9_2_contains
  · exact a9_3_contains
  · exact a9_4_contains
  · exact a9_5_contains
lemma bRow9_contains (j : Fin 6) : (bRow9 j).Contains (basisBeta 9 j.val) := by
  fin_cases j
  · exact b9_0_contains
  · exact b9_1_contains
  · exact b9_2_contains
  · exact b9_3_contains
  · exact b9_4_contains
  · exact b9_5_contains
lemma a10_0_contains : a10_0.Contains (basisAlpha 10 0) := by
  have he : alphaBox 10 0 = a10_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 0
lemma b10_0_contains : b10_0.Contains (basisBeta 10 0) := by
  have he : betaBox 10 0 = b10_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 0
lemma a10_1_contains : a10_1.Contains (basisAlpha 10 1) := by
  have he : alphaBox 10 1 = a10_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 1
lemma b10_1_contains : b10_1.Contains (basisBeta 10 1) := by
  have he : betaBox 10 1 = b10_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 1
lemma a10_2_contains : a10_2.Contains (basisAlpha 10 2) := by
  have he : alphaBox 10 2 = a10_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 2
lemma b10_2_contains : b10_2.Contains (basisBeta 10 2) := by
  have he : betaBox 10 2 = b10_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 2
lemma a10_3_contains : a10_3.Contains (basisAlpha 10 3) := by
  have he : alphaBox 10 3 = a10_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 3
lemma b10_3_contains : b10_3.Contains (basisBeta 10 3) := by
  have he : betaBox 10 3 = b10_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 3
lemma a10_4_contains : a10_4.Contains (basisAlpha 10 4) := by
  have he : alphaBox 10 4 = a10_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 4
lemma b10_4_contains : b10_4.Contains (basisBeta 10 4) := by
  have he : betaBox 10 4 = b10_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 4
lemma a10_5_contains : a10_5.Contains (basisAlpha 10 5) := by
  have he : alphaBox 10 5 = a10_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 5
lemma b10_5_contains : b10_5.Contains (basisBeta 10 5) := by
  have he : betaBox 10 5 = b10_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 5
lemma aRow10_contains (j : Fin 6) : (aRow10 j).Contains (basisAlpha 10 j.val) := by
  fin_cases j
  · exact a10_0_contains
  · exact a10_1_contains
  · exact a10_2_contains
  · exact a10_3_contains
  · exact a10_4_contains
  · exact a10_5_contains
lemma bRow10_contains (j : Fin 6) : (bRow10 j).Contains (basisBeta 10 j.val) := by
  fin_cases j
  · exact b10_0_contains
  · exact b10_1_contains
  · exact b10_2_contains
  · exact b10_3_contains
  · exact b10_4_contains
  · exact b10_5_contains
lemma a11_0_contains : a11_0.Contains (basisAlpha 11 0) := by
  have he : alphaBox 11 0 = a11_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 0
lemma b11_0_contains : b11_0.Contains (basisBeta 11 0) := by
  have he : betaBox 11 0 = b11_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 0
lemma a11_1_contains : a11_1.Contains (basisAlpha 11 1) := by
  have he : alphaBox 11 1 = a11_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 1
lemma b11_1_contains : b11_1.Contains (basisBeta 11 1) := by
  have he : betaBox 11 1 = b11_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 1
lemma a11_2_contains : a11_2.Contains (basisAlpha 11 2) := by
  have he : alphaBox 11 2 = a11_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 2
lemma b11_2_contains : b11_2.Contains (basisBeta 11 2) := by
  have he : betaBox 11 2 = b11_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 2
lemma a11_3_contains : a11_3.Contains (basisAlpha 11 3) := by
  have he : alphaBox 11 3 = a11_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 3
lemma b11_3_contains : b11_3.Contains (basisBeta 11 3) := by
  have he : betaBox 11 3 = b11_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 3
lemma a11_4_contains : a11_4.Contains (basisAlpha 11 4) := by
  have he : alphaBox 11 4 = a11_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 4
lemma b11_4_contains : b11_4.Contains (basisBeta 11 4) := by
  have he : betaBox 11 4 = b11_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 4
lemma a11_5_contains : a11_5.Contains (basisAlpha 11 5) := by
  have he : alphaBox 11 5 = a11_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 5
lemma b11_5_contains : b11_5.Contains (basisBeta 11 5) := by
  have he : betaBox 11 5 = b11_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 5
lemma aRow11_contains (j : Fin 6) : (aRow11 j).Contains (basisAlpha 11 j.val) := by
  fin_cases j
  · exact a11_0_contains
  · exact a11_1_contains
  · exact a11_2_contains
  · exact a11_3_contains
  · exact a11_4_contains
  · exact a11_5_contains
lemma bRow11_contains (j : Fin 6) : (bRow11 j).Contains (basisBeta 11 j.val) := by
  fin_cases j
  · exact b11_0_contains
  · exact b11_1_contains
  · exact b11_2_contains
  · exact b11_3_contains
  · exact b11_4_contains
  · exact b11_5_contains
lemma aTable_contains (n : Fin 12) (j : Fin 6) : (aTable n j).Contains (basisAlpha n.val j.val) := by
  fin_cases n
  · exact aRow0_contains j
  · exact aRow1_contains j
  · exact aRow2_contains j
  · exact aRow3_contains j
  · exact aRow4_contains j
  · exact aRow5_contains j
  · exact aRow6_contains j
  · exact aRow7_contains j
  · exact aRow8_contains j
  · exact aRow9_contains j
  · exact aRow10_contains j
  · exact aRow11_contains j
lemma aLookup_contains (n : ℕ) (j : Fin 6) : (aLookup n j).Contains (basisAlpha n j.val) := by
  simpa only [aLookup,basisAlpha_mod] using aTable_contains ⟨n%12,by omega⟩ j
lemma bTable_contains (n : Fin 12) (j : Fin 6) : (bTable n j).Contains (basisBeta n.val j.val) := by
  fin_cases n
  · exact bRow0_contains j
  · exact bRow1_contains j
  · exact bRow2_contains j
  · exact bRow3_contains j
  · exact bRow4_contains j
  · exact bRow5_contains j
  · exact bRow6_contains j
  · exact bRow7_contains j
  · exact bRow8_contains j
  · exact bRow9_contains j
  · exact bRow10_contains j
  · exact bRow11_contains j
lemma bLookup_contains (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod] using bTable_contains ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact
def row2_12 : Fin 16 → PointBox := ![p2_192,p2_193,p2_194,p2_195,p2_196,p2_197,p2_198,p2_199,p2_200,p2_201,p2_202,p2_203,p2_204,p2_205,p2_206,p2_207]
def row2 : Fin 16 → Fin 16 → PointBox := ![row2_0,row2_1,row2_2,row2_3,row2_4,row2_5,row2_6,row2_7,row2_8,row2_9,row2_10,row2_11,row2_12,row2_13,row2_14,row2_15]
def row4_8 : Fin 16 → PointBox := ![p4_128,p4_129,p4_130,p4_131,p4_132,p4_133,p4_134,p4_135,p4_136,p4_137,p4_138,p4_139,p4_140,p4_141,p4_142,p4_143]
def row4 : Fin 16 → Fin 16 → PointBox := ![row4_0,row4_1,row4_2,row4_3,row4_4,row4_5,row4_6,row4_7,row4_8,row4_9,row4_10,row4_11,row4_12,row4_13,row4_14,row4_15]
def gridRows : Fin 6 → Fin 16 → Fin 16 → PointBox := ![row0,row1,row2,row3,row4,row5]
end SharpPlanar.IntegerGrid

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
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
noncomputable def amp0_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 0 j) (bLookup 0 j) false)
lemma amp0_00_0_eq : ∀ k : Fin 16, amp0_0Expr 0 0 k = amp0_00_0 k := by decide +kernel
lemma amp0_00_1_eq : ∀ k : Fin 16, amp0_0Expr 0 1 k = amp0_00_1 k := by decide +kernel
lemma amp0_00_2_eq : ∀ k : Fin 16, amp0_0Expr 0 2 k = amp0_00_2 k := by decide +kernel
lemma amp0_00_3_eq : ∀ k : Fin 16, amp0_0Expr 0 3 k = amp0_00_3 k := by decide +kernel
lemma amp0_00_4_eq : ∀ k : Fin 16, amp0_0Expr 0 4 k = amp0_00_4 k := by decide +kernel
lemma amp0_00_5_eq : ∀ k : Fin 16, amp0_0Expr 0 5 k = amp0_00_5 k := by decide +kernel
lemma amp0_00_6_eq : ∀ k : Fin 16, amp0_0Expr 0 6 k = amp0_00_6 k := by decide +kernel
lemma amp0_00_7_eq : ∀ k : Fin 16, amp0_0Expr 0 7 k = amp0_00_7 k := by decide +kernel
lemma amp0_00_8_eq : ∀ k : Fin 16, amp0_0Expr 0 8 k = amp0_00_8 k := by decide +kernel
lemma amp0_00_9_eq : ∀ k : Fin 16, amp0_0Expr 0 9 k = amp0_00_9 k := by decide +kernel
lemma amp0_00_10_eq : ∀ k : Fin 16, amp0_0Expr 0 10 k = amp0_00_10 k := by decide +kernel
lemma amp0_00_11_eq : ∀ k : Fin 16, amp0_0Expr 0 11 k = amp0_00_11 k := by decide +kernel
lemma amp0_00_12_eq : ∀ k : Fin 16, amp0_0Expr 0 12 k = amp0_00_12 k := by decide +kernel
lemma amp0_00_13_eq : ∀ k : Fin 16, amp0_0Expr 0 13 k = amp0_00_13 k := by decide +kernel
lemma amp0_00_14_eq : ∀ k : Fin 16, amp0_0Expr 0 14 k = amp0_00_14 k := by decide +kernel
lemma amp0_00_15_eq : ∀ k : Fin 16, amp0_0Expr 0 15 k = amp0_00_15 k := by decide +kernel
lemma amp0_00_eq (i k : Fin 16) : amp0_0Expr 0 i k = amp0_00 i k := by
  fin_cases i
  · exact amp0_00_0_eq k
  · exact amp0_00_1_eq k
  · exact amp0_00_2_eq k
  · exact amp0_00_3_eq k
  · exact amp0_00_4_eq k
  · exact amp0_00_5_eq k
  · exact amp0_00_6_eq k
  · exact amp0_00_7_eq k
  · exact amp0_00_8_eq k
  · exact amp0_00_9_eq k
  · exact amp0_00_10_eq k
  · exact amp0_00_11_eq k
  · exact amp0_00_12_eq k
  · exact amp0_00_13_eq k
  · exact amp0_00_14_eq k
  · exact amp0_00_15_eq k
lemma amp0_01_0_eq : ∀ k : Fin 16, amp0_0Expr 1 0 k = amp0_01_0 k := by decide +kernel
lemma amp0_01_1_eq : ∀ k : Fin 16, amp0_0Expr 1 1 k = amp0_01_1 k := by decide +kernel
lemma amp0_01_2_eq : ∀ k : Fin 16, amp0_0Expr 1 2 k = amp0_01_2 k := by decide +kernel
lemma amp0_01_3_eq : ∀ k : Fin 16, amp0_0Expr 1 3 k = amp0_01_3 k := by decide +kernel
lemma amp0_01_4_eq : ∀ k : Fin 16, amp0_0Expr 1 4 k = amp0_01_4 k := by decide +kernel
lemma amp0_01_5_eq : ∀ k : Fin 16, amp0_0Expr 1 5 k = amp0_01_5 k := by decide +kernel
lemma amp0_01_6_eq : ∀ k : Fin 16, amp0_0Expr 1 6 k = amp0_01_6 k := by decide +kernel
lemma amp0_01_7_eq : ∀ k : Fin 16, amp0_0Expr 1 7 k = amp0_01_7 k := by decide +kernel
lemma amp0_01_8_eq : ∀ k : Fin 16, amp0_0Expr 1 8 k = amp0_01_8 k := by decide +kernel
lemma amp0_01_9_eq : ∀ k : Fin 16, amp0_0Expr 1 9 k = amp0_01_9 k := by decide +kernel
lemma amp0_01_10_eq : ∀ k : Fin 16, amp0_0Expr 1 10 k = amp0_01_10 k := by decide +kernel
lemma amp0_01_11_eq : ∀ k : Fin 16, amp0_0Expr 1 11 k = amp0_01_11 k := by decide +kernel
lemma amp0_01_12_eq : ∀ k : Fin 16, amp0_0Expr 1 12 k = amp0_01_12 k := by decide +kernel
lemma amp0_01_13_eq : ∀ k : Fin 16, amp0_0Expr 1 13 k = amp0_01_13 k := by decide +kernel
lemma amp0_01_14_eq : ∀ k : Fin 16, amp0_0Expr 1 14 k = amp0_01_14 k := by decide +kernel
lemma amp0_01_15_eq : ∀ k : Fin 16, amp0_0Expr 1 15 k = amp0_01_15 k := by decide +kernel
lemma amp0_01_eq (i k : Fin 16) : amp0_0Expr 1 i k = amp0_01 i k := by
  fin_cases i
  · exact amp0_01_0_eq k
  · exact amp0_01_1_eq k
  · exact amp0_01_2_eq k
  · exact amp0_01_3_eq k
  · exact amp0_01_4_eq k
  · exact amp0_01_5_eq k
  · exact amp0_01_6_eq k
  · exact amp0_01_7_eq k
  · exact amp0_01_8_eq k
  · exact amp0_01_9_eq k
  · exact amp0_01_10_eq k
  · exact amp0_01_11_eq k
  · exact amp0_01_12_eq k
  · exact amp0_01_13_eq k
  · exact amp0_01_14_eq k
  · exact amp0_01_15_eq k
lemma amp0_02_0_eq : ∀ k : Fin 16, amp0_0Expr 2 0 k = amp0_02_0 k := by decide +kernel
lemma amp0_02_1_eq : ∀ k : Fin 16, amp0_0Expr 2 1 k = amp0_02_1 k := by decide +kernel
lemma amp0_02_2_eq : ∀ k : Fin 16, amp0_0Expr 2 2 k = amp0_02_2 k := by decide +kernel
lemma amp0_02_3_eq : ∀ k : Fin 16, amp0_0Expr 2 3 k = amp0_02_3 k := by decide +kernel
lemma amp0_02_4_eq : ∀ k : Fin 16, amp0_0Expr 2 4 k = amp0_02_4 k := by decide +kernel
lemma amp0_02_5_eq : ∀ k : Fin 16, amp0_0Expr 2 5 k = amp0_02_5 k := by decide +kernel
lemma amp0_02_6_eq : ∀ k : Fin 16, amp0_0Expr 2 6 k = amp0_02_6 k := by decide +kernel
lemma amp0_02_7_eq : ∀ k : Fin 16, amp0_0Expr 2 7 k = amp0_02_7 k := by decide +kernel
lemma amp0_02_8_eq : ∀ k : Fin 16, amp0_0Expr 2 8 k = amp0_02_8 k := by decide +kernel
lemma amp0_02_9_eq : ∀ k : Fin 16, amp0_0Expr 2 9 k = amp0_02_9 k := by decide +kernel
lemma amp0_02_10_eq : ∀ k : Fin 16, amp0_0Expr 2 10 k = amp0_02_10 k := by decide +kernel
lemma amp0_02_11_eq : ∀ k : Fin 16, amp0_0Expr 2 11 k = amp0_02_11 k := by decide +kernel
lemma amp0_02_12_eq : ∀ k : Fin 16, amp0_0Expr 2 12 k = amp0_02_12 k := by decide +kernel
lemma amp0_02_13_eq : ∀ k : Fin 16, amp0_0Expr 2 13 k = amp0_02_13 k := by decide +kernel
lemma amp0_02_14_eq : ∀ k : Fin 16, amp0_0Expr 2 14 k = amp0_02_14 k := by decide +kernel
lemma amp0_02_15_eq : ∀ k : Fin 16, amp0_0Expr 2 15 k = amp0_02_15 k := by decide +kernel
lemma amp0_02_eq (i k : Fin 16) : amp0_0Expr 2 i k = amp0_02 i k := by
  fin_cases i
  · exact amp0_02_0_eq k
  · exact amp0_02_1_eq k
  · exact amp0_02_2_eq k
  · exact amp0_02_3_eq k
  · exact amp0_02_4_eq k
  · exact amp0_02_5_eq k
  · exact amp0_02_6_eq k
  · exact amp0_02_7_eq k
  · exact amp0_02_8_eq k
  · exact amp0_02_9_eq k
  · exact amp0_02_10_eq k
  · exact amp0_02_11_eq k
  · exact amp0_02_12_eq k
  · exact amp0_02_13_eq k
  · exact amp0_02_14_eq k
  · exact amp0_02_15_eq k
lemma amp0_03_0_eq : ∀ k : Fin 16, amp0_0Expr 3 0 k = amp0_03_0 k := by decide +kernel
lemma amp0_03_1_eq : ∀ k : Fin 16, amp0_0Expr 3 1 k = amp0_03_1 k := by decide +kernel
lemma amp0_03_2_eq : ∀ k : Fin 16, amp0_0Expr 3 2 k = amp0_03_2 k := by decide +kernel
lemma amp0_03_3_eq : ∀ k : Fin 16, amp0_0Expr 3 3 k = amp0_03_3 k := by decide +kernel
lemma amp0_03_4_eq : ∀ k : Fin 16, amp0_0Expr 3 4 k = amp0_03_4 k := by decide +kernel
lemma amp0_03_5_eq : ∀ k : Fin 16, amp0_0Expr 3 5 k = amp0_03_5 k := by decide +kernel
lemma amp0_03_6_eq : ∀ k : Fin 16, amp0_0Expr 3 6 k = amp0_03_6 k := by decide +kernel
lemma amp0_03_7_eq : ∀ k : Fin 16, amp0_0Expr 3 7 k = amp0_03_7 k := by decide +kernel
lemma amp0_03_8_eq : ∀ k : Fin 16, amp0_0Expr 3 8 k = amp0_03_8 k := by decide +kernel
lemma amp0_03_9_eq : ∀ k : Fin 16, amp0_0Expr 3 9 k = amp0_03_9 k := by decide +kernel
lemma amp0_03_10_eq : ∀ k : Fin 16, amp0_0Expr 3 10 k = amp0_03_10 k := by decide +kernel
lemma amp0_03_11_eq : ∀ k : Fin 16, amp0_0Expr 3 11 k = amp0_03_11 k := by decide +kernel
lemma amp0_03_12_eq : ∀ k : Fin 16, amp0_0Expr 3 12 k = amp0_03_12 k := by decide +kernel
lemma amp0_03_13_eq : ∀ k : Fin 16, amp0_0Expr 3 13 k = amp0_03_13 k := by decide +kernel
lemma amp0_03_14_eq : ∀ k : Fin 16, amp0_0Expr 3 14 k = amp0_03_14 k := by decide +kernel
lemma amp0_03_15_eq : ∀ k : Fin 16, amp0_0Expr 3 15 k = amp0_03_15 k := by decide +kernel
lemma amp0_03_eq (i k : Fin 16) : amp0_0Expr 3 i k = amp0_03 i k := by
  fin_cases i
  · exact amp0_03_0_eq k
  · exact amp0_03_1_eq k
  · exact amp0_03_2_eq k
  · exact amp0_03_3_eq k
  · exact amp0_03_4_eq k
  · exact amp0_03_5_eq k
  · exact amp0_03_6_eq k
  · exact amp0_03_7_eq k
  · exact amp0_03_8_eq k
  · exact amp0_03_9_eq k
  · exact amp0_03_10_eq k
  · exact amp0_03_11_eq k
  · exact amp0_03_12_eq k
  · exact amp0_03_13_eq k
  · exact amp0_03_14_eq k
  · exact amp0_03_15_eq k
lemma amp0_04_0_eq : ∀ k : Fin 16, amp0_0Expr 4 0 k = amp0_04_0 k := by decide +kernel
lemma amp0_04_1_eq : ∀ k : Fin 16, amp0_0Expr 4 1 k = amp0_04_1 k := by decide +kernel
lemma amp0_04_2_eq : ∀ k : Fin 16, amp0_0Expr 4 2 k = amp0_04_2 k := by decide +kernel
lemma amp0_04_3_eq : ∀ k : Fin 16, amp0_0Expr 4 3 k = amp0_04_3 k := by decide +kernel
lemma amp0_04_4_eq : ∀ k : Fin 16, amp0_0Expr 4 4 k = amp0_04_4 k := by decide +kernel
lemma amp0_04_5_eq : ∀ k : Fin 16, amp0_0Expr 4 5 k = amp0_04_5 k := by decide +kernel
lemma amp0_04_6_eq : ∀ k : Fin 16, amp0_0Expr 4 6 k = amp0_04_6 k := by decide +kernel
lemma amp0_04_7_eq : ∀ k : Fin 16, amp0_0Expr 4 7 k = amp0_04_7 k := by decide +kernel
lemma amp0_04_8_eq : ∀ k : Fin 16, amp0_0Expr 4 8 k = amp0_04_8 k := by decide +kernel
lemma amp0_04_9_eq : ∀ k : Fin 16, amp0_0Expr 4 9 k = amp0_04_9 k := by decide +kernel
lemma amp0_04_10_eq : ∀ k : Fin 16, amp0_0Expr 4 10 k = amp0_04_10 k := by decide +kernel
lemma amp0_04_11_eq : ∀ k : Fin 16, amp0_0Expr 4 11 k = amp0_04_11 k := by decide +kernel
lemma amp0_04_12_eq : ∀ k : Fin 16, amp0_0Expr 4 12 k = amp0_04_12 k := by decide +kernel
lemma amp0_04_13_eq : ∀ k : Fin 16, amp0_0Expr 4 13 k = amp0_04_13 k := by decide +kernel
lemma amp0_04_14_eq : ∀ k : Fin 16, amp0_0Expr 4 14 k = amp0_04_14 k := by decide +kernel
lemma amp0_04_15_eq : ∀ k : Fin 16, amp0_0Expr 4 15 k = amp0_04_15 k := by decide +kernel
lemma amp0_04_eq (i k : Fin 16) : amp0_0Expr 4 i k = amp0_04 i k := by
  fin_cases i
  · exact amp0_04_0_eq k
  · exact amp0_04_1_eq k
  · exact amp0_04_2_eq k
  · exact amp0_04_3_eq k
  · exact amp0_04_4_eq k
  · exact amp0_04_5_eq k
  · exact amp0_04_6_eq k
  · exact amp0_04_7_eq k
  · exact amp0_04_8_eq k
  · exact amp0_04_9_eq k
  · exact amp0_04_10_eq k
  · exact amp0_04_11_eq k
  · exact amp0_04_12_eq k
  · exact amp0_04_13_eq k
  · exact amp0_04_14_eq k
  · exact amp0_04_15_eq k
lemma amp0_05_0_eq : ∀ k : Fin 16, amp0_0Expr 5 0 k = amp0_05_0 k := by decide +kernel
lemma amp0_05_1_eq : ∀ k : Fin 16, amp0_0Expr 5 1 k = amp0_05_1 k := by decide +kernel
lemma amp0_05_2_eq : ∀ k : Fin 16, amp0_0Expr 5 2 k = amp0_05_2 k := by decide +kernel
lemma amp0_05_3_eq : ∀ k : Fin 16, amp0_0Expr 5 3 k = amp0_05_3 k := by decide +kernel
lemma amp0_05_4_eq : ∀ k : Fin 16, amp0_0Expr 5 4 k = amp0_05_4 k := by decide +kernel
lemma amp0_05_5_eq : ∀ k : Fin 16, amp0_0Expr 5 5 k = amp0_05_5 k := by decide +kernel
lemma amp0_05_6_eq : ∀ k : Fin 16, amp0_0Expr 5 6 k = amp0_05_6 k := by decide +kernel
lemma amp0_05_7_eq : ∀ k : Fin 16, amp0_0Expr 5 7 k = amp0_05_7 k := by decide +kernel
lemma amp0_05_8_eq : ∀ k : Fin 16, amp0_0Expr 5 8 k = amp0_05_8 k := by decide +kernel
lemma amp0_05_9_eq : ∀ k : Fin 16, amp0_0Expr 5 9 k = amp0_05_9 k := by decide +kernel
lemma amp0_05_10_eq : ∀ k : Fin 16, amp0_0Expr 5 10 k = amp0_05_10 k := by decide +kernel
lemma amp0_05_11_eq : ∀ k : Fin 16, amp0_0Expr 5 11 k = amp0_05_11 k := by decide +kernel
lemma amp0_05_12_eq : ∀ k : Fin 16, amp0_0Expr 5 12 k = amp0_05_12 k := by decide +kernel
lemma amp0_05_13_eq : ∀ k : Fin 16, amp0_0Expr 5 13 k = amp0_05_13 k := by decide +kernel
lemma amp0_05_14_eq : ∀ k : Fin 16, amp0_0Expr 5 14 k = amp0_05_14 k := by decide +kernel
lemma amp0_05_15_eq : ∀ k : Fin 16, amp0_0Expr 5 15 k = amp0_05_15 k := by decide +kernel
lemma amp0_05_eq (i k : Fin 16) : amp0_0Expr 5 i k = amp0_05 i k := by
  fin_cases i
  · exact amp0_05_0_eq k
  · exact amp0_05_1_eq k
  · exact amp0_05_2_eq k
  · exact amp0_05_3_eq k
  · exact amp0_05_4_eq k
  · exact amp0_05_5_eq k
  · exact amp0_05_6_eq k
  · exact amp0_05_7_eq k
  · exact amp0_05_8_eq k
  · exact amp0_05_9_eq k
  · exact amp0_05_10_eq k
  · exact amp0_05_11_eq k
  · exact amp0_05_12_eq k
  · exact amp0_05_13_eq k
  · exact amp0_05_14_eq k
  · exact amp0_05_15_eq k
lemma amp0_0_eq (j : Fin 6) (i k : Fin 16) : amp0_0Expr j i k = amp0_0 j i k := by
  fin_cases j
  · exact amp0_00_eq i k
  · exact amp0_01_eq i k
  · exact amp0_02_eq i k
  · exact amp0_03_eq i k
  · exact amp0_04_eq i k
  · exact amp0_05_eq i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers100
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
noncomputable def power100Expr (j : Fin 6) (i k : Fin 16) : CBox := (power99 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


