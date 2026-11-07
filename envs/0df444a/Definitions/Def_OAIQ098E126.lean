-- Prove2me | Definitions.Def_OAIQ098E126
-- name    : OAIQ098E126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T19:39:45.502202+00:00
-- url     : https://prove2.me/theorems/c1d52425-680e-4cac-b5d6-51004b32f5f0
-- title:
--   Definitions bundle OAIQ098E126 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 760 declarations of OpenAI's Lean: 758 definitions and 2 instances. The definitions and types are `OAI.SharpPlanar.CachedData.amp7_1`, `OAI.SharpPlanar.CachedData.amp7_10`, `OAI.SharpPlanar.CachedData.amp7_15`, `OAI.SharpPlanar.CachedData.cm100_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm100_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm100_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm100_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm100_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm100_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm100_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm12_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm12_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm12_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm12_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm12_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm12_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm12_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm12_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm13_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm13_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm13_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm13_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm13_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm13_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm13_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm13_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm15_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm15_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm15_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm15_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm15_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm15_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm15_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm15_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm16_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm16_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm16_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm16_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm16_3_0_0.chunk` and 718 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_CanonicalRows`, `PlanarPacking_Certificate_Amplitudes`, `PlanarPacking_Certificate_Columns10`, `PlanarPacking_Certificate_Columns100`, `PlanarPacking_Certificate_Columns20`, `PlanarPacking_Certificate_Columns30`, `PlanarPacking_Certificate_Columns40`, `PlanarPacking_Certificate_Columns50`, `PlanarPacking_Certificate_Columns60`, `PlanarPacking_Certificate_Columns70`, `PlanarPacking_Certificate_Columns80`, `PlanarPacking_Certificate_Columns90`, `PlanarPacking_Certificate_KernelValues10`, `PlanarPacking_Certificate_KernelValues20`, `PlanarPacking_Certificate_LMoments12`, `PlanarPacking_Certificate_LMoments13`, `PlanarPacking_Certificate_LMoments15`, `PlanarPacking_Certificate_LMoments16`, `PlanarPacking_Certificate_LMoments7`, `PlanarPacking_Certificate_LMoments9`, `PlanarPacking_Certificate_Powers10`, `PlanarPacking_Certificate_Powers100`, `PlanarPacking_Certificate_Powers20`, `PlanarPacking_Certificate_Powers30`, `PlanarPacking_Certificate_Powers40`, `PlanarPacking_Certificate_Powers50`, `PlanarPacking_Certificate_Powers60`, `PlanarPacking_Certificate_Powers70`, `PlanarPacking_Certificate_Powers80`, `PlanarPacking_Certificate_Powers90`, `PlanarPacking_Certificate_TransformedPowers10`, `PlanarPacking_Certificate_TransformedPowers20`, `PlanarPacking_Certificate_UMoments100`, `PlanarPacking_Certificate_UMoments12`, `PlanarPacking_Certificate_UMoments13`, `PlanarPacking_Certificate_UMoments15`, `PlanarPacking_Certificate_UMoments16`, `PlanarPacking_Certificate_UMoments19`, `PlanarPacking_Certificate_UMoments21`, `PlanarPacking_Certificate_UMoments24`, `PlanarPacking_Certificate_UMoments25`, `PlanarPacking_Certificate_UMoments27`, `PlanarPacking_Certificate_UMoments28`, `PlanarPacking_Certificate_UMoments31`, `PlanarPacking_Certificate_UMoments33`, `PlanarPacking_Certificate_UMoments36`, `PlanarPacking_Certificate_UMoments37`, `PlanarPacking_Certificate_UMoments39`, `PlanarPacking_Certificate_UMoments40`, `PlanarPacking_Certificate_UMoments43`, `PlanarPacking_Certificate_UMoments45`, `PlanarPacking_Certificate_UMoments48`, `PlanarPacking_Certificate_UMoments49`, `PlanarPacking_Certificate_UMoments51`, `PlanarPacking_Certificate_UMoments52`, `PlanarPacking_Certificate_UMoments55`, `PlanarPacking_Certificate_UMoments57`, `PlanarPacking_Certificate_UMoments60`, `PlanarPacking_Certificate_UMoments61`, `PlanarPacking_Certificate_UMoments63`, `PlanarPacking_Certificate_UMoments64`, `PlanarPacking_Certificate_UMoments67`, `PlanarPacking_Certificate_UMoments69`, `PlanarPacking_Certificate_UMoments7`, `PlanarPacking_Certificate_UMoments72`, `PlanarPacking_Certificate_UMoments73`, `PlanarPacking_Certificate_UMoments75`, `PlanarPacking_Certificate_UMoments76`, `PlanarPacking_Certificate_UMoments79`, `PlanarPacking_Certificate_UMoments81`, `PlanarPacking_Certificate_UMoments84`, `PlanarPacking_Certificate_UMoments85`, `PlanarPacking_Certificate_UMoments87`, `PlanarPacking_Certificate_UMoments88`, `PlanarPacking_Certificate_UMoments9`, `PlanarPacking_Certificate_UMoments91`, `PlanarPacking_Certificate_UMoments93`, `PlanarPacking_Certificate_UMoments96`, `PlanarPacking_Certificate_UMoments97`, `PlanarPacking_Certificate_UMoments99`, `PlanarPacking_Certificate_WUCert100`, `PlanarPacking_Certificate_WUCert12`, `PlanarPacking_Certificate_WUCert13`, `PlanarPacking_Certificate_WUCert15`, `PlanarPacking_Certificate_WUCert16`, `PlanarPacking_Certificate_WUCert19`, `PlanarPacking_Certificate_WUCert21`, `PlanarPacking_Certificate_WUCert24`, `PlanarPacking_Certificate_WUCert25`, `PlanarPacking_Certificate_WUCert27`, `PlanarPacking_Certificate_WUCert9`, `PlanarPacking_FiniteFull`.
--
--   **Imports.** It imports the bundles `OAIQ098E033`, `OAIQ098E034`, `OAIQ098E035`, `OAIQ098E036`, `OAIQ098E037`, `OAIQ098E038`, `OAIQ098E039`, `OAIQ098E040`, `OAIQ098E041`, `OAIQ098E042`, `OAIQ098E043`, `OAIQ098E044`, `OAIQ098E045`, `OAIQ098E046`, `OAIQ098E047`, `OAIQ098E048`, `OAIQ098E049`, `OAIQ098E050`, `OAIQ098E051`, `OAIQ098E052`, `OAIQ098E053`, `OAIQ098E054`, `OAIQ098E055`, `OAIQ098E056`, `OAIQ098E057`, `OAIQ098E058`, `OAIQ098E059`, `OAIQ098E060`, `OAIQ098E061`, `OAIQ098E062`, `OAIQ098E063`, `OAIQ098E064`, `OAIQ098E065`, `OAIQ098E066`, `OAIQ098E067`, `OAIQ098E068`, `OAIQ098E069`, `OAIQ098E070`, `OAIQ098E071`, `OAIQ098E072`, `OAIQ098E073`, `OAIQ098E074`, `OAIQ098E075`, `OAIQ098E076`, `OAIQ098E077`, `OAIQ098E078`, `OAIQ098E079`, `OAIQ098E080`, `OAIQ098E081`, `OAIQ098E082`, `OAIQ098E083`, `OAIQ098E084`, `OAIQ098E085`, `OAIQ098E086`, `OAIQ098E087`, `OAIQ098E088`, `OAIQ098E089`, `OAIQ098E090`, `OAIQ098E091`, `OAIQ098E092`, `OAIQ098E093`, `OAIQ098E094`, `OAIQ098E095`, `OAIQ098E096`, `OAIQ098E097`, `OAIQ098E098`, `OAIQ098E099`, `OAIQ098E100`, `OAIQ098E101`, `OAIQ098E102`, `OAIQ098E103`, `OAIQ098E104`, `OAIQ098E105`, `OAIQ098E106`, `OAIQ098E107`, `OAIQ098E108`, `OAIQ098E109`, `OAIQ098E110`, `OAIQ098E111`, `OAIQ098E112`, `OAIQ098E113`, `OAIQ098E114`, `OAIQ098E115`, `OAIQ098E116`, `OAIQ098E117`, `OAIQ098E118`, `OAIQ098E119`, `OAIQ098E120`, `OAIQ098E121`, `OAIQ098E122`, `OAIQ098E123`, `OAIQ098E124` and `OAIQ098E125` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E239`; the statements `OAI.SharpPlanar.CachedData.column100_0_contains_e`, `OAI.SharpPlanar.CachedData.column12_0_contains_e`, `OAI.SharpPlanar.CachedData.column13_0_contains_e`, `OAI.SharpPlanar.CachedData.column19_0_contains_e`, `OAI.SharpPlanar.CachedData.column60_0_contains_e`, `OAI.SharpPlanar.CachedData.column61_0_contains_e`, `OAI.SharpPlanar.CachedData.column67_0_contains_e`, `OAI.SharpPlanar.CachedData.column69_0_contains_e`, `OAI.SharpPlanar.CachedData.column75_0_contains_e`, `OAI.SharpPlanar.CachedData.column76_0_contains_e`, `OAI.SharpPlanar.CachedData.column84_0_contains_e`, `OAI.SharpPlanar.CachedData.column85_0_contains_e`, `OAI.SharpPlanar.CachedData.column91_0_contains_e`, `OAI.SharpPlanar.CachedData.column93_0_contains_e`, `OAI.SharpPlanar.CachedData.column99_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel7_0_contains_e`, `OAI.SharpPlanar.CachedData.power15_contains_e`, `OAI.SharpPlanar.CachedData.power31_contains_e`, `OAI.SharpPlanar.CachedData.power37_contains_e`, `OAI.SharpPlanar.CachedData.power40_contains_e`, `OAI.SharpPlanar.CachedData.power48_contains_e`, `OAI.SharpPlanar.CachedData.power64_contains_e`, `OAI.SharpPlanar.CachedData.power7_contains_e`, `OAI.SharpPlanar.CachedData.power88_contains_e`, `OAI.SharpPlanar.CachedData.power8_contains_e`, `OAI.SharpPlanar.CachedData.power96_contains_e`, `OAI.SharpPlanar.CachedData.trans8_contains_e`, `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e`, `OAI.SharpPlanar.IntegerBasis.basis_density_bounds_e`, `OAI.SharpPlanar.IntegerBasis.density_check_e`, `OAI.SharpPlanar.IntegerBasis.density_finite_check_e`, `OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_e`, `OAI.SharpPlanar.Numerical.U100.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U100.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U100.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U100.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U100.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U100.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U12.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U12.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U12.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U12.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U12.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U12.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U13.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U13.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U13.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U13.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U13.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U13.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U15.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U15.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U16.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U19.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U19.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U19.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U19.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U19.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U19.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U21.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U21.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U25.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U27.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U27.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U27.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U27.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U27.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U27.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U9.wuplus_column_e`, `OAI.SharpPlanar.Numerical.signedVU_norm_e`, `OAI.SharpPlanar.densityCap_nonneg_e`, `OAI.SharpPlanar.piece_density_bound_e`, `OAI.SharpPlanar.piece_summand_bound_e`, `OAI.SharpPlanar.sharp_integral_piece_bound_e` and `OAI.SharpPlanar.sharp_moment_bound_e`; the proofs of `OAI.SharpPlanar.CachedData.cm25_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm25_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm33_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm33_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm49_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm49_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm57_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm57_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm73_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm73_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm81_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm81_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm97_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm97_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm9_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm9_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column100_0_contains_e`, `OAI.SharpPlanar.CachedData.column100_1_contains_e`, `OAI.SharpPlanar.CachedData.column12_0_contains_e`, `OAI.SharpPlanar.CachedData.column12_1_contains_e`, `OAI.SharpPlanar.CachedData.column13_0_contains_e`, `OAI.SharpPlanar.CachedData.column19_0_contains_e`, `OAI.SharpPlanar.CachedData.column19_1_contains_e`, `OAI.SharpPlanar.CachedData.column21_1_contains_e`, `OAI.SharpPlanar.CachedData.column27_0_contains_e`, `OAI.SharpPlanar.CachedData.column27_1_contains_e`, `OAI.SharpPlanar.CachedData.column28_0_contains_e`, `OAI.SharpPlanar.CachedData.column28_1_contains_e`, `OAI.SharpPlanar.CachedData.column36_0_contains_e`, `OAI.SharpPlanar.CachedData.column36_1_contains_e`, `OAI.SharpPlanar.CachedData.column37_1_contains_e`, `OAI.SharpPlanar.CachedData.column43_0_contains_e`, `OAI.SharpPlanar.CachedData.column43_1_contains_e`, `OAI.SharpPlanar.CachedData.column45_0_contains_e`, `OAI.SharpPlanar.CachedData.column45_1_contains_e`, `OAI.SharpPlanar.CachedData.column51_0_contains_e`, `OAI.SharpPlanar.CachedData.column51_1_contains_e`, `OAI.SharpPlanar.CachedData.column52_0_contains_e`, `OAI.SharpPlanar.CachedData.column52_1_contains_e`, `OAI.SharpPlanar.CachedData.column60_0_contains_e`, `OAI.SharpPlanar.CachedData.column60_1_contains_e`, `OAI.SharpPlanar.CachedData.column61_0_contains_e`, `OAI.SharpPlanar.CachedData.column61_1_contains_e`, `OAI.SharpPlanar.CachedData.column67_0_contains_e`, `OAI.SharpPlanar.CachedData.column67_1_contains_e`, `OAI.SharpPlanar.CachedData.column69_0_contains_e`, `OAI.SharpPlanar.CachedData.column69_1_contains_e`, `OAI.SharpPlanar.CachedData.column75_0_contains_e`, `OAI.SharpPlanar.CachedData.column75_1_contains_e`, `OAI.SharpPlanar.CachedData.column76_0_contains_e`, `OAI.SharpPlanar.CachedData.column76_1_contains_e`, `OAI.SharpPlanar.CachedData.column84_0_contains_e`, `OAI.SharpPlanar.CachedData.column84_1_contains_e`, `OAI.SharpPlanar.CachedData.column85_0_contains_e`, `OAI.SharpPlanar.CachedData.column85_1_contains_e`, `OAI.SharpPlanar.CachedData.column91_0_contains_e`, `OAI.SharpPlanar.CachedData.column91_1_contains_e`, `OAI.SharpPlanar.CachedData.column93_0_contains_e`, `OAI.SharpPlanar.CachedData.column93_1_contains_e`, `OAI.SharpPlanar.CachedData.column99_0_contains_e`, `OAI.SharpPlanar.CachedData.column99_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel12_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel12_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel13_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel13_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel15_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel15_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel7_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel7_1_contains_e`, `OAI.SharpPlanar.CachedData.power13_contains_e`, `OAI.SharpPlanar.CachedData.power15_contains_e`, `OAI.SharpPlanar.CachedData.power16_contains_e`, `OAI.SharpPlanar.CachedData.power21_contains_e`, `OAI.SharpPlanar.CachedData.power24_contains_e`, `OAI.SharpPlanar.CachedData.power31_contains_e`, `OAI.SharpPlanar.CachedData.power32_contains_e`, `OAI.SharpPlanar.CachedData.power37_contains_e`, `OAI.SharpPlanar.CachedData.power39_contains_e`, `OAI.SharpPlanar.CachedData.power40_contains_e`, `OAI.SharpPlanar.CachedData.power48_contains_e`, `OAI.SharpPlanar.CachedData.power55_contains_e`, `OAI.SharpPlanar.CachedData.power56_contains_e`, `OAI.SharpPlanar.CachedData.power63_contains_e`, `OAI.SharpPlanar.CachedData.power64_contains_e`, `OAI.SharpPlanar.CachedData.power6_contains_e`, `OAI.SharpPlanar.CachedData.power72_contains_e`, `OAI.SharpPlanar.CachedData.power79_contains_e`, `OAI.SharpPlanar.CachedData.power7_contains_e`, `OAI.SharpPlanar.CachedData.power80_contains_e`, `OAI.SharpPlanar.CachedData.power87_contains_e`, `OAI.SharpPlanar.CachedData.power88_contains_e`, `OAI.SharpPlanar.CachedData.power8_contains_e`, `OAI.SharpPlanar.CachedData.power96_contains_e`, `OAI.SharpPlanar.CachedData.trans16_contains_e`, `OAI.SharpPlanar.CachedData.trans8_contains_e`, `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e`, `OAI.SharpPlanar.IntegerBasis.basis_density_bounds_e`, `OAI.SharpPlanar.IntegerBasis.density_check_e`, `OAI.SharpPlanar.IntegerBasis.density_finite_check_e`, `OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_e`, `OAI.SharpPlanar.Numerical.Lmat_column_e`, `OAI.SharpPlanar.Numerical.U100.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U100.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U100.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U100.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U100.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U100.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U12.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U12.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U12.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U12.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U12.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U12.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U13.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U13.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U13.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U13.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U13.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U13.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U15.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U15.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U16.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U19.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U19.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U19.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U19.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U19.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U19.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U21.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U21.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U25.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U27.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U27.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U27.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U27.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U27.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U27.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U28.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U28.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U31.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U31.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U33.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U33.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U36.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U36.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U36.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U36.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U37.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U37.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U39.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U39.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U40.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U40.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U43.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U43.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U45.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U45.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U48.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U49.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U51.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U51.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U51.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U51.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U52.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U52.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U52.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U52.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U55.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U55.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U57.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U60.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U60.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U60.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U60.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U61.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U61.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U61.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U61.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U63.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U63.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U64.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U64.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U67.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U67.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U67.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U67.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U69.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U69.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U69.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U69.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U72.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U72.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U73.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U73.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U75.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U75.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U75.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U75.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U76.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U76.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U76.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U76.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U79.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U79.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U7.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U7.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U81.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U81.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U84.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U84.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U84.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U84.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U85.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U85.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U85.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U85.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U87.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U87.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U88.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U88.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U91.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U91.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U91.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U91.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U93.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U93.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U93.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U93.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U96.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U96.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U97.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U97.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U99.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U99.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U99.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U99.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U9.wuplus_column_e`, `OAI.SharpPlanar.Numerical.finiteA_bijective_e`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_e`, `OAI.SharpPlanar.Numerical.lentry0_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_5_contains_e`, `OAI.SharpPlanar.Numerical.signedVU_norm_e`, `OAI.SharpPlanar.densityCap_nonneg_e`, `OAI.SharpPlanar.piece_density_bound_e`, `OAI.SharpPlanar.piece_summand_bound_e`, `OAI.SharpPlanar.sharp_integral_piece_bound_e` and `OAI.SharpPlanar.sharp_moment_bound_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E033
import Definitions.Def_OAIQ098E034
import Definitions.Def_OAIQ098E035
import Definitions.Def_OAIQ098E036
import Definitions.Def_OAIQ098E037
import Definitions.Def_OAIQ098E038
import Definitions.Def_OAIQ098E039
import Definitions.Def_OAIQ098E040
import Definitions.Def_OAIQ098E041
import Definitions.Def_OAIQ098E042
import Definitions.Def_OAIQ098E043
import Definitions.Def_OAIQ098E044
import Definitions.Def_OAIQ098E045
import Definitions.Def_OAIQ098E046
import Definitions.Def_OAIQ098E047
import Definitions.Def_OAIQ098E048
import Definitions.Def_OAIQ098E049
import Definitions.Def_OAIQ098E050
import Definitions.Def_OAIQ098E051
import Definitions.Def_OAIQ098E052
import Definitions.Def_OAIQ098E053
import Definitions.Def_OAIQ098E054
import Definitions.Def_OAIQ098E055
import Definitions.Def_OAIQ098E056
import Definitions.Def_OAIQ098E057
import Definitions.Def_OAIQ098E058
import Definitions.Def_OAIQ098E059
import Definitions.Def_OAIQ098E060
import Definitions.Def_OAIQ098E061
import Definitions.Def_OAIQ098E062
import Definitions.Def_OAIQ098E063
import Definitions.Def_OAIQ098E064
import Definitions.Def_OAIQ098E065
import Definitions.Def_OAIQ098E066
import Definitions.Def_OAIQ098E067
import Definitions.Def_OAIQ098E068
import Definitions.Def_OAIQ098E069
import Definitions.Def_OAIQ098E070
import Definitions.Def_OAIQ098E071
import Definitions.Def_OAIQ098E072
import Definitions.Def_OAIQ098E073
import Definitions.Def_OAIQ098E074
import Definitions.Def_OAIQ098E075
import Definitions.Def_OAIQ098E076
import Definitions.Def_OAIQ098E077
import Definitions.Def_OAIQ098E078
import Definitions.Def_OAIQ098E079
import Definitions.Def_OAIQ098E080
import Definitions.Def_OAIQ098E081
import Definitions.Def_OAIQ098E082
import Definitions.Def_OAIQ098E083
import Definitions.Def_OAIQ098E084
import Definitions.Def_OAIQ098E085
import Definitions.Def_OAIQ098E086
import Definitions.Def_OAIQ098E087
import Definitions.Def_OAIQ098E088
import Definitions.Def_OAIQ098E089
import Definitions.Def_OAIQ098E090
import Definitions.Def_OAIQ098E091
import Definitions.Def_OAIQ098E092
import Definitions.Def_OAIQ098E093
import Definitions.Def_OAIQ098E094
import Definitions.Def_OAIQ098E095
import Definitions.Def_OAIQ098E096
import Definitions.Def_OAIQ098E097
import Definitions.Def_OAIQ098E098
import Definitions.Def_OAIQ098E099
import Definitions.Def_OAIQ098E100
import Definitions.Def_OAIQ098E101
import Definitions.Def_OAIQ098E102
import Definitions.Def_OAIQ098E103
import Definitions.Def_OAIQ098E104
import Definitions.Def_OAIQ098E105
import Definitions.Def_OAIQ098E106
import Definitions.Def_OAIQ098E107
import Definitions.Def_OAIQ098E108
import Definitions.Def_OAIQ098E109
import Definitions.Def_OAIQ098E110
import Definitions.Def_OAIQ098E111
import Definitions.Def_OAIQ098E112
import Definitions.Def_OAIQ098E113
import Definitions.Def_OAIQ098E114
import Definitions.Def_OAIQ098E115
import Definitions.Def_OAIQ098E116
import Definitions.Def_OAIQ098E117
import Definitions.Def_OAIQ098E118
import Definitions.Def_OAIQ098E119
import Definitions.Def_OAIQ098E120
import Definitions.Def_OAIQ098E121
import Definitions.Def_OAIQ098E122
import Definitions.Def_OAIQ098E123
import Definitions.Def_OAIQ098E124
import Definitions.Def_OAIQ098E125

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerIntervals

instance instDecidableSqNormCheck (a : CBox) (m n : ℤ) : Decidable (a.SqNormCheck m n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

noncomputable def densityCap (j : Fin 6) : ℝ := (densityNum j:ℝ)/(densityDen j:ℝ)

def DensityCheck (n : ℕ) (j : Fin 6) : Prop :=
  (uAmplitudeBox (RBox.rat j.val 6) (aLookup n j) (bLookup n j)).SqNormCheck (densityNum j) (densityDen j) ∧
  (uAmplitudeBox (RBox.rat (j.val+1) 6) (aLookup n j) (bLookup n j)).SqNormCheck (densityNum j) (densityDen j) ∧
  (vAmplitudeBox (aLookup n j)).SqNormCheck (densityNum j) (densityDen j)
instance instDecidableDensityCheck (n : ℕ) (j : Fin 6) : Decidable (DensityCheck n j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerBasis


noncomputable def rowFactor (j : Fin 6) (n : ℕ) : ℝ :=
  (1+|D n|+Real.pi*zCap ⟨j.val,by omega⟩)/Q n*densityCap j
noncomputable def rowPiece (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then rowFactor j n * pieceL j n else 0
noncomputable def rowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
    (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def factorRational (j : Fin 6) (n : ℕ) : ℝ :=
  (1+rowDUpper n+(31416/10000:ℝ)*zCap ⟨j.val,by omega⟩)/rowQLower n*densityCap j
noncomputable def pieceRational (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then factorRational j n *
    (lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n) else 0
noncomputable def tableRational (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, pieceRational j (N+1+a.val))/(1-pieceBase j^12)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def amp7_10 : Fin 16 → Fin 16 → CBox := ![amp7_10_0,amp7_10_1,amp7_10_2,amp7_10_3,amp7_10_4,amp7_10_5,amp7_10_6,amp7_10_7,amp7_10_8,amp7_10_9,amp7_10_10,amp7_10_11,amp7_10_12,amp7_10_13,amp7_10_14,amp7_10_15]
noncomputable def amp7_15 : Fin 16 → Fin 16 → CBox := ![amp7_15_0,amp7_15_1,amp7_15_2,amp7_15_3,amp7_15_4,amp7_15_5,amp7_15_6,amp7_15_7,amp7_15_8,amp7_15_9,amp7_15_10,amp7_15_11,amp7_15_12,amp7_15_13,amp7_15_14,amp7_15_15]
noncomputable def amp7_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp7_10,amp7_11,amp7_12,amp7_13,amp7_14,amp7_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power5_r5 : Fin 16 → Fin 16 → CBox := ![power5_r5_0,power5_r5_1,power5_r5_2,power5_r5_3,power5_r5_4,power5_r5_5,power5_r5_6,power5_r5_7,power5_r5_8,power5_r5_9,power5_r5_10,power5_r5_11,power5_r5_12,power5_r5_13,power5_r5_14,power5_r5_15]
noncomputable def power5 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power5_r0,power5_r1,power5_r2,power5_r3,power5_r4,power5_r5]
noncomputable def power6Expr (j : Fin 6) (i k : Fin 16) : CBox := (power5 j i k).mul (gridRows j i k).direct
noncomputable def power7Expr (j : Fin 6) (i k : Fin 16) : CBox := (power6 j i k).mul (gridRows j i k).direct
noncomputable def power7_r2 : Fin 16 → Fin 16 → CBox := ![power7_r2_0,power7_r2_1,power7_r2_2,power7_r2_3,power7_r2_4,power7_r2_5,power7_r2_6,power7_r2_7,power7_r2_8,power7_r2_9,power7_r2_10,power7_r2_11,power7_r2_12,power7_r2_13,power7_r2_14,power7_r2_15]
noncomputable def power7 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power7_r0,power7_r1,power7_r2,power7_r3,power7_r4,power7_r5]
noncomputable def power8Expr (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).mul (gridRows j i k).direct
noncomputable def power8_r3 : Fin 16 → Fin 16 → CBox := ![power8_r3_0,power8_r3_1,power8_r3_2,power8_r3_3,power8_r3_4,power8_r3_5,power8_r3_6,power8_r3_7,power8_r3_8,power8_r3_9,power8_r3_10,power8_r3_11,power8_r3_12,power8_r3_13,power8_r3_14,power8_r3_15]
noncomputable def power8 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power8_r0,power8_r1,power8_r2,power8_r3,power8_r4,power8_r5]
noncomputable def power9Expr (j : Fin 6) (i k : Fin 16) : CBox := (power8 j i k).mul (gridRows j i k).direct
noncomputable def power9 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power9_r0,power9_r1,power9_r2,power9_r3,power9_r4,power9_r5]
noncomputable def power10Expr (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column7_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power7 j i k)
noncomputable def column7_0_r3 : Fin 16 → Fin 16 → CBox := ![column7_0_r3_0,column7_0_r3_1,column7_0_r3_2,column7_0_r3_3,column7_0_r3_4,column7_0_r3_5,column7_0_r3_6,column7_0_r3_7,column7_0_r3_8,column7_0_r3_9,column7_0_r3_10,column7_0_r3_11,column7_0_r3_12,column7_0_r3_13,column7_0_r3_14,column7_0_r3_15]
noncomputable def column7_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column7_0_r0,column7_0_r1,column7_0_r2,column7_0_r3,column7_0_r4,column7_0_r5]
noncomputable def column7_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power7 j i k)
noncomputable def column9_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power9 j i k)
noncomputable def column9_0_r2 : Fin 16 → Fin 16 → CBox := ![column9_0_r2_0,column9_0_r2_1,column9_0_r2_2,column9_0_r2_3,column9_0_r2_4,column9_0_r2_5,column9_0_r2_6,column9_0_r2_7,column9_0_r2_8,column9_0_r2_9,column9_0_r2_10,column9_0_r2_11,column9_0_r2_12,column9_0_r2_13,column9_0_r2_14,column9_0_r2_15]
noncomputable def column9_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column9_0_r0,column9_0_r1,column9_0_r2,column9_0_r3,column9_0_r4,column9_0_r5]
noncomputable def column9_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power9 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers20
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power11_r3 : Fin 16 → Fin 16 → CBox := ![power11_r3_0,power11_r3_1,power11_r3_2,power11_r3_3,power11_r3_4,power11_r3_5,power11_r3_6,power11_r3_7,power11_r3_8,power11_r3_9,power11_r3_10,power11_r3_11,power11_r3_12,power11_r3_13,power11_r3_14,power11_r3_15]
noncomputable def power11 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power11_r0,power11_r1,power11_r2,power11_r3,power11_r4,power11_r5]
noncomputable def power12Expr (j : Fin 6) (i k : Fin 16) : CBox := (power11 j i k).mul (gridRows j i k).direct
noncomputable def power15_r0 : Fin 16 → Fin 16 → CBox := ![power15_r0_0,power15_r0_1,power15_r0_2,power15_r0_3,power15_r0_4,power15_r0_5,power15_r0_6,power15_r0_7,power15_r0_8,power15_r0_9,power15_r0_10,power15_r0_11,power15_r0_12,power15_r0_13,power15_r0_14,power15_r0_15]
noncomputable def power15 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power15_r0,power15_r1,power15_r2,power15_r3,power15_r4,power15_r5]
noncomputable def power16Expr (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).mul (gridRows j i k).direct
noncomputable def power17Expr (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).mul (gridRows j i k).direct
noncomputable def power18_r1 : Fin 16 → Fin 16 → CBox := ![power18_r1_0,power18_r1_1,power18_r1_2,power18_r1_3,power18_r1_4,power18_r1_5,power18_r1_6,power18_r1_7,power18_r1_8,power18_r1_9,power18_r1_10,power18_r1_11,power18_r1_12,power18_r1_13,power18_r1_14,power18_r1_15]
noncomputable def power18 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power18_r0,power18_r1,power18_r2,power18_r3,power18_r4,power18_r5]
noncomputable def power19Expr (j : Fin 6) (i k : Fin 16) : CBox := (power18 j i k).mul (gridRows j i k).direct
noncomputable def power19_r5 : Fin 16 → Fin 16 → CBox := ![power19_r5_0,power19_r5_1,power19_r5_2,power19_r5_3,power19_r5_4,power19_r5_5,power19_r5_6,power19_r5_7,power19_r5_8,power19_r5_9,power19_r5_10,power19_r5_11,power19_r5_12,power19_r5_13,power19_r5_14,power19_r5_15]
noncomputable def power19 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power19_r0,power19_r1,power19_r2,power19_r3,power19_r4,power19_r5]
noncomputable def power20Expr (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power22Expr (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).mul (gridRows j i k).direct
noncomputable def power23_r0 : Fin 16 → Fin 16 → CBox := ![power23_r0_0,power23_r0_1,power23_r0_2,power23_r0_3,power23_r0_4,power23_r0_5,power23_r0_6,power23_r0_7,power23_r0_8,power23_r0_9,power23_r0_10,power23_r0_11,power23_r0_12,power23_r0_13,power23_r0_14,power23_r0_15]
noncomputable def power23 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power23_r0,power23_r1,power23_r2,power23_r3,power23_r4,power23_r5]
noncomputable def power24Expr (j : Fin 6) (i k : Fin 16) : CBox := (power23 j i k).mul (gridRows j i k).direct
noncomputable def power25Expr (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).mul (gridRows j i k).direct
noncomputable def power25_r3 : Fin 16 → Fin 16 → CBox := ![power25_r3_0,power25_r3_1,power25_r3_2,power25_r3_3,power25_r3_4,power25_r3_5,power25_r3_6,power25_r3_7,power25_r3_8,power25_r3_9,power25_r3_10,power25_r3_11,power25_r3_12,power25_r3_13,power25_r3_14,power25_r3_15]
noncomputable def power25 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power25_r0,power25_r1,power25_r2,power25_r3,power25_r4,power25_r5]
noncomputable def power26Expr (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).mul (gridRows j i k).direct
noncomputable def power29Expr (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).mul (gridRows j i k).direct
noncomputable def power29_r5 : Fin 16 → Fin 16 → CBox := ![power29_r5_0,power29_r5_1,power29_r5_2,power29_r5_3,power29_r5_4,power29_r5_5,power29_r5_6,power29_r5_7,power29_r5_8,power29_r5_9,power29_r5_10,power29_r5_11,power29_r5_12,power29_r5_13,power29_r5_14,power29_r5_15]
noncomputable def power29 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power29_r0,power29_r1,power29_r2,power29_r3,power29_r4,power29_r5]
noncomputable def power30Expr (j : Fin 6) (i k : Fin 16) : CBox := (power29 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power34_r3 : Fin 16 → Fin 16 → CBox := ![power34_r3_0,power34_r3_1,power34_r3_2,power34_r3_3,power34_r3_4,power34_r3_5,power34_r3_6,power34_r3_7,power34_r3_8,power34_r3_9,power34_r3_10,power34_r3_11,power34_r3_12,power34_r3_13,power34_r3_14,power34_r3_15]
noncomputable def power34 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power34_r0,power34_r1,power34_r2,power34_r3,power34_r4,power34_r5]
noncomputable def power35Expr (j : Fin 6) (i k : Fin 16) : CBox := (power34 j i k).mul (gridRows j i k).direct
noncomputable def power37_r1 : Fin 16 → Fin 16 → CBox := ![power37_r1_0,power37_r1_1,power37_r1_2,power37_r1_3,power37_r1_4,power37_r1_5,power37_r1_6,power37_r1_7,power37_r1_8,power37_r1_9,power37_r1_10,power37_r1_11,power37_r1_12,power37_r1_13,power37_r1_14,power37_r1_15]
noncomputable def power37 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power37_r0,power37_r1,power37_r2,power37_r3,power37_r4,power37_r5]
noncomputable def power38Expr (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).mul (gridRows j i k).direct
noncomputable def power40_r5 : Fin 16 → Fin 16 → CBox := ![power40_r5_0,power40_r5_1,power40_r5_2,power40_r5_3,power40_r5_4,power40_r5_5,power40_r5_6,power40_r5_7,power40_r5_8,power40_r5_9,power40_r5_10,power40_r5_11,power40_r5_12,power40_r5_13,power40_r5_14,power40_r5_15]
noncomputable def power40 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power40_r0,power40_r1,power40_r2,power40_r3,power40_r4,power40_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers50
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power41Expr (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).mul (gridRows j i k).direct
noncomputable def power41_r2 : Fin 16 → Fin 16 → CBox := ![power41_r2_0,power41_r2_1,power41_r2_2,power41_r2_3,power41_r2_4,power41_r2_5,power41_r2_6,power41_r2_7,power41_r2_8,power41_r2_9,power41_r2_10,power41_r2_11,power41_r2_12,power41_r2_13,power41_r2_14,power41_r2_15]
noncomputable def power41 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power41_r0,power41_r1,power41_r2,power41_r3,power41_r4,power41_r5]
noncomputable def power42Expr (j : Fin 6) (i k : Fin 16) : CBox := (power41 j i k).mul (gridRows j i k).direct
noncomputable def power46 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power46_r0,power46_r1,power46_r2,power46_r3,power46_r4,power46_r5]
noncomputable def power47Expr (j : Fin 6) (i k : Fin 16) : CBox := (power46 j i k).mul (gridRows j i k).direct
noncomputable def power48_r4 : Fin 16 → Fin 16 → CBox := ![power48_r4_0,power48_r4_1,power48_r4_2,power48_r4_3,power48_r4_4,power48_r4_5,power48_r4_6,power48_r4_7,power48_r4_8,power48_r4_9,power48_r4_10,power48_r4_11,power48_r4_12,power48_r4_13,power48_r4_14,power48_r4_15]
noncomputable def power48 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power48_r0,power48_r1,power48_r2,power48_r3,power48_r4,power48_r5]
noncomputable def power49Expr (j : Fin 6) (i k : Fin 16) : CBox := (power48 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers60
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power52_r3 : Fin 16 → Fin 16 → CBox := ![power52_r3_0,power52_r3_1,power52_r3_2,power52_r3_3,power52_r3_4,power52_r3_5,power52_r3_6,power52_r3_7,power52_r3_8,power52_r3_9,power52_r3_10,power52_r3_11,power52_r3_12,power52_r3_13,power52_r3_14,power52_r3_15]
noncomputable def power52 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power52_r0,power52_r1,power52_r2,power52_r3,power52_r4,power52_r5]
noncomputable def power53Expr (j : Fin 6) (i k : Fin 16) : CBox := (power52 j i k).mul (gridRows j i k).direct
noncomputable def power54_r4 : Fin 16 → Fin 16 → CBox := ![power54_r4_0,power54_r4_1,power54_r4_2,power54_r4_3,power54_r4_4,power54_r4_5,power54_r4_6,power54_r4_7,power54_r4_8,power54_r4_9,power54_r4_10,power54_r4_11,power54_r4_12,power54_r4_13,power54_r4_14,power54_r4_15]
noncomputable def power54 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power54_r0,power54_r1,power54_r2,power54_r3,power54_r4,power54_r5]
noncomputable def power55Expr (j : Fin 6) (i k : Fin 16) : CBox := (power54 j i k).mul (gridRows j i k).direct
noncomputable def power56Expr (j : Fin 6) (i k : Fin 16) : CBox := (power55 j i k).mul (gridRows j i k).direct
noncomputable def power58Expr (j : Fin 6) (i k : Fin 16) : CBox := (power57 j i k).mul (gridRows j i k).direct
noncomputable def power59_r2 : Fin 16 → Fin 16 → CBox := ![power59_r2_0,power59_r2_1,power59_r2_2,power59_r2_3,power59_r2_4,power59_r2_5,power59_r2_6,power59_r2_7,power59_r2_8,power59_r2_9,power59_r2_10,power59_r2_11,power59_r2_12,power59_r2_13,power59_r2_14,power59_r2_15]
noncomputable def power59 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power59_r0,power59_r1,power59_r2,power59_r3,power59_r4,power59_r5]
noncomputable def power60Expr (j : Fin 6) (i k : Fin 16) : CBox := (power59 j i k).mul (gridRows j i k).direct
noncomputable def power60_r1 : Fin 16 → Fin 16 → CBox := ![power60_r1_0,power60_r1_1,power60_r1_2,power60_r1_3,power60_r1_4,power60_r1_5,power60_r1_6,power60_r1_7,power60_r1_8,power60_r1_9,power60_r1_10,power60_r1_11,power60_r1_12,power60_r1_13,power60_r1_14,power60_r1_15]
noncomputable def power60 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power60_r0,power60_r1,power60_r2,power60_r3,power60_r4,power60_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers70
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power61Expr (j : Fin 6) (i k : Fin 16) : CBox := (power60 j i k).mul (gridRows j i k).direct
noncomputable def power62Expr (j : Fin 6) (i k : Fin 16) : CBox := (power61 j i k).mul (gridRows j i k).direct
noncomputable def power64Expr (j : Fin 6) (i k : Fin 16) : CBox := (power63 j i k).mul (gridRows j i k).direct
noncomputable def power64_r0 : Fin 16 → Fin 16 → CBox := ![power64_r0_0,power64_r0_1,power64_r0_2,power64_r0_3,power64_r0_4,power64_r0_5,power64_r0_6,power64_r0_7,power64_r0_8,power64_r0_9,power64_r0_10,power64_r0_11,power64_r0_12,power64_r0_13,power64_r0_14,power64_r0_15]
noncomputable def power64 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power64_r0,power64_r1,power64_r2,power64_r3,power64_r4,power64_r5]
noncomputable def power65Expr (j : Fin 6) (i k : Fin 16) : CBox := (power64 j i k).mul (gridRows j i k).direct
noncomputable def power65_r1 : Fin 16 → Fin 16 → CBox := ![power65_r1_0,power65_r1_1,power65_r1_2,power65_r1_3,power65_r1_4,power65_r1_5,power65_r1_6,power65_r1_7,power65_r1_8,power65_r1_9,power65_r1_10,power65_r1_11,power65_r1_12,power65_r1_13,power65_r1_14,power65_r1_15]
noncomputable def power65 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power65_r0,power65_r1,power65_r2,power65_r3,power65_r4,power65_r5]
noncomputable def power66Expr (j : Fin 6) (i k : Fin 16) : CBox := (power65 j i k).mul (gridRows j i k).direct
noncomputable def power69_r5 : Fin 16 → Fin 16 → CBox := ![power69_r5_0,power69_r5_1,power69_r5_2,power69_r5_3,power69_r5_4,power69_r5_5,power69_r5_6,power69_r5_7,power69_r5_8,power69_r5_9,power69_r5_10,power69_r5_11,power69_r5_12,power69_r5_13,power69_r5_14,power69_r5_15]
noncomputable def power69 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power69_r0,power69_r1,power69_r2,power69_r3,power69_r4,power69_r5]
noncomputable def power70Expr (j : Fin 6) (i k : Fin 16) : CBox := (power69 j i k).mul (gridRows j i k).direct
noncomputable def power70_r0 : Fin 16 → Fin 16 → CBox := ![power70_r0_0,power70_r0_1,power70_r0_2,power70_r0_3,power70_r0_4,power70_r0_5,power70_r0_6,power70_r0_7,power70_r0_8,power70_r0_9,power70_r0_10,power70_r0_11,power70_r0_12,power70_r0_13,power70_r0_14,power70_r0_15]
noncomputable def power70 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power70_r0,power70_r1,power70_r2,power70_r3,power70_r4,power70_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers80
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power71Expr (j : Fin 6) (i k : Fin 16) : CBox := (power70 j i k).mul (gridRows j i k).direct
noncomputable def power73Expr (j : Fin 6) (i k : Fin 16) : CBox := (power72 j i k).mul (gridRows j i k).direct
noncomputable def power74Expr (j : Fin 6) (i k : Fin 16) : CBox := (power73 j i k).mul (gridRows j i k).direct
noncomputable def power74_r4 : Fin 16 → Fin 16 → CBox := ![power74_r4_0,power74_r4_1,power74_r4_2,power74_r4_3,power74_r4_4,power74_r4_5,power74_r4_6,power74_r4_7,power74_r4_8,power74_r4_9,power74_r4_10,power74_r4_11,power74_r4_12,power74_r4_13,power74_r4_14,power74_r4_15]
noncomputable def power74 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power74_r0,power74_r1,power74_r2,power74_r3,power74_r4,power74_r5]
noncomputable def power75Expr (j : Fin 6) (i k : Fin 16) : CBox := (power74 j i k).mul (gridRows j i k).direct
noncomputable def power75_r3 : Fin 16 → Fin 16 → CBox := ![power75_r3_0,power75_r3_1,power75_r3_2,power75_r3_3,power75_r3_4,power75_r3_5,power75_r3_6,power75_r3_7,power75_r3_8,power75_r3_9,power75_r3_10,power75_r3_11,power75_r3_12,power75_r3_13,power75_r3_14,power75_r3_15]
noncomputable def power75 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power75_r0,power75_r1,power75_r2,power75_r3,power75_r4,power75_r5]
noncomputable def power76Expr (j : Fin 6) (i k : Fin 16) : CBox := (power75 j i k).mul (gridRows j i k).direct
noncomputable def power77Expr (j : Fin 6) (i k : Fin 16) : CBox := (power76 j i k).mul (gridRows j i k).direct
noncomputable def power80Expr (j : Fin 6) (i k : Fin 16) : CBox := (power79 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers90
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power83_r2 : Fin 16 → Fin 16 → CBox := ![power83_r2_0,power83_r2_1,power83_r2_2,power83_r2_3,power83_r2_4,power83_r2_5,power83_r2_6,power83_r2_7,power83_r2_8,power83_r2_9,power83_r2_10,power83_r2_11,power83_r2_12,power83_r2_13,power83_r2_14,power83_r2_15]
noncomputable def power83 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power83_r0,power83_r1,power83_r2,power83_r3,power83_r4,power83_r5]
noncomputable def power84Expr (j : Fin 6) (i k : Fin 16) : CBox := (power83 j i k).mul (gridRows j i k).direct
noncomputable def power85_r1 : Fin 16 → Fin 16 → CBox := ![power85_r1_0,power85_r1_1,power85_r1_2,power85_r1_3,power85_r1_4,power85_r1_5,power85_r1_6,power85_r1_7,power85_r1_8,power85_r1_9,power85_r1_10,power85_r1_11,power85_r1_12,power85_r1_13,power85_r1_14,power85_r1_15]
noncomputable def power85 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power85_r0,power85_r1,power85_r2,power85_r3,power85_r4,power85_r5]
noncomputable def power86Expr (j : Fin 6) (i k : Fin 16) : CBox := (power85 j i k).mul (gridRows j i k).direct
noncomputable def power88_r5 : Fin 16 → Fin 16 → CBox := ![power88_r5_0,power88_r5_1,power88_r5_2,power88_r5_3,power88_r5_4,power88_r5_5,power88_r5_6,power88_r5_7,power88_r5_8,power88_r5_9,power88_r5_10,power88_r5_11,power88_r5_12,power88_r5_13,power88_r5_14,power88_r5_15]
noncomputable def power88 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power88_r0,power88_r1,power88_r2,power88_r3,power88_r4,power88_r5]
noncomputable def power89Expr (j : Fin 6) (i k : Fin 16) : CBox := (power88 j i k).mul (gridRows j i k).direct
noncomputable def power90_r0 : Fin 16 → Fin 16 → CBox := ![power90_r0_0,power90_r0_1,power90_r0_2,power90_r0_3,power90_r0_4,power90_r0_5,power90_r0_6,power90_r0_7,power90_r0_8,power90_r0_9,power90_r0_10,power90_r0_11,power90_r0_12,power90_r0_13,power90_r0_14,power90_r0_15]
noncomputable def power90 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power90_r0,power90_r1,power90_r2,power90_r3,power90_r4,power90_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers100
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def power91Expr (j : Fin 6) (i k : Fin 16) : CBox := (power90 j i k).mul (gridRows j i k).direct
noncomputable def power92Expr (j : Fin 6) (i k : Fin 16) : CBox := (power91 j i k).mul (gridRows j i k).direct
noncomputable def power94Expr (j : Fin 6) (i k : Fin 16) : CBox := (power93 j i k).mul (gridRows j i k).direct
noncomputable def power94_r5 : Fin 16 → Fin 16 → CBox := ![power94_r5_0,power94_r5_1,power94_r5_2,power94_r5_3,power94_r5_4,power94_r5_5,power94_r5_6,power94_r5_7,power94_r5_8,power94_r5_9,power94_r5_10,power94_r5_11,power94_r5_12,power94_r5_13,power94_r5_14,power94_r5_15]
noncomputable def power94 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power94_r0,power94_r1,power94_r2,power94_r3,power94_r4,power94_r5]
noncomputable def power95Expr (j : Fin 6) (i k : Fin 16) : CBox := (power94 j i k).mul (gridRows j i k).direct
noncomputable def power96_r4 : Fin 16 → Fin 16 → CBox := ![power96_r4_0,power96_r4_1,power96_r4_2,power96_r4_3,power96_r4_4,power96_r4_5,power96_r4_6,power96_r4_7,power96_r4_8,power96_r4_9,power96_r4_10,power96_r4_11,power96_r4_12,power96_r4_13,power96_r4_14,power96_r4_15]
noncomputable def power96 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power96_r0,power96_r1,power96_r2,power96_r3,power96_r4,power96_r5]
noncomputable def power97Expr (j : Fin 6) (i k : Fin 16) : CBox := (power96 j i k).mul (gridRows j i k).direct
noncomputable def power98Expr (j : Fin 6) (i k : Fin 16) : CBox := (power97 j i k).mul (gridRows j i k).direct
noncomputable def power100_r1 : Fin 16 → Fin 16 → CBox := ![power100_r1_0,power100_r1_1,power100_r1_2,power100_r1_3,power100_r1_4,power100_r1_5,power100_r1_6,power100_r1_7,power100_r1_8,power100_r1_9,power100_r1_10,power100_r1_11,power100_r1_12,power100_r1_13,power100_r1_14,power100_r1_15]
noncomputable def power100 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power100_r0,power100_r1,power100_r2,power100_r3,power100_r4,power100_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column91_0_r2 : Fin 16 → Fin 16 → CBox := ![column91_0_r2_0,column91_0_r2_1,column91_0_r2_2,column91_0_r2_3,column91_0_r2_4,column91_0_r2_5,column91_0_r2_6,column91_0_r2_7,column91_0_r2_8,column91_0_r2_9,column91_0_r2_10,column91_0_r2_11,column91_0_r2_12,column91_0_r2_13,column91_0_r2_14,column91_0_r2_15]
noncomputable def column91_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column91_0_r0,column91_0_r1,column91_0_r2,column91_0_r3,column91_0_r4,column91_0_r5]
noncomputable def column91_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power91 j i k)
noncomputable def column93_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power93 j i k)
noncomputable def column93_0_r2 : Fin 16 → Fin 16 → CBox := ![column93_0_r2_0,column93_0_r2_1,column93_0_r2_2,column93_0_r2_3,column93_0_r2_4,column93_0_r2_5,column93_0_r2_6,column93_0_r2_7,column93_0_r2_8,column93_0_r2_9,column93_0_r2_10,column93_0_r2_11,column93_0_r2_12,column93_0_r2_13,column93_0_r2_14,column93_0_r2_15]
noncomputable def column93_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column93_0_r0,column93_0_r1,column93_0_r2,column93_0_r3,column93_0_r4,column93_0_r5]
noncomputable def column93_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power93 j i k)
noncomputable def column96_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power96 j i k)
noncomputable def column96_0_r2 : Fin 16 → Fin 16 → CBox := ![column96_0_r2_0,column96_0_r2_1,column96_0_r2_2,column96_0_r2_3,column96_0_r2_4,column96_0_r2_5,column96_0_r2_6,column96_0_r2_7,column96_0_r2_8,column96_0_r2_9,column96_0_r2_10,column96_0_r2_11,column96_0_r2_12,column96_0_r2_13,column96_0_r2_14,column96_0_r2_15]
noncomputable def column96_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column96_0_r0,column96_0_r1,column96_0_r2,column96_0_r3,column96_0_r4,column96_0_r5]
noncomputable def column96_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power96 j i k)
noncomputable def column97_0_r2 : Fin 16 → Fin 16 → CBox := ![column97_0_r2_0,column97_0_r2_1,column97_0_r2_2,column97_0_r2_3,column97_0_r2_4,column97_0_r2_5,column97_0_r2_6,column97_0_r2_7,column97_0_r2_8,column97_0_r2_9,column97_0_r2_10,column97_0_r2_11,column97_0_r2_12,column97_0_r2_13,column97_0_r2_14,column97_0_r2_15]
noncomputable def column97_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column97_0_r0,column97_0_r1,column97_0_r2,column97_0_r3,column97_0_r4,column97_0_r5]
noncomputable def column99_0_r2 : Fin 16 → Fin 16 → CBox := ![column99_0_r2_0,column99_0_r2_1,column99_0_r2_2,column99_0_r2_3,column99_0_r2_4,column99_0_r2_5,column99_0_r2_6,column99_0_r2_7,column99_0_r2_8,column99_0_r2_9,column99_0_r2_10,column99_0_r2_11,column99_0_r2_12,column99_0_r2_13,column99_0_r2_14,column99_0_r2_15]
noncomputable def column99_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column99_0_r0,column99_0_r1,column99_0_r2,column99_0_r3,column99_0_r4,column99_0_r5]
noncomputable def column100_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power100 j i k)
noncomputable def column100_0_r0 : Fin 16 → Fin 16 → CBox := ![column100_0_r0_0,column100_0_r0_1,column100_0_r0_2,column100_0_r0_3,column100_0_r0_4,column100_0_r0_5,column100_0_r0_6,column100_0_r0_7,column100_0_r0_8,column100_0_r0_9,column100_0_r0_10,column100_0_r0_11,column100_0_r0_12,column100_0_r0_13,column100_0_r0_14,column100_0_r0_15]
noncomputable def column100_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column100_0_r0,column100_0_r1,column100_0_r2,column100_0_r3,column100_0_r4,column100_0_r5]
noncomputable def column100_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power100 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns20
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column12_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power12 j i k)
noncomputable def column12_0_r0 : Fin 16 → Fin 16 → CBox := ![column12_0_r0_0,column12_0_r0_1,column12_0_r0_2,column12_0_r0_3,column12_0_r0_4,column12_0_r0_5,column12_0_r0_6,column12_0_r0_7,column12_0_r0_8,column12_0_r0_9,column12_0_r0_10,column12_0_r0_11,column12_0_r0_12,column12_0_r0_13,column12_0_r0_14,column12_0_r0_15]
noncomputable def column12_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column12_0_r0,column12_0_r1,column12_0_r2,column12_0_r3,column12_0_r4,column12_0_r5]
noncomputable def column12_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power12 j i k)
noncomputable def column13_0_r0 : Fin 16 → Fin 16 → CBox := ![column13_0_r0_0,column13_0_r0_1,column13_0_r0_2,column13_0_r0_3,column13_0_r0_4,column13_0_r0_5,column13_0_r0_6,column13_0_r0_7,column13_0_r0_8,column13_0_r0_9,column13_0_r0_10,column13_0_r0_11,column13_0_r0_12,column13_0_r0_13,column13_0_r0_14,column13_0_r0_15]
noncomputable def column13_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column13_0_r0,column13_0_r1,column13_0_r2,column13_0_r3,column13_0_r4,column13_0_r5]
noncomputable def column15_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power15 j i k)
noncomputable def column15_0_r0 : Fin 16 → Fin 16 → CBox := ![column15_0_r0_0,column15_0_r0_1,column15_0_r0_2,column15_0_r0_3,column15_0_r0_4,column15_0_r0_5,column15_0_r0_6,column15_0_r0_7,column15_0_r0_8,column15_0_r0_9,column15_0_r0_10,column15_0_r0_11,column15_0_r0_12,column15_0_r0_13,column15_0_r0_14,column15_0_r0_15]
noncomputable def column15_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column15_0_r0,column15_0_r1,column15_0_r2,column15_0_r3,column15_0_r4,column15_0_r5]
noncomputable def column15_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power15 j i k)
noncomputable def column16_0_r0 : Fin 16 → Fin 16 → CBox := ![column16_0_r0_0,column16_0_r0_1,column16_0_r0_2,column16_0_r0_3,column16_0_r0_4,column16_0_r0_5,column16_0_r0_6,column16_0_r0_7,column16_0_r0_8,column16_0_r0_9,column16_0_r0_10,column16_0_r0_11,column16_0_r0_12,column16_0_r0_13,column16_0_r0_14,column16_0_r0_15]
noncomputable def column16_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column16_0_r0,column16_0_r1,column16_0_r2,column16_0_r3,column16_0_r4,column16_0_r5]
noncomputable def column19_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power19 j i k)
noncomputable def column19_0_r0 : Fin 16 → Fin 16 → CBox := ![column19_0_r0_0,column19_0_r0_1,column19_0_r0_2,column19_0_r0_3,column19_0_r0_4,column19_0_r0_5,column19_0_r0_6,column19_0_r0_7,column19_0_r0_8,column19_0_r0_9,column19_0_r0_10,column19_0_r0_11,column19_0_r0_12,column19_0_r0_13,column19_0_r0_14,column19_0_r0_15]
noncomputable def column19_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column19_0_r0,column19_0_r1,column19_0_r2,column19_0_r3,column19_0_r4,column19_0_r5]
noncomputable def column19_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power19 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns30
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column21_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power21 j i k)
noncomputable def column21_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power21 j i k)
noncomputable def column24_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power24 j i k)
noncomputable def column24_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power24 j i k)
noncomputable def column25_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power25 j i k)
noncomputable def column25_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power25 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns40
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column31_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power31 j i k)
noncomputable def column33_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power33 j i k)
noncomputable def column33_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power33 j i k)
noncomputable def column36_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power36 j i k)
noncomputable def column36_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power36 j i k)
noncomputable def column37_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power37 j i k)
noncomputable def column37_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power37 j i k)
noncomputable def column40_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power40 j i k)
noncomputable def column40_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power40 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns50
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column43_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power43 j i k)
noncomputable def column43_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power43 j i k)
noncomputable def column45_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power45 j i k)
noncomputable def column45_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power45 j i k)
noncomputable def column48_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power48 j i k)
noncomputable def column48_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power48 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns60
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column52_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power52 j i k)
noncomputable def column52_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power52 j i k)
noncomputable def column55_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power55 j i k)
noncomputable def column55_0_r5 : Fin 16 → Fin 16 → CBox := ![column55_0_r5_0,column55_0_r5_1,column55_0_r5_2,column55_0_r5_3,column55_0_r5_4,column55_0_r5_5,column55_0_r5_6,column55_0_r5_7,column55_0_r5_8,column55_0_r5_9,column55_0_r5_10,column55_0_r5_11,column55_0_r5_12,column55_0_r5_13,column55_0_r5_14,column55_0_r5_15]
noncomputable def column55_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column55_0_r0,column55_0_r1,column55_0_r2,column55_0_r3,column55_0_r4,column55_0_r5]
noncomputable def column55_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power55 j i k)
noncomputable def column57_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power57 j i k)
noncomputable def column57_0_r5 : Fin 16 → Fin 16 → CBox := ![column57_0_r5_0,column57_0_r5_1,column57_0_r5_2,column57_0_r5_3,column57_0_r5_4,column57_0_r5_5,column57_0_r5_6,column57_0_r5_7,column57_0_r5_8,column57_0_r5_9,column57_0_r5_10,column57_0_r5_11,column57_0_r5_12,column57_0_r5_13,column57_0_r5_14,column57_0_r5_15]
noncomputable def column57_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column57_0_r0,column57_0_r1,column57_0_r2,column57_0_r3,column57_0_r4,column57_0_r5]
noncomputable def column57_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power57 j i k)
noncomputable def column60_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power60 j i k)
noncomputable def column60_0_r5 : Fin 16 → Fin 16 → CBox := ![column60_0_r5_0,column60_0_r5_1,column60_0_r5_2,column60_0_r5_3,column60_0_r5_4,column60_0_r5_5,column60_0_r5_6,column60_0_r5_7,column60_0_r5_8,column60_0_r5_9,column60_0_r5_10,column60_0_r5_11,column60_0_r5_12,column60_0_r5_13,column60_0_r5_14,column60_0_r5_15]
noncomputable def column60_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column60_0_r0,column60_0_r1,column60_0_r2,column60_0_r3,column60_0_r4,column60_0_r5]
noncomputable def column60_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power60 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns70
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column61_0_r5 : Fin 16 → Fin 16 → CBox := ![column61_0_r5_0,column61_0_r5_1,column61_0_r5_2,column61_0_r5_3,column61_0_r5_4,column61_0_r5_5,column61_0_r5_6,column61_0_r5_7,column61_0_r5_8,column61_0_r5_9,column61_0_r5_10,column61_0_r5_11,column61_0_r5_12,column61_0_r5_13,column61_0_r5_14,column61_0_r5_15]
noncomputable def column61_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column61_0_r0,column61_0_r1,column61_0_r2,column61_0_r3,column61_0_r4,column61_0_r5]
noncomputable def column63_0_r5 : Fin 16 → Fin 16 → CBox := ![column63_0_r5_0,column63_0_r5_1,column63_0_r5_2,column63_0_r5_3,column63_0_r5_4,column63_0_r5_5,column63_0_r5_6,column63_0_r5_7,column63_0_r5_8,column63_0_r5_9,column63_0_r5_10,column63_0_r5_11,column63_0_r5_12,column63_0_r5_13,column63_0_r5_14,column63_0_r5_15]
noncomputable def column63_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column63_0_r0,column63_0_r1,column63_0_r2,column63_0_r3,column63_0_r4,column63_0_r5]
noncomputable def column64_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power64 j i k)
noncomputable def column64_0_r5 : Fin 16 → Fin 16 → CBox := ![column64_0_r5_0,column64_0_r5_1,column64_0_r5_2,column64_0_r5_3,column64_0_r5_4,column64_0_r5_5,column64_0_r5_6,column64_0_r5_7,column64_0_r5_8,column64_0_r5_9,column64_0_r5_10,column64_0_r5_11,column64_0_r5_12,column64_0_r5_13,column64_0_r5_14,column64_0_r5_15]
noncomputable def column64_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column64_0_r0,column64_0_r1,column64_0_r2,column64_0_r3,column64_0_r4,column64_0_r5]
noncomputable def column64_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power64 j i k)
noncomputable def column67_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power67 j i k)
noncomputable def column67_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column67_0_r0,column67_0_r1,column67_0_r2,column67_0_r3,column67_0_r4,column67_0_r5]
noncomputable def column67_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power67 j i k)
noncomputable def column69_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power69 j i k)
noncomputable def column69_0_r4 : Fin 16 → Fin 16 → CBox := ![column69_0_r4_0,column69_0_r4_1,column69_0_r4_2,column69_0_r4_3,column69_0_r4_4,column69_0_r4_5,column69_0_r4_6,column69_0_r4_7,column69_0_r4_8,column69_0_r4_9,column69_0_r4_10,column69_0_r4_11,column69_0_r4_12,column69_0_r4_13,column69_0_r4_14,column69_0_r4_15]
noncomputable def column69_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column69_0_r0,column69_0_r1,column69_0_r2,column69_0_r3,column69_0_r4,column69_0_r5]
noncomputable def column69_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power69 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns80
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column72_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power72 j i k)
noncomputable def column72_0_r4 : Fin 16 → Fin 16 → CBox := ![column72_0_r4_0,column72_0_r4_1,column72_0_r4_2,column72_0_r4_3,column72_0_r4_4,column72_0_r4_5,column72_0_r4_6,column72_0_r4_7,column72_0_r4_8,column72_0_r4_9,column72_0_r4_10,column72_0_r4_11,column72_0_r4_12,column72_0_r4_13,column72_0_r4_14,column72_0_r4_15]
noncomputable def column72_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column72_0_r0,column72_0_r1,column72_0_r2,column72_0_r3,column72_0_r4,column72_0_r5]
noncomputable def column72_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power72 j i k)
noncomputable def column73_0_r4 : Fin 16 → Fin 16 → CBox := ![column73_0_r4_0,column73_0_r4_1,column73_0_r4_2,column73_0_r4_3,column73_0_r4_4,column73_0_r4_5,column73_0_r4_6,column73_0_r4_7,column73_0_r4_8,column73_0_r4_9,column73_0_r4_10,column73_0_r4_11,column73_0_r4_12,column73_0_r4_13,column73_0_r4_14,column73_0_r4_15]
noncomputable def column73_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column73_0_r0,column73_0_r1,column73_0_r2,column73_0_r3,column73_0_r4,column73_0_r5]
noncomputable def column75_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power75 j i k)
noncomputable def column75_0_r4 : Fin 16 → Fin 16 → CBox := ![column75_0_r4_0,column75_0_r4_1,column75_0_r4_2,column75_0_r4_3,column75_0_r4_4,column75_0_r4_5,column75_0_r4_6,column75_0_r4_7,column75_0_r4_8,column75_0_r4_9,column75_0_r4_10,column75_0_r4_11,column75_0_r4_12,column75_0_r4_13,column75_0_r4_14,column75_0_r4_15]
noncomputable def column75_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column75_0_r0,column75_0_r1,column75_0_r2,column75_0_r3,column75_0_r4,column75_0_r5]
noncomputable def column75_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power75 j i k)
noncomputable def column76_0_r4 : Fin 16 → Fin 16 → CBox := ![column76_0_r4_0,column76_0_r4_1,column76_0_r4_2,column76_0_r4_3,column76_0_r4_4,column76_0_r4_5,column76_0_r4_6,column76_0_r4_7,column76_0_r4_8,column76_0_r4_9,column76_0_r4_10,column76_0_r4_11,column76_0_r4_12,column76_0_r4_13,column76_0_r4_14,column76_0_r4_15]
noncomputable def column76_0_r5 : Fin 16 → Fin 16 → CBox := ![column76_0_r5_0,column76_0_r5_1,column76_0_r5_2,column76_0_r5_3,column76_0_r5_4,column76_0_r5_5,column76_0_r5_6,column76_0_r5_7,column76_0_r5_8,column76_0_r5_9,column76_0_r5_10,column76_0_r5_11,column76_0_r5_12,column76_0_r5_13,column76_0_r5_14,column76_0_r5_15]
noncomputable def column76_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column76_0_r0,column76_0_r1,column76_0_r2,column76_0_r3,column76_0_r4,column76_0_r5]
noncomputable def column79_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power79 j i k)
noncomputable def column79_0_r4 : Fin 16 → Fin 16 → CBox := ![column79_0_r4_0,column79_0_r4_1,column79_0_r4_2,column79_0_r4_3,column79_0_r4_4,column79_0_r4_5,column79_0_r4_6,column79_0_r4_7,column79_0_r4_8,column79_0_r4_9,column79_0_r4_10,column79_0_r4_11,column79_0_r4_12,column79_0_r4_13,column79_0_r4_14,column79_0_r4_15]
noncomputable def column79_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column79_0_r0,column79_0_r1,column79_0_r2,column79_0_r3,column79_0_r4,column79_0_r5]
noncomputable def column79_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power79 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns90
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def column81_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power81 j i k)
noncomputable def column81_0_r3 : Fin 16 → Fin 16 → CBox := ![column81_0_r3_0,column81_0_r3_1,column81_0_r3_2,column81_0_r3_3,column81_0_r3_4,column81_0_r3_5,column81_0_r3_6,column81_0_r3_7,column81_0_r3_8,column81_0_r3_9,column81_0_r3_10,column81_0_r3_11,column81_0_r3_12,column81_0_r3_13,column81_0_r3_14,column81_0_r3_15]
noncomputable def column81_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column81_0_r0,column81_0_r1,column81_0_r2,column81_0_r3,column81_0_r4,column81_0_r5]
noncomputable def column81_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power81 j i k)
noncomputable def column84_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power84 j i k)
noncomputable def column84_0_r3 : Fin 16 → Fin 16 → CBox := ![column84_0_r3_0,column84_0_r3_1,column84_0_r3_2,column84_0_r3_3,column84_0_r3_4,column84_0_r3_5,column84_0_r3_6,column84_0_r3_7,column84_0_r3_8,column84_0_r3_9,column84_0_r3_10,column84_0_r3_11,column84_0_r3_12,column84_0_r3_13,column84_0_r3_14,column84_0_r3_15]
noncomputable def column84_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column84_0_r0,column84_0_r1,column84_0_r2,column84_0_r3,column84_0_r4,column84_0_r5]
noncomputable def column84_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power84 j i k)
noncomputable def column85_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power85 j i k)
noncomputable def column85_0_r3 : Fin 16 → Fin 16 → CBox := ![column85_0_r3_0,column85_0_r3_1,column85_0_r3_2,column85_0_r3_3,column85_0_r3_4,column85_0_r3_5,column85_0_r3_6,column85_0_r3_7,column85_0_r3_8,column85_0_r3_9,column85_0_r3_10,column85_0_r3_11,column85_0_r3_12,column85_0_r3_13,column85_0_r3_14,column85_0_r3_15]
noncomputable def column85_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column85_0_r0,column85_0_r1,column85_0_r2,column85_0_r3,column85_0_r4,column85_0_r5]
noncomputable def column85_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power85 j i k)
noncomputable def column87_0_r3 : Fin 16 → Fin 16 → CBox := ![column87_0_r3_0,column87_0_r3_1,column87_0_r3_2,column87_0_r3_3,column87_0_r3_4,column87_0_r3_5,column87_0_r3_6,column87_0_r3_7,column87_0_r3_8,column87_0_r3_9,column87_0_r3_10,column87_0_r3_11,column87_0_r3_12,column87_0_r3_13,column87_0_r3_14,column87_0_r3_15]
noncomputable def column87_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column87_0_r0,column87_0_r1,column87_0_r2,column87_0_r3,column87_0_r4,column87_0_r5]
noncomputable def column88_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power88 j i k)
noncomputable def column88_0_r3 : Fin 16 → Fin 16 → CBox := ![column88_0_r3_0,column88_0_r3_1,column88_0_r3_2,column88_0_r3_3,column88_0_r3_4,column88_0_r3_5,column88_0_r3_6,column88_0_r3_7,column88_0_r3_8,column88_0_r3_9,column88_0_r3_10,column88_0_r3_11,column88_0_r3_12,column88_0_r3_13,column88_0_r3_14,column88_0_r3_15]
noncomputable def column88_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column88_0_r0,column88_0_r1,column88_0_r2,column88_0_r3,column88_0_r4,column88_0_r5]
noncomputable def column88_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power88 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def trans8Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans7 j i k).mul (transStep j i k)
noncomputable def trans8_r3 : Fin 16 → Fin 16 → CBox := ![trans8_r3_0,trans8_r3_1,trans8_r3_2,trans8_r3_3,trans8_r3_4,trans8_r3_5,trans8_r3_6,trans8_r3_7,trans8_r3_8,trans8_r3_9,trans8_r3_10,trans8_r3_11,trans8_r3_12,trans8_r3_13,trans8_r3_14,trans8_r3_15]
noncomputable def trans8 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans8_r0,trans8_r1,trans8_r2,trans8_r3,trans8_r4,trans8_r5]
noncomputable def trans9Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans8 j i k).mul (transStep j i k)
noncomputable def trans9_r0 : Fin 16 → Fin 16 → CBox := ![trans9_r0_0,trans9_r0_1,trans9_r0_2,trans9_r0_3,trans9_r0_4,trans9_r0_5,trans9_r0_6,trans9_r0_7,trans9_r0_8,trans9_r0_9,trans9_r0_10,trans9_r0_11,trans9_r0_12,trans9_r0_13,trans9_r0_14,trans9_r0_15]
noncomputable def trans9 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans9_r0,trans9_r1,trans9_r2,trans9_r3,trans9_r4,trans9_r5]
noncomputable def trans10Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans9 j i k).mul (transStep j i k)
noncomputable def trans10_r0 : Fin 16 → Fin 16 → CBox := ![trans10_r0_0,trans10_r0_1,trans10_r0_2,trans10_r0_3,trans10_r0_4,trans10_r0_5,trans10_r0_6,trans10_r0_7,trans10_r0_8,trans10_r0_9,trans10_r0_10,trans10_r0_11,trans10_r0_12,trans10_r0_13,trans10_r0_14,trans10_r0_15]
noncomputable def trans10_r1 : Fin 16 → Fin 16 → CBox := ![trans10_r1_0,trans10_r1_1,trans10_r1_2,trans10_r1_3,trans10_r1_4,trans10_r1_5,trans10_r1_6,trans10_r1_7,trans10_r1_8,trans10_r1_9,trans10_r1_10,trans10_r1_11,trans10_r1_12,trans10_r1_13,trans10_r1_14,trans10_r1_15]
noncomputable def trans10_r2 : Fin 16 → Fin 16 → CBox := ![trans10_r2_0,trans10_r2_1,trans10_r2_2,trans10_r2_3,trans10_r2_4,trans10_r2_5,trans10_r2_6,trans10_r2_7,trans10_r2_8,trans10_r2_9,trans10_r2_10,trans10_r2_11,trans10_r2_12,trans10_r2_13,trans10_r2_14,trans10_r2_15]
noncomputable def trans10 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans10_r0,trans10_r1,trans10_r2,trans10_r3,trans10_r4,trans10_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def kernel7_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans7 j i k)
noncomputable def kernel7_0_r1 : Fin 16 → Fin 16 → CBox := ![kernel7_0_r1_0,kernel7_0_r1_1,kernel7_0_r1_2,kernel7_0_r1_3,kernel7_0_r1_4,kernel7_0_r1_5,kernel7_0_r1_6,kernel7_0_r1_7,kernel7_0_r1_8,kernel7_0_r1_9,kernel7_0_r1_10,kernel7_0_r1_11,kernel7_0_r1_12,kernel7_0_r1_13,kernel7_0_r1_14,kernel7_0_r1_15]
noncomputable def kernel7_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel7_0_r0,kernel7_0_r1,kernel7_0_r2,kernel7_0_r3,kernel7_0_r4,kernel7_0_r5]
noncomputable def kernel7_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans7 j i k)).mul (piI.mul (gridRows j i k).z)
noncomputable def kernel9_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans9 j i k)
noncomputable def kernel9_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans9 j i k)).mul (piI.mul (gridRows j i k).z)
noncomputable def kernel9_1_r4 : Fin 16 → Fin 16 → CBox := ![kernel9_1_r4_0,kernel9_1_r4_1,kernel9_1_r4_2,kernel9_1_r4_3,kernel9_1_r4_4,kernel9_1_r4_5,kernel9_1_r4_6,kernel9_1_r4_7,kernel9_1_r4_8,kernel9_1_r4_9,kernel9_1_r4_10,kernel9_1_r4_11,kernel9_1_r4_12,kernel9_1_r4_13,kernel9_1_r4_14,kernel9_1_r4_15]
noncomputable def kernel9_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel9_1_r0,kernel9_1_r1,kernel9_1_r2,kernel9_1_r3,kernel9_1_r4,kernel9_1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers20
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def trans11Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans10 j i k).mul (transStep j i k)
noncomputable def trans11_r2 : Fin 16 → Fin 16 → CBox := ![trans11_r2_0,trans11_r2_1,trans11_r2_2,trans11_r2_3,trans11_r2_4,trans11_r2_5,trans11_r2_6,trans11_r2_7,trans11_r2_8,trans11_r2_9,trans11_r2_10,trans11_r2_11,trans11_r2_12,trans11_r2_13,trans11_r2_14,trans11_r2_15]
noncomputable def trans11 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans11_r0,trans11_r1,trans11_r2,trans11_r3,trans11_r4,trans11_r5]
noncomputable def trans12Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans11 j i k).mul (transStep j i k)
noncomputable def trans12_r0 : Fin 16 → Fin 16 → CBox := ![trans12_r0_0,trans12_r0_1,trans12_r0_2,trans12_r0_3,trans12_r0_4,trans12_r0_5,trans12_r0_6,trans12_r0_7,trans12_r0_8,trans12_r0_9,trans12_r0_10,trans12_r0_11,trans12_r0_12,trans12_r0_13,trans12_r0_14,trans12_r0_15]
noncomputable def trans12_r1 : Fin 16 → Fin 16 → CBox := ![trans12_r1_0,trans12_r1_1,trans12_r1_2,trans12_r1_3,trans12_r1_4,trans12_r1_5,trans12_r1_6,trans12_r1_7,trans12_r1_8,trans12_r1_9,trans12_r1_10,trans12_r1_11,trans12_r1_12,trans12_r1_13,trans12_r1_14,trans12_r1_15]
noncomputable def trans12 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans12_r0,trans12_r1,trans12_r2,trans12_r3,trans12_r4,trans12_r5]
noncomputable def trans13Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans12 j i k).mul (transStep j i k)
noncomputable def trans16Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans15 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues20
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def kernel12_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans12 j i k)
noncomputable def kernel12_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans12 j i k)).mul (piI.mul (gridRows j i k).z)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments12
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm3_12_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel12_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm3_12_0_0
namespace cm3_12_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel12_1 j i k))
end cm3_12_0_1
namespace cm3_12_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel12_0 j i k))
end cm3_12_1_0
namespace cm3_12_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel12_1 j i k))
end cm3_12_1_1
namespace cm4_12_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel12_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm4_12_0_0
namespace cm4_12_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel12_1 j i k))
end cm4_12_0_1
namespace cm4_12_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel12_0 j i k))
end cm4_12_1_0
namespace cm4_12_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel12_1 j i k))
end cm4_12_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments13
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm1_13_1_1
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_13_1_1
namespace cm3_13_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel13_0 j i k))
end cm3_13_0_0
namespace cm3_13_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel13_1 j i k))
end cm3_13_0_1
namespace cm3_13_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel13_0 j i k))
end cm3_13_1_0
namespace cm3_13_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel13_1 j i k))
end cm3_13_1_1
namespace cm4_13_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel13_0 j i k))
end cm4_13_0_0
namespace cm4_13_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel13_1 j i k))
end cm4_13_0_1
namespace cm4_13_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel13_0 j i k))
end cm4_13_1_0
namespace cm4_13_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel13_1 j i k))
end cm4_13_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments15
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm1_15_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_15_0_0
namespace cm3_15_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel15_0 j i k))
end cm3_15_0_0
namespace cm3_15_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel15_1 j i k))
end cm3_15_0_1
namespace cm3_15_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel15_0 j i k))
end cm3_15_1_0
namespace cm3_15_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel15_1 j i k))
end cm3_15_1_1
namespace cm4_15_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel15_0 j i k))
end cm4_15_0_0
namespace cm4_15_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel15_1 j i k))
end cm4_15_0_1
namespace cm4_15_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel15_0 j i k))
end cm4_15_1_0
namespace cm4_15_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel15_1 j i k))
end cm4_15_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments16
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm3_16_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel16_0 j i k))
end cm3_16_0_0
namespace cm3_16_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel16_1 j i k))
end cm3_16_0_1
namespace cm3_16_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel16_0 j i k))
end cm3_16_1_0
namespace cm3_16_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel16_1 j i k))
end cm3_16_1_1
namespace cm4_16_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel16_0 j i k))
end cm4_16_0_0
namespace cm4_16_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel16_1 j i k))
end cm4_16_0_1
namespace cm4_16_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel16_0 j i k))
end cm4_16_1_0
namespace cm4_16_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel16_1 j i k))
end cm4_16_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments7
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel7_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_7_0_0
namespace cm1_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel7_0 j i k))
end cm1_7_1_0
namespace cm3_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel7_0 j i k))
end cm3_7_0_0
namespace cm3_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel7_1 j i k))
end cm3_7_0_1
namespace cm3_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel7_0 j i k))
end cm3_7_1_0
namespace cm3_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel7_1 j i k))
end cm3_7_1_1
namespace cm4_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel7_0 j i k))
end cm4_7_0_0
namespace cm4_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel7_1 j i k))
end cm4_7_0_1
namespace cm4_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel7_0 j i k))
end cm4_7_1_0
namespace cm4_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel7_1 j i k))
end cm4_7_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments9
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm1_9_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel9_1 j i k))
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_9_0_1
namespace cm1_9_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel9_0 j i k))
end cm1_9_1_0
namespace cm1_9_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel9_1 j i k))
end cm1_9_1_1
namespace cm3_9_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel9_0 j i k))
end cm3_9_0_0
namespace cm3_9_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel9_1 j i k))
end cm3_9_0_1
namespace cm3_9_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel9_0 j i k))
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm3_9_1_0
namespace cm3_9_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel9_1 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm3_9_1_1
namespace cm4_9_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel9_0 j i k))
end cm4_9_0_0
namespace cm4_9_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel9_1 j i k))
end cm4_9_0_1
namespace cm4_9_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel9_0 j i k))
end cm4_9_1_0
namespace cm4_9_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel9_1 j i k))
end cm4_9_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments100
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm100_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_1_0_0
namespace cm100_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel1_1 j i k))
end cm100_1_0_1
namespace cm100_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel3_0 j i k))
end cm100_3_0_0
namespace cm100_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel3_1 j i k))
end cm100_3_0_1
namespace cm100_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel4_0 j i k))
end cm100_4_0_0
namespace cm100_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel4_1 j i k))
end cm100_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments12
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm12_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column12_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm12_1_0_0
namespace cm12_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column12_0 j i k).mul (kernel1_1 j i k))
end cm12_1_0_1
namespace cm12_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column12_0 j i k).mul (kernel3_0 j i k))
end cm12_3_0_0
namespace cm12_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column12_0 j i k).mul (kernel3_1 j i k))
end cm12_3_0_1
namespace cm12_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column12_0 j i k).mul (kernel4_0 j i k))
end cm12_4_0_0
namespace cm12_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column12_0 j i k).mul (kernel4_1 j i k))
end cm12_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments13
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm13_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column13_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm13_1_0_0
namespace cm13_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column13_0 j i k).mul (kernel1_1 j i k))
end cm13_1_0_1
namespace cm13_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column13_0 j i k).mul (kernel3_0 j i k))
end cm13_3_0_0
namespace cm13_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column13_0 j i k).mul (kernel3_1 j i k))
end cm13_3_0_1
namespace cm13_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column13_0 j i k).mul (kernel4_0 j i k))
end cm13_4_0_0
namespace cm13_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column13_0 j i k).mul (kernel4_1 j i k))
end cm13_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments15
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm15_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column15_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm15_1_0_0
namespace cm15_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column15_0 j i k).mul (kernel1_1 j i k))
end cm15_1_0_1
namespace cm15_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column15_0 j i k).mul (kernel3_0 j i k))
end cm15_3_0_0
namespace cm15_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column15_0 j i k).mul (kernel3_1 j i k))
end cm15_3_0_1
namespace cm15_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column15_0 j i k).mul (kernel4_0 j i k))
end cm15_4_0_0
namespace cm15_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column15_0 j i k).mul (kernel4_1 j i k))
end cm15_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments16
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm16_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column16_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm16_1_0_0
namespace cm16_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column16_0 j i k).mul (kernel1_1 j i k))
end cm16_1_0_1
namespace cm16_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column16_0 j i k).mul (kernel3_0 j i k))
end cm16_3_0_0
namespace cm16_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column16_0 j i k).mul (kernel3_1 j i k))
end cm16_3_0_1
namespace cm16_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column16_0 j i k).mul (kernel4_0 j i k))
end cm16_4_0_0
namespace cm16_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column16_0 j i k).mul (kernel4_1 j i k))
end cm16_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments19
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm19_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column19_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm19_1_0_0
namespace cm19_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column19_0 j i k).mul (kernel1_1 j i k))
end cm19_1_0_1
namespace cm19_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column19_0 j i k).mul (kernel3_0 j i k))
end cm19_3_0_0
namespace cm19_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column19_0 j i k).mul (kernel3_1 j i k))
end cm19_3_0_1
namespace cm19_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column19_0 j i k).mul (kernel4_0 j i k))
end cm19_4_0_0
namespace cm19_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column19_0 j i k).mul (kernel4_1 j i k))
end cm19_4_0_1
namespace cm19_4_1_1
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm19_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments21
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm21_3_1_0
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm21_3_1_0
namespace cm21_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column21_1 j i k).mul (kernel3_1 j i k))
end cm21_3_1_1
namespace cm21_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column21_0 j i k).mul (kernel4_0 j i k))
end cm21_4_0_0
namespace cm21_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column21_0 j i k).mul (kernel4_1 j i k))
end cm21_4_0_1
namespace cm21_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column21_1 j i k).mul (kernel4_0 j i k))
end cm21_4_1_0
namespace cm21_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column21_1 j i k).mul (kernel4_1 j i k))
end cm21_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments24
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm24_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column24_1 j i k).mul (kernel3_0 j i k))
end cm24_3_1_0
namespace cm24_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column24_1 j i k).mul (kernel3_1 j i k))
end cm24_3_1_1
namespace cm24_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column24_0 j i k).mul (kernel4_0 j i k))
end cm24_4_0_0
namespace cm24_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column24_0 j i k).mul (kernel4_1 j i k))
end cm24_4_0_1
namespace cm24_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column24_1 j i k).mul (kernel4_0 j i k))
end cm24_4_1_0
namespace cm24_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column24_1 j i k).mul (kernel4_1 j i k))
end cm24_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments25
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm25_3_0_1
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm25_3_0_1
namespace cm25_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column25_1 j i k).mul (kernel3_1 j i k))
end cm25_3_1_1
namespace cm25_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column25_0 j i k).mul (kernel4_0 j i k))
end cm25_4_0_0
namespace cm25_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column25_0 j i k).mul (kernel4_1 j i k))
end cm25_4_0_1
namespace cm25_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column25_1 j i k).mul (kernel4_0 j i k))
end cm25_4_1_0
namespace cm25_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column25_1 j i k).mul (kernel4_1 j i k))
end cm25_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments27
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm27_3_0_1
namespace cm27_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column27_1 j i k).mul (kernel3_0 j i k))
end cm27_3_1_0
namespace cm27_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column27_1 j i k).mul (kernel3_1 j i k))
end cm27_3_1_1
namespace cm27_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column27_0 j i k).mul (kernel4_0 j i k))
end cm27_4_0_0
namespace cm27_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column27_0 j i k).mul (kernel4_1 j i k))
end cm27_4_0_1
namespace cm27_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column27_1 j i k).mul (kernel4_0 j i k))
end cm27_4_1_0
namespace cm27_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column27_1 j i k).mul (kernel4_1 j i k))
end cm27_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments28
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm28_3_0_1
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm28_3_0_1
namespace cm28_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel3_0 j i k))
end cm28_3_1_0
namespace cm28_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel3_1 j i k))
end cm28_3_1_1
namespace cm28_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_0 j i k).mul (kernel4_0 j i k))
end cm28_4_0_0
namespace cm28_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_0 j i k).mul (kernel4_1 j i k))
end cm28_4_0_1
namespace cm28_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel4_0 j i k))
end cm28_4_1_0
namespace cm28_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel4_1 j i k))
end cm28_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments31
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm31_3_0_0
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm31_3_0_0
namespace cm31_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_0 j i k).mul (kernel3_1 j i k))
end cm31_3_0_1
namespace cm31_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_1 j i k).mul (kernel3_0 j i k))
end cm31_3_1_0
namespace cm31_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_1 j i k).mul (kernel3_1 j i k))
end cm31_3_1_1
namespace cm31_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_0 j i k).mul (kernel4_0 j i k))
end cm31_4_0_0
namespace cm31_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_0 j i k).mul (kernel4_1 j i k))
end cm31_4_0_1
namespace cm31_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_1 j i k).mul (kernel4_0 j i k))
end cm31_4_1_0
namespace cm31_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column31_1 j i k).mul (kernel4_1 j i k))
end cm31_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments33
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm33_1_1_1
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm33_1_1_1
namespace cm33_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_0 j i k).mul (kernel3_0 j i k))
end cm33_3_0_0
namespace cm33_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_0 j i k).mul (kernel3_1 j i k))
end cm33_3_0_1
namespace cm33_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_1 j i k).mul (kernel3_0 j i k))
end cm33_3_1_0
namespace cm33_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_1 j i k).mul (kernel3_1 j i k))
end cm33_3_1_1
namespace cm33_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_0 j i k).mul (kernel4_0 j i k))
end cm33_4_0_0
namespace cm33_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_0 j i k).mul (kernel4_1 j i k))
end cm33_4_0_1
namespace cm33_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_1 j i k).mul (kernel4_0 j i k))
end cm33_4_1_0
namespace cm33_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column33_1 j i k).mul (kernel4_1 j i k))
end cm33_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments36
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm36_1_1_1
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm36_1_1_1
namespace cm36_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel3_0 j i k))
end cm36_3_0_0
namespace cm36_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel3_1 j i k))
end cm36_3_0_1
namespace cm36_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel3_0 j i k))
end cm36_3_1_0
namespace cm36_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel3_1 j i k))
end cm36_3_1_1
namespace cm36_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel4_0 j i k))
end cm36_4_0_0
namespace cm36_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel4_1 j i k))
end cm36_4_0_1
namespace cm36_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel4_0 j i k))
end cm36_4_1_0
namespace cm36_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel4_1 j i k))
end cm36_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments37
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm37_1_1_1
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm37_1_1_1
namespace cm37_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_0 j i k).mul (kernel3_0 j i k))
end cm37_3_0_0
namespace cm37_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_0 j i k).mul (kernel3_1 j i k))
end cm37_3_0_1
namespace cm37_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_1 j i k).mul (kernel3_0 j i k))
end cm37_3_1_0
namespace cm37_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_1 j i k).mul (kernel3_1 j i k))
end cm37_3_1_1
namespace cm37_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_0 j i k).mul (kernel4_0 j i k))
end cm37_4_0_0
namespace cm37_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_0 j i k).mul (kernel4_1 j i k))
end cm37_4_0_1
namespace cm37_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_1 j i k).mul (kernel4_0 j i k))
end cm37_4_1_0
namespace cm37_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column37_1 j i k).mul (kernel4_1 j i k))
end cm37_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments39
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm39_1_1_1
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm39_1_1_1
namespace cm39_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_0 j i k).mul (kernel3_0 j i k))
end cm39_3_0_0
namespace cm39_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_0 j i k).mul (kernel3_1 j i k))
end cm39_3_0_1
namespace cm39_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_1 j i k).mul (kernel3_0 j i k))
end cm39_3_1_0
namespace cm39_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_1 j i k).mul (kernel3_1 j i k))
end cm39_3_1_1
namespace cm39_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_0 j i k).mul (kernel4_0 j i k))
end cm39_4_0_0
namespace cm39_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_0 j i k).mul (kernel4_1 j i k))
end cm39_4_0_1
namespace cm39_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_1 j i k).mul (kernel4_0 j i k))
end cm39_4_1_0
namespace cm39_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column39_1 j i k).mul (kernel4_1 j i k))
end cm39_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments40
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm40_4_1_0
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm40_4_1_0
namespace cm40_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column40_1 j i k).mul (kernel4_1 j i k))
end cm40_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments43
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm43_4_0_1
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm43_4_0_1
namespace cm43_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column43_1 j i k).mul (kernel4_1 j i k))
end cm43_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments45
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm45_4_0_0
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm45_4_0_0
namespace cm45_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column45_0 j i k).mul (kernel4_1 j i k))
end cm45_4_0_1
namespace cm45_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column45_1 j i k).mul (kernel4_0 j i k))
end cm45_4_1_0
namespace cm45_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column45_1 j i k).mul (kernel4_1 j i k))
end cm45_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments48
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm48_4_0_0
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm48_4_0_0
namespace cm48_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column48_0 j i k).mul (kernel4_1 j i k))
end cm48_4_0_1
namespace cm48_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column48_1 j i k).mul (kernel4_0 j i k))
end cm48_4_1_0
namespace cm48_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column48_1 j i k).mul (kernel4_1 j i k))
end cm48_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments49
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm49_4_0_0
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm49_4_0_0
namespace cm49_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column49_0 j i k).mul (kernel4_1 j i k))
end cm49_4_0_1
namespace cm49_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column49_1 j i k).mul (kernel4_0 j i k))
end cm49_4_1_0
namespace cm49_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column49_1 j i k).mul (kernel4_1 j i k))
end cm49_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments51
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm51_1_0_0
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm51_1_0_0
namespace cm51_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column51_0 j i k).mul (kernel1_1 j i k))
end cm51_1_0_1
namespace cm51_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column51_0 j i k).mul (kernel3_0 j i k))
end cm51_3_0_0
namespace cm51_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column51_0 j i k).mul (kernel3_1 j i k))
end cm51_3_0_1
namespace cm51_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column51_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm51_4_0_0
namespace cm51_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column51_0 j i k).mul (kernel4_1 j i k))
end cm51_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments52
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm52_1_0_0
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm52_1_0_0
namespace cm52_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel1_1 j i k))
end cm52_1_0_1
namespace cm52_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel3_0 j i k))
end cm52_3_0_0
namespace cm52_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel3_1 j i k))
end cm52_3_0_1
namespace cm52_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel4_0 j i k))
end cm52_4_0_0
namespace cm52_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel4_1 j i k))
end cm52_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments55
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm55_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column55_0 j i k).mul (kernel1_0 j i k))
end cm55_1_0_0
namespace cm55_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column55_0 j i k).mul (kernel1_1 j i k))
end cm55_1_0_1
namespace cm55_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column55_0 j i k).mul (kernel3_0 j i k))
end cm55_3_0_0
namespace cm55_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column55_0 j i k).mul (kernel3_1 j i k))
end cm55_3_0_1
namespace cm55_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column55_0 j i k).mul (kernel4_0 j i k))
end cm55_4_0_0
namespace cm55_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column55_0 j i k).mul (kernel4_1 j i k))
end cm55_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments57
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm57_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm57_1_0_0
namespace cm57_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel1_1 j i k))
end cm57_1_0_1
namespace cm57_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel3_0 j i k))
end cm57_3_0_0
namespace cm57_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel3_1 j i k))
end cm57_3_0_1
namespace cm57_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm57_4_0_0
namespace cm57_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel4_1 j i k))
end cm57_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments60
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm60_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column60_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm60_1_0_0
namespace cm60_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column60_0 j i k).mul (kernel1_1 j i k))
end cm60_1_0_1
namespace cm60_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column60_0 j i k).mul (kernel3_0 j i k))
end cm60_3_0_0
namespace cm60_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column60_0 j i k).mul (kernel3_1 j i k))
end cm60_3_0_1
namespace cm60_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column60_0 j i k).mul (kernel4_0 j i k))
end cm60_4_0_0
namespace cm60_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column60_0 j i k).mul (kernel4_1 j i k))
end cm60_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments61
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm61_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm61_1_0_0
namespace cm61_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel1_1 j i k))
end cm61_1_0_1
namespace cm61_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel3_0 j i k))
end cm61_3_0_0
namespace cm61_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel3_1 j i k))
end cm61_3_0_1
namespace cm61_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel4_0 j i k))
end cm61_4_0_0
namespace cm61_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel4_1 j i k))
end cm61_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments63
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm63_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column63_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm63_1_0_0
namespace cm63_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column63_0 j i k).mul (kernel1_1 j i k))
end cm63_1_0_1
namespace cm63_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column63_0 j i k).mul (kernel3_0 j i k))
end cm63_3_0_0
namespace cm63_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column63_0 j i k).mul (kernel3_1 j i k))
end cm63_3_0_1
namespace cm63_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column63_0 j i k).mul (kernel4_0 j i k))
end cm63_4_0_0
namespace cm63_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column63_0 j i k).mul (kernel4_1 j i k))
end cm63_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments64
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm64_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column64_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm64_1_0_0
namespace cm64_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column64_0 j i k).mul (kernel1_1 j i k))
end cm64_1_0_1
namespace cm64_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column64_0 j i k).mul (kernel3_0 j i k))
end cm64_3_0_0
namespace cm64_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column64_0 j i k).mul (kernel3_1 j i k))
end cm64_3_0_1
namespace cm64_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column64_0 j i k).mul (kernel4_0 j i k))
end cm64_4_0_0
namespace cm64_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column64_0 j i k).mul (kernel4_1 j i k))
end cm64_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments67
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm67_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column67_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm67_1_0_0
namespace cm67_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column67_0 j i k).mul (kernel1_1 j i k))
end cm67_1_0_1
namespace cm67_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column67_0 j i k).mul (kernel3_0 j i k))
end cm67_3_0_0
namespace cm67_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column67_0 j i k).mul (kernel3_1 j i k))
end cm67_3_0_1
namespace cm67_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column67_0 j i k).mul (kernel4_0 j i k))
end cm67_4_0_0
namespace cm67_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column67_0 j i k).mul (kernel4_1 j i k))
end cm67_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments69
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm69_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column69_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm69_1_0_0
namespace cm69_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column69_0 j i k).mul (kernel1_1 j i k))
end cm69_1_0_1
namespace cm69_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column69_0 j i k).mul (kernel3_0 j i k))
end cm69_3_0_0
namespace cm69_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column69_0 j i k).mul (kernel3_1 j i k))
end cm69_3_0_1
namespace cm69_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column69_0 j i k).mul (kernel4_0 j i k))
end cm69_4_0_0
namespace cm69_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column69_0 j i k).mul (kernel4_1 j i k))
end cm69_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments7
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm7_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column7_0 j i k).mul (kernel1_0 j i k))
end cm7_1_0_0
namespace cm7_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column7_0 j i k).mul (kernel1_1 j i k))
end cm7_1_0_1
namespace cm7_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column7_0 j i k).mul (kernel3_0 j i k))
end cm7_3_0_0
namespace cm7_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column7_0 j i k).mul (kernel3_1 j i k))
end cm7_3_0_1
namespace cm7_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column7_0 j i k).mul (kernel4_0 j i k))
end cm7_4_0_0
namespace cm7_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column7_0 j i k).mul (kernel4_1 j i k))
end cm7_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments72
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm72_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column72_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm72_1_0_0
namespace cm72_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column72_0 j i k).mul (kernel1_1 j i k))
end cm72_1_0_1
namespace cm72_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column72_0 j i k).mul (kernel3_0 j i k))
end cm72_3_0_0
namespace cm72_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column72_0 j i k).mul (kernel3_1 j i k))
end cm72_3_0_1
namespace cm72_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column72_0 j i k).mul (kernel4_0 j i k))
end cm72_4_0_0
namespace cm72_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column72_0 j i k).mul (kernel4_1 j i k))
end cm72_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments73
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm73_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column73_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm73_1_0_0
namespace cm73_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column73_0 j i k).mul (kernel1_1 j i k))
end cm73_1_0_1
namespace cm73_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column73_0 j i k).mul (kernel3_0 j i k))
end cm73_3_0_0
namespace cm73_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column73_0 j i k).mul (kernel3_1 j i k))
end cm73_3_0_1
namespace cm73_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column73_0 j i k).mul (kernel4_0 j i k))
end cm73_4_0_0
namespace cm73_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column73_0 j i k).mul (kernel4_1 j i k))
end cm73_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments75
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm75_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel1_0 j i k))
end cm75_1_0_0
namespace cm75_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel1_1 j i k))
end cm75_1_0_1
namespace cm75_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm75_3_0_0
namespace cm75_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel3_1 j i k))
end cm75_3_0_1
namespace cm75_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel4_0 j i k))
end cm75_4_0_0
namespace cm75_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel4_1 j i k))
end cm75_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments76
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm76_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel1_0 j i k))
end cm76_1_0_0
namespace cm76_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel1_1 j i k))
end cm76_1_0_1
namespace cm76_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel3_0 j i k))
end cm76_3_0_0
namespace cm76_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel3_1 j i k))
end cm76_3_0_1
namespace cm76_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel4_0 j i k))
end cm76_4_0_0
namespace cm76_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel4_1 j i k))
end cm76_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments79
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm79_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column79_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm79_1_0_0
namespace cm79_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column79_0 j i k).mul (kernel1_1 j i k))
end cm79_1_0_1
namespace cm79_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column79_0 j i k).mul (kernel3_0 j i k))
end cm79_3_0_0
namespace cm79_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column79_0 j i k).mul (kernel3_1 j i k))
end cm79_3_0_1
namespace cm79_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column79_0 j i k).mul (kernel4_0 j i k))
end cm79_4_0_0
namespace cm79_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column79_0 j i k).mul (kernel4_1 j i k))
end cm79_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments81
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm81_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column81_0 j i k).mul (kernel1_0 j i k))
end cm81_1_0_0
namespace cm81_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column81_0 j i k).mul (kernel1_1 j i k))
end cm81_1_0_1
namespace cm81_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column81_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm81_3_0_0
namespace cm81_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column81_0 j i k).mul (kernel3_1 j i k))
end cm81_3_0_1
namespace cm81_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column81_0 j i k).mul (kernel4_0 j i k))
end cm81_4_0_0
namespace cm81_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column81_0 j i k).mul (kernel4_1 j i k))
end cm81_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments84
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm84_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column84_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm84_1_0_0
namespace cm84_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column84_0 j i k).mul (kernel1_1 j i k))
end cm84_1_0_1
namespace cm84_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column84_0 j i k).mul (kernel3_0 j i k))
end cm84_3_0_0
namespace cm84_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column84_0 j i k).mul (kernel3_1 j i k))
end cm84_3_0_1
namespace cm84_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column84_0 j i k).mul (kernel4_0 j i k))
end cm84_4_0_0
namespace cm84_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column84_0 j i k).mul (kernel4_1 j i k))
end cm84_4_0_1
namespace cm84_4_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm84_4_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments85
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm85_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column85_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm85_1_0_0
namespace cm85_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column85_0 j i k).mul (kernel1_1 j i k))
end cm85_1_0_1
namespace cm85_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column85_0 j i k).mul (kernel3_0 j i k))
end cm85_3_0_0
namespace cm85_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column85_0 j i k).mul (kernel3_1 j i k))
end cm85_3_0_1
namespace cm85_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column85_0 j i k).mul (kernel4_0 j i k))
end cm85_4_0_0
namespace cm85_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column85_0 j i k).mul (kernel4_1 j i k))
end cm85_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments87
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm87_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column87_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm87_1_0_0
namespace cm87_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column87_0 j i k).mul (kernel1_1 j i k))
end cm87_1_0_1
namespace cm87_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column87_0 j i k).mul (kernel3_0 j i k))
end cm87_3_0_0
namespace cm87_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column87_0 j i k).mul (kernel3_1 j i k))
end cm87_3_0_1
namespace cm87_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column87_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm87_4_0_0
namespace cm87_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column87_0 j i k).mul (kernel4_1 j i k))
end cm87_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments88
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm88_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel1_0 j i k))
end cm88_1_0_0
namespace cm88_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel1_1 j i k))
end cm88_1_0_1
namespace cm88_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel3_0 j i k))
end cm88_3_0_0
namespace cm88_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel3_1 j i k))
end cm88_3_0_1
namespace cm88_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel4_0 j i k))
end cm88_4_0_0
namespace cm88_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel4_1 j i k))
end cm88_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments9
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm9_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column9_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm9_1_0_0
namespace cm9_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column9_0 j i k).mul (kernel1_1 j i k))
end cm9_1_0_1
namespace cm9_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column9_0 j i k).mul (kernel3_0 j i k))
end cm9_3_0_0
namespace cm9_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column9_0 j i k).mul (kernel3_1 j i k))
end cm9_3_0_1
namespace cm9_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column9_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm9_4_0_0
namespace cm9_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column9_0 j i k).mul (kernel4_1 j i k))
end cm9_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments91
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm91_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column91_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm91_1_0_0
namespace cm91_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column91_0 j i k).mul (kernel1_1 j i k))
end cm91_1_0_1
namespace cm91_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column91_0 j i k).mul (kernel3_0 j i k))
end cm91_3_0_0
namespace cm91_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column91_0 j i k).mul (kernel3_1 j i k))
end cm91_3_0_1
namespace cm91_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column91_0 j i k).mul (kernel4_0 j i k))
end cm91_4_0_0
namespace cm91_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column91_0 j i k).mul (kernel4_1 j i k))
end cm91_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments93
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm93_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column93_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm93_1_0_0
namespace cm93_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column93_0 j i k).mul (kernel1_1 j i k))
end cm93_1_0_1
namespace cm93_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column93_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm93_3_0_0
namespace cm93_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column93_0 j i k).mul (kernel3_1 j i k))
end cm93_3_0_1
namespace cm93_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column93_0 j i k).mul (kernel4_0 j i k))
end cm93_4_0_0
namespace cm93_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column93_0 j i k).mul (kernel4_1 j i k))
end cm93_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments96
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm96_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm96_1_0_0
namespace cm96_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel1_1 j i k))
end cm96_1_0_1
namespace cm96_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel3_0 j i k))
end cm96_3_0_0
namespace cm96_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel3_1 j i k))
end cm96_3_0_1
namespace cm96_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm96_4_0_0
namespace cm96_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel4_1 j i k))
end cm96_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments97
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm97_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm97_1_0_0
namespace cm97_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel1_1 j i k))
end cm97_1_0_1
namespace cm97_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm97_3_0_0
namespace cm97_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel3_1 j i k))
end cm97_3_0_1
namespace cm97_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel4_0 j i k))
end cm97_4_0_0
namespace cm97_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel4_1 j i k))
end cm97_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments99
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
namespace cm99_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column99_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm99_1_0_0
namespace cm99_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column99_0 j i k).mul (kernel1_1 j i k))
end cm99_1_0_1
namespace cm99_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column99_0 j i k).mul (kernel3_0 j i k))
end cm99_3_0_0
namespace cm99_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column99_0 j i k).mul (kernel3_1 j i k))
end cm99_3_0_1
namespace cm99_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column99_0 j i k).mul (kernel4_0 j i k))
end cm99_4_0_0
namespace cm99_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column99_0 j i k).mul (kernel4_1 j i k))
end cm99_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert100
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

namespace SharpPlanar.Numerical.U100
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
end SharpPlanar.Numerical.U100

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert12
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

namespace SharpPlanar.Numerical.U12
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
end SharpPlanar.Numerical.U12

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert13
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

namespace SharpPlanar.Numerical.U13
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U13

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert15
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

namespace SharpPlanar.Numerical.U15
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U15

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

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert19
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

namespace SharpPlanar.Numerical.U19
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U19

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert21
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

namespace SharpPlanar.Numerical.U21
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U21

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert24
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

namespace SharpPlanar.Numerical.U24
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U24

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert25
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

namespace SharpPlanar.Numerical.U25
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U25

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert27
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

namespace SharpPlanar.Numerical.U27
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U27

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert9
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

namespace SharpPlanar.Numerical.U9
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U9

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
noncomputable def signedU (neg : Bool) := RJ.comp ((signedS neg).comp IE)
noncomputable def signedL (neg : Bool) := RE.comp ((signedS neg).comp IJ)
noncomputable def signedE (neg : Bool) := RE.comp ((signedS neg).comp IE)
end SharpPlanar.Numerical

end OAI
end


