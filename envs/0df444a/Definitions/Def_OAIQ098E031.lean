-- Prove2me | Definitions.Def_OAIQ098E031
-- name    : OAIQ098E031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T21:04:25.625609+00:00
-- url     : https://prove2.me/theorems/c6d4f8ae-e5e6-43b7-bfa8-6d99b30f282d
-- title:
--   Definitions bundle OAIQ098E031 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 571 declarations of OpenAI's Lean: 566 definitions and 5 instances. The definitions and types are `OAI.SharpPlanar.CachedData.amp1_0Expr`, `OAI.SharpPlanar.CachedData.amp1_1Expr`, `OAI.SharpPlanar.CachedData.amp3_0Expr`, `OAI.SharpPlanar.CachedData.amp3_1`, `OAI.SharpPlanar.CachedData.amp3_15`, `OAI.SharpPlanar.CachedData.amp3_1Expr`, `OAI.SharpPlanar.CachedData.amp4_0Expr`, `OAI.SharpPlanar.CachedData.amp4_1Expr`, `OAI.SharpPlanar.CachedData.cm1_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm1_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm1_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm1_1_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_1_1_0.s0`, `OAI.SharpPlanar.CachedData.cm1_1_1_0.sums`, `OAI.SharpPlanar.CachedData.cm1_1_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm1_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm1_3_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_3_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm1_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_4_0_0.s0`, `OAI.SharpPlanar.CachedData.cm1_4_0_0.sums`, `OAI.SharpPlanar.CachedData.cm1_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm1_4_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_4_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_1_0_0.s2`, `OAI.SharpPlanar.CachedData.cm3_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm3_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_1_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_1_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_3_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_3_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_4_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_4_1_1.chunk` and 526 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_BasisIntervals`, `PlanarPacking_Certificate_Amplitudes`, `PlanarPacking_Certificate_Columns10`, `PlanarPacking_Certificate_DMoments1`, `PlanarPacking_Certificate_DMoments3`, `PlanarPacking_Certificate_DMoments4`, `PlanarPacking_Certificate_KernelValues10`, `PlanarPacking_Certificate_Powers10`, `PlanarPacking_Certificate_TransformedPowers10`, `PlanarPacking_Certificate_WCertificates`, `PlanarPacking_Fejer`, `PlanarPacking_Grid`, `PlanarPacking_Intervals`, `PlanarPacking_NodeIntervals`, `PlanarPacking_Roots`.
--
--   **Imports.** It imports the bundles `OAIQ098E004`, `OAIQ098E019`, `OAIQ098E020`, `OAIQ098E021`, `OAIQ098E022`, `OAIQ098E023`, `OAIQ098E024`, `OAIQ098E025`, `OAIQ098E026`, `OAIQ098E027`, `OAIQ098E028`, `OAIQ098E029` and `OAIQ098E030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E033`, `OAIQ098E034`, `OAIQ098E035`, `OAIQ098E036`, `OAIQ098E037`, `OAIQ098E038`, `OAIQ098E039`, `OAIQ098E040`, `OAIQ098E041`, `OAIQ098E042`, `OAIQ098E043`, `OAIQ098E055`, `OAIQ098E056`, `OAIQ098E057`, `OAIQ098E058`, `OAIQ098E059`, `OAIQ098E061`, `OAIQ098E062`, `OAIQ098E063`, `OAIQ098E064`, `OAIQ098E065`, `OAIQ098E066`, `OAIQ098E067`, `OAIQ098E068`, `OAIQ098E069`, `OAIQ098E070`, `OAIQ098E071`, `OAIQ098E072`, `OAIQ098E073`, `OAIQ098E074`, `OAIQ098E075`, `OAIQ098E076`, `OAIQ098E077`, `OAIQ098E078`, `OAIQ098E079`, `OAIQ098E080`, `OAIQ098E081`, `OAIQ098E082`, `OAIQ098E083`, `OAIQ098E084`, `OAIQ098E085`, `OAIQ098E086`, `OAIQ098E087`, `OAIQ098E088`, `OAIQ098E091`, `OAIQ098E092`, `OAIQ098E093`, `OAIQ098E094`, `OAIQ098E095`, `OAIQ098E097`, `OAIQ098E098`, `OAIQ098E101`, `OAIQ098E102`, `OAIQ098E104`, `OAIQ098E105`, `OAIQ098E106`, `OAIQ098E107`, `OAIQ098E108`, `OAIQ098E109`, `OAIQ098E110`, `OAIQ098E111`, `OAIQ098E112`, `OAIQ098E113`, `OAIQ098E114`, `OAIQ098E115`, `OAIQ098E116`, `OAIQ098E117`, `OAIQ098E118`, `OAIQ098E119`, `OAIQ098E120`, `OAIQ098E121`, `OAIQ098E122`, `OAIQ098E123`, `OAIQ098E125`, `OAIQ098E139`, `OAIQ098E177`, `OAIQ098E214`, `OAIQ098E215`, `OAIQ098E216`, `OAIQ098E217`, `OAIQ098E218`, `OAIQ098E219`, `OAIQ098E220`, `OAIQ098E221`, `OAIQ098E222`, `OAIQ098E223`, `OAIQ098E224`, `OAIQ098E225`, `OAIQ098E226`, `OAIQ098E227`, `OAIQ098E228` and `OAIQ098E229`; the statements `OAI.SharpPlanar.CachedData.cm1_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm1_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm25_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm25_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.cm33_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm33_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column21_1_contains_e`, `OAI.SharpPlanar.CachedData.column27_0_contains_e`, `OAI.SharpPlanar.CachedData.column27_1_contains_e`, `OAI.SharpPlanar.CachedData.column28_0_contains_e`, `OAI.SharpPlanar.CachedData.column28_1_contains_e`, `OAI.SharpPlanar.CachedData.column36_0_contains_e`, `OAI.SharpPlanar.CachedData.column36_1_contains_e`, `OAI.SharpPlanar.CachedData.column37_1_contains_e`, `OAI.SharpPlanar.CachedData.column3_0_contains_e`, `OAI.SharpPlanar.CachedData.column3_1_contains_e`, `OAI.SharpPlanar.CachedData.column4_0_contains_e`, `OAI.SharpPlanar.CachedData.column4_1_contains_e`, `OAI.SharpPlanar.CachedData.column51_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel21_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel28_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel31_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel36_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel3_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel3_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel4_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel4_1_contains_e`, `OAI.SharpPlanar.CachedData.power16_contains_e`, `OAI.SharpPlanar.CachedData.power21_contains_e`, `OAI.SharpPlanar.CachedData.power24_contains_e`, `OAI.SharpPlanar.CachedData.power55_contains_e`, `OAI.SharpPlanar.CachedData.power72_contains_e`, `OAI.SharpPlanar.CachedData.power79_contains_e`, `OAI.SharpPlanar.CachedData.trans32_contains_e`, `OAI.SharpPlanar.CachedData.trans56_contains_e`, `OAI.SharpPlanar.CachedData.trans80_contains_e`, `OAI.SharpPlanar.CachedData.transStep_r0_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_9_eq_e`, `OAI.SharpPlanar.IntegerAlpha.a0_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_5_contains_e`, `OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_e`, `OAI.SharpPlanar.IntegerBasis.phaseBase_contains_e`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.add_check_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_add_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_horner_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_mul_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_scale_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_squareIter_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.mul_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.scale_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_e`, `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e`, `OAI.SharpPlanar.IntegerIntervals.exp_from_horner_e`, `OAI.SharpPlanar.IntegerIntervals.finSum_contains_e`, `OAI.SharpPlanar.IntegerIntervals.horner_step_e`, `OAI.SharpPlanar.IntegerIntervals.lamBox_contains_e`, `OAI.SharpPlanar.IntegerIntervals.piI_contains_e`, `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_e`, `OAI.SharpPlanar.IntegerIntervals.zBox_contains_e`, `OAI.SharpPlanar.Numerical.qiBox_contains_e` and `OAI.SharpPlanar.cached_density_rule_contains_e`; the proofs of `OAI.SharpPlanar.CachedData.cm1_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm1_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column3_0_contains_e`, `OAI.SharpPlanar.CachedData.column3_1_contains_e`, `OAI.SharpPlanar.CachedData.column4_0_contains_e`, `OAI.SharpPlanar.CachedData.column4_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel3_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel3_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel4_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel4_1_contains_e`, `OAI.SharpPlanar.CachedData.transStep_r0_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r0_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r1_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r2_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r3_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r4_9_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_0_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_10_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_11_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_12_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_13_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_14_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_15_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_1_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_2_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_3_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_4_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_5_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_6_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_7_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_8_eq_e`, `OAI.SharpPlanar.CachedData.transStep_r5_9_eq_e`, `OAI.SharpPlanar.IntegerAlpha.a0_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a0_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a10_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a11_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a1_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a2_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a3_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a4_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a5_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a6_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a7_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a8_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.a9_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b0_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b10_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b11_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b1_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b2_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b3_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b4_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b5_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b6_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b7_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b8_5_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_0_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_1_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_2_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_3_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_4_contains_e`, `OAI.SharpPlanar.IntegerAlpha.b9_5_contains_e`, `OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_e`, `OAI.SharpPlanar.IntegerBasis.phaseBase_contains_e`, `OAI.SharpPlanar.IntegerCompact.weightRows_contains_e`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.add_check_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_add_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_horner_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_mul_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_scale_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_squareIter_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.mul_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.scale_contains_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_e`, `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e`, `OAI.SharpPlanar.IntegerIntervals.exp_from_horner_e`, `OAI.SharpPlanar.IntegerIntervals.finSum_contains_e`, `OAI.SharpPlanar.IntegerIntervals.horner_step_e`, `OAI.SharpPlanar.IntegerIntervals.lamBox_contains_e`, `OAI.SharpPlanar.IntegerIntervals.piI_contains_e`, `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_e`, `OAI.SharpPlanar.IntegerIntervals.zBox_contains_e`, `OAI.SharpPlanar.Numerical.defectminus_norm_e`, `OAI.SharpPlanar.Numerical.defectplus_norm_e`, `OAI.SharpPlanar.Numerical.dentry0_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry2_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_5_contains_e`, `OAI.SharpPlanar.Numerical.qiBox_contains_e` and `OAI.SharpPlanar.cached_density_rule_contains_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E004
import Definitions.Def_OAIQ098E019
import Definitions.Def_OAIQ098E020
import Definitions.Def_OAIQ098E021
import Definitions.Def_OAIQ098E022
import Definitions.Def_OAIQ098E023
import Definitions.Def_OAIQ098E024
import Definitions.Def_OAIQ098E025
import Definitions.Def_OAIQ098E026
import Definitions.Def_OAIQ098E027
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E029
import Definitions.Def_OAIQ098E030

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

def CBox.Contains (a : CBox) (x : ℂ) : Prop := a.re.Contains x.re ∧ a.im.Contains x.im

instance instDecidableAddCheck (a b c : RBox) : Decidable (a.AddCheck b c) := inferInstanceAs (Decidable (_ ∧ _))

def CBox.AddCheck (a b c : CBox) : Prop := a.re.AddCheck b.re c.re ∧ a.im.AddCheck b.im c.im
instance instDecidableAddCheck_1 (a b c : CBox) : Decidable (a.AddCheck b c) := inferInstanceAs (Decidable (_ ∧ _))

def CBox.NormCheck (a : CBox) (n : ℤ) : Prop := a.re.bound+a.im.bound ≤ precision*n
instance instDecidableNormCheck (a : CBox) (n : ℤ) : Decidable (a.NormCheck n) := inferInstanceAs (Decidable (_ ≤ _))

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

def CBox.inv (a : CBox) : CBox :=
  let d := (a.re.mul a.re).add (a.im.mul a.im)
  let di := d.inv
  ⟨a.re.mul di,a.im.neg.mul di⟩
def CBox.horner (a : CBox) (k : ℕ) : ℕ → CBox
  | 0 => CBox.rat 1 (k.factorial:ℤ) 0 1
  | n+1 => (CBox.rat 1 (k.factorial:ℤ) 0 1).add (a.mul (a.horner (k+1) n))
def CBox.exp (a : CBox) (k : ℕ := 11) : CBox :=
  (((a.scale 1 (2^k)).horner 0 32).widen 1).squareIter k

def CBox.powBin (a : CBox) : ℕ → ℕ → CBox
  | 0, _ => CBox.rat 1 1 0 1
  | k+1, n =>
    let b := a.powBin k (n/2)
    let b2 := b.mul b
    if n%2 = 0 then b2 else b2.mul a

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

def denBox (a : RBox) : CBox := ⟨a,RBox.rat 2 5⟩
def lamDenBox (a : RBox) : CBox := (rcast bBounds).mul (denBox a)
def lamBox (a : RBox) : CBox := (CBox.rat 0 1 1 1).mul (lamDenBox a).inv
def zBox (a : RBox) : CBox := ((denBox a).inv.scale (-4) 3).add (CBox.rat 0 1 (-2) 5)
def quarterArgBox (a : RBox) : CBox := (piI.mul (zBox a)).scale 1 4

def CBox.GoodInv (a : CBox) : Prop :=
  ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
    ((a.re.mul a.re).add (a.im.mul a.im)).inv
instance instDecidableGoodInv (a : CBox) : Decidable a.GoodInv := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def PointBox.Check (a : RBox) : Prop :=
  (denBox a).GoodInv ∧ (lamDenBox a).GoodInv ∧
  ((directArgBox a).scale 1 8).NormCheck 1 ∧
  ((quarterArgBox a).scale 1 8).NormCheck 1
instance instDecidableCheck (a : RBox) : Decidable (PointBox.Check a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def PointBox.calc (a : RBox) : PointBox :=
  ⟨a,lamBox a,zBox a,(directArgBox a).exp 3,(quarterArgBox a).exp 3⟩

def PointBox.Contains (a : PointBox) (x : ℝ) : Prop :=
  a.t.Contains x ∧ a.lam.Contains (pointLambda x) ∧ a.z.Contains (pointZ x) ∧
  a.direct.Contains (Complex.exp (-Complex.I*Real.pi*x)) ∧
  a.quarter.Contains (Complex.exp (Complex.I*Real.pi*pointZ x/4))

end SharpPlanar.IntegerIntervals

end OAI
end

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
def mid3 : CBox := root2
def mid5 : CBox := root4
def mid7 : CBox := root6
def mid9 : CBox := root8
def mid11 : CBox := root10
def mid13 : CBox := root12
def mid15 : CBox := root14
def mid17 : CBox := root16
def mid19 : CBox := root18
def mid21 : CBox := root20
def mid23 : CBox := root22
def mid25 : CBox := root24
def mid27 : CBox := root26
def mid29 : CBox := root28
def mid31 : CBox := root30
def mid33 : CBox := root32
def mid35 : CBox := root34
def mid37 : CBox := root36
def mid39 : CBox := root38
def mid41 : CBox := root40
def mid43 : CBox := root42
def mid45 : CBox := root44
def mid47 : CBox := root46
def mid49 : CBox := root48
def mid51 : CBox := root50
def mid53 : CBox := root52
def mid55 : CBox := root54
def mid57 : CBox := root56
def mid59 : CBox := root58
def mid61 : CBox := root60
def mid63 : CBox := root62
def mid65 : CBox := root64
def mid67 : CBox := root66
def mid69 : CBox := root68
def mid71 : CBox := root70
def mid73 : CBox := root72
def mid75 : CBox := root74
def mid77 : CBox := root76
def mid79 : CBox := root78
def mid81 : CBox := root80
def mid83 : CBox := root82
def mid85 : CBox := root84
def mid87 : CBox := root86
def mid89 : CBox := root88
def mid91 : CBox := root90
def mid93 : CBox := root92
def mid95 : CBox := root94
def mid97 : CBox := root96
def mid99 : CBox := root98
def mid101 : CBox := root100
def mid103 : CBox := root102
def mid105 : CBox := root104
def mid107 : CBox := root106
def mid109 : CBox := root108
def mid111 : CBox := root110
def mid113 : CBox := root112
def mid115 : CBox := root114
def mid117 : CBox := root116
def mid119 : CBox := root118
def mid121 : CBox := root120
def mid123 : CBox := root122
def mid125 : CBox := root124
def mid127 : CBox := root126
def mid129 : CBox := root128
def mid131 : CBox := root130
def mid133 : CBox := root132
def mid135 : CBox := root134
def mid137 : CBox := root136
def mid139 : CBox := root138
def mid141 : CBox := root140
def mid143 : CBox := root142
def mid145 : CBox := root144
def mid147 : CBox := root146
def mid149 : CBox := root148
def mid151 : CBox := root150
def mid153 : CBox := root152
def mid155 : CBox := root154
def mid157 : CBox := root156
def mid159 : CBox := root158
def mid161 : CBox := root160
def mid163 : CBox := root162
def mid321 : CBox := root320
def mid323 : CBox := root322
def mid325 : CBox := root324
def mid327 : CBox := root326
def mid329 : CBox := root328
def mid331 : CBox := root330
def mid333 : CBox := root332
def mid335 : CBox := root334
def mid337 : CBox := root336
def mid339 : CBox := root338
def mid341 : CBox := root340
def mid343 : CBox := root342
def mid345 : CBox := root344
def mid347 : CBox := root346
def mid349 : CBox := root348
def mid351 : CBox := root350
def mid353 : CBox := root352
def mid355 : CBox := root354
def mid357 : CBox := root356
def mid359 : CBox := root358
def mid361 : CBox := root360
def mid363 : CBox := root362
def mid365 : CBox := root364
def mid367 : CBox := root366
def mid369 : CBox := root368
def mid371 : CBox := root370
def mid373 : CBox := root372
def mid375 : CBox := root374
def mid377 : CBox := root376
def mid379 : CBox := root378
def mid381 : CBox := root380
def mid383 : CBox := root382
def mid385 : CBox := root384
def mid387 : CBox := root386
def mid389 : CBox := root388
def mid391 : CBox := root390
def mid393 : CBox := root392
def mid395 : CBox := root394
def mid397 : CBox := root396
def mid399 : CBox := root398
def mid401 : CBox := root400
def mid403 : CBox := root402
def mid405 : CBox := root404
def mid407 : CBox := root406
def mid409 : CBox := root408
def mid411 : CBox := root410
def mid413 : CBox := root412
def mid415 : CBox := root414
def mid417 : CBox := root416
def mid419 : CBox := root418
def mid421 : CBox := root420
def mid423 : CBox := root422
def mid425 : CBox := root424
def mid427 : CBox := root426
def mid429 : CBox := root428
def mid431 : CBox := root430
def mid433 : CBox := root432
def mid435 : CBox := root434
def mid437 : CBox := root436
def mid439 : CBox := root438
def mid441 : CBox := root440
def mid443 : CBox := root442
def mid445 : CBox := root444
def mid447 : CBox := root446
def mid449 : CBox := root448
def mid451 : CBox := root450
def mid453 : CBox := root452
def mid455 : CBox := root454
def mid457 : CBox := root456
def mid459 : CBox := root458
def mid461 : CBox := root460
def mid463 : CBox := root462
def mid465 : CBox := root464
def mid467 : CBox := root466
def mid469 : CBox := root468
def mid471 : CBox := root470
def mid473 : CBox := root472
def mid475 : CBox := root474
def mid477 : CBox := root476
def mid479 : CBox := root478
def mid481 : CBox := root480
def mid483 : CBox := root482
def mid485 : CBox := root484
def mid487 : CBox := root486
def mid489 : CBox := root488
def mid491 : CBox := root490
def mid493 : CBox := root492
def mid495 : CBox := root494
def mid497 : CBox := root496
def mid499 : CBox := root498
def mid501 : CBox := root500
def mid503 : CBox := root502
def mid505 : CBox := root504
def mid507 : CBox := root506
def mid509 : CBox := root508
def mid511 : CBox := root510
def mid513 : CBox := root512
def mid515 : CBox := root514
def mid517 : CBox := root516
def mid519 : CBox := root518
def mid521 : CBox := root520
def mid523 : CBox := root522
def mid525 : CBox := root524
def mid527 : CBox := root526
def mid529 : CBox := root528
def mid531 : CBox := root530
def mid533 : CBox := root532
def mid535 : CBox := root534
def mid537 : CBox := root536
def mid539 : CBox := root538
def mid541 : CBox := root540
def mid543 : CBox := root542
def mid545 : CBox := root544
def mid547 : CBox := root546
def mid549 : CBox := root548
def mid551 : CBox := root550
def mid553 : CBox := root552
def mid555 : CBox := root554
def mid557 : CBox := root556
def mid559 : CBox := root558
def mid561 : CBox := root560
def mid563 : CBox := root562
def mid565 : CBox := root564
def mid567 : CBox := root566
def mid569 : CBox := root568
def mid571 : CBox := root570
def mid573 : CBox := root572
def mid575 : CBox := root574
def mid577 : CBox := root576
def mid579 : CBox := root578
def mid581 : CBox := root580
def mid583 : CBox := root582
def mid585 : CBox := root584
def mid587 : CBox := root586
def mid589 : CBox := root588
def mid591 : CBox := root590
def mid593 : CBox := root592
def mid595 : CBox := root594
def mid597 : CBox := root596
def mid599 : CBox := root598
def mid601 : CBox := root600
def mid603 : CBox := root602
def mid605 : CBox := root604
def mid607 : CBox := root606
def mid609 : CBox := root608
def mid611 : CBox := root610
def mid613 : CBox := root612
def mid615 : CBox := root614
def mid617 : CBox := root616
def mid619 : CBox := root618
def mid621 : CBox := root620
def mid623 : CBox := root622
def mid625 : CBox := root624
def mid627 : CBox := root626
def mid629 : CBox := root628
def mid631 : CBox := root630
def mid633 : CBox := root632
def mid635 : CBox := root634
def mid637 : CBox := root636
def mid639 : CBox := root638
def mid641 : CBox := root640
def mid643 : CBox := root642
def mid645 : CBox := root644
def mid647 : CBox := root646
def mid649 : CBox := root648
def mid651 : CBox := root650
def mid653 : CBox := root652
def mid655 : CBox := root654
def mid657 : CBox := root656
def mid659 : CBox := root658
def mid661 : CBox := root660
def mid663 : CBox := root662
def mid665 : CBox := root664
def mid667 : CBox := root666
def mid669 : CBox := root668
def mid671 : CBox := root670
def mid673 : CBox := root672
def mid675 : CBox := root674
def mid677 : CBox := root676
def mid679 : CBox := root678
def mid681 : CBox := root680
def mid683 : CBox := root682
def mid685 : CBox := root684
def mid687 : CBox := root686
def mid689 : CBox := root688
def mid691 : CBox := root690
def mid693 : CBox := root692
def mid695 : CBox := root694
def mid697 : CBox := root696
def mid699 : CBox := root698
def mid701 : CBox := root700
def mid703 : CBox := root702
def mid705 : CBox := root704
def mid707 : CBox := root706
def mid709 : CBox := root708
def mid711 : CBox := root710
def mid713 : CBox := root712
def mid715 : CBox := root714
def mid717 : CBox := root716
def mid719 : CBox := root718
def mid721 : CBox := root720
def mid723 : CBox := root722
def mid725 : CBox := root724
def mid727 : CBox := root726
def mid729 : CBox := root728
def mid731 : CBox := root730
def mid733 : CBox := root732
def mid735 : CBox := root734
def mid737 : CBox := root736
def mid739 : CBox := root738
def mid741 : CBox := root740
def mid743 : CBox := root742
def mid745 : CBox := root744
def mid747 : CBox := root746
def mid749 : CBox := root748
def mid751 : CBox := root750
def mid753 : CBox := root752
def mid755 : CBox := root754
def mid757 : CBox := root756
def mid759 : CBox := root758
def mid761 : CBox := root760
def mid763 : CBox := root762
def mid765 : CBox := root764
def mid767 : CBox := root766
def mid769 : CBox := root768
def mid771 : CBox := root770
def mid773 : CBox := root772
def mid775 : CBox := root774
def mid777 : CBox := root776
def mid779 : CBox := root778
def mid781 : CBox := root780
def mid783 : CBox := root782
def mid785 : CBox := root784
def mid787 : CBox := root786
def mid789 : CBox := root788
def mid791 : CBox := root790
def mid793 : CBox := root792
def mid795 : CBox := root794
def mid797 : CBox := root796
def mid799 : CBox := root798
def mid801 : CBox := root800
def mid803 : CBox := root802
def mid805 : CBox := root804
def mid807 : CBox := root806
def mid809 : CBox := root808
def mid811 : CBox := root810
def mid813 : CBox := root812
def mid815 : CBox := root814
def mid817 : CBox := root816
def mid819 : CBox := root818
def mid821 : CBox := root820
def mid823 : CBox := root822
def mid825 : CBox := root824
def mid827 : CBox := root826
def mid829 : CBox := root828
def mid831 : CBox := root830
def mid833 : CBox := root832
def mid835 : CBox := root834
def mid837 : CBox := root836
def mid839 : CBox := root838
def mid841 : CBox := root840
def mid843 : CBox := root842
def mid845 : CBox := root844
def mid847 : CBox := root846
def mid849 : CBox := root848
def mid851 : CBox := root850
def mid853 : CBox := root852
def mid855 : CBox := root854
def mid857 : CBox := root856
def mid859 : CBox := root858
def mid861 : CBox := root860
def mid863 : CBox := root862
def mid865 : CBox := root864
def mid867 : CBox := root866
def mid869 : CBox := root868
def mid871 : CBox := root870
def mid873 : CBox := root872
def mid875 : CBox := root874
def mid877 : CBox := root876
def mid879 : CBox := root878
def mid881 : CBox := root880
def mid883 : CBox := root882
def mid885 : CBox := root884
def mid887 : CBox := root886
def mid889 : CBox := root888
def mid891 : CBox := root890
def mid893 : CBox := root892
def mid895 : CBox := root894
def mid897 : CBox := root896
def mid899 : CBox := root898
def mid901 : CBox := root900
def mid903 : CBox := root902
def mid905 : CBox := root904
def mid907 : CBox := root906
def mid909 : CBox := root908
def mid911 : CBox := root910
def mid913 : CBox := root912
def mid915 : CBox := root914
def mid917 : CBox := root916
def mid919 : CBox := root918
def mid921 : CBox := root920
def mid923 : CBox := root922
def mid925 : CBox := root924
def mid927 : CBox := root926
def mid929 : CBox := root928
def mid931 : CBox := root930
def mid933 : CBox := root932
def mid935 : CBox := root934
def mid937 : CBox := root936
def mid939 : CBox := root938
def mid941 : CBox := root940
def mid943 : CBox := root942
def mid945 : CBox := root944
def mid947 : CBox := root946
def mid949 : CBox := root948
def mid951 : CBox := root950
def mid953 : CBox := root952
def mid955 : CBox := root954
def mid957 : CBox := root956
def mid959 : CBox := root958
def mid961 : CBox := root960
def mid963 : CBox := root962
def mid965 : CBox := root964
def mid967 : CBox := root966
def mid969 : CBox := root968
def mid971 : CBox := root970
def mid973 : CBox := root972
def mid975 : CBox := root974
def mid977 : CBox := root976
def mid979 : CBox := root978
def mid981 : CBox := root980
def mid983 : CBox := root982
def mid985 : CBox := root984
def mid987 : CBox := root986
def mid989 : CBox := root988
def mid991 : CBox := root990
def mid993 : CBox := root992
def mid995 : CBox := root994
def mid997 : CBox := root996
def mid999 : CBox := root998
def mid1001 : CBox := root1000
def mid1003 : CBox := root1002
def mid1005 : CBox := root1004
def mid1007 : CBox := root1006
def mid1009 : CBox := root1008
def mid1011 : CBox := root1010
def mid1013 : CBox := root1012
def mid1015 : CBox := root1014
def mid1017 : CBox := root1016
def mid1019 : CBox := root1018
def mid1021 : CBox := root1020
def mid1023 : CBox := root1022
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
def roots0 : Fin 32 → CBox := ![IntegerRoots.root0,IntegerRoots.root1,IntegerRoots.root2,IntegerRoots.root3,IntegerRoots.root4,IntegerRoots.root5,IntegerRoots.root6,IntegerRoots.root7,IntegerRoots.root8,IntegerRoots.root9,IntegerRoots.root10,IntegerRoots.root11,IntegerRoots.root12,IntegerRoots.root13,IntegerRoots.root14,IntegerRoots.root15,IntegerRoots.root16,IntegerRoots.root17,IntegerRoots.root18,IntegerRoots.root19,IntegerRoots.root20,IntegerRoots.root21,IntegerRoots.root22,IntegerRoots.root23,IntegerRoots.root24,IntegerRoots.root25,IntegerRoots.root26,IntegerRoots.root27,IntegerRoots.root28,IntegerRoots.root29,IntegerRoots.root30,IntegerRoots.root31]
def roots4 : Fin 32 → CBox := ![IntegerRoots.root128,IntegerRoots.root129,IntegerRoots.root130,IntegerRoots.root131,IntegerRoots.root132,IntegerRoots.root133,IntegerRoots.root134,IntegerRoots.root135,IntegerRoots.root136,IntegerRoots.root137,IntegerRoots.root138,IntegerRoots.root139,IntegerRoots.root140,IntegerRoots.root141,IntegerRoots.root142,IntegerRoots.root143,IntegerRoots.root144,IntegerRoots.root145,IntegerRoots.root146,IntegerRoots.root147,IntegerRoots.root148,IntegerRoots.root149,IntegerRoots.root150,IntegerRoots.root151,IntegerRoots.root152,IntegerRoots.root153,IntegerRoots.root154,IntegerRoots.root155,IntegerRoots.root156,IntegerRoots.root157,IntegerRoots.root158,IntegerRoots.root159]
def roots5 : Fin 32 → CBox := ![IntegerRoots.root160,IntegerRoots.root161,IntegerRoots.root162,IntegerRoots.root163,IntegerRoots.root164,IntegerRoots.root165,IntegerRoots.root166,IntegerRoots.root167,IntegerRoots.root168,IntegerRoots.root169,IntegerRoots.root170,IntegerRoots.root171,IntegerRoots.root172,IntegerRoots.root173,IntegerRoots.root174,IntegerRoots.root175,IntegerRoots.root176,IntegerRoots.root177,IntegerRoots.root178,IntegerRoots.root179,IntegerRoots.root180,IntegerRoots.root181,IntegerRoots.root182,IntegerRoots.root183,IntegerRoots.root184,IntegerRoots.root185,IntegerRoots.root186,IntegerRoots.root187,IntegerRoots.root188,IntegerRoots.root189,IntegerRoots.root190,IntegerRoots.root191]
def roots16 : Fin 32 → CBox := ![IntegerRoots.root512,IntegerRoots.root513,IntegerRoots.root514,IntegerRoots.root515,IntegerRoots.root516,IntegerRoots.root517,IntegerRoots.root518,IntegerRoots.root519,IntegerRoots.root520,IntegerRoots.root521,IntegerRoots.root522,IntegerRoots.root523,IntegerRoots.root524,IntegerRoots.root525,IntegerRoots.root526,IntegerRoots.root527,IntegerRoots.root528,IntegerRoots.root529,IntegerRoots.root530,IntegerRoots.root531,IntegerRoots.root532,IntegerRoots.root533,IntegerRoots.root534,IntegerRoots.root535,IntegerRoots.root536,IntegerRoots.root537,IntegerRoots.root538,IntegerRoots.root539,IntegerRoots.root540,IntegerRoots.root541,IntegerRoots.root542,IntegerRoots.root543]
def rootRows : Fin 32 → Fin 32 → CBox := ![roots0,roots1,roots2,roots3,roots4,roots5,roots6,roots7,roots8,roots9,roots10,roots11,roots12,roots13,roots14,roots15,roots16,roots17,roots18,roots19,roots20,roots21,roots22,roots23,roots24,roots25,roots26,roots27,roots28,roots29,roots30,roots31]
def rootLookup (n : ℕ) : CBox :=
  rootRows ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩

def partialBox (v : ℕ) : ℕ → RBox
  | 0 => ⟨0,0⟩
  | N+1 => (partialBox v N).add ((rootLookup (2*(N+1)*(2*v+1))).re.scale 1
      (4*((N+1:ℕ):ℤ)^2-1))

def weightBoxCalc (v : ℕ) : RBox :=
  ((RBox.rat 1 1).add ((partialBox v 127).scale (-2) 1)).scale 1 256

def nodeLookup (n : Fin 256) : RBox := (rootLookup (2*n.val+1)).re
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

def phaseBase : CBox := (piI.scale 1 6).exp 1

def phaseBox (n : ℕ) : CBox := phaseBase.powBin 4 (n%12)

def coefficientBox : ℕ → CBox
  | 0 => CBox.rat 5 1 0 1
  | 1 => ⟨RBox.rat (-1) 1,bBounds.scale 2 1⟩
  | 2 => ⟨RBox.rat 1 1,bBounds.scale 2 1⟩
  | 3 => CBox.rat (-2) 1 0 1
  | 4 => ⟨RBox.rat (-1) 2,bBounds⟩
  | 5 => ⟨RBox.rat (-1) 1,bBounds.scale (-2) 1⟩
  | 6 => CBox.rat 1 1 0 1
  | _ => CBox.rat 0 1 0 1
def spectralCoefficientBox (n l : ℕ) : CBox := (coefficientBox l).mul (phaseBox (l*n))

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def alphaBox (n j : ℕ) : CBox := boxSum
  (fun l => if j<l then spectralCoefficientBox n l else zeroBox) 7
def betaBox (n j : ℕ) : CBox := boxSum
  (fun l => if j<l then (spectralCoefficientBox n l).scale l 6 else zeroBox) 7

end SharpPlanar.IntegerBasis

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
def row5_7 : Fin 16 → PointBox := ![p5_112,p5_113,p5_114,p5_115,p5_116,p5_117,p5_118,p5_119,p5_120,p5_121,p5_122,p5_123,p5_124,p5_125,p5_126,p5_127]
def row5 : Fin 16 → Fin 16 → PointBox := ![row5_0,row5_1,row5_2,row5_3,row5_4,row5_5,row5_6,row5_7,row5_8,row5_9,row5_10,row5_11,row5_12,row5_13,row5_14,row5_15]
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
noncomputable def amp1_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 1 j) (bLookup 1 j) false)
noncomputable def amp1_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 1 j) (bLookup 1 j) true)
noncomputable def amp3_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 3 j) (bLookup 3 j) false)
noncomputable def amp3_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 3 j) (bLookup 3 j) true)
noncomputable def amp3_15 : Fin 16 → Fin 16 → CBox := ![amp3_15_0,amp3_15_1,amp3_15_2,amp3_15_3,amp3_15_4,amp3_15_5,amp3_15_6,amp3_15_7,amp3_15_8,amp3_15_9,amp3_15_10,amp3_15_11,amp3_15_12,amp3_15_13,amp3_15_14,amp3_15_15]
noncomputable def amp3_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp3_10,amp3_11,amp3_12,amp3_13,amp3_14,amp3_15]
noncomputable def amp4_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 4 j) (bLookup 4 j) false)
noncomputable def amp4_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 4 j) (bLookup 4 j) true)
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def power1Expr (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).mul (gridRows j i k).direct
noncomputable def power1_r5 : Fin 16 → Fin 16 → CBox := ![power1_r5_0,power1_r5_1,power1_r5_2,power1_r5_3,power1_r5_4,power1_r5_5,power1_r5_6,power1_r5_7,power1_r5_8,power1_r5_9,power1_r5_10,power1_r5_11,power1_r5_12,power1_r5_13,power1_r5_14,power1_r5_15]
noncomputable def power1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power1_r0,power1_r1,power1_r2,power1_r3,power1_r4,power1_r5]
noncomputable def power2Expr (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).mul (gridRows j i k).direct
noncomputable def power2_r4 : Fin 16 → Fin 16 → CBox := ![power2_r4_0,power2_r4_1,power2_r4_2,power2_r4_3,power2_r4_4,power2_r4_5,power2_r4_6,power2_r4_7,power2_r4_8,power2_r4_9,power2_r4_10,power2_r4_11,power2_r4_12,power2_r4_13,power2_r4_14,power2_r4_15]
noncomputable def power2 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power2_r0,power2_r1,power2_r2,power2_r3,power2_r4,power2_r5]
noncomputable def power3Expr (j : Fin 6) (i k : Fin 16) : CBox := (power2 j i k).mul (gridRows j i k).direct
noncomputable def power4Expr (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def column1_0_r5 : Fin 16 → Fin 16 → CBox := ![column1_0_r5_0,column1_0_r5_1,column1_0_r5_2,column1_0_r5_3,column1_0_r5_4,column1_0_r5_5,column1_0_r5_6,column1_0_r5_7,column1_0_r5_8,column1_0_r5_9,column1_0_r5_10,column1_0_r5_11,column1_0_r5_12,column1_0_r5_13,column1_0_r5_14,column1_0_r5_15]
noncomputable def column1_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column1_0_r0,column1_0_r1,column1_0_r2,column1_0_r3,column1_0_r4,column1_0_r5]
noncomputable def column1_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power1 j i k)
noncomputable def column1_1_r3 : Fin 16 → Fin 16 → CBox := ![column1_1_r3_0,column1_1_r3_1,column1_1_r3_2,column1_1_r3_3,column1_1_r3_4,column1_1_r3_5,column1_1_r3_6,column1_1_r3_7,column1_1_r3_8,column1_1_r3_9,column1_1_r3_10,column1_1_r3_11,column1_1_r3_12,column1_1_r3_13,column1_1_r3_14,column1_1_r3_15]
noncomputable def column1_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column1_1_r0,column1_1_r1,column1_1_r2,column1_1_r3,column1_1_r4,column1_1_r5]
noncomputable def column3_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power3 j i k)
noncomputable def column3_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_1 j i k).mul (power3 j i k)
noncomputable def column4_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power4 j i k)
noncomputable def column4_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power4 j i k)
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
noncomputable def transStepExpr (j : Fin 6) (i k : Fin 16) : CBox := transformedStepBox (gridRows j i k)
noncomputable def trans1Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans0 j i k).mul (transStep j i k)
noncomputable def trans1_r4 : Fin 16 → Fin 16 → CBox := ![trans1_r4_0,trans1_r4_1,trans1_r4_2,trans1_r4_3,trans1_r4_4,trans1_r4_5,trans1_r4_6,trans1_r4_7,trans1_r4_8,trans1_r4_9,trans1_r4_10,trans1_r4_11,trans1_r4_12,trans1_r4_13,trans1_r4_14,trans1_r4_15]
noncomputable def trans1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans1_r0,trans1_r1,trans1_r2,trans1_r3,trans1_r4,trans1_r5]
noncomputable def trans2Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans1 j i k).mul (transStep j i k)
noncomputable def trans4Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans3 j i k).mul (transStep j i k)
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
noncomputable def kernel1_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans1 j i k)
noncomputable def kernel1_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans1 j i k)).mul (piI.mul (gridRows j i k).z)
noncomputable def kernel3_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans3 j i k)
noncomputable def kernel3_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans3 j i k)).mul (piI.mul (gridRows j i k).z)
noncomputable def kernel4_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans4 j i k)
noncomputable def kernel4_0_r1 : Fin 16 → Fin 16 → CBox := ![kernel4_0_r1_0,kernel4_0_r1_1,kernel4_0_r1_2,kernel4_0_r1_3,kernel4_0_r1_4,kernel4_0_r1_5,kernel4_0_r1_6,kernel4_0_r1_7,kernel4_0_r1_8,kernel4_0_r1_9,kernel4_0_r1_10,kernel4_0_r1_11,kernel4_0_r1_12,kernel4_0_r1_13,kernel4_0_r1_14,kernel4_0_r1_15]
noncomputable def kernel4_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel4_0_r0,kernel4_0_r1,kernel4_0_r2,kernel4_0_r3,kernel4_0_r4,kernel4_0_r5]
noncomputable def kernel4_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans4 j i k)).mul (piI.mul (gridRows j i k).z)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments1
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
namespace cm1_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_1_0_0
namespace cm1_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel1_1 j i k))
end cm1_1_0_1
namespace cm1_1_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_1_1_0
namespace cm1_1_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel1_1 j i k))
end cm1_1_1_1
namespace cm1_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel3_0 j i k))
end cm1_3_0_0
namespace cm1_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel3_1 j i k))
end cm1_3_0_1
namespace cm1_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel3_0 j i k))
end cm1_3_1_0
namespace cm1_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel3_1 j i k))
end cm1_3_1_1
namespace cm1_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_4_0_0
namespace cm1_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel4_1 j i k))
end cm1_4_0_1
namespace cm1_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel4_0 j i k))
end cm1_4_1_0
namespace cm1_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel4_1 j i k))
end cm1_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments3
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
namespace cm3_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel1_0 j i k))
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm3_1_0_0
namespace cm3_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel1_1 j i k))
end cm3_1_0_1
namespace cm3_1_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel1_0 j i k))
end cm3_1_1_0
namespace cm3_1_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel1_1 j i k))
end cm3_1_1_1
namespace cm3_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel3_0 j i k))
end cm3_3_0_0
namespace cm3_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel3_1 j i k))
end cm3_3_0_1
namespace cm3_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel3_0 j i k))
end cm3_3_1_0
namespace cm3_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel3_1 j i k))
end cm3_3_1_1
namespace cm3_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel4_0 j i k))
end cm3_4_0_0
namespace cm3_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel4_1 j i k))
end cm3_4_0_1
namespace cm3_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel4_0 j i k))
end cm3_4_1_0
namespace cm3_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel4_1 j i k))
end cm3_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments4
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
namespace cm4_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel1_0 j i k))
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm4_1_0_0
namespace cm4_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel1_1 j i k))
end cm4_1_0_1
namespace cm4_1_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel1_0 j i k))
end cm4_1_1_0
namespace cm4_1_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel1_1 j i k))
end cm4_1_1_1
namespace cm4_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm4_3_0_0
namespace cm4_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel3_1 j i k))
end cm4_3_0_1
namespace cm4_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel3_0 j i k))
end cm4_3_1_0
namespace cm4_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel3_1 j i k))
end cm4_3_1_1
namespace cm4_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel4_0 j i k))
end cm4_4_0_0
namespace cm4_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel4_1 j i k))
end cm4_4_0_1
namespace cm4_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel4_0 j i k))
end cm4_4_1_0
namespace cm4_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel4_1 j i k))
end cm4_4_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

def qSmall : RBox := ((piBounds.mul piBounds).scale 2 3).mul
  ((RBox.rat 2 1).add (bBounds.scale (-2) 1))
def qLarge : RBox := ((piBounds.mul piBounds).scale 2 3).mul
  ((RBox.rat 2 1).add (bBounds.scale 2 1))

def dSmall : RBox := (piBounds.mul ((RBox.rat 3 1).add (bBounds.scale 2 1))).scale 1 18
def dOther : RBox := (piBounds.mul ((RBox.rat 3 1).add (bBounds.scale (-2) 1))).scale 1 18
def dBase : RBox := (piBounds.mul bBounds).scale 7 9

def qBox (n : ℕ) : RBox := if n%12=0 ∨ n%12=4 then qBase else if n%12=1 ∨ n%12=3 then qSmall else qLarge
def dBox (n : ℕ) : RBox := match n%12 with
  | 0 => dBase.neg
  | 1 => dSmall
  | 3 => dSmall.neg
  | 4 => dBase
  | 7 => dOther.neg
  | _ => dOther

def qiBox (n : ℕ) : RBox := invBox (qBox n)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
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

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
noncomputable def WminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => RBox.rat (WminusInt i j) 10000
noncomputable def AminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((dEntries i j))
noncomputable def defectminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((matrixMulBox WminusBox AminusBox i j).neg)
end SharpPlanar.Numerical

end OAI
end


