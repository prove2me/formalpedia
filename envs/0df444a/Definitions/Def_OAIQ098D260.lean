-- Prove2me | Definitions.Def_OAIQ098D260
-- name    : OAIQ098D260
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:12:37.032012+00:00
-- url     : https://prove2.me/theorems/3ee48ac5-7829-4c38-b259-4469954df6b5
-- title:
--   Definitions bundle OAIQ098D260 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 238 declarations of OpenAI's Lean: 235 definitions, 1 instance and 2 theorems. The definitions and types are `OAI.SharpPlanar.Numerical.U73.umat`, `OAI.SharpPlanar.Numerical.U75.umat`, `OAI.SharpPlanar.Numerical.U76.umat`, `OAI.SharpPlanar.Numerical.U79.umat`, `OAI.SharpPlanar.Numerical.U81.umat`, `OAI.SharpPlanar.Numerical.U85.umat`, `OAI.SharpPlanar.Numerical.U87.umat`, `OAI.SharpPlanar.Numerical.U88.umat`, `OAI.SharpPlanar.Numerical.U9.umat`, `OAI.SharpPlanar.Numerical.U93.umat`, `OAI.SharpPlanar.Numerical.U96.umat`, `OAI.SharpPlanar.Numerical.U97.umat`, `OAI.SharpPlanar.Numerical.U99.umat`, `OAI.SharpPlanar.Residual1.box0_0`, `OAI.SharpPlanar.Residual1.box0_1`, `OAI.SharpPlanar.Residual1.box1_0`, `OAI.SharpPlanar.Residual1.box1_1`, `OAI.SharpPlanar.Residual100.box0_0`, `OAI.SharpPlanar.Residual100.box0_1`, `OAI.SharpPlanar.Residual100.box1_0`, `OAI.SharpPlanar.Residual100.box1_1`, `OAI.SharpPlanar.Residual12.box0_0`, `OAI.SharpPlanar.Residual12.box0_1`, `OAI.SharpPlanar.Residual12.box1_0`, `OAI.SharpPlanar.Residual12.box1_1`, `OAI.SharpPlanar.Residual13.box0_0`, `OAI.SharpPlanar.Residual13.box0_1`, `OAI.SharpPlanar.Residual13.box1_0`, `OAI.SharpPlanar.Residual13.box1_1`, `OAI.SharpPlanar.Residual15.box0_0`, `OAI.SharpPlanar.Residual15.box0_1`, `OAI.SharpPlanar.Residual15.box1_0`, `OAI.SharpPlanar.Residual15.box1_1`, `OAI.SharpPlanar.Residual16.box0_0`, `OAI.SharpPlanar.Residual16.box0_1`, `OAI.SharpPlanar.Residual16.box1_0`, `OAI.SharpPlanar.Residual16.box1_1`, `OAI.SharpPlanar.Residual19.box0_0`, `OAI.SharpPlanar.Residual19.box0_1`, `OAI.SharpPlanar.Residual19.box1_0` and 195 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_BernsteinBoxes`, `PlanarPacking_Certificate_Residual1`, `PlanarPacking_Certificate_Residual100`, `PlanarPacking_Certificate_Residual12`, `PlanarPacking_Certificate_Residual13`, `PlanarPacking_Certificate_Residual15`, `PlanarPacking_Certificate_Residual16`, `PlanarPacking_Certificate_Residual19`, `PlanarPacking_Certificate_Residual21`, `PlanarPacking_Certificate_Residual24`, `PlanarPacking_Certificate_Residual25`, `PlanarPacking_Certificate_Residual27`, `PlanarPacking_Certificate_Residual28`, `PlanarPacking_Certificate_Residual3`, `PlanarPacking_Certificate_Residual31`, `PlanarPacking_Certificate_Residual33`, `PlanarPacking_Certificate_Residual36`, `PlanarPacking_Certificate_Residual37`, `PlanarPacking_Certificate_Residual39`, `PlanarPacking_Certificate_Residual4`, `PlanarPacking_Certificate_Residual40`, `PlanarPacking_Certificate_Residual43`, `PlanarPacking_Certificate_Residual45`, `PlanarPacking_Certificate_Residual48`, `PlanarPacking_Certificate_Residual49`, `PlanarPacking_Certificate_Residual51`, `PlanarPacking_Certificate_Residual52`, `PlanarPacking_Certificate_Residual55`, `PlanarPacking_Certificate_Residual57`, `PlanarPacking_Certificate_Residual60`, `PlanarPacking_Certificate_Residual61`, `PlanarPacking_Certificate_Residual63`, `PlanarPacking_Certificate_Residual64`, `PlanarPacking_Certificate_Residual67`, `PlanarPacking_Certificate_Residual69`, `PlanarPacking_Certificate_Residual7`, `PlanarPacking_Certificate_Residual72`, `PlanarPacking_Certificate_Residual73`, `PlanarPacking_Certificate_Residual75`, `PlanarPacking_Certificate_Residual76`, `PlanarPacking_Certificate_Residual79`, `PlanarPacking_Certificate_Residual81`, `PlanarPacking_Certificate_Residual84`, `PlanarPacking_Certificate_Residual85`, `PlanarPacking_Certificate_Residual87`, `PlanarPacking_Certificate_Residual88`, `PlanarPacking_Certificate_Residual9`, `PlanarPacking_Certificate_Residual91`, `PlanarPacking_Certificate_Residual93`, `PlanarPacking_Certificate_Residual96`, `PlanarPacking_Certificate_Residual97`, `PlanarPacking_Certificate_Residual99`, `PlanarPacking_Certificate_WUCert73`, `PlanarPacking_Certificate_WUCert75`, `PlanarPacking_Certificate_WUCert76`, `PlanarPacking_Certificate_WUCert79`, `PlanarPacking_Certificate_WUCert81`, `PlanarPacking_Certificate_WUCert85`, `PlanarPacking_Certificate_WUCert87`, `PlanarPacking_Certificate_WUCert88`, `PlanarPacking_Certificate_WUCert9`, `PlanarPacking_Certificate_WUCert93`, `PlanarPacking_Certificate_WUCert96`, `PlanarPacking_Certificate_WUCert97`, `PlanarPacking_Certificate_WUCert99`, `PlanarPacking_ContactData`, `PlanarPacking_FullMomentBridge`, `PlanarPacking_HighMomentsBase`, `PlanarPacking_Intervals`, `PlanarPacking_ResidualBase`, `PlanarPacking_TableMomentsBase`.
--
--   **Imports.** It imports the bundles `OAIQ098D004` and `OAIQ098D005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098D693`; the statements `OAI.SharpPlanar.Bernstein0.N1_right.bound`, `OAI.SharpPlanar.Bernstein0.N1_right.bound16`, `OAI.SharpPlanar.Bernstein0.N1_right.bound17`, `OAI.SharpPlanar.Bernstein0.N1_right.bound18`, `OAI.SharpPlanar.Bernstein0.N1_right.bound19`, `OAI.SharpPlanar.Bernstein0.N1_right.bound20`, `OAI.SharpPlanar.Bernstein0.N1_right.bound21`, `OAI.SharpPlanar.Bernstein0.N1_right.bound22`, `OAI.SharpPlanar.Bernstein0.N1_right.bound23`, `OAI.SharpPlanar.Bernstein0.N1_right.bound24`, `OAI.SharpPlanar.Bernstein0.N1_right.bound25`, `OAI.SharpPlanar.Bernstein0.N1_right.bound26`, `OAI.SharpPlanar.Bernstein0.N1_right.bound27`, `OAI.SharpPlanar.Bernstein0.N1_right.bound28`, `OAI.SharpPlanar.Bernstein0.N1_right.t21_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t22_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t23_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t24_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t25_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t26_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t27_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t28_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.ts_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t10_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t8_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t9_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.ts_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t10_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t8_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t9_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.ts_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t10_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t8_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t9_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.ts_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t10_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t8_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t9_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.ts_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.bound`, `OAI.SharpPlanar.Bernstein19.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t10_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t11_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t8_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t9_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.bound`, `OAI.SharpPlanar.Bernstein19.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t10_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t11_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t8_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t9_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.bound`, `OAI.SharpPlanar.Bernstein19.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t10_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t11_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t8_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t9_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.bound`, `OAI.SharpPlanar.Bernstein19.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t10_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t11_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t8_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t9_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.bound`, `OAI.SharpPlanar.Bernstein1.N0_right.bound10`, `OAI.SharpPlanar.Bernstein1.N0_right.bound11`, `OAI.SharpPlanar.Bernstein1.N0_right.bound12`, `OAI.SharpPlanar.Bernstein1.N0_right.bound13`, `OAI.SharpPlanar.Bernstein1.N0_right.bound14`, `OAI.SharpPlanar.Bernstein1.N0_right.bound15`, `OAI.SharpPlanar.Bernstein1.N0_right.bound16`, `OAI.SharpPlanar.Bernstein1.N0_right.bound17`, `OAI.SharpPlanar.Bernstein1.N0_right.bound18`, `OAI.SharpPlanar.Bernstein1.N0_right.bound19`, `OAI.SharpPlanar.Bernstein1.N0_right.bound2`, `OAI.SharpPlanar.Bernstein1.N0_right.bound20`, `OAI.SharpPlanar.Bernstein1.N0_right.bound21`, `OAI.SharpPlanar.Bernstein1.N0_right.bound22`, `OAI.SharpPlanar.Bernstein1.N0_right.bound23`, `OAI.SharpPlanar.Bernstein1.N0_right.bound24`, `OAI.SharpPlanar.Bernstein1.N0_right.bound25`, `OAI.SharpPlanar.Bernstein1.N0_right.bound26`, `OAI.SharpPlanar.Bernstein1.N0_right.bound27`, `OAI.SharpPlanar.Bernstein1.N0_right.bound28`, `OAI.SharpPlanar.Bernstein1.N0_right.bound3`, `OAI.SharpPlanar.Bernstein1.N0_right.bound4`, `OAI.SharpPlanar.Bernstein1.N0_right.bound5`, `OAI.SharpPlanar.Bernstein1.N0_right.bound6`, `OAI.SharpPlanar.Bernstein1.N0_right.bound7`, `OAI.SharpPlanar.Bernstein1.N0_right.bound8`, `OAI.SharpPlanar.Bernstein1.N0_right.bound9`, `OAI.SharpPlanar.Bernstein1.N0_right.t14_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t16_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t17_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t18_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t19_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t20_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t21_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t22_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t23_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t24_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t25_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t26_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t27_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t28_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.bound`, `OAI.SharpPlanar.Bernstein1.N1_left.bound28`, `OAI.SharpPlanar.Bernstein1.N1_left.t13_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t15_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t16_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t17_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t18_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t19_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t20_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t21_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t22_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t23_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t24_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t25_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t26_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t27_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t28_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.bound`, `OAI.SharpPlanar.Bernstein1.N1_right.bound28`, `OAI.SharpPlanar.Bernstein1.N1_right.t13_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t15_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t16_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t17_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t18_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t19_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t20_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t21_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t22_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t23_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t24_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t25_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t26_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t27_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t28_contains`, `OAI.SharpPlanar.Bernstein21.N0_left.bound`, `OAI.SharpPlanar.Bernstein21.N0_left.bound27`, `OAI.SharpPlanar.Bernstein21.N0_left.bound28`, `OAI.SharpPlanar.Bernstein21.N0_right.bound`, `OAI.SharpPlanar.Bernstein21.N0_right.bound27`, `OAI.SharpPlanar.Bernstein21.N0_right.bound28`, `OAI.SharpPlanar.Bernstein21.N1_left.bound`, `OAI.SharpPlanar.Bernstein21.N1_left.bound27`, `OAI.SharpPlanar.Bernstein21.N1_left.bound28`, `OAI.SharpPlanar.Bernstein21.N1_right.bound`, `OAI.SharpPlanar.Bernstein21.N1_right.bound27`, `OAI.SharpPlanar.Bernstein21.N1_right.bound28`, `OAI.SharpPlanar.Bernstein27.N0_left.bound`, `OAI.SharpPlanar.Bernstein27.N0_left.bound26`, `OAI.SharpPlanar.Bernstein27.N0_left.bound27`, `OAI.SharpPlanar.Bernstein27.N0_left.bound28`, `OAI.SharpPlanar.Bernstein27.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t10_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.bound`, `OAI.SharpPlanar.Bernstein27.N0_right.bound26`, `OAI.SharpPlanar.Bernstein27.N0_right.bound27`, `OAI.SharpPlanar.Bernstein27.N0_right.bound28`, `OAI.SharpPlanar.Bernstein27.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t10_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.bound`, `OAI.SharpPlanar.Bernstein27.N1_left.bound26`, `OAI.SharpPlanar.Bernstein27.N1_left.bound27`, `OAI.SharpPlanar.Bernstein27.N1_left.bound28`, `OAI.SharpPlanar.Bernstein27.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t10_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.bound`, `OAI.SharpPlanar.Bernstein27.N1_right.bound26`, `OAI.SharpPlanar.Bernstein27.N1_right.bound27`, `OAI.SharpPlanar.Bernstein27.N1_right.bound28`, `OAI.SharpPlanar.Bernstein27.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t10_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.bound`, `OAI.SharpPlanar.Bernstein28.N0_left.bound27`, `OAI.SharpPlanar.Bernstein28.N0_left.bound28`, `OAI.SharpPlanar.Bernstein28.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.bound`, `OAI.SharpPlanar.Bernstein28.N0_right.bound27`, `OAI.SharpPlanar.Bernstein28.N0_right.bound28`, `OAI.SharpPlanar.Bernstein28.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.bound`, `OAI.SharpPlanar.Bernstein28.N1_left.bound27`, `OAI.SharpPlanar.Bernstein28.N1_left.bound28`, `OAI.SharpPlanar.Bernstein28.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.bound`, `OAI.SharpPlanar.Bernstein28.N1_right.bound27`, `OAI.SharpPlanar.Bernstein28.N1_right.bound28`, `OAI.SharpPlanar.Bernstein28.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein4.N0_left.bound`, `OAI.SharpPlanar.Bernstein4.N0_right.bound`, `OAI.SharpPlanar.Bernstein4.N1_left.bound`, `OAI.SharpPlanar.Bernstein4.N1_right.bound`, `OAI.SharpPlanar.Residual100.bound0_0`, `OAI.SharpPlanar.Residual100.bound0_1`, `OAI.SharpPlanar.Residual100.bound1_0`, `OAI.SharpPlanar.Residual100.bound1_1`, `OAI.SharpPlanar.Residual33.bound0_1`, `OAI.SharpPlanar.Residual33.bound1_1`, `OAI.SharpPlanar.Residual36.bound0_1`, `OAI.SharpPlanar.Residual36.bound1_1`, `OAI.SharpPlanar.Residual37.bound0_1`, `OAI.SharpPlanar.Residual37.bound1_1`, `OAI.SharpPlanar.Residual39.bound0_1`, `OAI.SharpPlanar.Residual39.bound1_0`, `OAI.SharpPlanar.Residual39.bound1_1`, `OAI.SharpPlanar.Residual40.bound0_0`, `OAI.SharpPlanar.Residual40.bound0_1`, `OAI.SharpPlanar.Residual40.bound1_0`, `OAI.SharpPlanar.Residual40.bound1_1`, `OAI.SharpPlanar.Residual43.bound0_0`, `OAI.SharpPlanar.Residual43.bound0_1`, `OAI.SharpPlanar.Residual43.bound1_0`, `OAI.SharpPlanar.Residual43.bound1_1`, `OAI.SharpPlanar.Residual45.bound0_0`, `OAI.SharpPlanar.Residual45.bound0_1`, `OAI.SharpPlanar.Residual45.bound1_0`, `OAI.SharpPlanar.Residual45.bound1_1`, `OAI.SharpPlanar.Residual48.bound0_0`, `OAI.SharpPlanar.Residual48.bound0_1`, `OAI.SharpPlanar.Residual48.bound1_0`, `OAI.SharpPlanar.Residual48.bound1_1`, `OAI.SharpPlanar.Residual49.bound0_0`, `OAI.SharpPlanar.Residual49.bound0_1`, `OAI.SharpPlanar.Residual49.bound1_0`, `OAI.SharpPlanar.Residual49.bound1_1`, `OAI.SharpPlanar.Residual51.bound0_0`, `OAI.SharpPlanar.Residual51.bound0_1`, `OAI.SharpPlanar.Residual51.bound1_0`, `OAI.SharpPlanar.Residual51.bound1_1`, `OAI.SharpPlanar.Residual52.bound0_0`, `OAI.SharpPlanar.Residual52.bound0_1`, `OAI.SharpPlanar.Residual52.bound1_0`, `OAI.SharpPlanar.Residual52.bound1_1`, `OAI.SharpPlanar.Residual55.bound0_0`, `OAI.SharpPlanar.Residual55.bound0_1`, `OAI.SharpPlanar.Residual55.bound1_0`, `OAI.SharpPlanar.Residual55.bound1_1`, `OAI.SharpPlanar.Residual57.bound0_0`, `OAI.SharpPlanar.Residual57.bound0_1`, `OAI.SharpPlanar.Residual57.bound1_0`, `OAI.SharpPlanar.Residual57.bound1_1`, `OAI.SharpPlanar.Residual60.bound0_0`, `OAI.SharpPlanar.Residual60.bound0_1`, `OAI.SharpPlanar.Residual60.bound1_0`, `OAI.SharpPlanar.Residual60.bound1_1`, `OAI.SharpPlanar.Residual61.bound0_0`, `OAI.SharpPlanar.Residual61.bound0_1`, `OAI.SharpPlanar.Residual61.bound1_0`, `OAI.SharpPlanar.Residual61.bound1_1`, `OAI.SharpPlanar.Residual63.bound0_0`, `OAI.SharpPlanar.Residual63.bound0_1`, `OAI.SharpPlanar.Residual63.bound1_0`, `OAI.SharpPlanar.Residual63.bound1_1`, `OAI.SharpPlanar.Residual64.bound0_0`, `OAI.SharpPlanar.Residual64.bound0_1`, `OAI.SharpPlanar.Residual64.bound1_0`, `OAI.SharpPlanar.Residual64.bound1_1`, `OAI.SharpPlanar.Residual67.bound0_0`, `OAI.SharpPlanar.Residual67.bound0_1`, `OAI.SharpPlanar.Residual67.bound1_0`, `OAI.SharpPlanar.Residual67.bound1_1`, `OAI.SharpPlanar.Residual69.bound0_0`, `OAI.SharpPlanar.Residual69.bound0_1`, `OAI.SharpPlanar.Residual69.bound1_0`, `OAI.SharpPlanar.Residual69.bound1_1`, `OAI.SharpPlanar.Residual72.bound0_0`, `OAI.SharpPlanar.Residual72.bound0_1`, `OAI.SharpPlanar.Residual72.bound1_0`, `OAI.SharpPlanar.Residual72.bound1_1`, `OAI.SharpPlanar.Residual73.bound0_0`, `OAI.SharpPlanar.Residual73.bound0_1`, `OAI.SharpPlanar.Residual73.bound1_0`, `OAI.SharpPlanar.Residual73.bound1_1`, `OAI.SharpPlanar.Residual75.bound0_0`, `OAI.SharpPlanar.Residual75.bound0_1`, `OAI.SharpPlanar.Residual75.bound1_0`, `OAI.SharpPlanar.Residual75.bound1_1`, `OAI.SharpPlanar.Residual76.bound0_0`, `OAI.SharpPlanar.Residual76.bound0_1`, `OAI.SharpPlanar.Residual76.bound1_0`, `OAI.SharpPlanar.Residual76.bound1_1`, `OAI.SharpPlanar.Residual79.bound0_0`, `OAI.SharpPlanar.Residual79.bound0_1`, `OAI.SharpPlanar.Residual79.bound1_0`, `OAI.SharpPlanar.Residual79.bound1_1`, `OAI.SharpPlanar.Residual81.bound0_0`, `OAI.SharpPlanar.Residual81.bound0_1`, `OAI.SharpPlanar.Residual81.bound1_0`, `OAI.SharpPlanar.Residual81.bound1_1`, `OAI.SharpPlanar.Residual84.bound0_0`, `OAI.SharpPlanar.Residual84.bound0_1`, `OAI.SharpPlanar.Residual84.bound1_0`, `OAI.SharpPlanar.Residual84.bound1_1`, `OAI.SharpPlanar.Residual85.bound0_0`, `OAI.SharpPlanar.Residual85.bound0_1`, `OAI.SharpPlanar.Residual85.bound1_0`, `OAI.SharpPlanar.Residual85.bound1_1`, `OAI.SharpPlanar.Residual87.bound0_0`, `OAI.SharpPlanar.Residual87.bound0_1`, `OAI.SharpPlanar.Residual87.bound1_0`, `OAI.SharpPlanar.Residual87.bound1_1`, `OAI.SharpPlanar.Residual88.bound0_0`, `OAI.SharpPlanar.Residual88.bound0_1`, `OAI.SharpPlanar.Residual88.bound1_0`, `OAI.SharpPlanar.Residual88.bound1_1`, `OAI.SharpPlanar.Residual91.bound0_0`, `OAI.SharpPlanar.Residual91.bound0_1`, `OAI.SharpPlanar.Residual91.bound1_0`, `OAI.SharpPlanar.Residual91.bound1_1`, `OAI.SharpPlanar.Residual93.bound0_0`, `OAI.SharpPlanar.Residual93.bound0_1`, `OAI.SharpPlanar.Residual93.bound1_0`, `OAI.SharpPlanar.Residual93.bound1_1`, `OAI.SharpPlanar.Residual96.bound0_0`, `OAI.SharpPlanar.Residual96.bound0_1`, `OAI.SharpPlanar.Residual96.bound1_0`, `OAI.SharpPlanar.Residual96.bound1_1`, `OAI.SharpPlanar.Residual97.bound0_0`, `OAI.SharpPlanar.Residual97.bound0_1`, `OAI.SharpPlanar.Residual97.bound1_0`, `OAI.SharpPlanar.Residual97.bound1_1`, `OAI.SharpPlanar.Residual99.bound0_0`, `OAI.SharpPlanar.Residual99.bound0_1`, `OAI.SharpPlanar.Residual99.bound1_0`, `OAI.SharpPlanar.Residual99.bound1_1`, `OAI.SharpPlanar.bernsteinBox_contains`, `OAI.SharpPlanar.fullFactor_step_contains`, `OAI.SharpPlanar.fullMoment_direct`, `OAI.SharpPlanar.fullMoment_transformed_bound`, `OAI.SharpPlanar.normalizedH_table`, `OAI.SharpPlanar.residual_finite_exterior_0`, `OAI.SharpPlanar.residual_finite_exterior_1`, `OAI.SharpPlanar.sourcePower_of_cap`, `OAI.SharpPlanar.sourcePower_sharp`, `OAI.SharpPlanar.tableMomentK_eq`, `OAI.SharpPlanar.table_jet_rat` and `OAI.SharpPlanar.table_jet_sharp`; the proofs of `OAI.SharpPlanar.Bernstein0.N1_right.bound`, `OAI.SharpPlanar.Bernstein0.N1_right.bound16`, `OAI.SharpPlanar.Bernstein0.N1_right.bound17`, `OAI.SharpPlanar.Bernstein0.N1_right.bound18`, `OAI.SharpPlanar.Bernstein0.N1_right.bound19`, `OAI.SharpPlanar.Bernstein0.N1_right.bound20`, `OAI.SharpPlanar.Bernstein0.N1_right.bound21`, `OAI.SharpPlanar.Bernstein0.N1_right.bound22`, `OAI.SharpPlanar.Bernstein0.N1_right.bound23`, `OAI.SharpPlanar.Bernstein0.N1_right.bound24`, `OAI.SharpPlanar.Bernstein0.N1_right.bound25`, `OAI.SharpPlanar.Bernstein0.N1_right.bound26`, `OAI.SharpPlanar.Bernstein0.N1_right.bound27`, `OAI.SharpPlanar.Bernstein0.N1_right.bound28`, `OAI.SharpPlanar.Bernstein0.N1_right.t21_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t22_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t23_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t24_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t25_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t26_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t27_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.t28_contains`, `OAI.SharpPlanar.Bernstein0.N1_right.ts_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t10_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t8_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.t9_contains`, `OAI.SharpPlanar.Bernstein15.N0_left.ts_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t10_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t8_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.t9_contains`, `OAI.SharpPlanar.Bernstein15.N0_right.ts_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t10_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t8_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.t9_contains`, `OAI.SharpPlanar.Bernstein15.N1_left.ts_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t10_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t8_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.t9_contains`, `OAI.SharpPlanar.Bernstein15.N1_right.ts_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.bound`, `OAI.SharpPlanar.Bernstein19.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t10_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t11_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t8_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t9_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.bound`, `OAI.SharpPlanar.Bernstein19.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t10_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t11_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t8_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t9_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.bound`, `OAI.SharpPlanar.Bernstein19.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t10_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t11_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t8_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t9_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.bound`, `OAI.SharpPlanar.Bernstein19.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t10_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t11_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t8_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t9_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.bound`, `OAI.SharpPlanar.Bernstein1.N0_right.bound10`, `OAI.SharpPlanar.Bernstein1.N0_right.bound11`, `OAI.SharpPlanar.Bernstein1.N0_right.bound12`, `OAI.SharpPlanar.Bernstein1.N0_right.bound13`, `OAI.SharpPlanar.Bernstein1.N0_right.bound14`, `OAI.SharpPlanar.Bernstein1.N0_right.bound15`, `OAI.SharpPlanar.Bernstein1.N0_right.bound16`, `OAI.SharpPlanar.Bernstein1.N0_right.bound17`, `OAI.SharpPlanar.Bernstein1.N0_right.bound18`, `OAI.SharpPlanar.Bernstein1.N0_right.bound19`, `OAI.SharpPlanar.Bernstein1.N0_right.bound2`, `OAI.SharpPlanar.Bernstein1.N0_right.bound20`, `OAI.SharpPlanar.Bernstein1.N0_right.bound21`, `OAI.SharpPlanar.Bernstein1.N0_right.bound22`, `OAI.SharpPlanar.Bernstein1.N0_right.bound23`, `OAI.SharpPlanar.Bernstein1.N0_right.bound24`, `OAI.SharpPlanar.Bernstein1.N0_right.bound25`, `OAI.SharpPlanar.Bernstein1.N0_right.bound26`, `OAI.SharpPlanar.Bernstein1.N0_right.bound27`, `OAI.SharpPlanar.Bernstein1.N0_right.bound28`, `OAI.SharpPlanar.Bernstein1.N0_right.bound3`, `OAI.SharpPlanar.Bernstein1.N0_right.bound4`, `OAI.SharpPlanar.Bernstein1.N0_right.bound5`, `OAI.SharpPlanar.Bernstein1.N0_right.bound6`, `OAI.SharpPlanar.Bernstein1.N0_right.bound7`, `OAI.SharpPlanar.Bernstein1.N0_right.bound8`, `OAI.SharpPlanar.Bernstein1.N0_right.bound9`, `OAI.SharpPlanar.Bernstein1.N0_right.t14_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t16_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t17_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t18_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t19_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t20_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t21_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t22_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t23_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t24_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t25_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t26_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t27_contains`, `OAI.SharpPlanar.Bernstein1.N0_right.t28_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.bound`, `OAI.SharpPlanar.Bernstein1.N1_left.bound28`, `OAI.SharpPlanar.Bernstein1.N1_left.t13_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t15_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t16_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t17_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t18_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t19_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t20_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t21_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t22_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t23_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t24_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t25_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t26_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t27_contains`, `OAI.SharpPlanar.Bernstein1.N1_left.t28_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.bound`, `OAI.SharpPlanar.Bernstein1.N1_right.bound28`, `OAI.SharpPlanar.Bernstein1.N1_right.t13_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t15_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t16_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t17_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t18_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t19_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t20_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t21_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t22_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t23_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t24_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t25_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t26_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t27_contains`, `OAI.SharpPlanar.Bernstein1.N1_right.t28_contains`, `OAI.SharpPlanar.Bernstein21.N0_left.bound`, `OAI.SharpPlanar.Bernstein21.N0_left.bound27`, `OAI.SharpPlanar.Bernstein21.N0_left.bound28`, `OAI.SharpPlanar.Bernstein21.N0_right.bound`, `OAI.SharpPlanar.Bernstein21.N0_right.bound27`, `OAI.SharpPlanar.Bernstein21.N0_right.bound28`, `OAI.SharpPlanar.Bernstein21.N1_left.bound`, `OAI.SharpPlanar.Bernstein21.N1_left.bound27`, `OAI.SharpPlanar.Bernstein21.N1_left.bound28`, `OAI.SharpPlanar.Bernstein21.N1_right.bound`, `OAI.SharpPlanar.Bernstein21.N1_right.bound27`, `OAI.SharpPlanar.Bernstein21.N1_right.bound28`, `OAI.SharpPlanar.Bernstein27.N0_left.bound`, `OAI.SharpPlanar.Bernstein27.N0_left.bound26`, `OAI.SharpPlanar.Bernstein27.N0_left.bound27`, `OAI.SharpPlanar.Bernstein27.N0_left.bound28`, `OAI.SharpPlanar.Bernstein27.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t10_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.bound`, `OAI.SharpPlanar.Bernstein27.N0_right.bound26`, `OAI.SharpPlanar.Bernstein27.N0_right.bound27`, `OAI.SharpPlanar.Bernstein27.N0_right.bound28`, `OAI.SharpPlanar.Bernstein27.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t10_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.bound`, `OAI.SharpPlanar.Bernstein27.N1_left.bound26`, `OAI.SharpPlanar.Bernstein27.N1_left.bound27`, `OAI.SharpPlanar.Bernstein27.N1_left.bound28`, `OAI.SharpPlanar.Bernstein27.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t10_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.bound`, `OAI.SharpPlanar.Bernstein27.N1_right.bound26`, `OAI.SharpPlanar.Bernstein27.N1_right.bound27`, `OAI.SharpPlanar.Bernstein27.N1_right.bound28`, `OAI.SharpPlanar.Bernstein27.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t10_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.bound`, `OAI.SharpPlanar.Bernstein28.N0_left.bound27`, `OAI.SharpPlanar.Bernstein28.N0_left.bound28`, `OAI.SharpPlanar.Bernstein28.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.bound`, `OAI.SharpPlanar.Bernstein28.N0_right.bound27`, `OAI.SharpPlanar.Bernstein28.N0_right.bound28`, `OAI.SharpPlanar.Bernstein28.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.bound`, `OAI.SharpPlanar.Bernstein28.N1_left.bound27`, `OAI.SharpPlanar.Bernstein28.N1_left.bound28`, `OAI.SharpPlanar.Bernstein28.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.bound`, `OAI.SharpPlanar.Bernstein28.N1_right.bound27`, `OAI.SharpPlanar.Bernstein28.N1_right.bound28`, `OAI.SharpPlanar.Bernstein28.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein4.N0_left.bound`, `OAI.SharpPlanar.Bernstein4.N0_right.bound`, `OAI.SharpPlanar.Bernstein4.N1_left.bound`, `OAI.SharpPlanar.Bernstein4.N1_right.bound`, `OAI.SharpPlanar.Residual100.bound0_0`, `OAI.SharpPlanar.Residual100.bound0_1`, `OAI.SharpPlanar.Residual100.bound1_0`, `OAI.SharpPlanar.Residual100.bound1_1`, `OAI.SharpPlanar.Residual33.bound0_1`, `OAI.SharpPlanar.Residual33.bound1_1`, `OAI.SharpPlanar.Residual36.bound0_1`, `OAI.SharpPlanar.Residual36.bound1_1`, `OAI.SharpPlanar.Residual37.bound0_1`, `OAI.SharpPlanar.Residual37.bound1_1`, `OAI.SharpPlanar.Residual39.bound0_1`, `OAI.SharpPlanar.Residual39.bound1_0`, `OAI.SharpPlanar.Residual39.bound1_1`, `OAI.SharpPlanar.Residual40.bound0_0`, `OAI.SharpPlanar.Residual40.bound0_1`, `OAI.SharpPlanar.Residual40.bound1_0`, `OAI.SharpPlanar.Residual40.bound1_1`, `OAI.SharpPlanar.Residual43.bound0_0`, `OAI.SharpPlanar.Residual43.bound0_1`, `OAI.SharpPlanar.Residual43.bound1_0`, `OAI.SharpPlanar.Residual43.bound1_1`, `OAI.SharpPlanar.Residual45.bound0_0`, `OAI.SharpPlanar.Residual45.bound0_1`, `OAI.SharpPlanar.Residual45.bound1_0`, `OAI.SharpPlanar.Residual45.bound1_1`, `OAI.SharpPlanar.Residual48.bound0_0`, `OAI.SharpPlanar.Residual48.bound0_1`, `OAI.SharpPlanar.Residual48.bound1_0`, `OAI.SharpPlanar.Residual48.bound1_1`, `OAI.SharpPlanar.Residual49.bound0_0`, `OAI.SharpPlanar.Residual49.bound0_1`, `OAI.SharpPlanar.Residual49.bound1_0`, `OAI.SharpPlanar.Residual49.bound1_1`, `OAI.SharpPlanar.Residual51.bound0_0`, `OAI.SharpPlanar.Residual51.bound0_1`, `OAI.SharpPlanar.Residual51.bound1_0`, `OAI.SharpPlanar.Residual51.bound1_1`, `OAI.SharpPlanar.Residual52.bound0_0`, `OAI.SharpPlanar.Residual52.bound0_1`, `OAI.SharpPlanar.Residual52.bound1_0`, `OAI.SharpPlanar.Residual52.bound1_1`, `OAI.SharpPlanar.Residual55.bound0_0`, `OAI.SharpPlanar.Residual55.bound0_1`, `OAI.SharpPlanar.Residual55.bound1_0`, `OAI.SharpPlanar.Residual55.bound1_1`, `OAI.SharpPlanar.Residual57.bound0_0`, `OAI.SharpPlanar.Residual57.bound0_1`, `OAI.SharpPlanar.Residual57.bound1_0`, `OAI.SharpPlanar.Residual57.bound1_1`, `OAI.SharpPlanar.Residual60.bound0_0`, `OAI.SharpPlanar.Residual60.bound0_1`, `OAI.SharpPlanar.Residual60.bound1_0`, `OAI.SharpPlanar.Residual60.bound1_1`, `OAI.SharpPlanar.Residual61.bound0_0`, `OAI.SharpPlanar.Residual61.bound0_1`, `OAI.SharpPlanar.Residual61.bound1_0`, `OAI.SharpPlanar.Residual61.bound1_1`, `OAI.SharpPlanar.Residual63.bound0_0`, `OAI.SharpPlanar.Residual63.bound0_1`, `OAI.SharpPlanar.Residual63.bound1_0`, `OAI.SharpPlanar.Residual63.bound1_1`, `OAI.SharpPlanar.Residual64.bound0_0`, `OAI.SharpPlanar.Residual64.bound0_1`, `OAI.SharpPlanar.Residual64.bound1_0`, `OAI.SharpPlanar.Residual64.bound1_1`, `OAI.SharpPlanar.Residual67.bound0_0`, `OAI.SharpPlanar.Residual67.bound0_1`, `OAI.SharpPlanar.Residual67.bound1_0`, `OAI.SharpPlanar.Residual67.bound1_1`, `OAI.SharpPlanar.Residual69.bound0_0`, `OAI.SharpPlanar.Residual69.bound0_1`, `OAI.SharpPlanar.Residual69.bound1_0`, `OAI.SharpPlanar.Residual69.bound1_1`, `OAI.SharpPlanar.Residual72.bound0_0`, `OAI.SharpPlanar.Residual72.bound0_1`, `OAI.SharpPlanar.Residual72.bound1_0`, `OAI.SharpPlanar.Residual72.bound1_1`, `OAI.SharpPlanar.Residual73.bound0_0`, `OAI.SharpPlanar.Residual73.bound0_1`, `OAI.SharpPlanar.Residual73.bound1_0`, `OAI.SharpPlanar.Residual73.bound1_1`, `OAI.SharpPlanar.Residual75.bound0_0`, `OAI.SharpPlanar.Residual75.bound0_1`, `OAI.SharpPlanar.Residual75.bound1_0`, `OAI.SharpPlanar.Residual75.bound1_1`, `OAI.SharpPlanar.Residual76.bound0_0`, `OAI.SharpPlanar.Residual76.bound0_1`, `OAI.SharpPlanar.Residual76.bound1_0`, `OAI.SharpPlanar.Residual76.bound1_1`, `OAI.SharpPlanar.Residual79.bound0_0`, `OAI.SharpPlanar.Residual79.bound0_1`, `OAI.SharpPlanar.Residual79.bound1_0`, `OAI.SharpPlanar.Residual79.bound1_1`, `OAI.SharpPlanar.Residual81.bound0_0`, `OAI.SharpPlanar.Residual81.bound0_1`, `OAI.SharpPlanar.Residual81.bound1_0`, `OAI.SharpPlanar.Residual81.bound1_1`, `OAI.SharpPlanar.Residual84.bound0_0`, `OAI.SharpPlanar.Residual84.bound0_1`, `OAI.SharpPlanar.Residual84.bound1_0`, `OAI.SharpPlanar.Residual84.bound1_1`, `OAI.SharpPlanar.Residual85.bound0_0`, `OAI.SharpPlanar.Residual85.bound0_1`, `OAI.SharpPlanar.Residual85.bound1_0`, `OAI.SharpPlanar.Residual85.bound1_1`, `OAI.SharpPlanar.Residual87.bound0_0`, `OAI.SharpPlanar.Residual87.bound0_1`, `OAI.SharpPlanar.Residual87.bound1_0`, `OAI.SharpPlanar.Residual87.bound1_1`, `OAI.SharpPlanar.Residual88.bound0_0`, `OAI.SharpPlanar.Residual88.bound0_1`, `OAI.SharpPlanar.Residual88.bound1_0`, `OAI.SharpPlanar.Residual88.bound1_1`, `OAI.SharpPlanar.Residual91.bound0_0`, `OAI.SharpPlanar.Residual91.bound0_1`, `OAI.SharpPlanar.Residual91.bound1_0`, `OAI.SharpPlanar.Residual91.bound1_1`, `OAI.SharpPlanar.Residual93.bound0_0`, `OAI.SharpPlanar.Residual93.bound0_1`, `OAI.SharpPlanar.Residual93.bound1_0`, `OAI.SharpPlanar.Residual93.bound1_1`, `OAI.SharpPlanar.Residual96.bound0_0`, `OAI.SharpPlanar.Residual96.bound0_1`, `OAI.SharpPlanar.Residual96.bound1_0`, `OAI.SharpPlanar.Residual96.bound1_1`, `OAI.SharpPlanar.Residual97.bound0_0`, `OAI.SharpPlanar.Residual97.bound0_1`, `OAI.SharpPlanar.Residual97.bound1_0`, `OAI.SharpPlanar.Residual97.bound1_1`, `OAI.SharpPlanar.Residual99.bound0_0`, `OAI.SharpPlanar.Residual99.bound0_1`, `OAI.SharpPlanar.Residual99.bound1_0`, `OAI.SharpPlanar.Residual99.bound1_1`, `OAI.SharpPlanar.bernsteinBox_contains`, `OAI.SharpPlanar.fullFactor_step_contains`, `OAI.SharpPlanar.fullMoment_direct`, `OAI.SharpPlanar.fullMoment_transformed_bound`, `OAI.SharpPlanar.normalizedH_table`, `OAI.SharpPlanar.residual_finite_exterior_0`, `OAI.SharpPlanar.residual_finite_exterior_1`, `OAI.SharpPlanar.sourcePower_of_cap`, `OAI.SharpPlanar.sourcePower_sharp`, `OAI.SharpPlanar.tableMomentK_eq`, `OAI.SharpPlanar.table_jet_rat` and `OAI.SharpPlanar.table_jet_sharp`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D004
import Definitions.Def_OAIQ098D005

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

instance instDecidableMulCheck (a b c : RBox) : Decidable (a.MulCheck b c) := inferInstanceAs (Decidable (_ ∧ _))

end IntegerIntervals
end SharpPlanar

end OAI
end

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

noncomputable def tableMomentRule (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceRule (fun t => tableDensity a j.val t * complexTransformedFactor m 1 ell t) j.val
noncomputable def tableMomentIntegral (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceIntegral (fun t => tableDensity a j.val t * complexTransformedFactor m 1 ell t) j.val
noncomputable def tableMomentAtom (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ((tableConstant a:ℝ):ℂ) * ∑ j : Fin 7,
    (if j.val=0 then 1 else 2) * Pcoeff j.val *
      complexTransformedFactor m 1 ell ((j.val:ℝ)/6)
noncomputable def tableMomentK (a : Bool) (m : ℝ) (ell : ℕ) : ℝ :=
  (tableMomentAtom a m ell + tableMomentIntegral a m ell).re

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval enclosures for direct and transformed moments of arbitrary order -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def fullFactor (tr : Bool) (m : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  if tr then complexTransformedFactor m 1 ell t else complexDirectFactor m 1 ell t
noncomputable def fullMomentRule (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceRule (fun t => tableDensity a j.val t*fullFactor tr m ell t) j.val
noncomputable def fullMomentIntegral (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceIntegral (fun t => tableDensity a j.val t*fullFactor tr m ell t) j.val
noncomputable def fullMomentAtom (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ((tableConstant a:ℝ):ℂ)*∑ j : Fin 7,
    (if j.val=0 then 1 else 2)*Pcoeff j.val*fullFactor tr m ell ((j.val:ℝ)/6)
noncomputable def fullMoment (a tr : Bool) (m : ℝ) (ell : ℕ) : ℝ :=
  (fullMomentAtom a tr m ell+fullMomentIntegral a tr m ell).re
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BernsteinBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
open scoped BigOperators
noncomputable def normalizedH (a : Bool) (m : ℝ) (ell : ℕ) : ℝ :=
  fullMoment a false m ell+fullMoment (!a) true m ell
noncomputable def sourcePower (a : Bool) (m y : ℝ) (nu r : ℕ) : ℝ :=
  (if a then 1 else -1)*y^r*normalizedH a m (r+nu)
def bernsteinBox (T : Fin 29 → RBox) (k : Fin 29) : RBox :=
  sumBox (fun r : Fin (k.val+1) => (T ⟨r.val,by omega⟩).scale (k.val.choose r.val) ((28).choose r.val))
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ContactData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contact data for cardinal interpolation

The prescribed contacts and their Gaussian transforms give summable right hand sides for the interpolation equations.
-/

namespace SharpPlanar
noncomputable def transformedJets (p : CardinalData) (ni : Node×Bool) : ℝ :=
  if ni.2 then (D ni.1.val*K p 0 ni.1.val-K p 1 ni.1.val)/Q ni.1.val
  else -K p 0 ni.1.val/Q ni.1.val
lemma transformedJets_bound (p : CardinalData) (ni : Node×Bool) :
    |transformedJets p ni| ≤ allNodeWeight*dataMass p*
      (kernelEnvelope 0 ni.1.val+kernelEnvelope 1 ni.1.val) := by
  have he0 := kernelEnvelope_nonneg 0 (ni.1.val:ℝ)
  have he1 := kernelEnvelope_nonneg 1 (ni.1.val:ℝ)
  have hd := dataMass_nonneg p
  have hq := Q_pos ni.1.val
  have h0 := K_bound p 0 (Nat.cast_nonneg ni.1.val)
  have h1 := K_bound p 1 (Nat.cast_nonneg ni.1.val)
  change |K p 0 ni.1.val| ≤ dataMass p*kernelEnvelope 0 ni.1.val at h0
  change |K p 1 ni.1.val| ≤ dataMass p*kernelEnvelope 1 ni.1.val at h1
  have hlocal : |transformedJets p ni| ≤ nodeWeight ni.1.val*dataMass p*
      (kernelEnvelope 0 ni.1.val+kernelEnvelope 1 ni.1.val) := by
    unfold transformedJets nodeWeight
    split
    · rw [abs_div,abs_of_pos hq]
      calc
        _ ≤ (|D ni.1.val| *|K p 0 ni.1.val|+|K p 1 ni.1.val|)/Q ni.1.val := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact (abs_sub _ _).trans (by rw [abs_mul])
        _ ≤ (|D ni.1.val| *(dataMass p*kernelEnvelope 0 ni.1.val)+dataMass p*kernelEnvelope 1 ni.1.val)/Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val)) (mul_nonneg hd he1),mul_nonneg hd he0]
    · rw [abs_div,abs_neg,abs_of_pos hq]
      calc
        _ ≤ (dataMass p*kernelEnvelope 0 ni.1.val)/Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val)) (mul_nonneg hd (add_nonneg he0 he1)),mul_nonneg hd he1]
  exact hlocal.trans (by gcongr; exact nodeWeight_le ni.1)
lemma transformedJets_summable (p : CardinalData) : Summable (fun ni => |transformedJets p ni|) := by
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun ni => transformedJets_bound p ni)
    (pairEnvelope_summable.mul_left _)
noncomputable def transformedJetList (p : CardinalData) : X :=
  ⟨transformedJets p,memℓp_gen (by simpa using transformedJets_summable p)⟩
noncomputable def g₁ : X := transformedJetList (fixed₂ 0)-contactList
noncomputable def g₂ : X := transformedJetList (fixed₁ 0)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert73
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

namespace SharpPlanar.Numerical.U73
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U73

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert75
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

namespace SharpPlanar.Numerical.U75
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U75

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert76
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

namespace SharpPlanar.Numerical.U76
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U76

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert79
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

namespace SharpPlanar.Numerical.U79
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U79

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert81
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

namespace SharpPlanar.Numerical.U81
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U81

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert85
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

namespace SharpPlanar.Numerical.U85
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U85

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert87
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

namespace SharpPlanar.Numerical.U87
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U87

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert88
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

namespace SharpPlanar.Numerical.U88
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U88

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert93
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

namespace SharpPlanar.Numerical.U93
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U93

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert96
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

namespace SharpPlanar.Numerical.U96
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U96

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert97
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

namespace SharpPlanar.Numerical.U97
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U97

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert99
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

namespace SharpPlanar.Numerical.U99
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U99

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ResidualBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residuals of the cardinal interpolation equations

The finite coefficient families have small residuals in the exact interpolation equations.
-/

namespace SharpPlanar
open Numerical IntegerIntervals
noncomputable def tableResidual (a : Bool) : X :=
  if a then tableList true-S (tableList false)-g₂
  else tableList false-S (tableList true)-g₁
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual1
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

namespace SharpPlanar.Residual1
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-670689128) 10000000000).add ((tm1_1_0.realAnswer).mul (qiBox 1))
noncomputable def box0_1 : RBox := (RBox.rat (3601371201) 10000000000).add ((tm1_1_1.realAnswer.add (((dBox 1).mul tm1_1_0.realAnswer).neg)).mul (qiBox 1))
noncomputable def box1_0 : RBox := (RBox.rat (-250018302) 10000000000).add ((tm0_1_0.realAnswer).mul (qiBox 1))
noncomputable def box1_1 : RBox := (RBox.rat (4107732082) 10000000000).add ((tm0_1_1.realAnswer.add (((dBox 1).mul tm0_1_0.realAnswer).neg)).mul (qiBox 1))
end SharpPlanar.Residual1

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual100
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

namespace SharpPlanar.Residual100
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (0) 10000000000).add ((tm1_100_0.realAnswer).mul (qiBox 100))
noncomputable def box0_1 : RBox := (RBox.rat (2) 10000000000).add ((tm1_100_1.realAnswer.add (((dBox 100).mul tm1_100_0.realAnswer).neg)).mul (qiBox 100))
noncomputable def box1_0 : RBox := (RBox.rat (0) 10000000000).add ((tm0_100_0.realAnswer).mul (qiBox 100))
noncomputable def box1_1 : RBox := (RBox.rat (-2) 10000000000).add ((tm0_100_1.realAnswer.add (((dBox 100).mul tm0_100_0.realAnswer).neg)).mul (qiBox 100))
end SharpPlanar.Residual100

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual12
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

namespace SharpPlanar.Residual12
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (3646952) 10000000000).add ((tm1_12_0.realAnswer).mul (qiBox 12))
noncomputable def box0_1 : RBox := (RBox.rat (-34846939) 10000000000).add ((tm1_12_1.realAnswer.add (((dBox 12).mul tm1_12_0.realAnswer).neg)).mul (qiBox 12))
noncomputable def box1_0 : RBox := (RBox.rat (-6005382) 10000000000).add ((tm0_12_0.realAnswer).mul (qiBox 12))
noncomputable def box1_1 : RBox := (RBox.rat (34369042) 10000000000).add ((tm0_12_1.realAnswer.add (((dBox 12).mul tm0_12_0.realAnswer).neg)).mul (qiBox 12))
end SharpPlanar.Residual12

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual13
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

namespace SharpPlanar.Residual13
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (3183411) 10000000000).add ((tm1_13_0.realAnswer).mul (qiBox 13))
noncomputable def box0_1 : RBox := (RBox.rat (63030995) 10000000000).add ((tm1_13_1.realAnswer.add (((dBox 13).mul tm1_13_0.realAnswer).neg)).mul (qiBox 13))
noncomputable def box1_0 : RBox := (RBox.rat (-574123) 10000000000).add ((tm0_13_0.realAnswer).mul (qiBox 13))
noncomputable def box1_1 : RBox := (RBox.rat (-75237042) 10000000000).add ((tm0_13_1.realAnswer.add (((dBox 13).mul tm0_13_0.realAnswer).neg)).mul (qiBox 13))
end SharpPlanar.Residual13

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual15
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

namespace SharpPlanar.Residual15
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (11390977) 10000000000).add ((tm1_15_0.realAnswer).mul (qiBox 15))
noncomputable def box0_1 : RBox := (RBox.rat (27049982) 10000000000).add ((tm1_15_1.realAnswer.add (((dBox 15).mul tm1_15_0.realAnswer).neg)).mul (qiBox 15))
noncomputable def box1_0 : RBox := (RBox.rat (-11312377) 10000000000).add ((tm0_15_0.realAnswer).mul (qiBox 15))
noncomputable def box1_1 : RBox := (RBox.rat (-34985096) 10000000000).add ((tm0_15_1.realAnswer.add (((dBox 15).mul tm0_15_0.realAnswer).neg)).mul (qiBox 15))
end SharpPlanar.Residual15

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual16
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

namespace SharpPlanar.Residual16
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-5593246) 10000000000).add ((tm1_16_0.realAnswer).mul (qiBox 16))
noncomputable def box0_1 : RBox := (RBox.rat (13405071) 10000000000).add ((tm1_16_1.realAnswer.add (((dBox 16).mul tm1_16_0.realAnswer).neg)).mul (qiBox 16))
noncomputable def box1_0 : RBox := (RBox.rat (5915710) 10000000000).add ((tm0_16_0.realAnswer).mul (qiBox 16))
noncomputable def box1_1 : RBox := (RBox.rat (-10980954) 10000000000).add ((tm0_16_1.realAnswer.add (((dBox 16).mul tm0_16_0.realAnswer).neg)).mul (qiBox 16))
end SharpPlanar.Residual16

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual19
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

namespace SharpPlanar.Residual19
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (54905) 10000000000).add ((tm1_19_0.realAnswer).mul (qiBox 19))
noncomputable def box0_1 : RBox := (RBox.rat (-1515007) 10000000000).add ((tm1_19_1.realAnswer.add (((dBox 19).mul tm1_19_0.realAnswer).neg)).mul (qiBox 19))
noncomputable def box1_0 : RBox := (RBox.rat (-120136) 10000000000).add ((tm0_19_0.realAnswer).mul (qiBox 19))
noncomputable def box1_1 : RBox := (RBox.rat (1498351) 10000000000).add ((tm0_19_1.realAnswer.add (((dBox 19).mul tm0_19_0.realAnswer).neg)).mul (qiBox 19))
end SharpPlanar.Residual19

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual21
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

namespace SharpPlanar.Residual21
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-210208) 10000000000).add ((tm1_21_0.realAnswer).mul (qiBox 21))
noncomputable def box0_1 : RBox := (RBox.rat (-634307) 10000000000).add ((tm1_21_1.realAnswer.add (((dBox 21).mul tm1_21_0.realAnswer).neg)).mul (qiBox 21))
noncomputable def box1_0 : RBox := (RBox.rat (177992) 10000000000).add ((tm0_21_0.realAnswer).mul (qiBox 21))
noncomputable def box1_1 : RBox := (RBox.rat (747946) 10000000000).add ((tm0_21_1.realAnswer.add (((dBox 21).mul tm0_21_0.realAnswer).neg)).mul (qiBox 21))
end SharpPlanar.Residual21

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual24
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

namespace SharpPlanar.Residual24
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (976077) 10000000000).add ((tm1_24_0.realAnswer).mul (qiBox 24))
noncomputable def box0_1 : RBox := (RBox.rat (-804949) 10000000000).add ((tm1_24_1.realAnswer.add (((dBox 24).mul tm1_24_0.realAnswer).neg)).mul (qiBox 24))
noncomputable def box1_0 : RBox := (RBox.rat (-1037705) 10000000000).add ((tm0_24_0.realAnswer).mul (qiBox 24))
noncomputable def box1_1 : RBox := (RBox.rat (105643) 10000000000).add ((tm0_24_1.realAnswer.add (((dBox 24).mul tm0_24_0.realAnswer).neg)).mul (qiBox 24))
end SharpPlanar.Residual24

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual25
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

namespace SharpPlanar.Residual25
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-824472) 10000000000).add ((tm1_25_0.realAnswer).mul (qiBox 25))
noncomputable def box0_1 : RBox := (RBox.rat (7003719) 10000000000).add ((tm1_25_1.realAnswer.add (((dBox 25).mul tm1_25_0.realAnswer).neg)).mul (qiBox 25))
noncomputable def box1_0 : RBox := (RBox.rat (1011732) 10000000000).add ((tm0_25_0.realAnswer).mul (qiBox 25))
noncomputable def box1_1 : RBox := (RBox.rat (-6510015) 10000000000).add ((tm0_25_1.realAnswer.add (((dBox 25).mul tm0_25_0.realAnswer).neg)).mul (qiBox 25))
end SharpPlanar.Residual25

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual27
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

namespace SharpPlanar.Residual27
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (611891) 10000000000).add ((tm1_27_0.realAnswer).mul (qiBox 27))
noncomputable def box0_1 : RBox := (RBox.rat (4536095) 10000000000).add ((tm1_27_1.realAnswer.add (((dBox 27).mul tm1_27_0.realAnswer).neg)).mul (qiBox 27))
noncomputable def box1_0 : RBox := (RBox.rat (-428528) 10000000000).add ((tm0_27_0.realAnswer).mul (qiBox 27))
noncomputable def box1_1 : RBox := (RBox.rat (-4440927) 10000000000).add ((tm0_27_1.realAnswer.add (((dBox 27).mul tm0_27_0.realAnswer).neg)).mul (qiBox 27))
end SharpPlanar.Residual27

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual28
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

namespace SharpPlanar.Residual28
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-472882) 10000000000).add ((tm1_28_0.realAnswer).mul (qiBox 28))
noncomputable def box0_1 : RBox := (RBox.rat (-107613) 10000000000).add ((tm1_28_1.realAnswer.add (((dBox 28).mul tm1_28_0.realAnswer).neg)).mul (qiBox 28))
noncomputable def box1_0 : RBox := (RBox.rat (399655) 10000000000).add ((tm0_28_0.realAnswer).mul (qiBox 28))
noncomputable def box1_1 : RBox := (RBox.rat (403751) 10000000000).add ((tm0_28_1.realAnswer.add (((dBox 28).mul tm0_28_0.realAnswer).neg)).mul (qiBox 28))
end SharpPlanar.Residual28

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual3
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

namespace SharpPlanar.Residual3
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (93524468) 10000000000).add ((tm1_3_0.realAnswer).mul (qiBox 3))
noncomputable def box0_1 : RBox := (RBox.rat (564897270) 10000000000).add ((tm1_3_1.realAnswer.add (((dBox 3).mul tm1_3_0.realAnswer).neg)).mul (qiBox 3))
noncomputable def box1_0 : RBox := (RBox.rat (-186215974) 10000000000).add ((tm0_3_0.realAnswer).mul (qiBox 3))
noncomputable def box1_1 : RBox := (RBox.rat (-65204793) 10000000000).add ((tm0_3_1.realAnswer.add (((dBox 3).mul tm0_3_0.realAnswer).neg)).mul (qiBox 3))
end SharpPlanar.Residual3

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual31
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

namespace SharpPlanar.Residual31
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (30744) 10000000000).add ((tm1_31_0.realAnswer).mul (qiBox 31))
noncomputable def box0_1 : RBox := (RBox.rat (-112653) 10000000000).add ((tm1_31_1.realAnswer.add (((dBox 31).mul tm1_31_0.realAnswer).neg)).mul (qiBox 31))
noncomputable def box1_0 : RBox := (RBox.rat (-31773) 10000000000).add ((tm0_31_0.realAnswer).mul (qiBox 31))
noncomputable def box1_1 : RBox := (RBox.rat (90515) 10000000000).add ((tm0_31_1.realAnswer.add (((dBox 31).mul tm0_31_0.realAnswer).neg)).mul (qiBox 31))
end SharpPlanar.Residual31

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual33
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

namespace SharpPlanar.Residual33
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-4974) 10000000000).add ((tm1_33_0.realAnswer).mul (qiBox 33))
noncomputable def box0_1 : RBox := (RBox.rat (-105568) 10000000000).add ((tm1_33_1.realAnswer.add (((dBox 33).mul tm1_33_0.realAnswer).neg)).mul (qiBox 33))
noncomputable def box1_0 : RBox := (RBox.rat (1240) 10000000000).add ((tm0_33_0.realAnswer).mul (qiBox 33))
noncomputable def box1_1 : RBox := (RBox.rat (99081) 10000000000).add ((tm0_33_1.realAnswer.add (((dBox 33).mul tm0_33_0.realAnswer).neg)).mul (qiBox 33))
end SharpPlanar.Residual33

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual36
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

namespace SharpPlanar.Residual36
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (128313) 10000000000).add ((tm1_36_0.realAnswer).mul (qiBox 36))
noncomputable def box0_1 : RBox := (RBox.rat (246018) 10000000000).add ((tm1_36_1.realAnswer.add (((dBox 36).mul tm1_36_0.realAnswer).neg)).mul (qiBox 36))
noncomputable def box1_0 : RBox := (RBox.rat (-114876) 10000000000).add ((tm0_36_0.realAnswer).mul (qiBox 36))
noncomputable def box1_1 : RBox := (RBox.rat (-267388) 10000000000).add ((tm0_36_1.realAnswer.add (((dBox 36).mul tm0_36_0.realAnswer).neg)).mul (qiBox 36))
end SharpPlanar.Residual36

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual37
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

namespace SharpPlanar.Residual37
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-176685) 10000000000).add ((tm1_37_0.realAnswer).mul (qiBox 37))
noncomputable def box0_1 : RBox := (RBox.rat (505187) 10000000000).add ((tm1_37_1.realAnswer.add (((dBox 37).mul tm1_37_0.realAnswer).neg)).mul (qiBox 37))
noncomputable def box1_0 : RBox := (RBox.rat (166591) 10000000000).add ((tm0_37_0.realAnswer).mul (qiBox 37))
noncomputable def box1_1 : RBox := (RBox.rat (-396209) 10000000000).add ((tm0_37_1.realAnswer.add (((dBox 37).mul tm0_37_0.realAnswer).neg)).mul (qiBox 37))
end SharpPlanar.Residual37

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual39
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

namespace SharpPlanar.Residual39
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-21638) 10000000000).add ((tm1_39_0.realAnswer).mul (qiBox 39))
noncomputable def box0_1 : RBox := (RBox.rat (472037) 10000000000).add ((tm1_39_1.realAnswer.add (((dBox 39).mul tm1_39_0.realAnswer).neg)).mul (qiBox 39))
noncomputable def box1_0 : RBox := (RBox.rat (32128) 10000000000).add ((tm0_39_0.realAnswer).mul (qiBox 39))
noncomputable def box1_1 : RBox := (RBox.rat (-402283) 10000000000).add ((tm0_39_1.realAnswer.add (((dBox 39).mul tm0_39_0.realAnswer).neg)).mul (qiBox 39))
end SharpPlanar.Residual39

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual4
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

namespace SharpPlanar.Residual4
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-64146977) 10000000000).add ((tm1_4_0.realAnswer).mul (qiBox 4))
noncomputable def box0_1 : RBox := (RBox.rat (121133118) 10000000000).add ((tm1_4_1.realAnswer.add (((dBox 4).mul tm1_4_0.realAnswer).neg)).mul (qiBox 4))
noncomputable def box1_0 : RBox := (RBox.rat (82882809) 10000000000).add ((tm0_4_0.realAnswer).mul (qiBox 4))
noncomputable def box1_1 : RBox := (RBox.rat (-327822296) 10000000000).add ((tm0_4_1.realAnswer.add (((dBox 4).mul tm0_4_0.realAnswer).neg)).mul (qiBox 4))
end SharpPlanar.Residual4

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual40
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

namespace SharpPlanar.Residual40
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-18461) 10000000000).add ((tm1_40_0.realAnswer).mul (qiBox 40))
noncomputable def box0_1 : RBox := (RBox.rat (-165597) 10000000000).add ((tm1_40_1.realAnswer.add (((dBox 40).mul tm1_40_0.realAnswer).neg)).mul (qiBox 40))
noncomputable def box1_0 : RBox := (RBox.rat (10836) 10000000000).add ((tm0_40_0.realAnswer).mul (qiBox 40))
noncomputable def box1_1 : RBox := (RBox.rat (164974) 10000000000).add ((tm0_40_1.realAnswer.add (((dBox 40).mul tm0_40_0.realAnswer).neg)).mul (qiBox 40))
end SharpPlanar.Residual40

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual43
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

namespace SharpPlanar.Residual43
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (4565) 10000000000).add ((tm1_43_0.realAnswer).mul (qiBox 43))
noncomputable def box0_1 : RBox := (RBox.rat (-2296) 10000000000).add ((tm1_43_1.realAnswer.add (((dBox 43).mul tm1_43_0.realAnswer).neg)).mul (qiBox 43))
noncomputable def box1_0 : RBox := (RBox.rat (-4050) 10000000000).add ((tm0_43_0.realAnswer).mul (qiBox 43))
noncomputable def box1_1 : RBox := (RBox.rat (547) 10000000000).add ((tm0_43_1.realAnswer.add (((dBox 43).mul tm0_43_0.realAnswer).neg)).mul (qiBox 43))
end SharpPlanar.Residual43

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual45
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

namespace SharpPlanar.Residual45
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (1477) 10000000000).add ((tm1_45_0.realAnswer).mul (qiBox 45))
noncomputable def box0_1 : RBox := (RBox.rat (-10734) 10000000000).add ((tm1_45_1.realAnswer.add (((dBox 45).mul tm1_45_0.realAnswer).neg)).mul (qiBox 45))
noncomputable def box1_0 : RBox := (RBox.rat (-1524) 10000000000).add ((tm0_45_0.realAnswer).mul (qiBox 45))
noncomputable def box1_1 : RBox := (RBox.rat (8978) 10000000000).add ((tm0_45_1.realAnswer.add (((dBox 45).mul tm0_45_0.realAnswer).neg)).mul (qiBox 45))
end SharpPlanar.Residual45

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual48
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

namespace SharpPlanar.Residual48
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (10748) 10000000000).add ((tm1_48_0.realAnswer).mul (qiBox 48))
noncomputable def box0_1 : RBox := (RBox.rat (50050) 10000000000).add ((tm1_48_1.realAnswer.add (((dBox 48).mul tm1_48_0.realAnswer).neg)).mul (qiBox 48))
noncomputable def box1_0 : RBox := (RBox.rat (-8611) 10000000000).add ((tm0_48_0.realAnswer).mul (qiBox 48))
noncomputable def box1_1 : RBox := (RBox.rat (-45048) 10000000000).add ((tm0_48_1.realAnswer.add (((dBox 48).mul tm0_48_0.realAnswer).neg)).mul (qiBox 48))
end SharpPlanar.Residual48

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual49
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

namespace SharpPlanar.Residual49
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-20506) 10000000000).add ((tm1_49_0.realAnswer).mul (qiBox 49))
noncomputable def box0_1 : RBox := (RBox.rat (7495) 10000000000).add ((tm1_49_1.realAnswer.add (((dBox 49).mul tm1_49_0.realAnswer).neg)).mul (qiBox 49))
noncomputable def box1_0 : RBox := (RBox.rat (17354) 10000000000).add ((tm0_49_0.realAnswer).mul (qiBox 49))
noncomputable def box1_1 : RBox := (RBox.rat (-266) 10000000000).add ((tm0_49_1.realAnswer.add (((dBox 49).mul tm0_49_0.realAnswer).neg)).mul (qiBox 49))
end SharpPlanar.Residual49

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual51
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

namespace SharpPlanar.Residual51
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-10361) 10000000000).add ((tm1_51_0.realAnswer).mul (qiBox 51))
noncomputable def box0_1 : RBox := (RBox.rat (29035) 10000000000).add ((tm1_51_1.realAnswer.add (((dBox 51).mul tm1_51_0.realAnswer).neg)).mul (qiBox 51))
noncomputable def box1_0 : RBox := (RBox.rat (9641) 10000000000).add ((tm0_51_0.realAnswer).mul (qiBox 51))
noncomputable def box1_1 : RBox := (RBox.rat (-21534) 10000000000).add ((tm0_51_1.realAnswer.add (((dBox 51).mul tm0_51_0.realAnswer).neg)).mul (qiBox 51))
end SharpPlanar.Residual51

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual52
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

namespace SharpPlanar.Residual52
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (2121) 10000000000).add ((tm1_52_0.realAnswer).mul (qiBox 52))
noncomputable def box0_1 : RBox := (RBox.rat (-26523) 10000000000).add ((tm1_52_1.realAnswer.add (((dBox 52).mul tm1_52_0.realAnswer).neg)).mul (qiBox 52))
noncomputable def box1_0 : RBox := (RBox.rat (-2269) 10000000000).add ((tm0_52_0.realAnswer).mul (qiBox 52))
noncomputable def box1_1 : RBox := (RBox.rat (23159) 10000000000).add ((tm0_52_1.realAnswer.add (((dBox 52).mul tm0_52_0.realAnswer).neg)).mul (qiBox 52))
end SharpPlanar.Residual52

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual55
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

namespace SharpPlanar.Residual55
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (425) 10000000000).add ((tm1_55_0.realAnswer).mul (qiBox 55))
noncomputable def box0_1 : RBox := (RBox.rat (858) 10000000000).add ((tm1_55_1.realAnswer.add (((dBox 55).mul tm1_55_0.realAnswer).neg)).mul (qiBox 55))
noncomputable def box1_0 : RBox := (RBox.rat (-344) 10000000000).add ((tm0_55_0.realAnswer).mul (qiBox 55))
noncomputable def box1_1 : RBox := (RBox.rat (-839) 10000000000).add ((tm0_55_1.realAnswer.add (((dBox 55).mul tm0_55_0.realAnswer).neg)).mul (qiBox 55))
end SharpPlanar.Residual55

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual57
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

namespace SharpPlanar.Residual57
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (302) 10000000000).add ((tm1_57_0.realAnswer).mul (qiBox 57))
noncomputable def box0_1 : RBox := (RBox.rat (-632) 10000000000).add ((tm1_57_1.realAnswer.add (((dBox 57).mul tm1_57_0.realAnswer).neg)).mul (qiBox 57))
noncomputable def box1_0 : RBox := (RBox.rat (-266) 10000000000).add ((tm0_57_0.realAnswer).mul (qiBox 57))
noncomputable def box1_1 : RBox := (RBox.rat (463) 10000000000).add ((tm0_57_1.realAnswer.add (((dBox 57).mul tm0_57_0.realAnswer).neg)).mul (qiBox 57))
end SharpPlanar.Residual57

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual60
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

namespace SharpPlanar.Residual60
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (382) 10000000000).add ((tm1_60_0.realAnswer).mul (qiBox 60))
noncomputable def box0_1 : RBox := (RBox.rat (5658) 10000000000).add ((tm1_60_1.realAnswer.add (((dBox 60).mul tm1_60_0.realAnswer).neg)).mul (qiBox 60))
noncomputable def box1_0 : RBox := (RBox.rat (-231) 10000000000).add ((tm0_60_0.realAnswer).mul (qiBox 60))
noncomputable def box1_1 : RBox := (RBox.rat (-4688) 10000000000).add ((tm0_60_1.realAnswer.add (((dBox 60).mul tm0_60_0.realAnswer).neg)).mul (qiBox 60))
end SharpPlanar.Residual60

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual61
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

namespace SharpPlanar.Residual61
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-1481) 10000000000).add ((tm1_61_0.realAnswer).mul (qiBox 61))
noncomputable def box0_1 : RBox := (RBox.rat (-4320) 10000000000).add ((tm1_61_1.realAnswer.add (((dBox 61).mul tm1_61_0.realAnswer).neg)).mul (qiBox 61))
noncomputable def box1_0 : RBox := (RBox.rat (1140) 10000000000).add ((tm0_61_0.realAnswer).mul (qiBox 61))
noncomputable def box1_1 : RBox := (RBox.rat (4098) 10000000000).add ((tm0_61_1.realAnswer.add (((dBox 61).mul tm0_61_0.realAnswer).neg)).mul (qiBox 61))
end SharpPlanar.Residual61

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual63
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

namespace SharpPlanar.Residual63
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-1494) 10000000000).add ((tm1_63_0.realAnswer).mul (qiBox 63))
noncomputable def box0_1 : RBox := (RBox.rat (-352) 10000000000).add ((tm1_63_1.realAnswer.add (((dBox 63).mul tm1_63_0.realAnswer).neg)).mul (qiBox 63))
noncomputable def box1_0 : RBox := (RBox.rat (1265) 10000000000).add ((tm0_63_0.realAnswer).mul (qiBox 63))
noncomputable def box1_1 : RBox := (RBox.rat (647) 10000000000).add ((tm0_63_1.realAnswer.add (((dBox 63).mul tm0_63_0.realAnswer).neg)).mul (qiBox 63))
end SharpPlanar.Residual63

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual64
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

namespace SharpPlanar.Residual64
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (558) 10000000000).add ((tm1_64_0.realAnswer).mul (qiBox 64))
noncomputable def box0_1 : RBox := (RBox.rat (-2609) 10000000000).add ((tm1_64_1.realAnswer.add (((dBox 64).mul tm1_64_0.realAnswer).neg)).mul (qiBox 64))
noncomputable def box1_0 : RBox := (RBox.rat (-491) 10000000000).add ((tm0_64_0.realAnswer).mul (qiBox 64))
noncomputable def box1_1 : RBox := (RBox.rat (2114) 10000000000).add ((tm0_64_1.realAnswer.add (((dBox 64).mul tm0_64_0.realAnswer).neg)).mul (qiBox 64))
end SharpPlanar.Residual64

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual67
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

namespace SharpPlanar.Residual67
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (21) 10000000000).add ((tm1_67_0.realAnswer).mul (qiBox 67))
noncomputable def box0_1 : RBox := (RBox.rat (169) 10000000000).add ((tm1_67_1.realAnswer.add (((dBox 67).mul tm1_67_0.realAnswer).neg)).mul (qiBox 67))
noncomputable def box1_0 : RBox := (RBox.rat (-14) 10000000000).add ((tm0_67_0.realAnswer).mul (qiBox 67))
noncomputable def box1_1 : RBox := (RBox.rat (-145) 10000000000).add ((tm0_67_1.realAnswer.add (((dBox 67).mul tm0_67_0.realAnswer).neg)).mul (qiBox 67))
end SharpPlanar.Residual67

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual69
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

namespace SharpPlanar.Residual69
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (34) 10000000000).add ((tm1_69_0.realAnswer).mul (qiBox 69))
noncomputable def box0_1 : RBox := (RBox.rat (13) 10000000000).add ((tm1_69_1.realAnswer.add (((dBox 69).mul tm1_69_0.realAnswer).neg)).mul (qiBox 69))
noncomputable def box1_0 : RBox := (RBox.rat (-28) 10000000000).add ((tm0_69_0.realAnswer).mul (qiBox 69))
noncomputable def box1_1 : RBox := (RBox.rat (-18) 10000000000).add ((tm0_69_1.realAnswer.add (((dBox 69).mul tm0_69_0.realAnswer).neg)).mul (qiBox 69))
end SharpPlanar.Residual69

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual7
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

namespace SharpPlanar.Residual7
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-1358193) 10000000000).add ((tm1_7_0.realAnswer).mul (qiBox 7))
noncomputable def box0_1 : RBox := (RBox.rat (-16329465) 10000000000).add ((tm1_7_1.realAnswer.add (((dBox 7).mul tm1_7_0.realAnswer).neg)).mul (qiBox 7))
noncomputable def box1_0 : RBox := (RBox.rat (1979670) 10000000000).add ((tm0_7_0.realAnswer).mul (qiBox 7))
noncomputable def box1_1 : RBox := (RBox.rat (21637038) 10000000000).add ((tm0_7_1.realAnswer.add (((dBox 7).mul tm0_7_0.realAnswer).neg)).mul (qiBox 7))
end SharpPlanar.Residual7

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual72
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

namespace SharpPlanar.Residual72
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-55) 10000000000).add ((tm1_72_0.realAnswer).mul (qiBox 72))
noncomputable def box0_1 : RBox := (RBox.rat (394) 10000000000).add ((tm1_72_1.realAnswer.add (((dBox 72).mul tm1_72_0.realAnswer).neg)).mul (qiBox 72))
noncomputable def box1_0 : RBox := (RBox.rat (53) 10000000000).add ((tm0_72_0.realAnswer).mul (qiBox 72))
noncomputable def box1_1 : RBox := (RBox.rat (-301) 10000000000).add ((tm0_72_1.realAnswer.add (((dBox 72).mul tm0_72_0.realAnswer).neg)).mul (qiBox 72))
end SharpPlanar.Residual72

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual73
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

namespace SharpPlanar.Residual73
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-21) 10000000000).add ((tm1_73_0.realAnswer).mul (qiBox 73))
noncomputable def box0_1 : RBox := (RBox.rat (-805) 10000000000).add ((tm1_73_1.realAnswer.add (((dBox 73).mul tm1_73_0.realAnswer).neg)).mul (qiBox 73))
noncomputable def box1_0 : RBox := (RBox.rat (5) 10000000000).add ((tm0_73_0.realAnswer).mul (qiBox 73))
noncomputable def box1_1 : RBox := (RBox.rat (685) 10000000000).add ((tm0_73_1.realAnswer.add (((dBox 73).mul tm0_73_0.realAnswer).neg)).mul (qiBox 73))
end SharpPlanar.Residual73

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual75
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

namespace SharpPlanar.Residual75
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-136) 10000000000).add ((tm1_75_0.realAnswer).mul (qiBox 75))
noncomputable def box0_1 : RBox := (RBox.rat (-379) 10000000000).add ((tm1_75_1.realAnswer.add (((dBox 75).mul tm1_75_0.realAnswer).neg)).mul (qiBox 75))
noncomputable def box1_0 : RBox := (RBox.rat (108) 10000000000).add ((tm0_75_0.realAnswer).mul (qiBox 75))
noncomputable def box1_1 : RBox := (RBox.rat (338) 10000000000).add ((tm0_75_1.realAnswer.add (((dBox 75).mul tm0_75_0.realAnswer).neg)).mul (qiBox 75))
end SharpPlanar.Residual75

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual76
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

namespace SharpPlanar.Residual76
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (70) 10000000000).add ((tm1_76_0.realAnswer).mul (qiBox 76))
noncomputable def box0_1 : RBox := (RBox.rat (-144) 10000000000).add ((tm1_76_1.realAnswer.add (((dBox 76).mul tm1_76_0.realAnswer).neg)).mul (qiBox 76))
noncomputable def box1_0 : RBox := (RBox.rat (-58) 10000000000).add ((tm0_76_0.realAnswer).mul (qiBox 76))
noncomputable def box1_1 : RBox := (RBox.rat (104) 10000000000).add ((tm0_76_1.realAnswer.add (((dBox 76).mul tm0_76_0.realAnswer).neg)).mul (qiBox 76))
end SharpPlanar.Residual76

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual79
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

namespace SharpPlanar.Residual79
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-1) 10000000000).add ((tm1_79_0.realAnswer).mul (qiBox 79))
noncomputable def box0_1 : RBox := (RBox.rat (19) 10000000000).add ((tm1_79_1.realAnswer.add (((dBox 79).mul tm1_79_0.realAnswer).neg)).mul (qiBox 79))
noncomputable def box1_0 : RBox := (RBox.rat (1) 10000000000).add ((tm0_79_0.realAnswer).mul (qiBox 79))
noncomputable def box1_1 : RBox := (RBox.rat (-15) 10000000000).add ((tm0_79_1.realAnswer.add (((dBox 79).mul tm0_79_0.realAnswer).neg)).mul (qiBox 79))
end SharpPlanar.Residual79

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual81
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

namespace SharpPlanar.Residual81
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (2) 10000000000).add ((tm1_81_0.realAnswer).mul (qiBox 81))
noncomputable def box0_1 : RBox := (RBox.rat (9) 10000000000).add ((tm1_81_1.realAnswer.add (((dBox 81).mul tm1_81_0.realAnswer).neg)).mul (qiBox 81))
noncomputable def box1_0 : RBox := (RBox.rat (-2) 10000000000).add ((tm0_81_0.realAnswer).mul (qiBox 81))
noncomputable def box1_1 : RBox := (RBox.rat (-8) 10000000000).add ((tm0_81_1.realAnswer.add (((dBox 81).mul tm0_81_0.realAnswer).neg)).mul (qiBox 81))
end SharpPlanar.Residual81

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual84
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

namespace SharpPlanar.Residual84
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-13) 10000000000).add ((tm1_84_0.realAnswer).mul (qiBox 84))
noncomputable def box0_1 : RBox := (RBox.rat (3) 10000000000).add ((tm1_84_1.realAnswer.add (((dBox 84).mul tm1_84_0.realAnswer).neg)).mul (qiBox 84))
noncomputable def box1_0 : RBox := (RBox.rat (11) 10000000000).add ((tm0_84_0.realAnswer).mul (qiBox 84))
noncomputable def box1_1 : RBox := (RBox.rat (0) 10000000000).add ((tm0_84_1.realAnswer.add (((dBox 84).mul tm0_84_0.realAnswer).neg)).mul (qiBox 84))
end SharpPlanar.Residual84

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual85
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

namespace SharpPlanar.Residual85
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (13) 10000000000).add ((tm1_85_0.realAnswer).mul (qiBox 85))
noncomputable def box0_1 : RBox := (RBox.rat (-87) 10000000000).add ((tm1_85_1.realAnswer.add (((dBox 85).mul tm1_85_0.realAnswer).neg)).mul (qiBox 85))
noncomputable def box1_0 : RBox := (RBox.rat (-11) 10000000000).add ((tm0_85_0.realAnswer).mul (qiBox 85))
noncomputable def box1_1 : RBox := (RBox.rat (70) 10000000000).add ((tm0_85_1.realAnswer.add (((dBox 85).mul tm0_85_0.realAnswer).neg)).mul (qiBox 85))
end SharpPlanar.Residual85

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual87
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

namespace SharpPlanar.Residual87
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-6) 10000000000).add ((tm1_87_0.realAnswer).mul (qiBox 87))
noncomputable def box0_1 : RBox := (RBox.rat (-60) 10000000000).add ((tm1_87_1.realAnswer.add (((dBox 87).mul tm1_87_0.realAnswer).neg)).mul (qiBox 87))
noncomputable def box1_0 : RBox := (RBox.rat (4) 10000000000).add ((tm0_87_0.realAnswer).mul (qiBox 87))
noncomputable def box1_1 : RBox := (RBox.rat (49) 10000000000).add ((tm0_87_1.realAnswer.add (((dBox 87).mul tm0_87_0.realAnswer).neg)).mul (qiBox 87))
end SharpPlanar.Residual87

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual88
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

namespace SharpPlanar.Residual88
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (6) 10000000000).add ((tm1_88_0.realAnswer).mul (qiBox 88))
noncomputable def box0_1 : RBox := (RBox.rat (5) 10000000000).add ((tm1_88_1.realAnswer.add (((dBox 88).mul tm1_88_0.realAnswer).neg)).mul (qiBox 88))
noncomputable def box1_0 : RBox := (RBox.rat (-4) 10000000000).add ((tm0_88_0.realAnswer).mul (qiBox 88))
noncomputable def box1_1 : RBox := (RBox.rat (-5) 10000000000).add ((tm0_88_1.realAnswer.add (((dBox 88).mul tm0_88_0.realAnswer).neg)).mul (qiBox 88))
end SharpPlanar.Residual88

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual9
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

namespace SharpPlanar.Residual9
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-2932910) 10000000000).add ((tm1_9_0.realAnswer).mul (qiBox 9))
noncomputable def box0_1 : RBox := (RBox.rat (-940875) 10000000000).add ((tm1_9_1.realAnswer.add (((dBox 9).mul tm1_9_0.realAnswer).neg)).mul (qiBox 9))
noncomputable def box1_0 : RBox := (RBox.rat (3636920) 10000000000).add ((tm0_9_0.realAnswer).mul (qiBox 9))
noncomputable def box1_1 : RBox := (RBox.rat (2145806) 10000000000).add ((tm0_9_1.realAnswer.add (((dBox 9).mul tm0_9_0.realAnswer).neg)).mul (qiBox 9))
end SharpPlanar.Residual9

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual91
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

namespace SharpPlanar.Residual91
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (0) 10000000000).add ((tm1_91_0.realAnswer).mul (qiBox 91))
noncomputable def box0_1 : RBox := (RBox.rat (1) 10000000000).add ((tm1_91_1.realAnswer.add (((dBox 91).mul tm1_91_0.realAnswer).neg)).mul (qiBox 91))
noncomputable def box1_0 : RBox := (RBox.rat (0) 10000000000).add ((tm0_91_0.realAnswer).mul (qiBox 91))
noncomputable def box1_1 : RBox := (RBox.rat (-1) 10000000000).add ((tm0_91_1.realAnswer.add (((dBox 91).mul tm0_91_0.realAnswer).neg)).mul (qiBox 91))
end SharpPlanar.Residual91

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual93
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

namespace SharpPlanar.Residual93
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (0) 10000000000).add ((tm1_93_0.realAnswer).mul (qiBox 93))
noncomputable def box0_1 : RBox := (RBox.rat (1) 10000000000).add ((tm1_93_1.realAnswer.add (((dBox 93).mul tm1_93_0.realAnswer).neg)).mul (qiBox 93))
noncomputable def box1_0 : RBox := (RBox.rat (0) 10000000000).add ((tm0_93_0.realAnswer).mul (qiBox 93))
noncomputable def box1_1 : RBox := (RBox.rat (-1) 10000000000).add ((tm0_93_1.realAnswer.add (((dBox 93).mul tm0_93_0.realAnswer).neg)).mul (qiBox 93))
end SharpPlanar.Residual93

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual96
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

namespace SharpPlanar.Residual96
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (-2) 10000000000).add ((tm1_96_0.realAnswer).mul (qiBox 96))
noncomputable def box0_1 : RBox := (RBox.rat (-4) 10000000000).add ((tm1_96_1.realAnswer.add (((dBox 96).mul tm1_96_0.realAnswer).neg)).mul (qiBox 96))
noncomputable def box1_0 : RBox := (RBox.rat (1) 10000000000).add ((tm0_96_0.realAnswer).mul (qiBox 96))
noncomputable def box1_1 : RBox := (RBox.rat (3) 10000000000).add ((tm0_96_1.realAnswer.add (((dBox 96).mul tm0_96_0.realAnswer).neg)).mul (qiBox 96))
end SharpPlanar.Residual96

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual97
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

namespace SharpPlanar.Residual97
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (2) 10000000000).add ((tm1_97_0.realAnswer).mul (qiBox 97))
noncomputable def box0_1 : RBox := (RBox.rat (-6) 10000000000).add ((tm1_97_1.realAnswer.add (((dBox 97).mul tm1_97_0.realAnswer).neg)).mul (qiBox 97))
noncomputable def box1_0 : RBox := (RBox.rat (-2) 10000000000).add ((tm0_97_0.realAnswer).mul (qiBox 97))
noncomputable def box1_1 : RBox := (RBox.rat (4) 10000000000).add ((tm0_97_1.realAnswer.add (((dBox 97).mul tm0_97_0.realAnswer).neg)).mul (qiBox 97))
end SharpPlanar.Residual97

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual99
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

namespace SharpPlanar.Residual99
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_0 : RBox := (RBox.rat (0) 10000000000).add ((tm1_99_0.realAnswer).mul (qiBox 99))
noncomputable def box0_1 : RBox := (RBox.rat (-6) 10000000000).add ((tm1_99_1.realAnswer.add (((dBox 99).mul tm1_99_0.realAnswer).neg)).mul (qiBox 99))
noncomputable def box1_0 : RBox := (RBox.rat (0) 10000000000).add ((tm0_99_0.realAnswer).mul (qiBox 99))
noncomputable def box1_1 : RBox := (RBox.rat (5) 10000000000).add ((tm0_99_1.realAnswer.add (((dBox 99).mul tm0_99_0.realAnswer).neg)).mul (qiBox 99))
end SharpPlanar.Residual99

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
noncomputable def tableHJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (tableData a) ell s+K (tableData (!a)) ell s
end SharpPlanar

end OAI
end


