-- Prove2me | Definitions.Def_OAIQ098G072
-- name    : OAIQ098G072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:03:28.10319+00:00
-- url     : https://prove2.me/theorems/212f9a50-b4bf-4a0f-a088-8e55c6c36284
-- title:
--   Definitions bundle OAIQ098G072 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 36 definitions. The definitions and types are `OAI.SharpPlanar.IntegerBasis.basisAlpha`, `OAI.SharpPlanar.IntegerBasis.basisBeta`, `OAI.SharpPlanar.IntegerBasis.basisFunction`, `OAI.SharpPlanar.IntegerBasis.basisMoment`, `OAI.SharpPlanar.IntegerBasis.momentRuleValue`, `OAI.SharpPlanar.IntegerBasis.phase12`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient`, `OAI.SharpPlanar.IntegerBasis.waveAmplitude`, `OAI.SharpPlanar.IntegerGrid.quadraturePoint`, `OAI.SharpPlanar.IntegerIntervals.expHorner`, `OAI.SharpPlanar.IntegerIntervals.pointLambda`, `OAI.SharpPlanar.IntegerIntervals.pointZ`, `OAI.SharpPlanar.P`, `OAI.SharpPlanar.coeffMass`, `OAI.SharpPlanar.complexBasis`, `OAI.SharpPlanar.complexBasisMoment`, `OAI.SharpPlanar.complexLambda`, `OAI.SharpPlanar.complexTransformedFactor`, `OAI.SharpPlanar.complexU`, `OAI.SharpPlanar.complexV`, `OAI.SharpPlanar.complexZ`, `OAI.SharpPlanar.cosTable`, `OAI.SharpPlanar.diskAffine`, `OAI.SharpPlanar.diskCenter`, `OAI.SharpPlanar.fejerAngle`, `OAI.SharpPlanar.fejerNode`, `OAI.SharpPlanar.fejerPartial`, `OAI.SharpPlanar.fejerPolynomial`, `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.finiteDensity`, `OAI.SharpPlanar.pieceIntegral`, `OAI.SharpPlanar.pieceRule`, `OAI.SharpPlanar.rootPhase`, `OAI.SharpPlanar.sinTable`, `OAI.SharpPlanar.singleCoefficient`, `OAI.SharpPlanar.taylorPolynomial`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BasisIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean), [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean), [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean), [`PlanarPacking_Grid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean), [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean), [`PlanarPacking_Nodes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Nodes.lean), [`PlanarPacking_Quadrature`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean), [`PlanarPacking_Roots`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Roots.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G073`, `OAIQ098G074`, `OAIQ098G091`, `OAIQ098G1680`, `OAIQ098G1681`, `OAIQ098G235` and `OAIQ098G322`; the statements `OAI.SharpPlanar.CachedData.amp1_0_contains_g`, `OAI.SharpPlanar.CachedData.amp4_0_contains_g`, `OAI.SharpPlanar.CachedData.cm1_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_3_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.column100_0_contains_g`, `OAI.SharpPlanar.CachedData.column100_1_contains_g`, `OAI.SharpPlanar.CachedData.column12_0_contains_g`, `OAI.SharpPlanar.CachedData.column12_1_contains_g`, `OAI.SharpPlanar.CachedData.column13_0_contains_g`, `OAI.SharpPlanar.CachedData.column19_1_contains_g`, `OAI.SharpPlanar.CachedData.column1_0_contains_g`, `OAI.SharpPlanar.CachedData.column27_1_contains_g`, `OAI.SharpPlanar.CachedData.column28_1_contains_g`, `OAI.SharpPlanar.CachedData.column36_0_contains_g`, `OAI.SharpPlanar.CachedData.column43_0_contains_g`, `OAI.SharpPlanar.CachedData.column43_1_contains_g`, `OAI.SharpPlanar.CachedData.column51_0_contains_g`, `OAI.SharpPlanar.CachedData.column51_1_contains_g`, `OAI.SharpPlanar.CachedData.column52_0_contains_g`, `OAI.SharpPlanar.CachedData.column52_1_contains_g`, `OAI.SharpPlanar.CachedData.column60_0_contains_g`, `OAI.SharpPlanar.CachedData.column60_1_contains_g`, `OAI.SharpPlanar.CachedData.column67_0_contains_g`, `OAI.SharpPlanar.CachedData.column67_1_contains_g`, `OAI.SharpPlanar.CachedData.column75_0_contains_g`, `OAI.SharpPlanar.CachedData.column75_1_contains_g`, `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.CachedData.column76_1_contains_g`, `OAI.SharpPlanar.CachedData.column84_0_contains_g`, `OAI.SharpPlanar.CachedData.column84_1_contains_g`, `OAI.SharpPlanar.CachedData.column91_0_contains_g`, `OAI.SharpPlanar.CachedData.column91_1_contains_g`, `OAI.SharpPlanar.CachedData.column99_0_contains_g`, `OAI.SharpPlanar.CachedData.column99_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel12_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel12_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel19_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel1_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel21_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel21_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel24_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel25_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel27_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel28_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel28_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel31_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel33_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel39_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel3_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel3_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel40_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel49_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel49_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel4_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel4_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel63_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel63_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel7_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel7_1_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_19_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_6_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_7_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_8_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_9_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_10_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_14_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_15_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_20_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_25_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_30_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_4_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_5_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_9_contains_g`, `OAI.SharpPlanar.CachedData.power12_contains_g`, `OAI.SharpPlanar.CachedData.power13_contains_g`, `OAI.SharpPlanar.CachedData.power14_contains_g`, `OAI.SharpPlanar.CachedData.power19_contains_g`, `OAI.SharpPlanar.CachedData.power1_contains_g`, `OAI.SharpPlanar.CachedData.power21_contains_g`, `OAI.SharpPlanar.CachedData.power22_contains_g`, `OAI.SharpPlanar.CachedData.power27_contains_g`, `OAI.SharpPlanar.CachedData.power30_contains_g`, `OAI.SharpPlanar.CachedData.power36_contains_g`, `OAI.SharpPlanar.CachedData.power37_contains_g`, `OAI.SharpPlanar.CachedData.power3_contains_g`, `OAI.SharpPlanar.CachedData.power45_contains_g`, `OAI.SharpPlanar.CachedData.power46_contains_g`, `OAI.SharpPlanar.CachedData.power4_contains_g`, `OAI.SharpPlanar.CachedData.power54_contains_g`, `OAI.SharpPlanar.CachedData.power61_contains_g`, `OAI.SharpPlanar.CachedData.power62_contains_g`, `OAI.SharpPlanar.CachedData.power69_contains_g`, `OAI.SharpPlanar.CachedData.power6_contains_g`, `OAI.SharpPlanar.CachedData.power70_contains_g`, `OAI.SharpPlanar.CachedData.power78_contains_g`, `OAI.SharpPlanar.CachedData.power85_contains_g`, `OAI.SharpPlanar.CachedData.power86_contains_g`, `OAI.SharpPlanar.CachedData.power93_contains_g`, `OAI.SharpPlanar.CachedData.power94_contains_g`, `OAI.SharpPlanar.CachedData.trans15_contains_g`, `OAI.SharpPlanar.CachedData.trans1_contains_g`, `OAI.SharpPlanar.CachedData.trans22_contains_g`, `OAI.SharpPlanar.CachedData.trans29_contains_g`, `OAI.SharpPlanar.CachedData.trans36_contains_g`, `OAI.SharpPlanar.CachedData.trans43_contains_g`, `OAI.SharpPlanar.CachedData.trans50_contains_g`, `OAI.SharpPlanar.CachedData.trans57_contains_g`, `OAI.SharpPlanar.CachedData.trans64_contains_g`, `OAI.SharpPlanar.CachedData.trans71_contains_g`, `OAI.SharpPlanar.CachedData.trans78_contains_g`, `OAI.SharpPlanar.CachedData.trans84_contains_g`, `OAI.SharpPlanar.CachedData.trans85_contains_g`, `OAI.SharpPlanar.CachedData.trans8_contains_g`, `OAI.SharpPlanar.CachedData.trans91_contains_g`, `OAI.SharpPlanar.CachedData.trans92_contains_g`, `OAI.SharpPlanar.CachedData.trans99_contains_g`, `OAI.SharpPlanar.D_as_table_g`, `OAI.SharpPlanar.IntegerAlpha.a0_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aLookup_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow10_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow11_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow6_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow7_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow8_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow9_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aTable_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bLookup_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow10_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow11_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow6_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow7_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow8_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow9_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bTable_contains_g`, `OAI.SharpPlanar.IntegerBasis.basisAlpha_mod_g`, `OAI.SharpPlanar.IntegerBasis.basisBeta_mod_g`, `OAI.SharpPlanar.IntegerBasis.basisFunction_wave_g`, `OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_g`, `OAI.SharpPlanar.IntegerBasis.phase12_mod_g`, `OAI.SharpPlanar.IntegerBasis.phase12_periodic_g`, `OAI.SharpPlanar.IntegerBasis.pointLambda_eq_g`, `OAI.SharpPlanar.IntegerBasis.pointZ_eq_g`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient_eq_phase_g`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient_mod_g`, `OAI.SharpPlanar.IntegerBasis.u_factored_g`, `OAI.SharpPlanar.IntegerBasis.v_factored_g`, `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerIntervals.expHorner_eq_g`, `OAI.SharpPlanar.IntegerIntervals.exp_from_horner_g`, `OAI.SharpPlanar.IntegerIntervals.exp_small_error_g`, `OAI.SharpPlanar.IntegerIntervals.horner_step_g`, `OAI.SharpPlanar.IntegerIntervals.lamBox_contains_g`, `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g`, `OAI.SharpPlanar.IntegerIntervals.zBox_contains_g`, `OAI.SharpPlanar.Numerical.K_column_contains_g`, `OAI.SharpPlanar.Pcoeff_norm_g`, `OAI.SharpPlanar.Q_as_table_g`, `OAI.SharpPlanar.analytic_taylor_error_g`, `OAI.SharpPlanar.cached_density_rule_contains_g`, `OAI.SharpPlanar.complexBasis_rule_error_g`, `OAI.SharpPlanar.complexDirectFactor_disk_bound_g`, `OAI.SharpPlanar.complexLambda_differentiableAt_g`, `OAI.SharpPlanar.complexLambda_ofReal_g`, `OAI.SharpPlanar.complexTransformedFactor_differentiableAt_g`, `OAI.SharpPlanar.complexTransformedFactor_disk_bound_g`, `OAI.SharpPlanar.complexU_disk_bound_g`, `OAI.SharpPlanar.complexV_disk_bound_g`, `OAI.SharpPlanar.complexZ_ofReal_g`, `OAI.SharpPlanar.directIntegrand_analytic_g`, `OAI.SharpPlanar.directIntegrand_disk_bound_g`, `OAI.SharpPlanar.directMoment_piece_average_error_g`, `OAI.SharpPlanar.directMoment_piece_error_g`, `OAI.SharpPlanar.directMoment_rule_error_g`, `OAI.SharpPlanar.diskAffine_mem_g`, `OAI.SharpPlanar.disk_coordinate_bounds_g`, `OAI.SharpPlanar.disk_delta_bounds_g`, `OAI.SharpPlanar.disk_denominator_lower_g`, `OAI.SharpPlanar.disk_denominator_ne_g`, `OAI.SharpPlanar.disk_frequency_distance_g`, `OAI.SharpPlanar.disk_lambda_bound_g`, `OAI.SharpPlanar.disk_phase_bound_g`, `OAI.SharpPlanar.disk_z_bound_g`, `OAI.SharpPlanar.disk_z_imaginary_g`, `OAI.SharpPlanar.disk_z_imaginary_simple_g`, `OAI.SharpPlanar.fejerPolynomial_degree_g`, `OAI.SharpPlanar.fejerPolynomial_eval_g`, `OAI.SharpPlanar.fejerWeight_pos_g`, `OAI.SharpPlanar.fejer_analytic_average_error_g`, `OAI.SharpPlanar.fejer_cheb_integral_g`, `OAI.SharpPlanar.fejer_exact_complex_g`, `OAI.SharpPlanar.fejer_exact_g`, `OAI.SharpPlanar.fejer_exact_monomial_g`, `OAI.SharpPlanar.fejer_integral_even_g`, `OAI.SharpPlanar.fejer_integral_odd_g`, `OAI.SharpPlanar.fejer_integral_zero_g`, `OAI.SharpPlanar.fejer_polynomial_integral_g`, `OAI.SharpPlanar.fejer_weighted_orthogonal_g`, `OAI.SharpPlanar.finiteDensity_disk_bound_g`, `OAI.SharpPlanar.pieceIntegral_affine_g`, `OAI.SharpPlanar.piece_rule_error_scaling_g`, `OAI.SharpPlanar.taylorPolynomial_zero_g`, `OAI.SharpPlanar.transformedIntegrand_analytic_g`, `OAI.SharpPlanar.transformedIntegrand_disk_bound_g`, `OAI.SharpPlanar.transformedMoment_piece_average_error_g`, `OAI.SharpPlanar.transformedMoment_piece_error_g`, `OAI.SharpPlanar.transformedMoment_rule_error_g` and `OAI.SharpPlanar.trig_table_g`; the proofs of `OAI.SharpPlanar.CachedData.amp1_0_contains_g`, `OAI.SharpPlanar.CachedData.amp4_0_contains_g`, `OAI.SharpPlanar.CachedData.cm3_3_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.column12_0_contains_g`, `OAI.SharpPlanar.CachedData.column12_1_contains_g`, `OAI.SharpPlanar.CachedData.column13_0_contains_g`, `OAI.SharpPlanar.CachedData.column19_1_contains_g`, `OAI.SharpPlanar.CachedData.column1_0_contains_g`, `OAI.SharpPlanar.CachedData.column27_1_contains_g`, `OAI.SharpPlanar.CachedData.column28_1_contains_g`, `OAI.SharpPlanar.CachedData.column36_0_contains_g`, `OAI.SharpPlanar.CachedData.column51_0_contains_g`, `OAI.SharpPlanar.CachedData.column51_1_contains_g`, `OAI.SharpPlanar.CachedData.column52_0_contains_g`, `OAI.SharpPlanar.CachedData.column52_1_contains_g`, `OAI.SharpPlanar.CachedData.column60_0_contains_g`, `OAI.SharpPlanar.CachedData.column60_1_contains_g`, `OAI.SharpPlanar.CachedData.column67_0_contains_g`, `OAI.SharpPlanar.CachedData.column67_1_contains_g`, `OAI.SharpPlanar.CachedData.column75_0_contains_g`, `OAI.SharpPlanar.CachedData.column75_1_contains_g`, `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.CachedData.column76_1_contains_g`, `OAI.SharpPlanar.CachedData.column84_0_contains_g`, `OAI.SharpPlanar.CachedData.column84_1_contains_g`, `OAI.SharpPlanar.CachedData.column91_0_contains_g`, `OAI.SharpPlanar.CachedData.column91_1_contains_g`, `OAI.SharpPlanar.CachedData.column99_0_contains_g`, `OAI.SharpPlanar.CachedData.column99_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel1_1_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_19_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_6_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_7_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_8_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_9_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_10_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_14_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_15_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_20_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_25_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_30_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_4_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_5_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_9_contains_g`, `OAI.SharpPlanar.CachedData.power12_contains_g`, `OAI.SharpPlanar.CachedData.power13_contains_g`, `OAI.SharpPlanar.CachedData.power14_contains_g`, `OAI.SharpPlanar.CachedData.power19_contains_g`, `OAI.SharpPlanar.CachedData.power1_contains_g`, `OAI.SharpPlanar.CachedData.power21_contains_g`, `OAI.SharpPlanar.CachedData.power22_contains_g`, `OAI.SharpPlanar.CachedData.power27_contains_g`, `OAI.SharpPlanar.CachedData.power30_contains_g`, `OAI.SharpPlanar.CachedData.power37_contains_g`, `OAI.SharpPlanar.CachedData.power3_contains_g`, `OAI.SharpPlanar.CachedData.power46_contains_g`, `OAI.SharpPlanar.CachedData.power4_contains_g`, `OAI.SharpPlanar.CachedData.power54_contains_g`, `OAI.SharpPlanar.CachedData.power61_contains_g`, `OAI.SharpPlanar.CachedData.power62_contains_g`, `OAI.SharpPlanar.CachedData.power69_contains_g`, `OAI.SharpPlanar.CachedData.power70_contains_g`, `OAI.SharpPlanar.CachedData.power78_contains_g`, `OAI.SharpPlanar.CachedData.power85_contains_g`, `OAI.SharpPlanar.CachedData.power86_contains_g`, `OAI.SharpPlanar.CachedData.power93_contains_g`, `OAI.SharpPlanar.CachedData.power94_contains_g`, `OAI.SharpPlanar.D_0_g`, `OAI.SharpPlanar.D_1_g`, `OAI.SharpPlanar.D_3_g`, `OAI.SharpPlanar.D_4_g`, `OAI.SharpPlanar.D_7_g`, `OAI.SharpPlanar.D_9_g`, `OAI.SharpPlanar.D_as_table_g`, `OAI.SharpPlanar.IntegerAlpha.aLookup_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow10_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow11_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow6_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow7_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow8_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aRow9_contains_g`, `OAI.SharpPlanar.IntegerAlpha.aTable_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bLookup_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow10_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow11_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow6_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow7_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow8_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bRow9_contains_g`, `OAI.SharpPlanar.IntegerAlpha.bTable_contains_g`, `OAI.SharpPlanar.IntegerBasis.basisAlpha_mod_g`, `OAI.SharpPlanar.IntegerBasis.basisBeta_mod_g`, `OAI.SharpPlanar.IntegerBasis.basisFunction_wave_g`, `OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_g`, `OAI.SharpPlanar.IntegerBasis.phase12_mod_g`, `OAI.SharpPlanar.IntegerBasis.phase12_periodic_g`, `OAI.SharpPlanar.IntegerBasis.pointLambda_eq_g`, `OAI.SharpPlanar.IntegerBasis.pointZ_eq_g`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient_eq_phase_g`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient_mod_g`, `OAI.SharpPlanar.IntegerBasis.u_factored_g`, `OAI.SharpPlanar.IntegerBasis.v_factored_g`, `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerIntervals.expHorner_eq_g`, `OAI.SharpPlanar.IntegerIntervals.exp_from_horner_g`, `OAI.SharpPlanar.IntegerIntervals.exp_small_error_g`, `OAI.SharpPlanar.IntegerIntervals.horner_step_g`, `OAI.SharpPlanar.IntegerIntervals.lamBox_contains_g`, `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g`, `OAI.SharpPlanar.IntegerIntervals.zBox_contains_g`, `OAI.SharpPlanar.Numerical.K_column_contains_g`, `OAI.SharpPlanar.Numerical.Lmat_column_g`, `OAI.SharpPlanar.Numerical.U100.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U12.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U13.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U13.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U15.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U15.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U15.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U15.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U16.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U19.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U19.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U19.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U19.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U19.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U19.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U19.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U19.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U21.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U21.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U25.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U27.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U27.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U27.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U27.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U27.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U27.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U27.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U27.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U28.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U28.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U31.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U31.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U33.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.wuminus_contains_g`, `OAI.SharpPlanar.Numerical.U33.wuplus_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U36.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U37.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U37.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U43.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U43.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U43.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U43.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U43.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U43.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U45.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U45.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U45.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U45.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U48.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U48.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U49.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U49.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U51.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U51.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U51.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U51.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U51.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U51.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U52.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U52.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U52.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U52.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U52.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U52.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U55.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U55.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuminus_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuplus_contains_g`, `OAI.SharpPlanar.Numerical.U60.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U60.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U60.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U60.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U60.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U60.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U61.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U61.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U63.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U63.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U63.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U63.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U64.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U64.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U67.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U67.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U67.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U67.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U67.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U67.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U69.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U69.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U72.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U72.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U72.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U72.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U73.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U73.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U75.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U75.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U75.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U75.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U75.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U75.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U76.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U76.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U76.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U76.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U76.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U76.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U79.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U79.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U79.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U79.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U7.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U7.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U7.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U81.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U81.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U81.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U81.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U84.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U84.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U84.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U84.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U84.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U84.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U85.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U85.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U87.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U87.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U87.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U87.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U88.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U88.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U91.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U91.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U91.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U91.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U91.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U91.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U93.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U93.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U96.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U96.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U96.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U97.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U97.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U99.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U99.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U99.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U99.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U99.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U99.wuplus_column_g`, `OAI.SharpPlanar.Numerical.defectminus_column_g`, `OAI.SharpPlanar.Numerical.defectplus_column_g`, `OAI.SharpPlanar.Numerical.dentry0_0_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_0_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_5_contains_g`, `OAI.SharpPlanar.Numerical.signedVU_norm_g`, `OAI.SharpPlanar.Pcoeff_norm_g`, `OAI.SharpPlanar.Q_0_g`, `OAI.SharpPlanar.Q_1_g`, `OAI.SharpPlanar.Q_3_g`, `OAI.SharpPlanar.Q_4_g`, `OAI.SharpPlanar.Q_7_g`, `OAI.SharpPlanar.Q_9_g`, `OAI.SharpPlanar.Q_as_table_g`, `OAI.SharpPlanar.Scoords_mem_g`, `OAI.SharpPlanar.Slinear_bound_g`, `OAI.SharpPlanar.analytic_taylor_error_g`, `OAI.SharpPlanar.atomicCoefficient_norm_g`, `OAI.SharpPlanar.cached_density_rule_contains_g`, `OAI.SharpPlanar.complexBasis_rule_error_g`, `OAI.SharpPlanar.complexDirectFactor_disk_bound_g`, `OAI.SharpPlanar.complexLambda_differentiableAt_g`, `OAI.SharpPlanar.complexLambda_ofReal_g`, `OAI.SharpPlanar.complexTransformedFactor_differentiableAt_g`, `OAI.SharpPlanar.complexTransformedFactor_disk_bound_g`, `OAI.SharpPlanar.complexU_disk_bound_g`, `OAI.SharpPlanar.complexV_disk_bound_g`, `OAI.SharpPlanar.complexZ_ofReal_g`, `OAI.SharpPlanar.directIntegrand_analytic_g`, `OAI.SharpPlanar.directIntegrand_disk_bound_g`, `OAI.SharpPlanar.directMoment_piece_average_error_g`, `OAI.SharpPlanar.directMoment_piece_error_g`, `OAI.SharpPlanar.directMoment_rule_error_g`, `OAI.SharpPlanar.diskAffine_mem_g`, `OAI.SharpPlanar.disk_coordinate_bounds_g`, `OAI.SharpPlanar.disk_delta_bounds_g`, `OAI.SharpPlanar.disk_denominator_lower_g`, `OAI.SharpPlanar.disk_denominator_ne_g`, `OAI.SharpPlanar.disk_frequency_distance_g`, `OAI.SharpPlanar.disk_lambda_bound_g`, `OAI.SharpPlanar.disk_phase_bound_g`, `OAI.SharpPlanar.disk_z_bound_g`, `OAI.SharpPlanar.disk_z_imaginary_g`, `OAI.SharpPlanar.disk_z_imaginary_simple_g`, `OAI.SharpPlanar.exact_sign_tail_g`, `OAI.SharpPlanar.fejerPolynomial_degree_g`, `OAI.SharpPlanar.fejerPolynomial_eval_g`, `OAI.SharpPlanar.fejerWeight_pos_g`, `OAI.SharpPlanar.fejer_analytic_average_error_g`, `OAI.SharpPlanar.fejer_cheb_integral_g`, `OAI.SharpPlanar.fejer_exact_complex_g`, `OAI.SharpPlanar.fejer_exact_g`, `OAI.SharpPlanar.fejer_exact_monomial_g`, `OAI.SharpPlanar.fejer_integral_even_g`, `OAI.SharpPlanar.fejer_integral_odd_g`, `OAI.SharpPlanar.fejer_integral_zero_g`, `OAI.SharpPlanar.fejer_polynomial_integral_g`, `OAI.SharpPlanar.fejer_weighted_orthogonal_g`, `OAI.SharpPlanar.finiteDensity_disk_bound_g`, `OAI.SharpPlanar.pieceIntegral_affine_g`, `OAI.SharpPlanar.piece_rule_error_scaling_g`, `OAI.SharpPlanar.positive_coeff_mass_g`, `OAI.SharpPlanar.taylorPolynomial_zero_g`, `OAI.SharpPlanar.transformedIntegrand_analytic_g`, `OAI.SharpPlanar.transformedIntegrand_disk_bound_g`, `OAI.SharpPlanar.transformedJets_summable_g`, `OAI.SharpPlanar.transformedMoment_piece_average_error_g`, `OAI.SharpPlanar.transformedMoment_piece_error_g`, `OAI.SharpPlanar.transformedMoment_rule_error_g` and `OAI.SharpPlanar.trig_table_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G001

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def P (s : ℝ) : ℝ :=
  ∏ a ∈ residues, (2 * Real.sin (Real.pi * (s - a) / 12)) ^ 2


def coeffMass : ℕ → ℝ
  | 0 => 5
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | _ => 0

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexLambda (t : ℂ) : ℂ :=
  Complex.I / ((b:ℂ) * (t+Complex.I*(h:ℂ)))
noncomputable def complexZ (t : ℂ) : ℂ :=
  -(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)


noncomputable def diskCenter (j : ℕ) : ℝ := (2*(j:ℝ)+1)/12

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set


noncomputable def complexU (n j : ℕ) (t : ℂ) : ℂ :=
  -2 * (Real.pi:ℂ)^2 * Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)
noncomputable def complexV (n j : ℕ) (t : ℂ) : ℂ :=
  2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

noncomputable def finiteDensity (c d : ℕ → ℝ) (j : ℕ) (t : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 101, ((c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t)

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexTransformedFactor (m y : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  complexLambda t * Complex.exp (Complex.I*Real.pi*complexZ t*m) *
    (Complex.I*Real.pi*complexZ t*y)^ell / (ell.factorial:ℂ)

end SharpPlanar

end OAI
end

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

noncomputable def expHorner (z : ℂ) (k : ℕ) : ℕ → ℂ
  | 0 => (k.factorial:ℂ)⁻¹
  | n+1 => (k.factorial:ℂ)⁻¹ + z*expHorner z (k+1) n

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

-- These are exactly lambda,z from fourier:frequencies, restricted to real t.
noncomputable def pointLambda (t : ℝ) : ℂ :=
  Complex.I / (((Real.sqrt 3/2:ℝ):ℂ) * ((t:ℂ)+Complex.I*(2/5:ℂ)))
noncomputable def pointZ (t : ℝ) : ℂ :=
  -(4/3:ℂ) / ((t:ℂ)+Complex.I*(2/5:ℂ)) - Complex.I*(2/5:ℂ)

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
noncomputable def rootPhase (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/512))


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

namespace SharpPlanar
noncomputable def fejerAngle (v : ℕ) : ℝ := Real.pi*((v:ℝ)+1/2)/256
noncomputable def fejerNode (v : ℕ) : ℝ := Real.cos (fejerAngle v)
noncomputable def fejerWeight (v : ℕ) : ℝ :=
  (1-2*∑ a ∈ Finset.Icc (1:ℕ) 127,
    Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1))/256


end SharpPlanar

namespace SharpPlanar
open IntegerIntervals

noncomputable def fejerPartial (v N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.cos (2*((k+1:ℕ):ℝ)*fejerAngle v)/(4*((k+1:ℕ):ℝ)^2-1)

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar


noncomputable def fejerPolynomial :=
  1-∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1)) • T ℝ (2*a)

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar

noncomputable def taylorPolynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹*iteratedDeriv n f c*(z-c)^n

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def diskAffine (j : ℕ) (w : ℂ) : ℂ := (diskCenter j:ℂ)+w/12

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def pieceIntegral (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, F t
noncomputable def pieceRule (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  (1/6:ℂ) * ∑ v : Fin 256, (fejerWeight v.val:ℂ) *
    F (diskAffine j (fejerNode v.val))

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def singleCoefficient (n : ℕ) (k : ℕ) : ℝ := if k=n then 1 else 0

noncomputable def complexBasis (d : Bool) (n j : ℕ) (t : ℂ) : ℂ :=
  if d then complexV n j t else complexU n j t
noncomputable def complexBasisMoment (d e : Bool) (n j m : ℕ) (t : ℂ) : ℂ :=
  complexBasis d n j t * complexTransformedFactor m 1 (if e then 1 else 0) t

end SharpPlanar


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

noncomputable def phase12 (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/6))

noncomputable def spectralCoefficient (n l : ℕ) : ℂ :=
  Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def basisAlpha (n j : ℕ) : ℂ := ∑ l ∈ Finset.Icc (j+1) 6, spectralCoefficient n l
noncomputable def basisBeta (n j : ℕ) : ℂ :=
  ∑ l ∈ Finset.Icc (j+1) 6, ((l:ℂ)/6)*spectralCoefficient n l

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def basisFunction (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then v n j t else u n j t
noncomputable def basisMoment (d e : Bool) (n j m : ℕ) (t : ℝ) : ℂ :=
  basisFunction d n j t * (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) *
    (if e then Complex.I*Real.pi*z t else 1)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def momentRuleValue (t : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (n m : ℕ) (d e : Bool) : ℂ :=
  ∑ j : Fin 6, (1/6:ℂ)*∑ v : Fin 256, (w v.val:ℂ)*
    basisMoment d e n j.val m (t j.val v.val)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def waveAmplitude (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then 2*Complex.I*Real.pi*basisAlpha n j
  else -2*(Real.pi:ℂ)^2*(basisBeta n j-(t:ℂ)*basisAlpha n j)

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
open IntegerIntervals
noncomputable def quadraturePoint (j v : ℕ) : ℝ := (2*(j:ℝ)+1)/12+fejerNode v/12
end SharpPlanar.IntegerGrid

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

noncomputable def sinTable : ℕ → ℝ
  | 0 => 0 | 1 => 1/2 | 2 => b | 3 => 1 | 4 => b | 5 => 1/2
  | 6 => 0 | 7 => -1/2 | 8 => -b | 9 => -1 | 10 => -b | 11 => -1/2
  | _ => 0
noncomputable def cosTable : ℕ → ℝ
  | 0 => 1 | 1 => b | 2 => 1/2 | 3 => 0 | 4 => -1/2 | 5 => -b
  | 6 => -1 | 7 => -b | 8 => -1/2 | 9 => 0 | 10 => 1/2 | 11 => b
  | _ => 1

end SharpPlanar

end OAI
end


