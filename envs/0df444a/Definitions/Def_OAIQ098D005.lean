-- Prove2me | Definitions.Def_OAIQ098D005
-- name    : OAIQ098D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:26:45.806208+00:00
-- url     : https://prove2.me/theorems/780ccaea-f2bf-4063-b66c-b24003d04913
-- title:
--   Definitions bundle OAIQ098D005 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 919 declarations of OpenAI's Lean: 850 definitions and 69 theorems. The definitions and types are `OAI.SharpPlanar.IntegerBasis.densityCap`, `OAI.SharpPlanar.IntegerBasis.uAmplitude`, `OAI.SharpPlanar.IntegerBasis.vAmplitude`, `OAI.SharpPlanar.Numerical.IL`, `OAI.SharpPlanar.Numerical.RL`, `OAI.SharpPlanar.Numerical.U100.entries`, `OAI.SharpPlanar.Numerical.U100.entry0_0`, `OAI.SharpPlanar.Numerical.U100.entry0_1`, `OAI.SharpPlanar.Numerical.U100.entry1_0`, `OAI.SharpPlanar.Numerical.U100.entry1_1`, `OAI.SharpPlanar.Numerical.U100.entry2_0`, `OAI.SharpPlanar.Numerical.U100.entry2_1`, `OAI.SharpPlanar.Numerical.U100.entry3_0`, `OAI.SharpPlanar.Numerical.U100.entry3_1`, `OAI.SharpPlanar.Numerical.U100.entry4_0`, `OAI.SharpPlanar.Numerical.U100.entry4_1`, `OAI.SharpPlanar.Numerical.U100.entry5_0`, `OAI.SharpPlanar.Numerical.U100.entry5_1`, `OAI.SharpPlanar.Numerical.U12.entries`, `OAI.SharpPlanar.Numerical.U12.entry0_0`, `OAI.SharpPlanar.Numerical.U12.entry0_1`, `OAI.SharpPlanar.Numerical.U12.entry1_0`, `OAI.SharpPlanar.Numerical.U12.entry1_1`, `OAI.SharpPlanar.Numerical.U12.entry2_0`, `OAI.SharpPlanar.Numerical.U12.entry2_1`, `OAI.SharpPlanar.Numerical.U12.entry3_0`, `OAI.SharpPlanar.Numerical.U12.entry3_1`, `OAI.SharpPlanar.Numerical.U12.entry4_0`, `OAI.SharpPlanar.Numerical.U12.entry4_1`, `OAI.SharpPlanar.Numerical.U12.entry5_0`, `OAI.SharpPlanar.Numerical.U12.entry5_1`, `OAI.SharpPlanar.Numerical.U13.entries`, `OAI.SharpPlanar.Numerical.U13.entry0_0`, `OAI.SharpPlanar.Numerical.U13.entry0_1`, `OAI.SharpPlanar.Numerical.U13.entry1_0`, `OAI.SharpPlanar.Numerical.U13.entry1_1`, `OAI.SharpPlanar.Numerical.U13.entry2_0`, `OAI.SharpPlanar.Numerical.U13.entry2_1`, `OAI.SharpPlanar.Numerical.U13.entry3_0`, `OAI.SharpPlanar.Numerical.U13.entry3_1` and 810 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_AtomTail`, `PlanarPacking_BarrierProduct`, `PlanarPacking_CanonicalRows`, `PlanarPacking_Cardinal`, `PlanarPacking_Certificate_LEntries`, `PlanarPacking_Certificate_Residual1`, `PlanarPacking_Certificate_Residual100`, `PlanarPacking_Certificate_Residual12`, `PlanarPacking_Certificate_Residual13`, `PlanarPacking_Certificate_Residual15`, `PlanarPacking_Certificate_Residual16`, `PlanarPacking_Certificate_Residual19`, `PlanarPacking_Certificate_Residual21`, `PlanarPacking_Certificate_Residual24`, `PlanarPacking_Certificate_Residual25`, `PlanarPacking_Certificate_Residual27`, `PlanarPacking_Certificate_Residual28`, `PlanarPacking_Certificate_Residual3`, `PlanarPacking_Certificate_Residual31`, `PlanarPacking_Certificate_Residual33`, `PlanarPacking_Certificate_Residual36`, `PlanarPacking_Certificate_Residual37`, `PlanarPacking_Certificate_Residual39`, `PlanarPacking_Certificate_Residual4`, `PlanarPacking_Certificate_Residual40`, `PlanarPacking_Certificate_Residual43`, `PlanarPacking_Certificate_Residual45`, `PlanarPacking_Certificate_Residual48`, `PlanarPacking_Certificate_Residual49`, `PlanarPacking_Certificate_Residual51`, `PlanarPacking_Certificate_Residual52`, `PlanarPacking_Certificate_Residual55`, `PlanarPacking_Certificate_Residual57`, `PlanarPacking_Certificate_Residual60`, `PlanarPacking_Certificate_Residual61`, `PlanarPacking_Certificate_Residual63`, `PlanarPacking_Certificate_Residual64`, `PlanarPacking_Certificate_Residual67`, `PlanarPacking_Certificate_Residual69`, `PlanarPacking_Certificate_Residual7`, `PlanarPacking_Certificate_Residual72`, `PlanarPacking_Certificate_Residual73`, `PlanarPacking_Certificate_Residual75`, `PlanarPacking_Certificate_Residual76`, `PlanarPacking_Certificate_Residual79`, `PlanarPacking_Certificate_Residual81`, `PlanarPacking_Certificate_Residual84`, `PlanarPacking_Certificate_Residual85`, `PlanarPacking_Certificate_Residual87`, `PlanarPacking_Certificate_Residual88`, `PlanarPacking_Certificate_Residual9`, `PlanarPacking_Certificate_Residual91`, `PlanarPacking_Certificate_Residual93`, `PlanarPacking_Certificate_Residual96`, `PlanarPacking_Certificate_Residual97`, `PlanarPacking_Certificate_Residual99`, `PlanarPacking_Certificate_TableData`, `PlanarPacking_Certificate_TableList`, `PlanarPacking_Certificate_TailCoefficients`, `PlanarPacking_Certificate_WUCert100`, `PlanarPacking_Certificate_WUCert12`, `PlanarPacking_Certificate_WUCert13`, `PlanarPacking_Certificate_WUCert15`, `PlanarPacking_Certificate_WUCert16`, `PlanarPacking_Certificate_WUCert19`, `PlanarPacking_Certificate_WUCert21`, `PlanarPacking_Certificate_WUCert24`, `PlanarPacking_Certificate_WUCert25`, `PlanarPacking_Certificate_WUCert27`, `PlanarPacking_Certificate_WUCert28`, `PlanarPacking_Certificate_WUCert31`, `PlanarPacking_Certificate_WUCert33`, `PlanarPacking_Certificate_WUCert36`, `PlanarPacking_Certificate_WUCert37`, `PlanarPacking_Certificate_WUCert39`, `PlanarPacking_Certificate_WUCert40`, `PlanarPacking_Certificate_WUCert43`, `PlanarPacking_Certificate_WUCert45`, `PlanarPacking_Certificate_WUCert48`, `PlanarPacking_Certificate_WUCert49`, `PlanarPacking_Certificate_WUCert51`, `PlanarPacking_Certificate_WUCert52`, `PlanarPacking_Certificate_WUCert55`, `PlanarPacking_Certificate_WUCert57`, `PlanarPacking_Certificate_WUCert60`, `PlanarPacking_Certificate_WUCert61`, `PlanarPacking_Certificate_WUCert63`, `PlanarPacking_Certificate_WUCert64`, `PlanarPacking_Certificate_WUCert67`, `PlanarPacking_Certificate_WUCert69`, `PlanarPacking_Certificate_WUCert7`, `PlanarPacking_Certificate_WUCert72`, `PlanarPacking_Certificate_WUCert73`, `PlanarPacking_Certificate_WUCert75`, `PlanarPacking_Certificate_WUCert76`, `PlanarPacking_Certificate_WUCert79`, `PlanarPacking_Certificate_WUCert81`, `PlanarPacking_Certificate_WUCert84`, `PlanarPacking_Certificate_WUCert85`, `PlanarPacking_Certificate_WUCert87`, `PlanarPacking_Certificate_WUCert88`, `PlanarPacking_Certificate_WUCert9`, `PlanarPacking_Certificate_WUCert91`, `PlanarPacking_Certificate_WUCert93`, `PlanarPacking_Certificate_WUCert96`, `PlanarPacking_Certificate_WUCert97`, `PlanarPacking_Certificate_WUCert99`, `PlanarPacking_CoarseTaylor`, `PlanarPacking_ContactData`, `PlanarPacking_DataSplit`, `PlanarPacking_Dilation`, `PlanarPacking_Entire`, `PlanarPacking_Envelopes`, `PlanarPacking_ExactPair`, `PlanarPacking_FiniteCoordinates`, `PlanarPacking_FiniteProjection`, `PlanarPacking_FiniteSplit`, `PlanarPacking_FiniteTail`, `PlanarPacking_FourierPairSupport`, `PlanarPacking_HexLattice`, `PlanarPacking_Indices`, `PlanarPacking_LatticeGaussian`, `PlanarPacking_MatrixInverse`, `PlanarPacking_MixedTaylor`, `PlanarPacking_RationalBounds`, `PlanarPacking_TableDensityBase`, `PlanarPacking_TableNorms`, `PlanarPacking_TailHead`, `PlanarPacking_TailHeadBounds`.
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`; the bundles `OAIQ098D000`, `OAIQ098D001` and `OAIQ098D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D086`, `OAIQ098D098`, `OAIQ098D100`, `OAIQ098D101`, `OAIQ098D102`, `OAIQ098D103`, `OAIQ098D105`, `OAIQ098D112`, `OAIQ098D113`, `OAIQ098D116`, `OAIQ098D120`, `OAIQ098D121`, `OAIQ098D122`, `OAIQ098D124`, `OAIQ098D125`, `OAIQ098D127`, `OAIQ098D128`, `OAIQ098D129`, `OAIQ098D131`, `OAIQ098D132`, `OAIQ098D136`, `OAIQ098D137`, `OAIQ098D156`, `OAIQ098D157`, `OAIQ098D158`, `OAIQ098D159`, `OAIQ098D161`, `OAIQ098D164`, `OAIQ098D167`, `OAIQ098D168`, `OAIQ098D169`, `OAIQ098D170`, `OAIQ098D172`, `OAIQ098D174`, `OAIQ098D175`, `OAIQ098D177`, `OAIQ098D180`, `OAIQ098D182`, `OAIQ098D184`, `OAIQ098D186`, `OAIQ098D187`, `OAIQ098D188`, `OAIQ098D190`, `OAIQ098D191`, `OAIQ098D192`, `OAIQ098D198`, `OAIQ098D199`, `OAIQ098D202`, `OAIQ098D203`, `OAIQ098D205`, `OAIQ098D206`, `OAIQ098D208`, `OAIQ098D212`, `OAIQ098D214`, `OAIQ098D215`, `OAIQ098D217`, `OAIQ098D219`, `OAIQ098D220`, `OAIQ098D221`, `OAIQ098D223`, `OAIQ098D225`, `OAIQ098D228`, `OAIQ098D231`, `OAIQ098D242`, `OAIQ098D244`, `OAIQ098D247`, `OAIQ098D250`, `OAIQ098D254`, `OAIQ098D255`, `OAIQ098D256`, `OAIQ098D257`, `OAIQ098D259` and `OAIQ098D260`; the statements `OAI.SharpPlanar.Pmoment_norm_bound`, `OAI.SharpPlanar.atomIntCap_nonneg`, `OAI.SharpPlanar.atomL_le_intCap`, `OAI.SharpPlanar.atomL_nonneg`, `OAI.SharpPlanar.atomicEnvelope_le_rat`, `OAI.SharpPlanar.atomicEnvelope_nonneg`, `OAI.SharpPlanar.coarse_12_17`, `OAI.SharpPlanar.coarse_12_18`, `OAI.SharpPlanar.coarse_12_19`, `OAI.SharpPlanar.coarse_12_20`, `OAI.SharpPlanar.coarse_12_21`, `OAI.SharpPlanar.coarse_12_22`, `OAI.SharpPlanar.coarse_12_23`, `OAI.SharpPlanar.coarse_12_24`, `OAI.SharpPlanar.coarse_12_25`, `OAI.SharpPlanar.coarse_12_26`, `OAI.SharpPlanar.coarse_12_27`, `OAI.SharpPlanar.coarse_12_28`, `OAI.SharpPlanar.coarse_12_29`, `OAI.SharpPlanar.coarse_12_30`, `OAI.SharpPlanar.coarse_13_13`, `OAI.SharpPlanar.coarse_13_14`, `OAI.SharpPlanar.coarse_13_15`, `OAI.SharpPlanar.coarse_13_16`, `OAI.SharpPlanar.coarse_13_17`, `OAI.SharpPlanar.coarse_13_18`, `OAI.SharpPlanar.coarse_13_19`, `OAI.SharpPlanar.coarse_13_20`, `OAI.SharpPlanar.coarse_13_21`, `OAI.SharpPlanar.coarse_13_22`, `OAI.SharpPlanar.coarse_13_23`, `OAI.SharpPlanar.coarse_13_24`, `OAI.SharpPlanar.coarse_13_25`, `OAI.SharpPlanar.coarse_13_26`, `OAI.SharpPlanar.coarse_13_27`, `OAI.SharpPlanar.coarse_13_28`, `OAI.SharpPlanar.coarse_13_29`, `OAI.SharpPlanar.coarse_13_30`, `OAI.SharpPlanar.coarse_16_17`, `OAI.SharpPlanar.coarse_16_18`, `OAI.SharpPlanar.coarse_16_19`, `OAI.SharpPlanar.coarse_16_20`, `OAI.SharpPlanar.coarse_16_21`, `OAI.SharpPlanar.coarse_16_22`, `OAI.SharpPlanar.coarse_16_23`, `OAI.SharpPlanar.coarse_16_24`, `OAI.SharpPlanar.coarse_16_25`, `OAI.SharpPlanar.coarse_16_26`, `OAI.SharpPlanar.coarse_16_27`, `OAI.SharpPlanar.coarse_16_28`, `OAI.SharpPlanar.coarse_16_29`, `OAI.SharpPlanar.coarse_16_30`, `OAI.SharpPlanar.coarse_21_18`, `OAI.SharpPlanar.coarse_21_19`, `OAI.SharpPlanar.coarse_21_20`, `OAI.SharpPlanar.coarse_21_21`, `OAI.SharpPlanar.coarse_21_22`, `OAI.SharpPlanar.coarse_21_23`, `OAI.SharpPlanar.coarse_21_24`, `OAI.SharpPlanar.coarse_21_25`, `OAI.SharpPlanar.coarse_21_26`, `OAI.SharpPlanar.coarse_21_27`, `OAI.SharpPlanar.coarse_21_28`, `OAI.SharpPlanar.coarse_21_29`, `OAI.SharpPlanar.coarse_21_30`, `OAI.SharpPlanar.coarse_24_14`, `OAI.SharpPlanar.coarse_24_15`, `OAI.SharpPlanar.coarse_24_16`, `OAI.SharpPlanar.coarse_24_17`, `OAI.SharpPlanar.coarse_24_18`, `OAI.SharpPlanar.coarse_24_19`, `OAI.SharpPlanar.coarse_24_20`, `OAI.SharpPlanar.coarse_24_21`, `OAI.SharpPlanar.coarse_24_22`, `OAI.SharpPlanar.coarse_24_23`, `OAI.SharpPlanar.coarse_24_24`, `OAI.SharpPlanar.coarse_24_25`, `OAI.SharpPlanar.coarse_24_26`, `OAI.SharpPlanar.coarse_24_27`, `OAI.SharpPlanar.coarse_24_28`, `OAI.SharpPlanar.coarse_24_29`, `OAI.SharpPlanar.coarse_24_30`, `OAI.SharpPlanar.coarse_25_13`, `OAI.SharpPlanar.coarse_25_14`, `OAI.SharpPlanar.coarse_25_15`, `OAI.SharpPlanar.coarse_25_16`, `OAI.SharpPlanar.coarse_25_17`, `OAI.SharpPlanar.coarse_25_18`, `OAI.SharpPlanar.coarse_25_19`, `OAI.SharpPlanar.coarse_25_20`, `OAI.SharpPlanar.coarse_25_21`, `OAI.SharpPlanar.coarse_25_22`, `OAI.SharpPlanar.coarse_25_23`, `OAI.SharpPlanar.coarse_25_24`, `OAI.SharpPlanar.coarse_25_25`, `OAI.SharpPlanar.coarse_25_26`, `OAI.SharpPlanar.coarse_25_27`, `OAI.SharpPlanar.coarse_25_28`, `OAI.SharpPlanar.coarse_25_29`, `OAI.SharpPlanar.coarse_25_30`, `OAI.SharpPlanar.coarse_31_15`, `OAI.SharpPlanar.coarse_31_16`, `OAI.SharpPlanar.coarse_31_17`, `OAI.SharpPlanar.coarse_31_18`, `OAI.SharpPlanar.coarse_31_19`, `OAI.SharpPlanar.coarse_31_20`, `OAI.SharpPlanar.coarse_31_21`, `OAI.SharpPlanar.coarse_31_22`, `OAI.SharpPlanar.coarse_31_23`, `OAI.SharpPlanar.coarse_31_24`, `OAI.SharpPlanar.coarse_31_25`, `OAI.SharpPlanar.coarse_31_26`, `OAI.SharpPlanar.coarse_31_27`, `OAI.SharpPlanar.coarse_31_28`, `OAI.SharpPlanar.coarse_31_29`, `OAI.SharpPlanar.coarse_31_30`, `OAI.SharpPlanar.coarse_33_15`, `OAI.SharpPlanar.coarse_33_16`, `OAI.SharpPlanar.coarse_33_17`, `OAI.SharpPlanar.coarse_33_18`, `OAI.SharpPlanar.coarse_33_19`, `OAI.SharpPlanar.coarse_33_20`, `OAI.SharpPlanar.coarse_33_21`, `OAI.SharpPlanar.coarse_33_22`, `OAI.SharpPlanar.coarse_33_23`, `OAI.SharpPlanar.coarse_33_24`, `OAI.SharpPlanar.coarse_33_25`, `OAI.SharpPlanar.coarse_33_26`, `OAI.SharpPlanar.coarse_33_27`, `OAI.SharpPlanar.coarse_33_28`, `OAI.SharpPlanar.coarse_33_29`, `OAI.SharpPlanar.coarse_33_30`, `OAI.SharpPlanar.coarse_36_15`, `OAI.SharpPlanar.coarse_36_16`, `OAI.SharpPlanar.coarse_36_17`, `OAI.SharpPlanar.coarse_36_18`, `OAI.SharpPlanar.coarse_36_19`, `OAI.SharpPlanar.coarse_36_20`, `OAI.SharpPlanar.coarse_36_21`, `OAI.SharpPlanar.coarse_36_22`, `OAI.SharpPlanar.coarse_36_23`, `OAI.SharpPlanar.coarse_36_24`, `OAI.SharpPlanar.coarse_36_25`, `OAI.SharpPlanar.coarse_36_26`, `OAI.SharpPlanar.coarse_36_27`, `OAI.SharpPlanar.coarse_36_28`, `OAI.SharpPlanar.coarse_36_29`, `OAI.SharpPlanar.coarse_36_30`, `OAI.SharpPlanar.coarse_37_15`, `OAI.SharpPlanar.coarse_37_16`, `OAI.SharpPlanar.coarse_37_17`, `OAI.SharpPlanar.coarse_37_18`, `OAI.SharpPlanar.coarse_37_19`, `OAI.SharpPlanar.coarse_37_20`, `OAI.SharpPlanar.coarse_37_21`, `OAI.SharpPlanar.coarse_37_22`, `OAI.SharpPlanar.coarse_37_23`, `OAI.SharpPlanar.coarse_37_24`, `OAI.SharpPlanar.coarse_37_25`, `OAI.SharpPlanar.coarse_37_26`, `OAI.SharpPlanar.coarse_37_27`, `OAI.SharpPlanar.coarse_37_28`, `OAI.SharpPlanar.coarse_37_29`, `OAI.SharpPlanar.coarse_37_30`, `OAI.SharpPlanar.coarse_39_14`, `OAI.SharpPlanar.coarse_39_15`, `OAI.SharpPlanar.coarse_39_16`, `OAI.SharpPlanar.coarse_39_17`, `OAI.SharpPlanar.coarse_39_18`, `OAI.SharpPlanar.coarse_39_19`, `OAI.SharpPlanar.coarse_39_20`, `OAI.SharpPlanar.coarse_39_21`, `OAI.SharpPlanar.coarse_39_22`, `OAI.SharpPlanar.coarse_39_23`, `OAI.SharpPlanar.coarse_39_24`, `OAI.SharpPlanar.coarse_39_25`, `OAI.SharpPlanar.coarse_39_26`, `OAI.SharpPlanar.coarse_39_27`, `OAI.SharpPlanar.coarse_39_28`, `OAI.SharpPlanar.coarse_39_29`, `OAI.SharpPlanar.coarse_39_30`, `OAI.SharpPlanar.coarse_3_14`, `OAI.SharpPlanar.coarse_3_15`, `OAI.SharpPlanar.coarse_3_16`, `OAI.SharpPlanar.coarse_3_17`, `OAI.SharpPlanar.coarse_3_18`, `OAI.SharpPlanar.coarse_3_19`, `OAI.SharpPlanar.coarse_3_20`, `OAI.SharpPlanar.coarse_3_21`, `OAI.SharpPlanar.coarse_3_22`, `OAI.SharpPlanar.coarse_3_23`, `OAI.SharpPlanar.coarse_3_24`, `OAI.SharpPlanar.coarse_3_25`, `OAI.SharpPlanar.coarse_3_26`, `OAI.SharpPlanar.coarse_3_27`, `OAI.SharpPlanar.coarse_3_28`, `OAI.SharpPlanar.coarse_3_29`, `OAI.SharpPlanar.coarse_3_30`, `OAI.SharpPlanar.coarse_40_14`, `OAI.SharpPlanar.coarse_40_15`, `OAI.SharpPlanar.coarse_40_16`, `OAI.SharpPlanar.coarse_40_17`, `OAI.SharpPlanar.coarse_40_18`, `OAI.SharpPlanar.coarse_40_19`, `OAI.SharpPlanar.coarse_40_20`, `OAI.SharpPlanar.coarse_40_21`, `OAI.SharpPlanar.coarse_40_22`, `OAI.SharpPlanar.coarse_40_23`, `OAI.SharpPlanar.coarse_40_24`, `OAI.SharpPlanar.coarse_40_25`, `OAI.SharpPlanar.coarse_40_26`, `OAI.SharpPlanar.coarse_40_27`, `OAI.SharpPlanar.coarse_40_28`, `OAI.SharpPlanar.coarse_40_29`, `OAI.SharpPlanar.coarse_40_30`, `OAI.SharpPlanar.coarse_4_20`, `OAI.SharpPlanar.coarse_4_21`, `OAI.SharpPlanar.coarse_4_22`, `OAI.SharpPlanar.coarse_4_23`, `OAI.SharpPlanar.coarse_4_24`, `OAI.SharpPlanar.coarse_4_25`, `OAI.SharpPlanar.coarse_4_26`, `OAI.SharpPlanar.coarse_4_27`, `OAI.SharpPlanar.coarse_4_28`, `OAI.SharpPlanar.coarse_4_29`, `OAI.SharpPlanar.coarse_4_30`, `OAI.SharpPlanar.coarse_7_17`, `OAI.SharpPlanar.coarse_7_18`, `OAI.SharpPlanar.coarse_7_19`, `OAI.SharpPlanar.coarse_7_20`, `OAI.SharpPlanar.coarse_7_21`, `OAI.SharpPlanar.coarse_7_22`, `OAI.SharpPlanar.coarse_7_23`, `OAI.SharpPlanar.coarse_7_24`, `OAI.SharpPlanar.coarse_7_25`, `OAI.SharpPlanar.coarse_7_26`, `OAI.SharpPlanar.coarse_7_27`, `OAI.SharpPlanar.coarse_7_28`, `OAI.SharpPlanar.coarse_7_29`, `OAI.SharpPlanar.coarse_7_30`, `OAI.SharpPlanar.coarse_9_16`, `OAI.SharpPlanar.coarse_9_18`, `OAI.SharpPlanar.coarse_9_19`, `OAI.SharpPlanar.coarse_9_20`, `OAI.SharpPlanar.coarse_9_21`, `OAI.SharpPlanar.coarse_9_22`, `OAI.SharpPlanar.coarse_9_23`, `OAI.SharpPlanar.coarse_9_24`, `OAI.SharpPlanar.coarse_9_25`, `OAI.SharpPlanar.coarse_9_26`, `OAI.SharpPlanar.coarse_9_27`, `OAI.SharpPlanar.coarse_9_28`, `OAI.SharpPlanar.coarse_9_29`, `OAI.SharpPlanar.coarse_9_30`, `OAI.SharpPlanar.directDensity_series`, `OAI.SharpPlanar.directEnvelope_le_rat`, `OAI.SharpPlanar.directEnvelope_nonneg`, `OAI.SharpPlanar.direct_piece_bound`, `OAI.SharpPlanar.direct_positive_series`, `OAI.SharpPlanar.direct_spectral_bound`, `OAI.SharpPlanar.massRational_nonneg`, `OAI.SharpPlanar.mixed_24_12`, `OAI.SharpPlanar.mixed_24_13`, `OAI.SharpPlanar.pieceIntCap_nonneg`, `OAI.SharpPlanar.pieceL_le_intCap`, `OAI.SharpPlanar.tableC_offnode`, `OAI.SharpPlanar.tableD_offnode`, `OAI.SharpPlanar.tableData_density`, `OAI.SharpPlanar.tableDensity_weighted`, `OAI.SharpPlanar.tableList_apply`, `OAI.SharpPlanar.tableList_discard`, `OAI.SharpPlanar.tableList_norm`, `OAI.SharpPlanar.table_coeff_mass`, `OAI.SharpPlanar.table_constant_bound`, `OAI.SharpPlanar.transformEnvelope_le_rat` and `OAI.SharpPlanar.transformEnvelope_nonneg`; the proofs of `OAI.SharpPlanar.Pmoment_norm_bound`, `OAI.SharpPlanar.atomBase_contains`, `OAI.SharpPlanar.atomIntCap_nonneg`, `OAI.SharpPlanar.atomL_le_intCap`, `OAI.SharpPlanar.atomL_nonneg`, `OAI.SharpPlanar.atomicEnvelope_le_rat`, `OAI.SharpPlanar.atomicEnvelope_nonneg`, `OAI.SharpPlanar.coarse_12_17`, `OAI.SharpPlanar.coarse_12_18`, `OAI.SharpPlanar.coarse_12_19`, `OAI.SharpPlanar.coarse_12_20`, `OAI.SharpPlanar.coarse_12_21`, `OAI.SharpPlanar.coarse_12_22`, `OAI.SharpPlanar.coarse_12_23`, `OAI.SharpPlanar.coarse_12_24`, `OAI.SharpPlanar.coarse_12_25`, `OAI.SharpPlanar.coarse_12_26`, `OAI.SharpPlanar.coarse_12_27`, `OAI.SharpPlanar.coarse_12_28`, `OAI.SharpPlanar.coarse_12_29`, `OAI.SharpPlanar.coarse_12_30`, `OAI.SharpPlanar.coarse_13_13`, `OAI.SharpPlanar.coarse_13_14`, `OAI.SharpPlanar.coarse_13_15`, `OAI.SharpPlanar.coarse_13_16`, `OAI.SharpPlanar.coarse_13_17`, `OAI.SharpPlanar.coarse_13_18`, `OAI.SharpPlanar.coarse_13_19`, `OAI.SharpPlanar.coarse_13_20`, `OAI.SharpPlanar.coarse_13_21`, `OAI.SharpPlanar.coarse_13_22`, `OAI.SharpPlanar.coarse_13_23`, `OAI.SharpPlanar.coarse_13_24`, `OAI.SharpPlanar.coarse_13_25`, `OAI.SharpPlanar.coarse_13_26`, `OAI.SharpPlanar.coarse_13_27`, `OAI.SharpPlanar.coarse_13_28`, `OAI.SharpPlanar.coarse_13_29`, `OAI.SharpPlanar.coarse_13_30`, `OAI.SharpPlanar.coarse_16_17`, `OAI.SharpPlanar.coarse_16_18`, `OAI.SharpPlanar.coarse_16_19`, `OAI.SharpPlanar.coarse_16_20`, `OAI.SharpPlanar.coarse_16_21`, `OAI.SharpPlanar.coarse_16_22`, `OAI.SharpPlanar.coarse_16_23`, `OAI.SharpPlanar.coarse_16_24`, `OAI.SharpPlanar.coarse_16_25`, `OAI.SharpPlanar.coarse_16_26`, `OAI.SharpPlanar.coarse_16_27`, `OAI.SharpPlanar.coarse_16_28`, `OAI.SharpPlanar.coarse_16_29`, `OAI.SharpPlanar.coarse_16_30`, `OAI.SharpPlanar.coarse_21_18`, `OAI.SharpPlanar.coarse_21_19`, `OAI.SharpPlanar.coarse_21_20`, `OAI.SharpPlanar.coarse_21_21`, `OAI.SharpPlanar.coarse_21_22`, `OAI.SharpPlanar.coarse_21_23`, `OAI.SharpPlanar.coarse_21_24`, `OAI.SharpPlanar.coarse_21_25`, `OAI.SharpPlanar.coarse_21_26`, `OAI.SharpPlanar.coarse_21_27`, `OAI.SharpPlanar.coarse_21_28`, `OAI.SharpPlanar.coarse_21_29`, `OAI.SharpPlanar.coarse_21_30`, `OAI.SharpPlanar.coarse_24_14`, `OAI.SharpPlanar.coarse_24_15`, `OAI.SharpPlanar.coarse_24_16`, `OAI.SharpPlanar.coarse_24_17`, `OAI.SharpPlanar.coarse_24_18`, `OAI.SharpPlanar.coarse_24_19`, `OAI.SharpPlanar.coarse_24_20`, `OAI.SharpPlanar.coarse_24_21`, `OAI.SharpPlanar.coarse_24_22`, `OAI.SharpPlanar.coarse_24_23`, `OAI.SharpPlanar.coarse_24_24`, `OAI.SharpPlanar.coarse_24_25`, `OAI.SharpPlanar.coarse_24_26`, `OAI.SharpPlanar.coarse_24_27`, `OAI.SharpPlanar.coarse_24_28`, `OAI.SharpPlanar.coarse_24_29`, `OAI.SharpPlanar.coarse_24_30`, `OAI.SharpPlanar.coarse_25_13`, `OAI.SharpPlanar.coarse_25_14`, `OAI.SharpPlanar.coarse_25_15`, `OAI.SharpPlanar.coarse_25_16`, `OAI.SharpPlanar.coarse_25_17`, `OAI.SharpPlanar.coarse_25_18`, `OAI.SharpPlanar.coarse_25_19`, `OAI.SharpPlanar.coarse_25_20`, `OAI.SharpPlanar.coarse_25_21`, `OAI.SharpPlanar.coarse_25_22`, `OAI.SharpPlanar.coarse_25_23`, `OAI.SharpPlanar.coarse_25_24`, `OAI.SharpPlanar.coarse_25_25`, `OAI.SharpPlanar.coarse_25_26`, `OAI.SharpPlanar.coarse_25_27`, `OAI.SharpPlanar.coarse_25_28`, `OAI.SharpPlanar.coarse_25_29`, `OAI.SharpPlanar.coarse_25_30`, `OAI.SharpPlanar.coarse_31_15`, `OAI.SharpPlanar.coarse_31_16`, `OAI.SharpPlanar.coarse_31_17`, `OAI.SharpPlanar.coarse_31_18`, `OAI.SharpPlanar.coarse_31_19`, `OAI.SharpPlanar.coarse_31_20`, `OAI.SharpPlanar.coarse_31_21`, `OAI.SharpPlanar.coarse_31_22`, `OAI.SharpPlanar.coarse_31_23`, `OAI.SharpPlanar.coarse_31_24`, `OAI.SharpPlanar.coarse_31_25`, `OAI.SharpPlanar.coarse_31_26`, `OAI.SharpPlanar.coarse_31_27`, `OAI.SharpPlanar.coarse_31_28`, `OAI.SharpPlanar.coarse_31_29`, `OAI.SharpPlanar.coarse_31_30`, `OAI.SharpPlanar.coarse_33_15`, `OAI.SharpPlanar.coarse_33_16`, `OAI.SharpPlanar.coarse_33_17`, `OAI.SharpPlanar.coarse_33_18`, `OAI.SharpPlanar.coarse_33_19`, `OAI.SharpPlanar.coarse_33_20`, `OAI.SharpPlanar.coarse_33_21`, `OAI.SharpPlanar.coarse_33_22`, `OAI.SharpPlanar.coarse_33_23`, `OAI.SharpPlanar.coarse_33_24`, `OAI.SharpPlanar.coarse_33_25`, `OAI.SharpPlanar.coarse_33_26`, `OAI.SharpPlanar.coarse_33_27`, `OAI.SharpPlanar.coarse_33_28`, `OAI.SharpPlanar.coarse_33_29`, `OAI.SharpPlanar.coarse_33_30`, `OAI.SharpPlanar.coarse_36_15`, `OAI.SharpPlanar.coarse_36_16`, `OAI.SharpPlanar.coarse_36_17`, `OAI.SharpPlanar.coarse_36_18`, `OAI.SharpPlanar.coarse_36_19`, `OAI.SharpPlanar.coarse_36_20`, `OAI.SharpPlanar.coarse_36_21`, `OAI.SharpPlanar.coarse_36_22`, `OAI.SharpPlanar.coarse_36_23`, `OAI.SharpPlanar.coarse_36_24`, `OAI.SharpPlanar.coarse_36_25`, `OAI.SharpPlanar.coarse_36_26`, `OAI.SharpPlanar.coarse_36_27`, `OAI.SharpPlanar.coarse_36_28`, `OAI.SharpPlanar.coarse_36_29`, `OAI.SharpPlanar.coarse_36_30`, `OAI.SharpPlanar.coarse_37_15`, `OAI.SharpPlanar.coarse_37_16`, `OAI.SharpPlanar.coarse_37_17`, `OAI.SharpPlanar.coarse_37_18`, `OAI.SharpPlanar.coarse_37_19`, `OAI.SharpPlanar.coarse_37_20`, `OAI.SharpPlanar.coarse_37_21`, `OAI.SharpPlanar.coarse_37_22`, `OAI.SharpPlanar.coarse_37_23`, `OAI.SharpPlanar.coarse_37_24`, `OAI.SharpPlanar.coarse_37_25`, `OAI.SharpPlanar.coarse_37_26`, `OAI.SharpPlanar.coarse_37_27`, `OAI.SharpPlanar.coarse_37_28`, `OAI.SharpPlanar.coarse_37_29`, `OAI.SharpPlanar.coarse_37_30`, `OAI.SharpPlanar.coarse_39_14`, `OAI.SharpPlanar.coarse_39_15`, `OAI.SharpPlanar.coarse_39_16`, `OAI.SharpPlanar.coarse_39_17`, `OAI.SharpPlanar.coarse_39_18`, `OAI.SharpPlanar.coarse_39_19`, `OAI.SharpPlanar.coarse_39_20`, `OAI.SharpPlanar.coarse_39_21`, `OAI.SharpPlanar.coarse_39_22`, `OAI.SharpPlanar.coarse_39_23`, `OAI.SharpPlanar.coarse_39_24`, `OAI.SharpPlanar.coarse_39_25`, `OAI.SharpPlanar.coarse_39_26`, `OAI.SharpPlanar.coarse_39_27`, `OAI.SharpPlanar.coarse_39_28`, `OAI.SharpPlanar.coarse_39_29`, `OAI.SharpPlanar.coarse_39_30`, `OAI.SharpPlanar.coarse_3_14`, `OAI.SharpPlanar.coarse_3_15`, `OAI.SharpPlanar.coarse_3_16`, `OAI.SharpPlanar.coarse_3_17`, `OAI.SharpPlanar.coarse_3_18`, `OAI.SharpPlanar.coarse_3_19`, `OAI.SharpPlanar.coarse_3_20`, `OAI.SharpPlanar.coarse_3_21`, `OAI.SharpPlanar.coarse_3_22`, `OAI.SharpPlanar.coarse_3_23`, `OAI.SharpPlanar.coarse_3_24`, `OAI.SharpPlanar.coarse_3_25`, `OAI.SharpPlanar.coarse_3_26`, `OAI.SharpPlanar.coarse_3_27`, `OAI.SharpPlanar.coarse_3_28`, `OAI.SharpPlanar.coarse_3_29`, `OAI.SharpPlanar.coarse_3_30`, `OAI.SharpPlanar.coarse_40_14`, `OAI.SharpPlanar.coarse_40_15`, `OAI.SharpPlanar.coarse_40_16`, `OAI.SharpPlanar.coarse_40_17`, `OAI.SharpPlanar.coarse_40_18`, `OAI.SharpPlanar.coarse_40_19`, `OAI.SharpPlanar.coarse_40_20`, `OAI.SharpPlanar.coarse_40_21`, `OAI.SharpPlanar.coarse_40_22`, `OAI.SharpPlanar.coarse_40_23`, `OAI.SharpPlanar.coarse_40_24`, `OAI.SharpPlanar.coarse_40_25`, `OAI.SharpPlanar.coarse_40_26`, `OAI.SharpPlanar.coarse_40_27`, `OAI.SharpPlanar.coarse_40_28`, `OAI.SharpPlanar.coarse_40_29`, `OAI.SharpPlanar.coarse_40_30`, `OAI.SharpPlanar.coarse_4_20`, `OAI.SharpPlanar.coarse_4_21`, `OAI.SharpPlanar.coarse_4_22`, `OAI.SharpPlanar.coarse_4_23`, `OAI.SharpPlanar.coarse_4_24`, `OAI.SharpPlanar.coarse_4_25`, `OAI.SharpPlanar.coarse_4_26`, `OAI.SharpPlanar.coarse_4_27`, `OAI.SharpPlanar.coarse_4_28`, `OAI.SharpPlanar.coarse_4_29`, `OAI.SharpPlanar.coarse_4_30`, `OAI.SharpPlanar.coarse_7_17`, `OAI.SharpPlanar.coarse_7_18`, `OAI.SharpPlanar.coarse_7_19`, `OAI.SharpPlanar.coarse_7_20`, `OAI.SharpPlanar.coarse_7_21`, `OAI.SharpPlanar.coarse_7_22`, `OAI.SharpPlanar.coarse_7_23`, `OAI.SharpPlanar.coarse_7_24`, `OAI.SharpPlanar.coarse_7_25`, `OAI.SharpPlanar.coarse_7_26`, `OAI.SharpPlanar.coarse_7_27`, `OAI.SharpPlanar.coarse_7_28`, `OAI.SharpPlanar.coarse_7_29`, `OAI.SharpPlanar.coarse_7_30`, `OAI.SharpPlanar.coarse_9_16`, `OAI.SharpPlanar.coarse_9_18`, `OAI.SharpPlanar.coarse_9_19`, `OAI.SharpPlanar.coarse_9_20`, `OAI.SharpPlanar.coarse_9_21`, `OAI.SharpPlanar.coarse_9_22`, `OAI.SharpPlanar.coarse_9_23`, `OAI.SharpPlanar.coarse_9_24`, `OAI.SharpPlanar.coarse_9_25`, `OAI.SharpPlanar.coarse_9_26`, `OAI.SharpPlanar.coarse_9_27`, `OAI.SharpPlanar.coarse_9_28`, `OAI.SharpPlanar.coarse_9_29`, `OAI.SharpPlanar.coarse_9_30`, `OAI.SharpPlanar.decay_atomBase`, `OAI.SharpPlanar.directDensity_series`, `OAI.SharpPlanar.directEnvelope_le_rat`, `OAI.SharpPlanar.directEnvelope_nonneg`, `OAI.SharpPlanar.direct_positive_series`, `OAI.SharpPlanar.direct_spectral_bound`, `OAI.SharpPlanar.massRational_nonneg`, `OAI.SharpPlanar.mixed_24_12`, `OAI.SharpPlanar.mixed_24_13`, `OAI.SharpPlanar.pieceIntCap_nonneg`, `OAI.SharpPlanar.pieceL_le_intCap`, `OAI.SharpPlanar.tableC_offnode`, `OAI.SharpPlanar.tableD_offnode`, `OAI.SharpPlanar.tableData_density`, `OAI.SharpPlanar.tableDensity_weighted`, `OAI.SharpPlanar.tableList_apply`, `OAI.SharpPlanar.tableList_discard`, `OAI.SharpPlanar.tableList_norm`, `OAI.SharpPlanar.table_coeff_mass`, `OAI.SharpPlanar.table_constant_bound`, `OAI.SharpPlanar.transformEnvelope_le_rat` and `OAI.SharpPlanar.transformEnvelope_nonneg`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098D000
import Definitions.Def_OAIQ098D001
import Definitions.Def_OAIQ098D002

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

noncomputable def fixed₁ (x : X) : CardinalData := ⟨-13/1000, 1, 11/25, x⟩
noncomputable def fixed₂ (x : X) : CardinalData := ⟨17/1000, 0, -46/125, x⟩

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma kernel_den_sq (t : ℝ) : ‖(t:ℂ)+Complex.I*h‖^2 = t^2+h^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,pow_two]
lemma lambda_sq (t : ℝ) : ‖lambda t‖^2 = (4/3:ℝ)/(t^2+h^2) := by
  rw [lambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos b_pos,div_pow,mul_pow,kernel_den_sq,b_sq]
  field_simp

lemma lambda_sq_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖lambda t‖^2 ≤ ‖lambda s‖^2 := by
  rw [lambda_sq,lambda_sq]
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith

lemma piece_secant_bound (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    slopeCap j*(t^2+h^2)*((((j.val:ℝ)+1)/6)^2+h^2) ≤
      h*B*(t+((j.val:ℝ)+1)/6) := by
  have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
  fin_cases j <;> norm_num [slopeCap,h,B] at * <;> nlinarith

end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def uAmplitude (n j : ℕ) (t : ℝ) : ℂ :=
  -2*(Real.pi:ℂ)^2*(basisBeta n j-(t:ℂ)*basisAlpha n j)
noncomputable def vAmplitude (n j : ℕ) : ℂ :=
  2*Complex.I*Real.pi*basisAlpha n j

noncomputable def densityCap (j : Fin 6) : ℝ := (densityNum j:ℝ)/(densityDen j:ℝ)
lemma u_norm_amplitude (n j : ℕ) (t : ℝ) : ‖u n j t‖ = ‖uAmplitude n j t‖ := by
  rw [u_factored]
  have he : -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) = Complex.exp (-Complex.I*Real.pi*t*n)*uAmplitude n j t := by
    unfold uAmplitude; ring
  rw [he,norm_mul,unit_phase_norm,one_mul]
lemma v_norm_amplitude (n j : ℕ) (t : ℝ) : ‖v n j t‖ = ‖vAmplitude n j‖ := by
  rw [v_factored]
  have he : 2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j =
      Complex.exp (-Complex.I*Real.pi*t*n)*vAmplitude n j := by
    unfold vAmplitude; ring
  rw [he,norm_mul,unit_phase_norm,one_mul]


end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerBasis

lemma densityCap_nonneg (j : Fin 6) : 0 ≤ densityCap j := by
  fin_cases j <;> norm_num [densityCap,densityNum,densityDen]

lemma lambdaCap_nonneg (j : Fin 7) : 0 ≤ lambdaCap j := by fin_cases j <;> norm_num [lambdaCap]
lemma dampingCap_pos (j : Fin 7) : 0 < dampingCap j := by fin_cases j <;> norm_num [dampingCap]
lemma slopeCap_nonneg (j : Fin 6) : 0 ≤ slopeCap j := by fin_cases j <;> norm_num [slopeCap]

noncomputable def atomL (j : Fin 7) (s : ℝ) : ℝ :=
  atomMass j*lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)
noncomputable def segmentEnvelope (j : Fin 6) (ell : ℕ) (s t : ℝ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*(Real.pi*zCap ⟨j.val,by omega⟩)^ell *
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
    Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))

lemma pieceMass_nonneg (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceMass j s := by
  unfold pieceMass
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg _)) hs))

lemma segment_exp_integral_bound (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6,
      Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))) ≤ pieceMass j s := by
  have he := exp_segment_bound (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg j)) hs)
    (by linarith : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6)
  have hlen : ((j.val:ℝ)+1)/6-(j.val:ℝ)/6=1/6 := by ring
  simpa only [pieceMass,hlen,mul_assoc,mul_eq_zero,Real.pi_ne_zero,false_or] using he

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma segmentEnvelope_integral_bound (j : Fin 6) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, segmentEnvelope j ell s t) ≤
      pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
  unfold segmentEnvelope
  rw [intervalIntegral.integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left (segment_exp_integral_bound j hs)
    (mul_nonneg (mul_nonneg (lambdaCap_nonneg ⟨j.val,by omega⟩)
      (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg ⟨j.val,by omega⟩)) ell))
      (Real.exp_pos (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)).le)
  convert hb using 1 <;> first | rfl | (unfold pieceL; ring)

noncomputable def atomicCoefficient (j : Fin 7) : ℂ := if j.val=0 then Pcoeff 0 else 2*Pcoeff j.val
lemma atomicCoefficient_norm (j : Fin 7) : ‖atomicCoefficient j‖ = atomMass j := by
  fin_cases j <;> norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm,coeffMass]

end SharpPlanar

namespace SharpPlanar

lemma pieceMass_antitone (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    pieceMass j t ≤ pieceMass j s := by
  have ht : 0 ≤ t := hs.trans hst
  unfold pieceMass
  split_ifs with htz hsz hsz
  · rfl
  · exfalso
    have hz : slopeCap j*s=0 := by
      apply le_antisymm
      · calc
          _ ≤ slopeCap j*t := mul_le_mul_of_nonneg_left hst (slopeCap_nonneg _)
          _ = 0 := htz
      · exact mul_nonneg (slopeCap_nonneg _) hs
    exact hsz hz
  · exact min_le_left _ _
  · apply min_le_min_left
    apply one_div_le_one_div_of_le
    · have hh : 0 < slopeCap j*s := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg _) hs) (Ne.symm hsz)
      simpa only [mul_assoc] using mul_pos Real.pi_pos hh
    · exact mul_le_mul_of_nonneg_left hst (mul_nonneg Real.pi_pos.le (slopeCap_nonneg _))

lemma pieceL_nonneg (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceL j s := by
  exact mul_nonneg (mul_nonneg (lambdaCap_nonneg _) (Real.exp_pos _).le) (pieceMass_nonneg j hs)

lemma pieceL_shift_bound (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    pieceL j (s+t) ≤ Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t)*pieceL j s := by
  have hm := pieceMass_antitone j hs (show s ≤ s+t by linarith)
  unfold pieceL
  rw [mul_add,Real.exp_add]
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
        Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t))*pieceMass j s := by
      exact mul_le_mul_of_nonneg_left hm (mul_nonneg (lambdaCap_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    _ = _ := by ring

lemma pieceL_period_bound (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    pieceL j (s+12*k) ≤ (Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*pieceL j s := by
  have hh := pieceL_shift_bound j hs (by positivity : (0:ℝ) ≤ 12*k)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end SharpPlanar

namespace SharpPlanar
open IntegerBasis


noncomputable def rowFactor (j : Fin 6) (n : ℕ) : ℝ :=
  (1+|D n|+Real.pi*zCap ⟨j.val,by omega⟩)/Q n*densityCap j
noncomputable def rowPiece (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then rowFactor j n * pieceL j n else 0
noncomputable def rowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
    (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))

lemma rowFactor_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ rowFactor j n := by
  unfold rowFactor
  exact mul_nonneg (div_nonneg (by have hz := zCap_nonneg (⟨j.val,by omega⟩ : Fin 7); positivity) (Q_pos _).le) (densityCap_nonneg _)
lemma rowFactor_periodic (j : Fin 6) (n k : ℕ) : rowFactor j (n+12*k) = rowFactor j n := by
  have hmod : (n+12*k)%12 = n%12 := by omega
  unfold rowFactor Q D
  rw [hmod]
lemma rowPiece_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ rowPiece j n := by
  unfold rowPiece
  split_ifs
  · exact mul_nonneg (rowFactor_nonneg _ _) (pieceL_nonneg _ (Nat.cast_nonneg _))
  · rfl
lemma rowPiece_period_bound (j : Fin 6) (n k : ℕ) :
    rowPiece j (n+12*k) ≤ (Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*rowPiece j n := by
  have hmod : (n+12*k)%12 = n%12 := by omega
  unfold rowPiece
  rw [hmod]
  split_ifs with hn
  · rw [rowFactor_periodic]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ rowFactor j n*((Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*pieceL j n) :=
        mul_le_mul_of_nonneg_left (pieceL_period_bound j (Nat.cast_nonneg _) k) (rowFactor_nonneg _ _)
      _ = _ := by ring
  · simp

lemma rowPiece_tail_sum (j : Fin 6) (N : ℕ) :
    Summable (fun n : ℕ => rowPiece j (N+1+n)) ∧
    (∑' n : ℕ, rowPiece j (N+1+n)) ≤
      (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
        (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩)) := by
  apply periodic_geometric_sum (fun _ => rowPiece_nonneg j _) (Real.exp_pos _).le
  · apply Real.exp_lt_one_iff.mpr
    have hg := dampingCap_pos (⟨j.val+1,by omega⟩ : Fin 7)
    nlinarith [Real.pi_pos,mul_pos Real.pi_pos hg]
  · intro a k
    convert rowPiece_period_bound j (N+1+a.val) k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma rowTailNorm_summable (x : X) (N : ℕ) :
    Summable (fun n : {n : Node // N<n.val} => |x (n.val,false)|+|x (n.val,true)|) := by
  exact (X_summable_pairs x).subtype _

lemma natural_row_tail_summable (N : ℕ) :
    Summable (fun k : ℕ => ∑ j : Fin 6, rowPiece j (N+1+k)) := by
  exact (hasSum_sum (fun j _ => (rowPiece_tail_sum j N).1.hasSum)).summable

lemma natural_row_tail_bound (N : ℕ) :
    (∑' k : ℕ, ∑ j : Fin 6, rowPiece j (N+1+k)) ≤ rowTable N := by
  rw [Summable.tsum_finsetSum (fun j _ => (rowPiece_tail_sum j N).1)]
  exact Finset.sum_le_sum (fun j _ => (rowPiece_tail_sum j N).2)


end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma b_fine : (86602/100000:ℝ) < b ∧ b < 86603/100000 := by
  constructor <;> nlinarith [b_pos,b_sq]

lemma rowQLower_bound (n : ℕ) (hn : n%12 ∈ residues) : 0 < rowQLower n ∧ rowQLower n < Q n := by
  have hp := pi_fine
  have hb := b_fine
  have hp2 : (314159/100000:ℝ)^2 < Real.pi^2 := by nlinarith [Real.pi_pos]
  have hsmall : (2*(314159/100000:ℝ)^2/3)*(2-2*(86603/100000)) < (2*Real.pi^2/3)*(2-2*b) := by
    gcongr; linarith
  have hlarge : (2*(314159/100000:ℝ)^2/3)*(2+2*(86602/100000)) < (2*Real.pi^2/3)*(2+2*b) := by
    gcongr; linarith
  rw [← Q_mod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    simp [rowQLower,hn,Q_0,Q_1,Q_3,Q_4,Q_7,Q_9] <;> nlinarith

lemma rowDUpper_bound (n : ℕ) (hn : n%12 ∈ residues) : |D n| < rowDUpper n := by
  have hp := pi_fine
  have hb := b_fine
  have hpb : Real.pi*b < (31416/10000:ℝ)*(86603/100000) := by gcongr <;> linarith
  have hpb0 : (314159/100000:ℝ)*(86602/100000) < Real.pi*b := by gcongr <;> linarith
  have hpbpos : 0 < Real.pi*b := mul_pos Real.pi_pos b_pos
  rw [← D_mod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    norm_num [rowDUpper,hn]
  all_goals first | rw [D_0] | rw [D_1] | rw [D_3] | rw [D_4] | rw [D_7] | rw [D_9]
  all_goals apply abs_lt.mpr; constructor <;> nlinarith

end SharpPlanar

namespace SharpPlanar
open IntegerBasis
lemma pieceBase_contains (j : Fin 6) :
    Real.exp (-(314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩) ≤ pieceBase j := by
  have hg : 0 ≤ (314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩ := by
    exact mul_nonneg (by norm_num) (dampingCap_pos _).le
  have hp := Real.sum_le_exp_of_nonneg hg 20
  rw [neg_mul,Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  have ht : 1 ≤ pieceBase j * (∑ i ∈ Finset.range 20,
      ((314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩)^i/(i.factorial:ℝ)) := by
    fin_cases j <;> norm_num [pieceBase,dampingCap,Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hp (pieceBase_pos j).le)

lemma decay_pieceBase (j : Fin 6) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*n) ≤ pieceBase j^n := by
  have he : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩) ≤ pieceBase j :=
    (Real.exp_le_exp.mpr (by nlinarith [pi_fine,(dampingCap_pos ⟨j.val+1,by omega⟩)])).trans
      (pieceBase_contains j)
  rw [mul_comm _ (n:ℝ),Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he n

noncomputable def massRational (j : Fin 6) (n : ℕ) : ℝ :=
  if slopeCap j*(n:ℝ)=0 then 1/6 else min (1/6) (1/((314159/100000:ℝ)*slopeCap j*n))
lemma pieceMass_le (j : Fin 6) (n : ℕ) : pieceMass j n ≤ massRational j n := by
  unfold pieceMass massRational
  split_ifs with hz
  · rfl
  · apply min_le_min_left
    have hpos : 0 < slopeCap j*(n:ℝ) := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg j) (Nat.cast_nonneg n)) (Ne.symm hz)
    apply one_div_le_one_div_of_le
    · nlinarith
    · nlinarith [pi_fine]

noncomputable def factorRational (j : Fin 6) (n : ℕ) : ℝ :=
  (1+rowDUpper n+(31416/10000:ℝ)*zCap ⟨j.val,by omega⟩)/rowQLower n*densityCap j
noncomputable def pieceRational (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then factorRational j n *
    (lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n) else 0
noncomputable def tableRational (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, pieceRational j (N+1+a.val))/(1-pieceBase j^12)
lemma factorRational_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ factorRational j n := by
  have hq : 0 ≤ rowQLower n := by unfold rowQLower; split_ifs <;> norm_num
  have hd : 0 ≤ rowDUpper n := by unfold rowDUpper; split_ifs <;> norm_num
  have hz := zCap_nonneg ⟨j.val,by omega⟩
  unfold factorRational
  exact mul_nonneg (div_nonneg (by positivity) hq) (densityCap_nonneg j)
lemma rowFactor_le (j : Fin 6) (n : ℕ) (hn : n%12 ∈ residues) :
    rowFactor j n ≤ factorRational j n := by
  unfold rowFactor factorRational
  have hq := rowQLower_bound n hn
  have hd := rowDUpper_bound n hn
  have hz := zCap_nonneg ⟨j.val,by omega⟩
  apply mul_le_mul_of_nonneg_right _ (densityCap_nonneg j)
  have hd0 : 0 ≤ rowDUpper n := (abs_nonneg (D n)).trans hd.le
  apply div_le_div₀ (by positivity)
  · exact add_le_add (add_le_add le_rfl hd.le) (mul_le_mul_of_nonneg_right pi_fine.2.le hz)
  · exact hq.1
  · exact hq.2.le
lemma rowPiece_le (j : Fin 6) (n : ℕ) : rowPiece j n ≤ pieceRational j n := by
  unfold rowPiece pieceRational
  split_ifs with hn
  · unfold pieceL
    apply mul_le_mul (rowFactor_le j n hn)
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (decay_pieceBase j n) (lambdaCap_nonneg _)
      · exact pieceMass_le j n
      · exact pieceMass_nonneg j (Nat.cast_nonneg n)
      · exact mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (pieceBase_pos j).le _)
    · exact pieceL_nonneg j (Nat.cast_nonneg n)
    · exact factorRational_nonneg j n
  · rfl
lemma rowTable_le (N : ℕ) : rowTable N ≤ tableRational N := by
  unfold rowTable tableRational
  apply Finset.sum_le_sum
  intro j _
  have hd : 0 < 1-pieceBase j^12 := sub_pos.mpr (pow_lt_one₀ (pieceBase_pos j).le (pieceBase_lt_one j) (by norm_num))
  apply div_le_div₀
  · exact Finset.sum_nonneg (fun a _ => (rowPiece_nonneg j _).trans (rowPiece_le j _))
  · exact Finset.sum_le_sum (fun a _ => rowPiece_le j _)
  · exact hd
  · have he := decay_pieceBase j 12
    have heq : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*(12:ℕ)) = Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩) := by congr 1; push_cast; ring
    rw [heq] at he
    exact sub_le_sub_left he 1

lemma tableRational_zero : tableRational 0 < 28 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]
lemma tableRational_four : tableRational 4 < 28/100 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]
lemma tableRational_sixteen : tableRational 16 < 15/1000 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]
lemma tableRational_hundred : tableRational 100 < 5/10^10 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]

theorem rowTable_bounds : rowTable 0 < 28 ∧ rowTable 4 < 28/100 ∧
    rowTable 16 < 15/1000 ∧ rowTable 100 < 5/10^10 :=
  ⟨(rowTable_le 0).trans_lt tableRational_zero,(rowTable_le 4).trans_lt tableRational_four,
    (rowTable_le 16).trans_lt tableRational_sixteen,(rowTable_le 100).trans_lt tableRational_hundred⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
noncomputable def atomRowFactor (j : Fin 7) (n : ℕ) : ℝ := (1+|D n|+Real.pi*zCap j)/Q n
noncomputable def atomRow (j : Fin 7) (n : ℕ) : ℝ :=
  if n%12∈residues then atomRowFactor j n*atomL j n else 0
noncomputable def atomRowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 7, (∑ a : Fin 12, atomRow j (N+1+a.val))/(1-Real.exp (-12*Real.pi*dampingCap j))
noncomputable def atomRowRat (j : Fin 7) (n : ℕ) : ℝ :=
  if n%12∈residues then atomFactorRat j n*(atomMass j*lambdaCap j*atomBase j^n) else 0
noncomputable def atomTableRat (N : ℕ) : ℝ := ∑ j : Fin 7,(∑ a : Fin 12,atomRowRat j (N+1+a.val))/(1-atomBase j^12)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BarrierProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpPlanar
open Set Filter
open scoped Topology

noncomputable def dividedP (a : ℕ) (u : ℝ) : ℝ :=
  (Real.pi/6)^2 * (Real.sinc (Real.pi*u/12))^2 *
    ∏ r ∈ residues.erase a, (2*Real.sin (Real.pi*(a+u-r)/12))^2

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

def node7 : Node := ⟨7,by norm_num [residues]⟩
def node9 : Node := ⟨9,by norm_num [residues]⟩
def node13 : Node := ⟨13,by norm_num [residues]⟩
def node15 : Node := ⟨15,by norm_num [residues]⟩
def node16 : Node := ⟨16,by norm_num [residues]⟩
def lNode : Fin 12 → Node := ![node7,node9,node12,node13,node15,node16,node7,node9,node12,node13,node15,node16]
open scoped BigOperators
def lowExteriorIndex (i : Fin 12) : Node × Bool := (lNode i,lDeriv i)
lemma lowExteriorIndex_injective : Function.Injective lowExteriorIndex := by decide +kernel
lemma finiteIndex_bound (i : FiniteIndex) : (finiteIndex i).1.val ≤ 100 := by revert i; decide +kernel
lemma lowExteriorIndex_bound (i : Fin 12) : 4 < (lowExteriorIndex i).1.val ∧ (lowExteriorIndex i).1.val ≤ 16 := by revert i; decide +kernel
lemma finiteIndex_cover_check : ∀ n : Fin 101, 0<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : FiniteIndex, (finiteIndex i).1.val=n.val ∧ (finiteIndex i).2=d := by decide +kernel
lemma finiteIndex_range (n : Node) (d : Bool) : (∃ i, finiteIndex i = (n,d)) ↔ n.val ≤ 100 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := finiteIndex_bound i
    simpa only [hi] using hh
  · intro hn
    obtain ⟨i,hin,hid⟩ := finiteIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hn⟩ n.prop d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
lemma lowExteriorIndex_cover_check : ∀ n : Fin 17, 4<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : Fin 12, (lowExteriorIndex i).1.val=n.val ∧ (lowExteriorIndex i).2=d := by decide +kernel
lemma lowExteriorIndex_range (n : Node) (d : Bool) : (∃ i, lowExteriorIndex i = (n,d)) ↔ 4<n.val ∧ n.val ≤ 16 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := lowExteriorIndex_bound i
    simpa only [hi] using hh
  · rintro ⟨hn,hm⟩
    obtain ⟨i,hin,hid⟩ := lowExteriorIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hm⟩ ⟨hn,n.prop.2⟩ d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LEntries
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
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def lentry6_0 : RBox := ⟨(-428037821451401034679013730),(-428037821451401027790023895)⟩
noncomputable def lentry7_0 : RBox := ⟨(-596386320756599937937491488),(-596386320756599933047674875)⟩
noncomputable def lentry8_0 : RBox := ⟨1156450605893201085971615858,1156450605893201123879614487⟩
noncomputable def lentry3_0 : RBox := ⟨(-497900663495165887403278912),(-497900663495165876692203228)⟩
noncomputable def lentry9_0 : RBox := ⟨726695844980284058022282278,726695844980284110485485687⟩
noncomputable def lentry4_0 : RBox := ⟨(-129722376498730229479424854),(-129722376498730219846221208)⟩
noncomputable def lentry5_0 : RBox := ⟨5192157766382216813328101,5192157766382221815251673⟩
noncomputable def lentry6_3 : RBox := ⟨(-10884852847347014469371491535),(-10884852847347014445864444233)⟩
noncomputable def lentry7_3 : RBox := ⟨(-4465708184822282113792278974),(-4465708184822282091488397712)⟩
noncomputable def lentry2_3 : RBox := ⟨4605024524144134428523673830,4605024524144134467976903087⟩
noncomputable def lentry8_3 : RBox := ⟨9348829383490770441808543,9348829383491012494286692⟩
noncomputable def lentry3_3 : RBox := ⟨(-4308649990873823136416589661),(-4308649990873823060803451595)⟩
noncomputable def lentry9_3 : RBox := ⟨26226240502596733865099430434,26226240502596734231105827117⟩
noncomputable def lentry4_3 : RBox := ⟨1369022879160941407076210245,1369022879160941487324115228⟩
noncomputable def lentry5_3 : RBox := ⟨(-1289552013974452050024155783),(-1289552013974452005347604255)⟩
noncomputable def lentry6_1 : RBox := ⟨257993788917541150498000107,257993788917541157888863267⟩
noncomputable def lentry7_1 : RBox := ⟨(-663777977784782234746612750),(-663777977784782229394005574)⟩
noncomputable def lentry8_1 : RBox := ⟨1619108661149769913016706898,1619108661149769955303200794⟩
noncomputable def lentry3_1 : RBox := ⟨(-579591941864548585450896356),(-579591941864548573447403574)⟩
noncomputable def lentry9_1 : RBox := ⟨377184322890016097180070227,377184322890016155875518461⟩
noncomputable def lentry4_1 : RBox := ⟨(-195228355766339276704702654),(-195228355766339265841016551)⟩
noncomputable def lentry5_1 : RBox := ⟨25977920002013968828483999,25977920002013974478303761⟩
noncomputable def lentry6_4 : RBox := ⟨(-11139267443296261033356468182),(-11139267443296261006716194412)⟩
noncomputable def lentry7_4 : RBox := ⟨(-5743618610332307669422004880),(-5743618610332307644322228913)⟩
noncomputable def lentry2_4 : RBox := ⟨5321012643203737848682181032,5321012643203737892803135677⟩
noncomputable def lentry8_4 : RBox := ⟨2776571492109706045337114003,2776571492109706316069623773⟩
noncomputable def lentry3_4 : RBox := ⟨(-5389978260281014816719222713),(-5389978260281014732262209926)⟩
noncomputable def lentry9_4 : RBox := ⟨27368681932658456888679605519,27368681932658457297208750387⟩
noncomputable def lentry4_4 : RBox := ⟨1046331030113728873277846982,1046331030113728962453513129⟩
noncomputable def lentry5_4 : RBox := ⟨(-1259566801050796385474280065),(-1259566801050796335904409976)⟩
noncomputable def lentry6_2 : RBox := ⟨767399171832372983257164636,767399171832372988906161653⟩
noncomputable def lentry7_2 : RBox := ⟨(-644392944651544272181557039),(-644392944651544267855959278)⟩
noncomputable def lentry2_2 : RBox := ⟨344129241302690651571586296,344129241302690657533194559⟩
noncomputable def lentry8_2 : RBox := ⟨1856497232206901564546533917,1856497232206901601841142359⟩
noncomputable def lentry3_2 : RBox := ⟨(-607660233060482493251090964),(-607660233060482482498102625)⟩
noncomputable def lentry9_2 : RBox := ⟨109451628144957371825678763,109451628144957424719076512⟩
noncomputable def lentry4_2 : RBox := ⟨(-232443036487199701392321254),(-232443036487199691183528398)⟩
noncomputable def lentry5_2 : RBox := ⟨39065964993206543259829543,39065964993206548649635729⟩
noncomputable def lentry6_5 : RBox := ⟨(-10633079943167156175729829310),(-10633079943167156148566371119)⟩
noncomputable def lentry7_5 : RBox := ⟨(-6401538002129311513332102913),(-6401538002129311487912931512)⟩
noncomputable def lentry2_5 : RBox := ⟨5673870684468758906815253281,5673870684468758951656584385⟩
noncomputable def lentry8_5 : RBox := ⟨4515061100882060574473274188,4515061100882060849421864762⟩
noncomputable def lentry3_5 : RBox := ⟨(-5984619825577872881362402157),(-5984619825577872795340231432)⟩
noncomputable def lentry9_5 : RBox := ⟨27617495594282279521247988788,27617495594282279936739730868⟩
noncomputable def lentry4_5 : RBox := ⟨832688775810658666830659423,832688775810658757889595712⟩
noncomputable def lentry5_5 : RBox := ⟨(-1227193748716980633078098857),(-1227193748716980582381799584)⟩
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableData
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

open scoped BigOperators
namespace SharpPlanar


noncomputable def tableC (i : Bool) (n : ℕ) : ℚ :=
  if n = 0 then (if i then 0 else 1)
  else (if i then (tableRaw n).2.2.1 else (tableRaw n).1)/10000000000

noncomputable def tableD (i : Bool) (n : ℕ) : ℚ :=
  if n = 0 then (if i then -46/125 else 11/25)
  else (if i then (tableRaw n).2.2.2 else (tableRaw n).2.1)/10000000000

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

noncomputable def tableDensity (i : Bool) (j : ℕ) (t : ℂ) : ℂ :=
  finiteDensity (fun n => (tableC i n:ℝ)) (fun n => (tableD i n:ℝ)) j t

end SharpPlanar

namespace SharpPlanar
lemma table_range_mass (a : Bool) :
    ∑ n ∈ Finset.range 101, (|(tableC a n:ℝ)|+|(tableD a n:ℝ)|) ≤ 3 := by
  have hq : ∑ n ∈ Finset.range 101, (|tableC a n|+|tableD a n|) ≤ 3 := by
    cases a <;> decide +kernel
  exact_mod_cast hq
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
noncomputable def dataMass (p : CardinalData) : ℝ :=
  25*|p.C|+densityBound*(|p.c₀|+|p.d₀|+‖p.x‖)
lemma dataMass_nonneg (p : CardinalData) : 0 ≤ dataMass p := by
  unfold dataMass
  exact add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
    (mul_nonneg densityBound_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)))
noncomputable def firstNode : Node := ⟨1,by norm_num [residues]⟩
noncomputable def contactList : X := columnVector firstNode true

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DataSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed and summable parts of cardinal data

Splitting cardinal data separates the fixed coefficients from the absolutely summable interpolation unknowns.
-/

namespace SharpPlanar
open MeasureTheory
noncomputable def fixedPart (p : CardinalData) : CardinalData := ⟨p.C,p.c₀,p.d₀,0⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate

namespace SharpPlanar

noncomputable def foldedU (n : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

noncomputable def foldedV (n : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

end SharpPlanar

namespace SharpPlanar

noncomputable def Pmoment (ell : ℕ) (s : ℝ) : ℝ :=
  (Pcoeff 0 * (0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
    2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
      Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar
open MeasureTheory Set

noncomputable def basisMoment (sec : Bool) (n ell : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
    (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def cardinalSeries (p : CardinalData) (ell : ℕ) (s : ℝ) : ℝ :=
  p.C*Pmoment ell s + p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
    ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s)

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

namespace SharpPlanar

noncomputable def qSchwartz (p : CardinalData) : SchwartzMap Plane ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun x : Plane => cardinal p (b*‖x‖^2))
    (gaussianSchwartz (Real.pi*h*b) (mul_pos (mul_pos Real.pi_pos h_pos) b_pos))

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma certified_inverse_comp_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A W : E →L[ℝ] E) (U : F →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖((certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap).comp U‖ ≤
      ‖W.comp U‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)) = U x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply _
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm (U x)‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W (U x)‖/(1-δ) := by rw [he]
    _ ≤ (‖W.comp U‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right ((W.comp U).le_opNorm x) hd0.le
    _ = (‖W.comp U‖/(1-δ))*‖x‖ := by ring
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_norm : ‖finiteRestriction e he‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (finiteRestriction_bound e he)
lemma finiteEmbedding_norm_le : ‖finiteEmbedding e‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (finiteEmbedding_bound e)
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite decompositions of ℓ¹ coordinates

The central and exterior coordinate blocks give an additive decomposition of the ℓ¹ norm.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι κ : Type*}
lemma l1Split_norm [Fintype ι] [Fintype κ] (x : L1Finite (ι ⊕ κ)) :
    ‖x‖ = ‖l1Left x‖+‖l1Right x‖ := by
  classical
  rw [l1Finite_norm, l1Finite_norm, l1Finite_norm, Fintype.sum_sum_type]
  rfl
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteProjection_apply (x : X) (k : Node × Bool) :
    finiteEmbedding e (finiteRestriction e he x) k = if ∃ i, e i=k then x k else 0 := by
  classical
  rw [finiteEmbedding_apply]
  split_ifs with h
  · obtain ⟨i,rfl⟩ := h
    simp only [he.eq_iff, finiteRestriction_apply]
    simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => h ⟨i,hh⟩)]
end
end SharpPlanar

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable abbrev RL := finiteRestriction lowExteriorIndex lowExteriorIndex_injective
noncomputable abbrev IL := finiteEmbedding lowExteriorIndex
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
lemma rowTailNorm_zero (x : X) : rowTailNorm x 0 = ‖x‖ := by
  rw [← tailScalar_eq,X_norm_scalar]
  apply tsum_congr
  intro k
  exact ite_eq_left k.1.prop.1
end SharpPlanar
namespace SharpPlanar.Numerical
open scoped BigOperators
lemma exterior_low_tail (x : X) : ‖RE x‖ ≤ ‖RL x‖ + rowTailNorm x 16 := by
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable x 16)
    (fun k => by split_ifs <;> positivity) exteriorIndex_injective
  have hh' : (∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0)
      ≤ rowTailNorm x 16 := by
    rw [← tailScalar_eq]
    simpa only [Function.comp_apply,tsum_fintype,tailScalar] using hh
  have hi : ‖RE (IL (RL x))‖ ≤ ‖RL x‖ := by
    exact (finiteRestriction_bound _ exteriorIndex_injective _).trans_eq (by rw [one_mul,finiteEmbedding_norm _ lowExteriorIndex_injective])
  calc
    ‖RE x‖ ≤ ‖RE (IL (RL x))‖ +
        ∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0 := by
      rw [l1Finite_norm,l1Finite_norm,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simp only [finiteRestriction_apply]
      rw [finiteProjection_apply]
      by_cases h : 16<(exteriorIndex i).1.val
      · simp only [h,ite_true, if_true]
        exact le_add_of_nonneg_left (abs_nonneg _)
      · have hmem : ∃ j, lowExteriorIndex j=exteriorIndex i :=
          (lowExteriorIndex_range (exteriorIndex i).1 (exteriorIndex i).2).mpr
            ⟨(exteriorIndex_bound i).1, Nat.le_of_not_gt h⟩
        rw [ite_eq_left hmem,ite_eq_right h,add_zero]
    _ ≤ ‖RL x‖ + rowTailNorm x 16 := add_le_add hi hh'
lemma finite_discard_norm (x : X) : ‖x - IF (RF x)‖ = rowTailNorm x 100 := by
  rw [X_norm_scalar,← tailScalar_eq]
  apply tsum_congr
  intro k
  change |x k - IF (RF x) k| = _
  rw [finiteProjection_apply]
  simp only [finiteIndex_range]
  by_cases h : k.1.val ≤ 100
  · simp [h, Nat.not_lt_of_ge h]
  · simp [h, Nat.lt_of_not_ge h]
end SharpPlanar.Numerical

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
noncomputable def entry0_0 : RBox := ⟨14781435199538402187044371,21443121497131187683926438⟩
noncomputable def entry3_0 : RBox := ⟨(-18428513460674290002726905),21256699935175278722748150⟩
noncomputable def entry1_0 : RBox := ⟨43118132771417015947254617,44052033704054954902984396⟩
noncomputable def entry4_0 : RBox := ⟨62249279422698173481479787,67002192453404308329484995⟩
noncomputable def entry2_0 : RBox := ⟨(-25316692483062824372958517),(-25144841957016010059206459)⟩
noncomputable def entry5_0 : RBox := ⟨98795775754591403559925370,99934702821008685089375682⟩
noncomputable def entry0_1 : RBox := ⟨(-1782897877067077534249252508),(-1771136235844994531428048743)⟩
noncomputable def entry3_1 : RBox := ⟨(-200040303437058571524248177),(-130503295645971782920930062)⟩
noncomputable def entry1_1 : RBox := ⟨(-4227003622713142673109780884),(-4225227526010445946447219255)⟩
noncomputable def entry4_1 : RBox := ⟨(-6385027231970970763445868229),(-6375964958390364122462332351)⟩
noncomputable def entry2_1 : RBox := ⟨2454584419698238493925595563,2454914611379085872954715743⟩
noncomputable def entry5_1 : RBox := ⟨(-9387194252434294605314696679),(-9385005491815614794777512308)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def entry0_0 : RBox := ⟨1869675485089840175607983460,1869675485089841408177867513⟩
noncomputable def entry3_0 : RBox := ⟨(-1055221510065375439330557423),(-1055221510065368315022491651)⟩
noncomputable def entry1_0 : RBox := ⟨5693502919653421702687239420,5693502919653421896965019540⟩
noncomputable def entry4_0 : RBox := ⟨5789844446019218325785596098,5789844446019219332084826631⟩
noncomputable def entry2_0 : RBox := ⟨(-2112129605447203556634481396),(-2112129605447203504203995682)⟩
noncomputable def entry5_0 : RBox := ⟨19879651157153146100952668834,19879651157153146437425318346⟩
noncomputable def entry0_1 : RBox := ⟨(-17689009481045755197175573764),(-17689009481045752997121735007)⟩
noncomputable def entry3_1 : RBox := ⟨2365101911282630684490069330,2365101911282642860795334664⟩
noncomputable def entry1_1 : RBox := ⟨(-47057998223704903504653894595),(-47057998223704902997319227491)⟩
noncomputable def entry4_1 : RBox := ⟨(-58926380648056114064017326845),(-58926380648056111506424253444)⟩
noncomputable def entry2_1 : RBox := ⟨24298434952238939884465501345,24298434952238940042951834498⟩
noncomputable def entry5_1 : RBox := ⟨(-132961498390156263788907228999),(-132961498390156262791306714514)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨13,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨1514686089768423485082071492,1514686089768424805138973932⟩
noncomputable def entry3_0 : RBox := ⟨(-633187383965310545884170014),(-633187383965303263672854607)⟩
noncomputable def entry1_0 : RBox := ⟨4459277439234840373526773384,4459277439234840623340996972⟩
noncomputable def entry4_0 : RBox := ⟨4644192435700190308181373519,4644192435700191575859100654⟩
noncomputable def entry2_0 : RBox := ⟨(-1904239948375286102830461186),(-1904239948375286031415396907)⟩
noncomputable def entry5_0 : RBox := ⟨14992034118501790197838411969,14992034118501790646377908731⟩
noncomputable def entry0_1 : RBox := ⟨(-16006816087119788909792694652),(-16006816087119786162792803680)⟩
noncomputable def entry3_1 : RBox := ⟨1555122448636839702576573738,1555122448636854708636269568⟩
noncomputable def entry1_1 : RBox := ⟨(-42026174835983939341911186170),(-42026174835983938708480722396)⟩
noncomputable def entry4_1 : RBox := ⟨(-53746174737134993681723946784),(-53746174737134990504585088015)⟩
noncomputable def entry2_1 : RBox := ⟨22280752521098527995107168941,22280752521098528186245898735⟩
noncomputable def entry5_1 : RBox := ⟨(-115685193358212424474739631317),(-115685193358212423277367553200)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨15,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨1061579508246790519280932425,1061579508246792586461290800⟩
noncomputable def entry3_0 : RBox := ⟨(-296335957511163135130540350),(-296335957511151738717073053)⟩
noncomputable def entry1_0 : RBox := ⟨3002443179363073501422921823,3002443179363073883585724050⟩
noncomputable def entry4_0 : RBox := ⟨3342661709854074726744831947,3342661709854076665513874282⟩
noncomputable def entry2_0 : RBox := ⟨(-1437813973820552424622003430),(-1437813973820552319793278777)⟩
noncomputable def entry5_0 : RBox := ⟨9422135324312595359548890053,9422135324312596018262920539⟩
noncomputable def entry0_1 : RBox := ⟨(-13472225824399337150041998493),(-13472225824399332193005864365)⟩
noncomputable def entry3_1 : RBox := ⟨678445811898494367897161215,678445811898521545129332500⟩
noncomputable def entry1_1 : RBox := ⟨(-34714862514256600108782163293),(-34714862514256599063524242358)⟩
noncomputable def entry4_1 : RBox := ⟨(-45896113580750486652787542679),(-45896113580750481389914075066)⟩
noncomputable def entry2_1 : RBox := ⟨18956977099474432968801452848,18956977099474433262921777009⟩
noncomputable def entry5_1 : RBox := ⟨(-91943890478298412156312132417),(-91943890478298410313433909466)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨16,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨909436800928886232377891616,909436800928890522725980059⟩
noncomputable def entry3_0 : RBox := ⟨(-213279942367921212625056631),(-213279942367896584910320027)⟩
noncomputable def entry1_0 : RBox := ⟨2534378294183524808382830309,2534378294183525419833780882⟩
noncomputable def entry4_0 : RBox := ⟨2902496732249764468990994416,2902496732249767626848240905⟩
noncomputable def entry2_0 : RBox := ⟨(-1253848263969943656026530445),(-1253848263969943508536834263)⟩
noncomputable def entry5_0 : RBox := ⟨7755638814025872877426413856,7755638814025873818666258287⟩
noncomputable def entry0_1 : RBox := ⟨(-12489739198211868559472706042),(-12489739198211861334901656365)⟩
noncomputable def entry3_1 : RBox := ⟨426330017086272531191536326,426330017086312605820178081⟩
noncomputable def entry1_1 : RBox := ⟨(-31956657307121592755401289939),(-31956657307121591369148326651)⟩
noncomputable def entry4_1 : RBox := ⟨(-42781277958223009310615104419),(-42781277958223002291295150889)⟩
noncomputable def entry2_1 : RBox := ⟨17613883082074708970987801679,17613883082074709346637216306⟩
noncomputable def entry5_1 : RBox := ⟨(-83395651674863442525515780876),(-83395651674863440165001482350)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨19,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨609632836493450924132688321,609632836493467555708566057⟩
noncomputable def entry3_0 : RBox := ⟨(-88388737316621956856488704),(-88388737316524499997426906)⟩
noncomputable def entry1_0 : RBox := ⟨1645108600586911323128058793,1645108600586913351500167654⟩
noncomputable def entry4_0 : RBox := ⟨2005007637295831696480533861,2005007637295842236291748290⟩
noncomputable def entry2_0 : RBox := ⟨(-862071455215955747609287964),(-862071455215955305272469607)⟩
noncomputable def entry5_0 : RBox := ⟨4748333893047747905556744962,4748333893047750749287696042⟩
noncomputable def entry0_1 : RBox := ⟨(-10256736477445427423281384758),(-10256736477445390359006215778)⟩
noncomputable def entry3_1 : RBox := ⟨5941444204424899838730897,5941444204635751216927410⟩
noncomputable def entry1_1 : RBox := ⟨(-25833480247750740604184608020),(-25833480247750734874827811406)⟩
noncomputable def entry4_1 : RBox := ⟨(-35545303020991510566813039213),(-35545303020991480956526835313)⟩
noncomputable def entry2_1 : RBox := ⟨14491013047718096997306533293,14491013047718098296155313023⟩
noncomputable def entry5_1 : RBox := ⟨(-65191634497841147105721793257),(-65191634497841138829238380363)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨21,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨485966258789149736694357765,485966258789180235251119359⟩
noncomputable def entry3_0 : RBox := ⟨(-51876621983823187733002458),(-51876621983644365750087028)⟩
noncomputable def entry1_0 : RBox := ⟨1291545348698928340048288309,1291545348698932065650877013⟩
noncomputable def entry4_0 : RBox := ⟨1619459325911299753137686236,1619459325911319111948979445⟩
noncomputable def entry2_0 : RBox := ⟨(-691689217331358710017367516),(-691689217331357915939927602)⟩
noncomputable def entry5_0 : RBox := ⟨3622037794270154248059013971,3622037794270159363221246573⟩
noncomputable def entry0_1 : RBox := ⟨(-9168218227879751666198655917),(-9168218227879681406995229249)⟩
noncomputable def entry3_1 : RBox := ⟨(-130743248738124761378508098),(-130743248737724299964632911)⟩
noncomputable def entry1_1 : RBox := ⟨(-22918446386967264381065288629),(-22918446386967253660090586729)⟩
noncomputable def entry4_1 : RBox := ⟨(-31941360350535334308390688764),(-31941360350535278822431021781)⟩
noncomputable def entry2_1 : RBox := ⟨12946312314073658753094509345,12946312314073661117933415865⟩
noncomputable def entry5_1 : RBox := ⟨(-56897199962254830373798563262),(-56897199962254815270317043210)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨24,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨361066638446297468762256867,361066638446348436202686001⟩
noncomputable def entry3_0 : RBox := ⟨(-24080202515203398362635142),(-24080202514909445127868213)⟩
noncomputable def entry1_0 : RBox := ⟨943144543663669496151509919,943144543663676538571788741⟩
noncomputable def entry4_0 : RBox := ⟨1220326035904610387591949040,1220326035904646818238138047⟩
noncomputable def entry2_0 : RBox := ⟨(-515821320621010914028500214),(-515821320621009366784521922)⟩
noncomputable def entry5_0 : RBox := ⟨2557113746397753350060655643,2557113746397763266929958001⟩
noncomputable def entry0_1 : RBox := ⟨(-7911673511695496777591697076),(-7911673511695406972260846530)⟩
noncomputable def entry3_1 : RBox := ⟨(-239283827899688084542999291),(-239283827899182647834186993)⟩
noncomputable def entry1_1 : RBox := ⟨(-19607740777453375364938093828),(-19607740777453360407061024691)⟩
noncomputable def entry4_1 : RBox := ⟨(-27723891329601188482925271931),(-27723891329601111783666725799)⟩
noncomputable def entry2_1 : RBox := ⟨11153955111407173405560197539,11153955111407176893766558558⟩
noncomputable def entry5_1 : RBox := ⟨(-47766810642294232261642086112),(-47766810642294210122775908395)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨25,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨330063619719224744085061654,330063619719269140255052494⟩
noncomputable def entry3_0 : RBox := ⟨(-18611913465530738863016299),(-18611913465281695253923614)⟩
noncomputable def entry1_0 : RBox := ⟨858112981223572875022772933,858112981223580029031490806⟩
noncomputable def entry4_0 : RBox := ⟨1119636661327193722348392507,1119636661327230517100616329⟩
noncomputable def entry2_0 : RBox := ⟨(-471707679190942963777199221),(-471707679190941287099563170)⟩
noncomputable def entry5_0 : RBox := ⟨2304856454407464539675839353,2304856454407475187410103946⟩
noncomputable def entry0_1 : RBox := ⟨(-7566458553939264789342472303),(-7566458553939145664042657675)⟩
noncomputable def entry3_1 : RBox := ⟨(-260520064658947849661693994),(-260520064658279283725488027)⟩
noncomputable def entry1_1 : RBox := ⟨(-18708122626285041712309554998),(-18708122626285021358367332589)⟩
noncomputable def entry4_1 : RBox := ⟨(-26554992275231355496970697274),(-26554992275231251141299015985)⟩
noncomputable def entry2_1 : RBox := ⟨10660676103009534733426250498,10660676103009539446559648433⟩
noncomputable def entry5_1 : RBox := ⟨(-45339090891491547470642302262),(-45339090891491517536301370236)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨27,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨278990510479936712403226109,278990510480021405447007896⟩
noncomputable def entry3_0 : RBox := ⟨(-10873029152966477351440904),(-10873029152489746509988316)⟩
noncomputable def entry1_0 : RBox := ⟨719383639276547676356262135,719383639276561177049384890⟩
noncomputable def entry4_0 : RBox := ⟨952303372127389678880776151,952303372127459233741271076⟩
noncomputable def entry2_0 : RBox := ⟨(-398736274042741587092780032),(-398736274042738477592431984)⟩
noncomputable def entry5_0 : RBox := ⟨1900443575246792638162255771,1900443575246812426686586162⟩
noncomputable def entry0_1 : RBox := ⟨(-6959561865246361327217453820),(-6959561865246132060634644946)⟩
noncomputable def entry3_1 : RBox := ⟨(-289413124349156839881543258),(-289413124347865335965726789)⟩
noncomputable def entry1_1 : RBox := ⟨(-17136771796223399386248855538),(-17136771796223360893755434176)⟩
noncomputable def entry4_1 : RBox := ⟨(-24489813837920627876059576684),(-24489813837920430082653551426)⟩
noncomputable def entry2_1 : RBox := ⟨9793258629831515550378575395,9793258629831524288911413105⟩
noncomputable def entry5_1 : RBox := ⟨(-41153229096449685758068078648),(-41153229096449630112530202299)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U27

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert28
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

namespace SharpPlanar.Numerical.U28
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨28,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨257808870054295162167312766,257808870054483228993065205⟩
noncomputable def entry3_0 : RBox := ⟨(-8134329832227502049575591),(-8134329831138634963372595)⟩
noncomputable def entry1_0 : RBox := ⟨662362090007803242082438407,662362090007829032363110413⟩
noncomputable def entry4_0 : RBox := ⟨882356844753485630129459628,882356844753619255551255154⟩
noncomputable def entry2_0 : RBox := ⟨(-368383467988750066558018932),(-368383467988744562592790364)⟩
noncomputable def entry5_0 : RBox := ⟨1736949516812908886823159146,1736949516812944290489417503⟩
noncomputable def entry0_1 : RBox := ⟨(-6691372244609415125320234691),(-6691372244609084754401679073)⟩
noncomputable def entry3_1 : RBox := ⟨(-298866391396277379826242490),(-298866391394405768152519017)⟩
noncomputable def entry1_1 : RBox := ⟨(-16446490262609769631422685287),(-16446490262609716199873066534)⟩
noncomputable def entry4_1 : RBox := ⟨(-23573150182335431328600607873),(-23573150182335156193317191251)⟩
noncomputable def entry2_1 : RBox := ⟨9409996066634420135604286879,9409996066634432115678662659⟩
noncomputable def entry5_1 : RBox := ⟨(-39336365811079536164846908923),(-39336365811079459744555685187)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U28

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert31
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

namespace SharpPlanar.Numerical.U31
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨31,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨206994690679640943347524580,206994690680415835253266618⟩
noncomputable def entry3_0 : RBox := ⟨(-2717834254602583801954924),(-2717834250036930353033561)⟩
noncomputable def entry1_0 : RBox := ⟨526874541362934738302875492,526874541363031045676196267⟩
noncomputable def entry4_0 : RBox := ⟨713195608864848830758316310,713195608865349537389177949⟩
noncomputable def entry2_0 : RBox := ⟨(-295420842619721907288987223),(-295420842619702657692258385)⟩
noncomputable def entry5_0 : RBox := ⟨1355404789508252247926940541,1355404789508377278955809048⟩
noncomputable def entry0_1 : RBox := ⟨(-5998363308759049786232234029),(-5998363308757191469765203146)⟩
noncomputable def entry3_1 : RBox := ⟨(-314286876208078853259183418),(-314286876197386277300312382)⟩
noncomputable def entry1_1 : RBox := ⟨(-14674295877641880461316673085),(-14674295877641602381834014676)⟩
noncomputable def entry4_1 : RBox := ⟨(-21193304251227429495262252317),(-21193304251225985421353944807)⟩
noncomputable def entry2_1 : RBox := ⟨8420273248236518121055353933,8420273248236575287107162119⟩
noncomputable def entry5_1 : RBox := ⟨(-34733187700800980777552408142),(-34733187700800612063761630263)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U31

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert33
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

namespace SharpPlanar.Numerical.U33
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨33,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨181056821799494978165737624,181056821800993448292005624⟩
noncomputable def entry3_0 : RBox := ⟨(-596996660207130631490625),(-596996651369887754772763)⟩
noncomputable def entry1_0 : RBox := ⟨458468465271364701651297385,458468465271551712348196301⟩
noncomputable def entry4_0 : RBox := ⟨626078576344261362320942694,626078576345233335520958627⟩
noncomputable def entry2_0 : RBox := ⟨(-258130794954339919614376015),(-258130794954302837324469120)⟩
noncomputable def entry5_0 : RBox := ⟨1166764246282439741601291949,1166764246282680916818086743⟩
noncomputable def entry0_1 : RBox := ⟨(-5611182599303430478267671145),(-5611182599299823181732307752)⟩
noncomputable def entry3_1 : RBox := ⟨(-317456615042704561463676724),(-317456615021915743872236835)⟩
noncomputable def entry1_1 : RBox := ⟨(-13691337797940579375687224240),(-13691337797940039851225448133)⟩
noncomputable def entry4_1 : RBox := ⟨(-19856865764452257648534002185),(-19856865764449455849313540161)⟩
noncomputable def entry2_1 : RBox := ⟨7867971015801272572735214879,7867971015801382566845004371⟩
noncomputable def entry5_1 : RBox := ⟨(-32218066528705742827984144795),(-32218066528705032284106633797)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U33

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert36
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

namespace SharpPlanar.Numerical.U36
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨36,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨150439081766810608761770954,150439081769445342672018404⟩
noncomputable def entry3_0 : RBox := ⟨1325803259979195373216914,1325803275334725273801108⟩
noncomputable def entry1_0 : RBox := ⟨378426586309438097846350342,378426586309797835679401224⟩
noncomputable def entry4_0 : RBox := ⟨522538747415706809706033850,522538747417571989909008448⟩
noncomputable def entry2_0 : RBox := ⟨(-214109704348761179944843841),(-214109704348687596740831337)⟩
noncomputable def entry5_0 : RBox := ⟨949782460938339974061210268,949782460938816317771368363⟩
noncomputable def entry0_1 : RBox := ⟨(-5116070322861830304448041109),(-5116070322857197800695339323)⟩
noncomputable def entry3_1 : RBox := ⟨(-316070029738523634731709956),(-316070029712008885120098114)⟩
noncomputable def entry1_1 : RBox := ⟨(-12441764991146162949373802311),(-12441764991145436402247167861)⟩
noncomputable def entry4_1 : RBox := ⟨(-18140953284142905074170532377),(-18140953284139149089465884118)⟩
noncomputable def entry2_1 : RBox := ⟨7162678693969194502233602017,7162678693969348928626537296⟩
noncomputable def entry5_1 : RBox := ⟨(-29059937712183052076397762614),(-29059937712182059004882917403)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U36

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert37
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

namespace SharpPlanar.Numerical.U37
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨37,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨141948146896465605449539921,141948146898737130064405565⟩
noncomputable def entry3_0 : RBox := ⟨1744542188297282697350514,1744542201265740923994049⟩
noncomputable def entry1_0 : RBox := ⟨356372400749712144140078510,356372400750062050217603808⟩
noncomputable def entry4_0 : RBox := ⟨493684571556779447333487086,493684571558589781482447211⟩
noncomputable def entry2_0 : RBox := ⟨(-201906382628628861158669748),(-201906382628553493920070785)⟩
noncomputable def entry5_0 : RBox := ⟨890755902237755058257906895,890755902238239177711230362⟩
noncomputable def entry0_1 : RBox := ⟨(-4969938520158845949989828276),(-4969938520152546870707964882)⟩
noncomputable def entry3_1 : RBox := ⟨(-314527595443821912533061718),(-314527595407830094373889711)⟩
noncomputable def entry1_1 : RBox := ⟨(-12074531392725403452154717021),(-12074531392724397683055276267)⟩
noncomputable def entry4_1 : RBox := ⟨(-17633046474644703260729936994),(-17633046474639507077054438701)⟩
noncomputable def entry2_1 : RBox := ⟨6954759767601439423185056898,6954759767601652586170853774⟩
noncomputable def entry5_1 : RBox := ⟨(-28140140948963205569011081086),(-28140140948961834093280348255)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U37

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert39
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

namespace SharpPlanar.Numerical.U39
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨39,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨126993009847497525141430677,126993009851910599277408764⟩
noncomputable def entry3_0 : RBox := ⟨2357767521265211879503233,2357767546517979913330052⟩
noncomputable def entry1_0 : RBox := ⟨317687417376969339464647603,317687417377646312042477637⟩
noncomputable def entry4_0 : RBox := ⟨442709520574007407147388333,442709520577510607057713331⟩
noncomputable def entry2_0 : RBox := ⟨(-180422787031220825804182068),(-180422787031076563802742163)⟩
noncomputable def entry5_0 : RBox := ⟨788061506537027561788239739,788061506537955767502218573⟩
noncomputable def entry0_1 : RBox := ⟨(-4701414442986735082981472177),(-4701414442974451014123768764)⟩
noncomputable def entry3_1 : RBox := ⟨(-310381528996314065790455012),(-310381528925970678483971926)⟩
noncomputable def entry1_1 : RBox := ⟨(-11401584849190827343902447365),(-11401584849188877434290374592)⟩
noncomputable def entry4_1 : RBox := ⟨(-16698040879274522448122855648),(-16698040879264445310878446206)⟩
noncomputable def entry2_1 : RBox := ⟨6573032281717246475927616809,6573032281717655556472001086⟩
noncomputable def entry5_1 : RBox := ⟨(-26464461415825020396056387798),(-26464461415822383936898903991)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U39

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert40
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

namespace SharpPlanar.Numerical.U40
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨40,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨120388284586305779507548334,120388284596283209428950586⟩
noncomputable def entry3_0 : RBox := ⟨2577192455032076857753707,2577192513339892624049141⟩
noncomputable def entry1_0 : RBox := ⟨300669538919884463075256364,300669538921246670476500092⟩
noncomputable def entry4_0 : RBox := ⟨420133030853069922578164336,420133030860129208118325392⟩
noncomputable def entry2_0 : RBox := ⟨(-170940356231783517698780166),(-170940356231509416323118057)⟩
noncomputable def entry5_0 : RBox := ⟨743238946671632339153032429,743238946673411605496804289⟩
noncomputable def entry0_1 : RBox := ⟨(-4577767979643956334624500857),(-4577767979626405505276034294)⟩
noncomputable def entry3_1 : RBox := ⟨(-307909926371293170983104223),(-307909926270429155104841245)⟩
noncomputable def entry1_1 : RBox := ⟨(-11092523698265831539395823065),(-11092523698263102787204873091)⟩
noncomputable def entry4_1 : RBox := ⟨(-16266767311596517110427054432),(-16266767311582403021677285638)⟩
noncomputable def entry2_1 : RBox := ⟨6397414470489198154145710768,6397414470489766677522584440⟩
noncomputable def entry5_1 : RBox := ⟨(-25699138663079219455832598309),(-25699138663075551201556503421)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U40

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert43
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

namespace SharpPlanar.Numerical.U43
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨43,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨103399111598806655445737636,103399111640563633874169918⟩
noncomputable def entry3_0 : RBox := ⟨2993066081249458682429470,2993066328488680523003023⟩
noncomputable def entry1_0 : RBox := ⟨257091854966104688733119713,257091854971412881879779485⟩
noncomputable def entry4_0 : RBox := ⟨361873266329210127313154087,361873266356720858773626263⟩
noncomputable def entry2_0 : RBox := ⟨(-146569903904056636073477159),(-146569903903035063129763575)⟩
noncomputable def entry5_0 : RBox := ⟨629501814886342956222803739,629501814893022792861068517⟩
noncomputable def entry0_1 : RBox := ⟨(-4243057406611405181754031919),(-4243057406509711361117570004)⟩
noncomputable def entry3_1 : RBox := ⟨(-299476763840350537672758857),(-299476763250379180324119746)⟩
noncomputable def entry1_1 : RBox := ⟨(-10258443248866466129672651948),(-10258443248851245181809488710)⟩
noncomputable def entry4_1 : RBox := ⟨(-15097017825849700263961238846),(-15097017825770782547479687509)⟩
noncomputable def entry2_1 : RBox := ⟨5922549654149551440521449000,5922549654152559453281896574⟩
noncomputable def entry5_1 : RBox := ⟨(-23647095363783265410519994023),(-23647095363763707859300571063)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U43

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert45
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

namespace SharpPlanar.Numerical.U45
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨45,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨93998575640662247302938600,93998575722237395873069859⟩
noncomputable def entry3_0 : RBox := ⟨3128817481794886388799814,3128817965117834286617989⟩
noncomputable def entry1_0 : RBox := ⟨233106697834797128509908927,233106697845201257108703146⟩
noncomputable def entry4_0 : RBox := ⟨329517033483131527940506359,329517033537014001966905330⟩
noncomputable def entry2_0 : RBox := ⟨(-133101421809267909885465355),(-133101421807274635631320702)⟩
noncomputable def entry5_0 : RBox := ⟨567572710666977685170590737,567572710680022852297653012⟩
noncomputable def entry0_1 : RBox := ⟨(-4045884048501023052226183679),(-4045884048302051291279419980)⟩
noncomputable def entry3_1 : RBox := ⟨(-293340231291230644403780962),(-293340230135594257978317525)⟩
noncomputable def entry1_1 : RBox := ⟨(-9768832672031863794664796887),(-9768832672002071456462470705)⟩
noncomputable def entry4_1 : RBox := ⟨(-14406385109185792883972300022),(-14406385109031404810501237159)⟩
noncomputable def entry2_1 : RBox := ⟨5643201950044088201886389979,5643201950049947581282591911⟩
noncomputable def entry5_1 : RBox := ⟨(-22451621321395641006042462845),(-22451621321357501736758379311)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U45

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert48
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

namespace SharpPlanar.Numerical.U48
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨48,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨82133868317200423831573911,82133868462420427765627308⟩
noncomputable def entry3_0 : RBox := ⟨3200771713407597504620354,3200772565921084678533667⟩
noncomputable def entry1_0 : RBox := ⟨202971658772349404417187273,202971658792217269213108023⟩
noncomputable def entry4_0 : RBox := ⟨288551909601015701964150606,288551909703775783743222583⟩
noncomputable def entry2_0 : RBox := ⟨(-116123516773840887956646368),(-116123516769945661619046608)⟩
noncomputable def entry5_0 : RBox := ⟨490486903247212548061076962,490486903272617165961958637⟩
noncomputable def entry0_1 : RBox := ⟨(-3782286352537761620043098891),(-3782286352282004144294697473)⟩
noncomputable def entry3_1 : RBox := ⟨(-283814070014290880212547018),(-283814068534608626106602169)⟩
noncomputable def entry1_1 : RBox := ⟨(-9116280800458015686191718238),(-9116280800418689391291134047)⟩
noncomputable def entry4_1 : RBox := ⟨(-13481320453846934664519842835),(-13481320453643627448894346836)⟩
noncomputable def entry2_1 : RBox := ⟨5270230945893394990648327715,5270230945901333495115393375⟩
noncomputable def entry5_1 : RBox := ⟨(-20868743551745457583621725048),(-20868743551693938613459576443)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U48

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert49
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

namespace SharpPlanar.Numerical.U49
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨49,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨78675485700104630648508937,78675485824729821064586271⟩
noncomputable def entry3_0 : RBox := ⟨3200320143299372199280894,3200320863261826983704361⟩
noncomputable def entry1_0 : RBox := ⟨194217841504591364145196106,194217841523441997206368308⟩
noncomputable def entry4_0 : RBox := ⟨276583544869538701219186731,276583544967012377001977311⟩
noncomputable def entry2_0 : RBox := ⟨(-111179847886112125500997964),(-111179847882268607105243245)⟩
noncomputable def entry5_0 : RBox := ⟨468252560014943978175656459,468252560039859798381347374⟩
noncomputable def entry0_1 : RBox := ⟨(-3701900296010466959109685102),(-3701900295658305422599371944)⟩
noncomputable def entry3_1 : RBox := ⟨(-280612707890954684683234117),(-280612705856227910804122421)⟩
noncomputable def entry1_1 : RBox := ⟨(-8917734342363892660260195077),(-8917734342309081574493774585)⟩
noncomputable def entry4_1 : RBox := ⟨(-13198816105392848476616843997),(-13198816105109689469068654110)⟩
noncomputable def entry2_1 : RBox := ⟨5156606090089471925752870098,5156606090100515538583384949⟩
noncomputable def entry5_1 : RBox := ⟨(-20389502574004400419372450505),(-20389502573932700558721828063)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U49

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert51
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

namespace SharpPlanar.Numerical.U51
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨51,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨72383900743044221867288862,72383900986919659919509903⟩
noncomputable def entry3_0 : RBox := ⟨3174052461983741626084770,3174053873089608818146213⟩
noncomputable def entry1_0 : RBox := ⟨178328925047793459025515149,178328925084612981001407203⟩
noncomputable def entry4_0 : RBox := ⟨254777298188298170639857614,254777298378612301138181515⟩
noncomputable def entry2_0 : RBox := ⟨(-102192936669286833789386208),(-102192936661833554897236043)⟩
noncomputable def entry5_0 : RBox := ⟨428085500777927792069644162,428085500826308980154471125⟩
noncomputable def entry0_1 : RBox := ⟨(-3550972147686013274503580791),(-3550972146995236713804067208)⟩
noncomputable def entry3_1 : RBox := ⟨(-274233365496701091243002280),(-274233361499647296339549543)⟩
noncomputable def entry1_1 : RBox := ⟨(-8545526909342593819120226582),(-8545526909235363823320967328)⟩
noncomputable def entry4_1 : RBox := ⟨(-12667902939192722639432231866),(-12667902938638941954925088734)⟩
noncomputable def entry2_1 : RBox := ⟨4943422274521871225317810314,4943422274543338177344728480⟩
noncomputable def entry5_1 : RBox := ⟨(-19494063797932837810263364658),(-19494063797793285495336828924)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U51

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert52
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

namespace SharpPlanar.Numerical.U52
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨52,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨69517727021523410486945986,69517727578779290067507387⟩
noncomputable def entry3_0 : RBox := ⟨3151015512774478293436740,3151018790364424410804850⟩
noncomputable def entry1_0 : RBox := ⟨171106545316240519820592722,171106545392605160143630048⟩
noncomputable def entry4_0 : RBox := ⟨244828868686704817934169961,244828869081187676843477420⟩
noncomputable def entry2_0 : RBox := ⟨(-98101999249782192966219609),(-98101999234963430203973774)⟩
noncomputable def entry5_0 : RBox := ⟨409910779536244513869347872,409910779633089456302756458⟩
noncomputable def entry0_1 : RBox := ⟨(-3480035824706599317191626456),(-3480035823724642055836333392)⟩
noncomputable def entry3_1 : RBox := ⟨(-271070364111832266041592147),(-271070358414886823107338138)⟩
noncomputable def entry1_1 : RBox := ⟨(-8370846533585071057007273560),(-8370846533434627627158523833)⟩
noncomputable def entry4_1 : RBox := ⟨(-12418149389843500265476536091),(-12418149389066302381804532439)⟩
noncomputable def entry2_1 : RBox := ⟨4843295659463558753806325018,4843295659493547014707640728⟩
noncomputable def entry5_1 : RBox := ⟨(-19075164093013467242857161331),(-19075164092818354990922889630)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U52

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert55
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

namespace SharpPlanar.Numerical.U55
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨55,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨61871995200570297981534943,61871997554946934924861803⟩
noncomputable def entry3_0 : RBox := ⟨3054835128135616905966271,3054849117938085018996769⟩
noncomputable def entry1_0 : RBox := ⟨151890896021495668746028124,151890896326250126156608648⟩
noncomputable def entry4_0 : RBox := ⟨218245094744878860841672288,218245096317102017738499836⟩
noncomputable def entry2_0 : RBox := ⟨(-87199643280630729394144827),(-87199643223263102665474926)⟩
noncomputable def entry5_0 : RBox := ⟨361820003104608654622561727,361820003481476407872878153⟩
noncomputable def entry0_1 : RBox := ⟨(-3283285560800118142110426724),(-3283285555026567179393554310)⟩
noncomputable def entry3_1 : RBox := ⟨(-261753046314993314077657901),(-261753012614463788142245919)⟩
noncomputable def entry1_1 : RBox := ⟨(-7887209268534531239926104509),(-7887209267668401744398772915)⟩
noncomputable def entry4_1 : RBox := ⟨(-11724684071240411734594855643),(-11724684066765254036727055982)⟩
noncomputable def entry2_1 : RBox := ⟨4565823894841596495916412321,4565823895008643970693645076⟩
noncomputable def entry5_1 : RBox := ⟨(-17919815102070681549015696918),(-17919815100977926867908993944)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U55

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert57
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

namespace SharpPlanar.Numerical.U57
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨57,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨57455447751623542805297982,57455452374859418442754197⟩
noncomputable def entry3_0 : RBox := ⟨2975703568240004272304316,2975731053446812924419861⟩
noncomputable def entry1_0 : RBox := ⟨140825746158373842589537305,140825746758408029310912476⟩
noncomputable def entry4_0 : RBox := ⟨202857883582104426808682849,202857886675239998793137943⟩
noncomputable def entry2_0 : RBox := ⟨(-80909543330943337476300439),(-80909543218298280683749464)⟩
noncomputable def entry5_0 : RBox := ⟨334308658968614616154488241,334308659709094131006187067⟩
noncomputable def entry0_1 : RBox := ⟨(-3164039955209597944955394424),(-3164039943863922566488428771)⟩
noncomputable def entry3_1 : RBox := ⟨(-255721045505623838843954820),(-255720979222077993020217342)⟩
noncomputable def entry1_1 : RBox := ⟨(-7594702006982408423955528402),(-7594702005279799042909323050)⟩
noncomputable def entry4_1 : RBox := ⟨(-11303862339075590892004506884),(-11303862330283980871725038269)⟩
noncomputable def entry2_1 : RBox := ⟨4397832250839476172052490754,4397832251166808345937760071⟩
noncomputable def entry5_1 : RBox := ⟨(-17224229698636092650016382050),(-17224229696492917922789073038)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U57

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert60
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

namespace SharpPlanar.Numerical.U60
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨60,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨51667898199205723056555104,51667906477564425310746330⟩
noncomputable def entry3_0 : RBox := ⟨2845043180501155694164424,2845092028861456632326628⟩
noncomputable def entry1_0 : RBox := ⟨126366052946688275695250561,126366054085485358503440298⟩
noncomputable def entry4_0 : RBox := ⟨182658241954899356056204536,182658247821870425101800263⟩
noncomputable def entry2_0 : RBox := ⟨(-72676282127505095177964362),(-72676281910111858496040759)⟩
noncomputable def entry5_0 : RBox := ⟨298567460267208288764729051,298567461692966933119523976⟩
noncomputable def entry0_1 : RBox := ⟨(-3000585503213456212078907993),(-3000585488613146243761545117)⟩
noncomputable def entry3_1 : RBox := ⟨(-246987333973370042690628494),(-246987248865336513279115110)⟩
noncomputable def entry1_1 : RBox := ⟨(-7194502047104587743737054567),(-7194502044879007495492062974)⟩
noncomputable def entry4_1 : RBox := ⟨(-10726382554144524920720115524),(-10726382542668877937494538101)⟩
noncomputable def entry2_1 : RBox := ⟨4167784323265799804523574841,4167784323700458173057390074⟩
noncomputable def entry5_1 : RBox := ⟨(-16276429053153227438973369872),(-16276429050312458356667852320)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U60

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert61
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

namespace SharpPlanar.Numerical.U61
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨61,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨49932157024947208150347894,49932164106553739815459958⟩
noncomputable def entry3_0 : RBox := ⟨2799761187494939402008320,2799802438518582766065000⟩
noncomputable def entry1_0 : RBox := ⟨122038678204978582898843270,122038679267207487925946663⟩
noncomputable def entry4_0 : RBox := ⟨176592012111921687615061943,176592017588627803332536933⟩
noncomputable def entry2_0 : RBox := ⟨(-70209295810167931973459978),(-70209295601430177977047416)⟩
noncomputable def entry5_0 : RBox := ⟨287919124158346957145987301,287919125521451109539025969⟩
noncomputable def entry0_1 : RBox := ⟨(-2949792894430838886827087598),(-2949792874181774918526027972)⟩
noncomputable def entry3_1 : RBox := ⟨(-244164881332038429772306846),(-244164763433597964328498989)⟩
noncomputable def entry1_1 : RBox := ⟨(-7070318541729844945154560604),(-7070318538616448262669024392)⟩
noncomputable def entry4_1 : RBox := ⟨(-10546783038972516874491843516),(-10546783022929131173671335558)⟩
noncomputable def entry2_1 : RBox := ⟨4096352170239745868754342033,4096352170847004193930472526⟩
noncomputable def entry5_1 : RBox := ⟨(-15983234052201612258960703383),(-15983234048231387128522017963)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U61

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert63
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

namespace SharpPlanar.Numerical.U63
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨63,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨46713316972589252952744686,46713330891173853006594711⟩
noncomputable def entry3_0 : RBox := ⟨2708135553761247907036342,2708216722986433475889353⟩
noncomputable def entry1_0 : RBox := ⟨114025446461083468957269084,114025448547000682587355390⟩
noncomputable def entry4_0 : RBox := ⟨165332273864093539559688634,165332284612672230718299107⟩
noncomputable def entry2_0 : RBox := ⟨(-65637350047876867107387377),(-65637349639951485383424800)⟩
noncomputable def entry5_0 : RBox := ⟨268261500435743838136281213,268261503102411102307754652⟩
noncomputable def entry0_1 : RBox := ⟨(-2853201077881291213561078820),(-2853201038023745104697560519)⟩
noncomputable def entry3_1 : RBox := ⟨(-238656844176541253333254263),(-238656611863860390134845253)⟩
noncomputable def entry1_1 : RBox := ⟨(-6834390546176732236397812410),(-6834390540056889566114444842)⟩
noncomputable def entry4_1 : RBox := ⟨(-10205044213536195116226386914),(-10205044182016681173477007070)⟩
noncomputable def entry2_1 : RBox := ⟨3960582390319061313755342661,3960582391507706069571135866⟩
noncomputable def entry5_1 : RBox := ⟨(-15427400609117670299737639876),(-15427400601338549537534805992)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U63

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert64
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

namespace SharpPlanar.Numerical.U64
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨64,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨45219454390568235740594577,45219486414191182863513578⟩
noncomputable def entry3_0 : RBox := ⟨2662151023479610314224244,2662340248328436960495100⟩
noncomputable def entry1_0 : RBox := ⟨110311775459980402488142193,110311779874238511435676556⟩
noncomputable def entry4_0 : RBox := ⟨160102048214956714561277462,160102070925486774249635625⟩
noncomputable def entry2_0 : RBox := ⟨(-63516878358025905669846105),(-63516877520831168828707984)⟩
noncomputable def entry5_0 : RBox := ⟨259178564505436645636225823,259178570004532547393699336⟩
noncomputable def entry0_1 : RBox := ⟨(-2807240762356106847122668090),(-2807240705858514010248846168)⟩
noncomputable def entry3_1 : RBox := ⟨(-235971686668894923222142453),(-235971356662886735976578696)⟩
noncomputable def entry1_1 : RBox := ⟨(-6722237313930026312391730844),(-6722237305333416700326396240)⟩
noncomputable def entry4_1 : RBox := ⟨(-10042348068055632766658352198),(-10042348023776844025122922755)⟩
noncomputable def entry2_1 : RBox := ⟨3896013970615293976588973858,3896013972280377757392436039⟩
noncomputable def entry5_1 : RBox := ⟨(-15163719648728554434649932966),(-15163719637824501568895419016)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U64

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert67
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

namespace SharpPlanar.Numerical.U67
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨67,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨41144117038353827352040091,41144253215625072146531225⟩
noncomputable def entry3_0 : RBox := ⟨2525284559656371587443281,2526095914106420989476938⟩
noncomputable def entry1_0 : RBox := ⟨100198191106662345388411319,100198208994722598417590314⟩
noncomputable def entry4_0 : RBox := ⟨145818547250374156204010268,145818639110304269611830704⟩
noncomputable def entry2_0 : RBox := ⟨(-57736799111960428763902231),(-57736795789566044330204199)⟩
noncomputable def entry5_0 : RBox := ⟨234533014310294588094451419,234533036210791544227356204⟩
noncomputable def entry0_1 : RBox := ⟨(-2677839822607937108524066522),(-2677839487574396719733261300)⟩
noncomputable def entry3_1 : RBox := ⟨(-228191285359579932896566146),(-228189320334774333304782312)⟩
noncomputable def entry1_1 : RBox := ⟨(-6406837195470622755860287503),(-6406837145126327724383559732)⟩
noncomputable def entry4_1 : RBox := ⟨(-9583967683531943045199386354),(-9583967424385424660663680779)⟩
noncomputable def entry2_1 : RBox := ⟨3714340005564704517279323281,3714340015115997701015574947⟩
noncomputable def entry5_1 : RBox := ⟨(-14424074804447666346931383622),(-14424074741661074717629399556)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U67

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert69
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

namespace SharpPlanar.Numerical.U69
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨69,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨38725965670525225173988637,38726233950065462968444784⟩
noncomputable def entry3_0 : RBox := ⟨2435911151130145466586002,2437510197121583701289176⟩
noncomputable def entry1_0 : RBox := ⟨94209684381694865581581506,94209719699379899665332753⟩
noncomputable def entry4_0 : RBox := ⟨137332539183258939388956414,137332720416214601659233243⟩
noncomputable def entry2_0 : RBox := ⟨(-54310566318772392074747182),(-54310559770062446508819593)⟩
noncomputable def entry5_0 : RBox := ⟨220004069749971399530346746,220004112938228963376066102⟩
noncomputable def entry0_1 : RBox := ⟨(-2598006335309187612586540705),(-2598005675047227549962016843)⟩
noncomputable def entry3_1 : RBox := ⟨(-223230185907015958228560627),(-223226310646643159035671876)⟩
noncomputable def entry1_1 : RBox := ⟨(-6212521620286261371316441794),(-6212521521051243729183730029)⟩
noncomputable def entry4_1 : RBox := ⟨(-9300943786022452540819591368),(-9300943275524044196390528427)⟩
noncomputable def entry2_1 : RBox := ⟨3602344987186456796463464676,3602345005971755492394610912⟩
noncomputable def entry5_1 : RBox := ⟨(-13969769799996556829710017856),(-13969769676420472527976043698)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U69

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert7
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

namespace SharpPlanar.Numerical.U7
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨7,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨9255017422072453473490139648,9255017422072454717820799592⟩
noncomputable def entry3_0 : RBox := ⟨(-100508126055243437517112231866),(-100508126055243430064537035367)⟩
noncomputable def entry1_0 : RBox := ⟨14475793593250040465576658016,14475793593250040641945152668⟩
noncomputable def entry4_0 : RBox := ⟨(-129758095535979493468319730684),(-129758095535979492527857057668)⟩
noncomputable def entry2_0 : RBox := ⟨10889203480125470801395493899,10889203480125470849869265135⟩
noncomputable def entry5_0 : RBox := ⟨18515849546934929952624570876,18515849546934930263622638767⟩
noncomputable def entry0_1 : RBox := ⟨(-41560171502891492574793833401),(-41560171502891491343620004895)⟩
noncomputable def entry3_1 : RBox := ⟨65377434667860078588954271372,65377434667860085816903480999⟩
noncomputable def entry1_1 : RBox := ⟨(-110357156794598649356301723156),(-110357156794598649067034458759)⟩
noncomputable def entry4_1 : RBox := ⟨56262096433527742637177105371,56262096433527744127651150527⟩
noncomputable def entry2_1 : RBox := ⟨17242940942900153746840048979,17242940942900153843358366447⟩
noncomputable def entry5_1 : RBox := ⟨(-293318260904490477980707240451),(-293318260904490477355664159679)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U7

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert72
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

namespace SharpPlanar.Numerical.U72
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨72,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨35479879035540439638778542,35480361061017534402009288⟩
noncomputable def entry3_0 : RBox := ⟨2306260362224451707306171,2309115455918318093691913⟩
noncomputable def entry1_0 : RBox := ⟨86185978743837743185788992,86186045460736138395017373⟩
noncomputable def entry4_0 : RBox := ⟨125928008247073504601549269,125928350565352195406232958⟩
noncomputable def entry2_0 : RBox := ⟨(-49715545070090928791419983),(-49715532548390559217970688)⟩
noncomputable def entry5_0 : RBox := ⟨200615561533833164265645468,200615644001608090825041865⟩
noncomputable def entry0_1 : RBox := ⟨(-2486803703743634532273507655),(-2486802852943212199735180365)⟩
noncomputable def entry3_1 : RBox := ⟨(-216115603598056511256387797),(-216110616412791745493429948)⟩
noncomputable def entry1_1 : RBox := ⟨(-5942195980334608247347454313),(-5942195851227113514677802454)⟩
noncomputable def entry4_1 : RBox := ⟨(-8906423381736092026386224231),(-8906422718214427401653603777)⟩
noncomputable def entry2_1 : RBox := ⟨3446457999894222494606404335,3446458024564212118053099234⟩
noncomputable def entry5_1 : RBox := ⟨(-13339510428892642243181425914),(-13339510266767303194227269150)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U72

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
noncomputable def node : Node := ⟨73,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨34488253847812278733259608,34488665312799100467314314⟩
noncomputable def entry3_0 : RBox := ⟨2264829848675343057745323,2267241145067239206030593⟩
noncomputable def entry1_0 : RBox := ⟨83738266703248066831489754,83738328175668707913243195⟩
noncomputable def entry4_0 : RBox := ⟨122440845760059227783084932,122441161592152615288762819⟩
noncomputable def entry2_0 : RBox := ⟨(-48312772025414556353684468),(-48312760240201808210966877)⟩
noncomputable def entry5_0 : RBox := ⟨194719240577039509567750577,194719317980119701688751305⟩
noncomputable def entry0_1 : RBox := ⟨(-2451823096882598899541210283),(-2451821911689465158771894948)⟩
noncomputable def entry3_1 : RBox := ⟨(-213829777562570047856758366),(-213822837869433937343256280)⟩
noncomputable def entry1_1 : RBox := ⟨(-5857242670472195039961905782),(-5857242489447693482234756572)⟩
noncomputable def entry4_1 : RBox := ⟨(-8782251165122008771969227700),(-8782250235265441543174697191)⟩
noncomputable def entry2_1 : RBox := ⟨3397448856970763237998794420,3397448891529140080892165264⟩
noncomputable def entry5_1 : RBox := ⟨(-13141864991847581246738610822),(-13141864764670065477559950790)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨75,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨32625566819179220838262644,32626377921259852044721805⟩
noncomputable def entry3_0 : RBox := ⟨2182541253560248758578198,2187298527241964209652724⟩
noncomputable def entry1_0 : RBox := ⟨79145685379987352314723010,79145806506027769359114622⟩
noncomputable def entry4_0 : RBox := ⟨115887277370568708946531251,115887899323702450149567298⟩
noncomputable def entry2_0 : RBox := ⟨(-45679522167017543667709955),(-45679499020354665148486775)⟩
noncomputable def entry5_0 : RBox := ⟨183679989917590276979305658,183680142065640869381633733⟩
noncomputable def entry0_1 : RBox := ⟨(-2384735102740524469298815226),(-2384732764288983486301068973)⟩
noncomputable def entry3_1 : RBox := ⟨(-209382698368409371269937171),(-209368995080230487168468676)⟩
noncomputable def entry1_1 : RBox := ⟨(-5694423498687897015754881480),(-5694423141802205957571698090)⟩
noncomputable def entry4_1 : RBox := ⟨(-8544013148801583575692063400),(-8544011316598723459783571788)⟩
noncomputable def entry2_1 : RBox := ⟨3303493427917271864152561446,3303493495856631758240490675⟩
noncomputable def entry5_1 : RBox := ⟨(-12763626708315328497192444880),(-12763626261349180276804794737)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨76,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨31749892276541849833545041,31751767091296732188752856⟩
noncomputable def entry3_0 : RBox := ⟨2139929102317770733246967,2151045447262493817818870⟩
noncomputable def entry1_0 : RBox := ⟨76989796045363432649683428,76990056058484399253015378⟩
noncomputable def entry4_0 : RBox := ⟨112805793159678091251233195,112807125524816394429729905⟩
noncomputable def entry2_0 : RBox := ⟨(-44442857458069928204862560),(-44442808861316138737997791)⟩
noncomputable def entry5_0 : RBox := ⟨178508840071558194509930856,178509160499616877314274539⟩
noncomputable def entry0_1 : RBox := ⟨(-2352550163096036010734042093),(-2352546853467976473879153361)⟩
noncomputable def entry3_1 : RBox := ⟨(-207220421518011207019234757),(-207200991297964937716883458)⟩
noncomputable def entry1_1 : RBox := ⟨(-5616363179939137249983859771),(-5616362678226151760793154958)⟩
noncomputable def entry4_1 : RBox := ⟨(-8429676875649119941778103548),(-8429674300059349367427847699)⟩
noncomputable def entry2_1 : RBox := ⟨3258436481831914072017499935,3258436577168650359507588654⟩
noncomputable def entry5_1 : RBox := ⟨(-12582550711548995825518137554),(-12582550084042315631481298919)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨79,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨29322811110552962865111491,29330820686050031952720321⟩
noncomputable def entry3_0 : RBox := ⟨2007867752622005968328981,2055689533360277215132587⟩
noncomputable def entry1_0 : RBox := ⟨71025361981880153066005645,71026426900150527422476902⟩
noncomputable def entry4_0 : RBox := ⟨104263256688204987237337740,104268702490694410184229669⟩
noncomputable def entry2_0 : RBox := ⟨(-41019725567522601226005323),(-41019529407171580370470519)⟩
noncomputable def entry5_0 : RBox := ⟨164240069663914498848115209,164241366017035553358202994⟩
noncomputable def entry0_1 : RBox := ⟨(-2261014121194042130851462068),(-2260994387195666474511458286)⟩
noncomputable def entry3_1 : RBox := ⟨(-201004629630956783334923914),(-200888438472502983430887563)⟩
noncomputable def entry1_1 : RBox := ⟨(-5394521055182237619700155447),(-5394518087116826157647661301)⟩
noncomputable def entry4_1 : RBox := ⟨(-8104326668282157289029008463),(-8104311444286469510677629778)⟩
noncomputable def entry2_1 : RBox := ⟨3130345365946406981446482680,3130345922594364175329489147⟩
noncomputable def entry5_1 : RBox := ⟨(-12068873053152704865244458821),(-12068869379493682377960785193)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨81,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨27853980445518076646272635,27869795572269928233744025⟩
noncomputable def entry3_0 : RBox := ⟨1912575514539140055652349,2007029626433532849370365⟩
noncomputable def entry1_0 : RBox := ⟨67425847373342292318171089,67427953875741309973050354⟩
noncomputable def entry4_0 : RBox := ⟨99094718235648998920539485,99105483549621009084573953⟩
noncomputable def entry2_0 : RBox := ⟨(-38952678946191913116459748),(-38952291324840006831204955)⟩
noncomputable def entry5_0 : RBox := ⟨155656510803837449004884597,155659073380274169105106698⟩
noncomputable def entry0_1 : RBox := ⟨(-2203853809339301902275929752),(-2203814838903789054847562520)⟩
noncomputable def entry3_1 : RBox := ⟨(-197070252662116353932533776),(-196840669142630715958973079)⟩
noncomputable def entry1_1 : RBox := ⟨(-5256116507905972182976778533),(-5256110646065698212563603436)⟩
noncomputable def entry4_1 : RBox := ⟨(-7901033627261356012688315915),(-7901003577109544663517449390)⟩
noncomputable def entry2_1 : RBox := ⟨3050399685646125444678751272,3050400783286973647811141329⟩
noncomputable def entry5_1 : RBox := ⟨(-11749091424183810132611030741),(-11749084175986101227482552601)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U81

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert84
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

namespace SharpPlanar.Numerical.U84
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨84,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨25847881075733630545568307,25876361972364754893635378⟩
noncomputable def entry3_0 : RBox := ⟨1772894991603785576002624,1942076371480515548638995⟩
noncomputable def entry1_0 : RBox := ⟨62518618603053901992289615,62522583796367012915295433⟩
noncomputable def entry4_0 : RBox := ⟨92032379334032134399491066,92052647643189649115720524⟩
noncomputable def entry2_0 : RBox := ⟨(-36133105221054246365380957),(-36132369097984728497728458)⟩
noncomputable def entry5_0 : RBox := ⟨143988977886786392464882979,143993841402202503037066912⟩
noncomputable def entry0_1 : RBox := ⟨(-2123329322789680392031358062),(-2123279037032293243072193407)⟩
noncomputable def entry3_1 : RBox := ⟨(-191379213521368048449310316),(-191083190342828496894896170)⟩
noncomputable def entry1_1 : RBox := ⟨(-5061335155642212619791146134),(-5061327545180151182235744270)⟩
noncomputable def entry4_1 : RBox := ⟨(-7614519693141032542380390222),(-7614480708497260498405663986)⟩
noncomputable def entry2_1 : RBox := ⟨2937851082966761316573966079,2937852515909833313363096872⟩
noncomputable def entry5_1 : RBox := ⟨(-11299959325427655891360974965),(-11299949867764102222716401392)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U84

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
noncomputable def node : Node := ⟨85,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨25231071068719851404578709,25255349313996943168416177⟩
noncomputable def entry3_0 : RBox := ⟨1753391962944408970701623,1896310424620706477456032⟩
noncomputable def entry1_0 : RBox := ⟨61001930332276108877402118,61005550505355022533736532⟩
noncomputable def entry4_0 : RBox := ⟨89847625010406581505911855,89866160671803456106707375⟩
noncomputable def entry2_0 : RBox := ⟨(-35260899591246753688092550),(-35260216953111999671585543)⟩
noncomputable def entry5_0 : RBox := ⟨140390505058273719270312734,140395008452464428675301805⟩
noncomputable def entry0_1 : RBox := ⟨(-2097788512945288765066997904),(-2097718264417475033662753142)⟩
noncomputable def entry3_1 : RBox := ⟨(-189596642125929614652028869),(-189183545437274374819625980)⟩
noncomputable def entry1_1 : RBox := ⟨(-4999579181483676639568768056),(-4999568494333555214254380621)⟩
noncomputable def entry4_1 : RBox := ⟨(-7523584424665376201239346106),(-7523529702625845941147875745)⟩
noncomputable def entry2_1 : RBox := ⟨2902156808558552618644536340,2902158819463200260094093913⟩
noncomputable def entry5_1 : RBox := ⟨(-11157780530099753802763251033),(-11157767254491668280634953253)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨87,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨24046266622162738396376086,24094226341776398649275587⟩
noncomputable def entry3_0 : RBox := ⟨1620471351517924438812870,1902975135992720958728974⟩
noncomputable def entry1_0 : RBox := ⟨58127526461835637743152314,58134676380057376715135564⟩
noncomputable def entry4_0 : RBox := ⟨85694604947617836439488877,85731193214892727115025811⟩
noncomputable def entry2_0 : RBox := ⟨(-33608959360100522782839631),(-33607614069353549291740829)⟩
noncomputable def entry5_0 : RBox := ⟨133584040736537279361997507,133592921306331281624072856⟩
noncomputable def entry0_1 : RBox := ⟨(-2048523313394386680424182629),(-2048384464969811390751494392)⟩
noncomputable def entry3_1 : RBox := ⟨(-186212490403477543954778930),(-185395489173839286135542958)⟩
noncomputable def entry1_1 : RBox := ⟨(-4880484200970883374236696433),(-4880463088112480903661062607)⟩
noncomputable def entry4_1 : RBox := ⟨(-7348090212237540847315202862),(-7347982161769340204071617862)⟩
noncomputable def entry2_1 : RBox := ⟨2833306798481800898457122575,2833310763482335677327585704⟩
noncomputable def entry5_1 : RBox := ⟨(-10883890211484943054744892019),(-10883864019253156288931109256)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨88,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨23458593387283988855079298,23569804333233292721358013⟩
noncomputable def entry3_0 : RBox := ⟨1400632984768580946264842,2061777370396554378420680⟩
noncomputable def entry1_0 : RBox := ⟨56762546911369065692099444,56778058432566919668878711⟩
noncomputable def entry4_0 : RBox := ⟨83707993752518244735457914,83787189459845203262737887⟩
noncomputable def entry2_0 : RBox := ⟨(-32826778677750089807391606),(-32823906800364200137731704)⟩
noncomputable def entry5_0 : RBox := ⟨130360777132513105488652736,130379768142631843571813354⟩
noncomputable def entry0_1 : RBox := ⟨(-2024761471350972067658769170),(-2024565111797397410479897248)⟩
noncomputable def entry3_1 : RBox := ⟨(-184636245217309466755194455),(-183478920372906970847710254)⟩
noncomputable def entry1_1 : RBox := ⟨(-4823041821962932113630054431),(-4823012123684616879781144837)⟩
noncomputable def entry4_1 : RBox := ⟨(-7263387626221238960338565646),(-7263235654402597683541946924)⟩
noncomputable def entry2_1 : RBox := ⟨2800091486591035040581417807,2800097057209807010918718511⟩
noncomputable def entry5_1 : RBox := ⟨(-10751925949057049325341695186),(-10751889137259213126869267731)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨9,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨4321341458338316295355166215,4321341458338317650979313652⟩
noncomputable def entry3_0 : RBox := ⟨496151243184250657026487414,496151243184258759022333537⟩
noncomputable def entry1_0 : RBox := ⟨15345464255445217043278564826,15345464255445217236927629884⟩
noncomputable def entry4_0 : RBox := ⟨(-13085806955470563891015732941),(-13085806955470562877394230982)⟩
noncomputable def entry2_0 : RBox := ⟨1105495588199776125195635368,1105495588199776177972243822⟩
noncomputable def entry5_0 : RBox := ⟨40215933342322435693105046347,40215933342322436032198617241⟩
noncomputable def entry0_1 : RBox := ⟨(-25861357817357871918782934785),(-25861357817357870002116339192)⟩
noncomputable def entry3_1 : RBox := ⟨7773129974041814931532587003,7773129974041825990779885955⟩
noncomputable def entry1_1 : RBox := ⟨(-76013290877195458512743853910),(-76013290877195458112690848658)⟩
noncomputable def entry4_1 : RBox := ⟨(-68671178755677197099137877228),(-68671178755677195032714349467)⟩
noncomputable def entry2_1 : RBox := ⟨28333295677012061102171718204,28333295677012061226750845807⟩
noncomputable def entry5_1 : RBox := ⟨(-224876512808182915990006099460),(-224876512808182915190848723603)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U9

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert91
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

namespace SharpPlanar.Numerical.U91
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨91,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨21718608090374570638359083,22195362735226830583877969⟩
noncomputable def entry3_0 : RBox := ⟨218056273345489766360124,3069297530120041530549068⟩
noncomputable def entry1_0 : RBox := ⟨52930818670688180981888043,52994845176066299870128110⟩
noncomputable def entry4_0 : RBox := ⟨78077721210580419747658045,78403945273728445678349377⟩
noncomputable def entry2_0 : RBox := ⟨(-30639709238165833179843376),(-30627975841321753226132755)⟩
noncomputable def entry5_0 : RBox := ⟨121344630989356205565960108,121422324102095068494734664⟩
noncomputable def entry0_1 : RBox := ⟨(-1957084141686511316275499844),(-1955908932467383314397227948)⟩
noncomputable def entry3_1 : RBox := ⟨(-182467396708296398662775952),(-175526091288494839314913699)⟩
noncomputable def entry1_1 : RBox := ⟨(-4658614819822969323323550243),(-4658437999840064069595034337)⟩
noncomputable def entry4_1 : RBox := ⟨(-7020921483578253934893376900),(-7020017420716694508652130960)⟩
noncomputable def entry2_1 : RBox := ⟨2704945797509002926526113375,2704978687532959338217415645⟩
noncomputable def entry5_1 : RBox := ⟨(-10374626354848746198701001861),(-10374408601872812149602022890)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U91

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
noncomputable def node : Node := ⟨93,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨20531789233365756941969145,21474723546212979197896502⟩
noncomputable def entry3_0 : RBox := ⟨(-1231764205723791927572526),4408849321426882235608558⟩
noncomputable def entry1_0 : RBox := ⟨50570068380059448872741670,50696891915767274666237957⟩
noncomputable def entry4_0 : RBox := ⟨74543101704563379601934149,75188924048348895880736487⟩
noncomputable def entry2_0 : RBox := ⟨(-29304107409178083505393061),(-29280880848157303147608911)⟩
noncomputable def entry5_0 : RBox := ⟨115821691316558788720363169,115975529692267459382723342⟩
noncomputable def entry0_1 : RBox := ⟨(-1914709094127801784933557069),(-1912384678932689944401191247)⟩
noncomputable def entry3_1 : RBox := ⟨(-182632659883881655967408718),(-168897222560039749961307273)⟩
noncomputable def entry1_1 : RBox := ⟨(-4555131162826296740461567387),(-4554781427766523363963068828)⟩
noncomputable def entry4_1 : RBox := ⟨(-6868293443375942876476661987),(-6866506170336171568911096378)⟩
noncomputable def entry2_1 : RBox := ⟨2645018422117926211894492028,2645083402516436367136438039⟩
noncomputable def entry5_1 : RBox := ⟨(-10137513968293276442824964668),(-10137083555986445788973291891)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨96,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨18834631545485148620096697,20535614420580931024470927⟩
noncomputable def entry3_0 : RBox := ⟨(-3552972653573772689247104),6573750542147599957150323⟩
noncomputable def entry1_0 : RBox := ⟨47298387912968468689962380,47536460892657485571678142⟩
noncomputable def entry4_0 : RBox := ⟨69592529115391539218053409,70805388688656718113157288⟩
noncomputable def entry2_0 : RBox := ⟨(-27461696485324824484545777),(-27417810748905469891672764)⟩
noncomputable def entry5_0 : RBox := ⟨108197375879926891790501312,108488029177644987406257782⟩
noncomputable def entry0_1 : RBox := ⟨(-1854048012087913694155546091),(-1851044712296977956620941020)⟩
noncomputable def entry3_1 : RBox := ⟨(-179987430171579307654003671),(-162248313254108228506292417)⟩
noncomputable def entry1_1 : RBox := ⟨(-4408185959446149063475160846),(-4407732226984725680845506983)⟩
noncomputable def entry4_1 : RBox := ⟨(-6651073626645190416046199306),(-6648756365369657116115011512)⟩
noncomputable def entry2_1 : RBox := ⟨2559955624701432692267952446,2560040198368948959186834693⟩
noncomputable def entry5_1 : RBox := ⟨(-9801407755790775247081537450),(-9800847670409817258140873062)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨97,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨18548879862342802182925828,19997588918259947846773960⟩
noncomputable def entry3_0 : RBox := ⟨(-2793240023322544140535954),5764229804166692709808920⟩
noncomputable def entry1_0 : RBox := ⟨46305364557657970744136479,46521192307785117132561845⟩
noncomputable def entry4_0 : RBox := ⟨68189135771070524822467874,69290728682439773422889605⟩
noncomputable def entry2_0 : RBox := ⟨(-26881208139486383073008675),(-26840962605301910622903582)⟩
noncomputable def entry5_0 : RBox := ⟨105854418411403062294372606,106120829026491078551458990⟩
noncomputable def entry0_1 : RBox := ⟨(-1835170018678880462543042323),(-1830966526384158725757071864)⟩
noncomputable def entry3_1 : RBox := ⟨(-182020781057671119730761486),(-157219172284256069955716896)⟩
noncomputable def entry1_1 : RBox := ⟨(-4361365354974999904753089867),(-4360727503017129180261621134)⟩
noncomputable def entry4_1 : RBox := ⟨(-6582077618911587605163192571),(-6578821143337379173517147623)⟩
noncomputable def entry2_1 : RBox := ⟨2532789615238144811735704908,2532908450926947817614306392⟩
noncomputable def entry5_1 : RBox := ⟨(-9694362589083153194799413403),(-9693575444717520516968906306)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
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
noncomputable def node : Node := ⟨99,by norm_num [residues]⟩
noncomputable def entry0_0 : RBox := ⟨17054153344218146115296913,19920493832963153098644698⟩
noncomputable def entry3_0 : RBox := ⟨(-7032495784590371389638405),9907216631776212413538007⟩
noncomputable def entry1_0 : RBox := ⟨44284890090173736410714602,44711878122094923968391024⟩
noncomputable def entry4_0 : RBox := ⟨64865958846679133205546001,67044257184185437692686868⟩
noncomputable def entry2_0 : RBox := ⟨(-25797072134934088623003537),(-25717568594770032992344542)⟩
noncomputable def entry5_0 : RBox := ⟨101238765297876400652392955,101765305944157033321839773⟩
noncomputable def entry0_1 : RBox := ⟨(-1799475741262405681133375653),(-1791156051417881422127050140)⟩
noncomputable def entry3_1 : RBox := ⟨(-191253504081492375884200029),(-142141461603194799729733828)⟩
noncomputable def entry1_1 : RBox := ⟨(-4270785954148737438115081601),(-4269523925969082705075490567)⟩
noncomputable def entry4_1 : RBox := ⟨(-6449003221571201814028171068),(-6442563045446121378844000521)⟩
noncomputable def entry2_1 : RBox := ⟨2480124794031989901696434847,2480359606821274880440530557⟩
noncomputable def entry5_1 : RBox := ⟨(-9487305878114569505909443245),(-9485749779782296144196224326)⟩
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
end SharpPlanar.Numerical.U99

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
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

namespace SharpPlanar
open Numerical
lemma tableRaw_large {n : ℕ} (hn : 100<n) : tableRaw n=(0,0,0,0) := by
  unfold tableRaw
  split <;> first | omega | rfl
lemma tableC_large (a : Bool) {n : ℕ} (hn : 100<n) : tableC a n=0 := by
  simp [tableC,tableRaw_large hn,show n≠0 by omega]
lemma tableD_large (a : Bool) {n : ℕ} (hn : 100<n) : tableD a n=0 := by
  simp [tableD,tableRaw_large hn,show n≠0 by omega]
noncomputable def tableCoords (a : Bool) (ni : Node×Bool) : ℝ :=
  if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ)
lemma tableCoords_mem (a : Bool) : Memℓp (tableCoords a) 1 := by
  classical
  apply memℓp_gen
  have hs : (Function.support (fun ni => |tableCoords a ni|)).Finite := by
    apply (Set.finite_range finiteIndex).subset
    intro ni hni
    change (∃ i, finiteIndex i=ni)
    have hindex : (∃ i, finiteIndex i=ni) ↔ ni.1.val≤100 := by
      rcases ni with ⟨n,d⟩
      exact finiteIndex_range n d
    rw [hindex]
    by_contra hn
    have hn' : 100<ni.1.val := by omega
    have hz : tableCoords a ni=0 := by
      simp [tableCoords,tableD_large a hn',tableC_large a hn']
    exact hni (by simp [hz])
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using summable_of_hasFiniteSupport hs
noncomputable def tableList (a : Bool) : X := ⟨tableCoords a,tableCoords_mem a⟩
noncomputable def tableData (a : Bool) : CardinalData :=
  ⟨(tableConstant a:ℝ),(tableC a 0:ℝ),(tableD a 0:ℝ),tableList a⟩
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
noncomputable def node : Node := ⟨1,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨100,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨12,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨13,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨15,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨16,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨19,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨21,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨24,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨25,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨27,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨28,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨3,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨31,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨33,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨36,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨37,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨39,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨4,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨40,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨43,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨45,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨48,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨49,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨51,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨52,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨55,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨57,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨60,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨61,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨63,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨64,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨67,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨69,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨7,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨72,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨73,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨75,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨76,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨79,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨81,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨84,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨85,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨87,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨88,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨9,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨91,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨93,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨96,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨97,by norm_num [residues]⟩
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
noncomputable def node : Node := ⟨99,by norm_num [residues]⟩
end SharpPlanar.Residual99

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
noncomputable def tableCoordRat (a : Bool) (ni : Node×Bool) : ℚ :=
  if ni.2 then tableD a ni.1.val else tableC a ni.1.val
noncomputable def tableFiniteNormRat (a : Bool) : ℚ := ∑ i : FiniteIndex, |tableCoordRat a (finiteIndex i)|
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TailCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation coefficients

Truncating a summable coefficient family contracts its norm. The finite rational
table for OpenAI's sharp planar Fourier construction bounds the tails of the
exact coefficients through the coefficient error estimate.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
noncomputable def tailList (x : X) (N : ℕ) : X :=
  ⟨(fun k => if N<k.1.val then x k else 0), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs,apply_ite,abs_zero]
      using tailScalar_summable x N⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def directEnvelope (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell
noncomputable def transformEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  ∑ j : Fin 6,densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell
noncomputable def atomicEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  ∑ j : Fin 7,atomL j s*(Real.pi*zCap j)^ell
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def pieceIntCap (j : Fin 6) (n : ℕ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n
noncomputable def atomIntCap (j : Fin 7) (n : ℕ) : ℝ :=
  atomMass j*lambdaCap j*atomBase j^n
noncomputable def directRational (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j/6*(piUpper*((j.val:ℝ)+1)/6)^ell
noncomputable def transformRational (ell n : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j*pieceIntCap j n*(piUpper*zCap ⟨j.val,by omega⟩)^ell
noncomputable def atomicRational (ell n : ℕ) : ℝ :=
  ∑ j : Fin 7,atomIntCap j n*(piUpper*zCap j)^ell
noncomputable def taylorEnvelope (ell n : ℕ) : ℝ :=
  80*piUpper^ell+(23:ℝ)/10*transformRational ell n+(17:ℝ)/1000*atomicRational ell n
noncomputable def halfMass (j : Fin 6) : ℝ :=
  if slopeCap j=0 then 1/6 else min (1/6) (2/((314159/100000:ℝ)*slopeCap j))
noncomputable def halfCap (j : Fin 6) : ℝ := lambdaCap ⟨j.val,by omega⟩*halfBase j*halfMass j
noncomputable def halfTransform (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j*halfCap j*(piUpper*zCap ⟨j.val,by omega⟩)^ell
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
noncomputable def sharpTaylor (ell n : ℕ) : ℝ :=
  (425:ℝ)/1000*piUpper^ell+(23:ℝ)/10*(directRational ell+transformRational ell n)+
    (17:ℝ)/1000*atomicRational ell n
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Dilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def scaleFactor : ℝ := (Real.sqrt b)⁻¹
lemma scaleFactor_pos : 0 < scaleFactor := inv_pos.mpr (Real.sqrt_pos.mpr b_pos)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FourierPairSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ComplexConjugate
open scoped FourierTransform RealInnerProductSpace

open scoped FourierTransform RealInnerProductSpace

namespace SharpPlanar


noncomputable def gaussianCoeff (t : ℝ) : ℂ :=
  (Real.pi : ℂ) * b * ((h : ℂ) - Complex.I*t)

noncomputable def spectralGaussian (t : ℝ) (x : Plane) : ℂ :=
  Complex.exp (-gaussianCoeff t * (‖x‖ : ℂ)^2)

end SharpPlanar

namespace SharpPlanar

noncomputable def gaussianSpectral (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) : ℂ :=
  ∫ t, spectralGaussian t x * f t ∂μ

noncomputable def qComplex (p : CardinalData) (x : Plane) : ℂ :=
  gaussianSpectral (Measure.dirac 0) (fun _ => (p.C : ℂ)*Pcoeff 0) x +
    (∑ j ∈ Finset.Icc (1 : ℕ) 6,
      gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j) x) +
    (∑ j ∈ Finset.range 6,
      gaussianSpectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) x)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def qComplexSchwartz (p : CardinalData) : SchwartzMap Plane ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (qSchwartz p)
noncomputable def kSchwartz (p : CardinalData) : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM Complex.reCLM (𝓕 (qComplexSchwartz p))
noncomputable def pairLeft (p q : CardinalData) : SchwartzMap Plane ℝ := qSchwartz p+kSchwartz q
noncomputable def pairRight (p q : CardinalData) : SchwartzMap Plane ℝ := qSchwartz q+kSchwartz p
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma hexResidue_table : ∀ a c : Fin 12,
    (a.val^2+a.val*c.val+c.val^2)%12 ∈ residues := by decide +kernel
lemma hexNat_residue (v : ℤ×ℤ) : hexNat v%12∈residues := by
  have ha : 0 ≤ v.1%12 := Int.emod_nonneg _ (by norm_num)
  have hc : 0 ≤ v.2%12 := Int.emod_nonneg _ (by norm_num)
  have ha' : (v.1%12).toNat<12 := by omega
  have hc' : (v.2%12).toNat<12 := by omega
  have hh := hexResidue_table ⟨(v.1%12).toNat,ha'⟩ ⟨(v.2%12).toNat,hc'⟩
  have he : (hexNat v:ℤ)%12=((v.1%12).toNat^2+(v.1%12).toNat*(v.2%12).toNat+(v.2%12).toNat^2:ℕ)%12 := by
    rw [hexNat_coe]
    push_cast
    rw [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hc]
    simp only [hexForm,pow_two,Int.add_emod,Int.mul_emod,Int.emod_emod]
  have he' : hexNat v%12=((v.1%12).toNat^2+(v.1%12).toNat*(v.2%12).toNat+(v.2%12).toNat^2)%12 := by exact_mod_cast he
  rw [he']; exact hh
noncomputable def hexNode (v : ℤ×ℤ) (hv : v≠0) : Node := ⟨hexNat v,hexNat_pos hv,hexNat_residue v⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticeGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def spectralParameter (t : ℝ) : ℂ := (b:ℂ)*((h:ℂ)-Complex.I*t)
noncomputable def latticeDamping (p : ℤ×ℤ) : ℝ :=
  Real.exp (-Real.pi*b*h*‖latticePoint p‖^2)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MixedTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
noncomputable def transformTaylor (ell n : ℕ) : ℝ :=
  (23:ℝ)/10*transformRational ell n+(17:ℝ)/1000*atomicRational ell n
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
def shortNode : Fin 21 → Node := ![⟨1,by norm_num [residues]⟩,⟨3,by norm_num [residues]⟩,⟨4,by norm_num [residues]⟩,⟨7,by norm_num [residues]⟩,⟨9,by norm_num [residues]⟩,⟨12,by norm_num [residues]⟩,⟨13,by norm_num [residues]⟩,⟨15,by norm_num [residues]⟩,⟨16,by norm_num [residues]⟩,⟨19,by norm_num [residues]⟩,⟨21,by norm_num [residues]⟩,⟨24,by norm_num [residues]⟩,⟨25,by norm_num [residues]⟩,⟨27,by norm_num [residues]⟩,⟨28,by norm_num [residues]⟩,⟨31,by norm_num [residues]⟩,⟨33,by norm_num [residues]⟩,⟨36,by norm_num [residues]⟩,⟨37,by norm_num [residues]⟩,⟨39,by norm_num [residues]⟩,⟨40,by norm_num [residues]⟩]
lemma shortNode_inj : Function.Injective shortNode := by decide +kernel
lemma shortNode_le (i : Fin 21) : (shortNode i).val ≤ 40 := by revert i; decide +kernel
lemma shortNode_cover_check : ∀ n : Fin 41,0<n.val ∧ n.val%12∈residues →
    ∃ i : Fin 21,(shortNode i).val=n.val := by decide +kernel
def headNodeNat : HeadNodeIndex → ℕ
  | none => 0
  | some i => (shortNode i).val
noncomputable def headC (p : CardinalData) : HeadNodeIndex → ℝ
  | none => p.c₀
  | some i => p.x (shortNode i,false)
noncomputable def headD (p : CardinalData) : HeadNodeIndex → ℝ
  | none => p.d₀
  | some i => p.x (shortNode i,true)
noncomputable def headRational (p : CardinalData) (s : ℝ) : ℝ :=
  p.C+∑ i,(headC p i/(s-headNodeNat i)^2+headD p i/(s-headNodeNat i))
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHeadBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def signedHeadC (a : Bool) (i : HeadNodeIndex) : ℝ :=
  (if a then 1 else -1)*headC (tableData a) i
noncomputable def signedHeadD (a : Bool) (i : HeadNodeIndex) : ℝ :=
  (if a then 1 else -1)*headD (tableData a) i
noncomputable def headLowerRat (a : Bool) : ℚ :=
  let σ : ℚ := if a then 1 else -1
  σ*tableConstant a+
    min (∑ i : HeadNodeIndex, σ*tableD a (headNodeNat i)) 0/(83/2)+
    ∑ i : HeadNodeIndex,(min (σ*tableC a (headNodeNat i)) 0/(83/2-headNodeNat i)^2+
      min (σ*tableD a (headNodeNat i)) 0*headNodeNat i/((83/2)*(83/2-headNodeNat i)))
lemma headLowerRat_check (a : Bool) : (12:ℚ)/1000<headLowerRat a := by
  cases a <;> decide +kernel
end SharpPlanar

end OAI
end


