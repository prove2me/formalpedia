-- Prove2me | Definitions.Def_OAIQ098E125
-- name    : OAIQ098E125
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T17:13:06.2612+00:00
-- url     : https://prove2.me/theorems/7323e796-4024-4831-a78a-23ab61dbc365
-- title:
--   Definitions bundle OAIQ098E125 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 908 declarations of OpenAI's Lean: 908 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans8_r3_10`, `OAI.SharpPlanar.CachedData.trans8_r3_11`, `OAI.SharpPlanar.CachedData.trans8_r3_12`, `OAI.SharpPlanar.CachedData.trans8_r3_13`, `OAI.SharpPlanar.CachedData.trans8_r3_14`, `OAI.SharpPlanar.CachedData.trans8_r3_2`, `OAI.SharpPlanar.CachedData.trans8_r3_3`, `OAI.SharpPlanar.CachedData.trans8_r3_4`, `OAI.SharpPlanar.CachedData.trans8_r3_5`, `OAI.SharpPlanar.CachedData.trans8_r3_6`, `OAI.SharpPlanar.CachedData.trans8_r3_7`, `OAI.SharpPlanar.CachedData.trans8_r3_8`, `OAI.SharpPlanar.CachedData.trans8_r3_9`, `OAI.SharpPlanar.CachedData.trans8_r4`, `OAI.SharpPlanar.CachedData.trans8_r4_0`, `OAI.SharpPlanar.CachedData.trans8_r4_1`, `OAI.SharpPlanar.CachedData.trans8_r4_10`, `OAI.SharpPlanar.CachedData.trans8_r4_11`, `OAI.SharpPlanar.CachedData.trans8_r4_12`, `OAI.SharpPlanar.CachedData.trans8_r4_13`, `OAI.SharpPlanar.CachedData.trans8_r4_14`, `OAI.SharpPlanar.CachedData.trans8_r4_15`, `OAI.SharpPlanar.CachedData.trans8_r4_2`, `OAI.SharpPlanar.CachedData.trans8_r4_3`, `OAI.SharpPlanar.CachedData.trans8_r4_4`, `OAI.SharpPlanar.CachedData.trans8_r4_5`, `OAI.SharpPlanar.CachedData.trans8_r4_6`, `OAI.SharpPlanar.CachedData.trans8_r4_7`, `OAI.SharpPlanar.CachedData.trans8_r4_8`, `OAI.SharpPlanar.CachedData.trans8_r4_9`, `OAI.SharpPlanar.CachedData.trans8_r5`, `OAI.SharpPlanar.CachedData.trans8_r5_0`, `OAI.SharpPlanar.CachedData.trans8_r5_1`, `OAI.SharpPlanar.CachedData.trans8_r5_10`, `OAI.SharpPlanar.CachedData.trans8_r5_11`, `OAI.SharpPlanar.CachedData.trans8_r5_12`, `OAI.SharpPlanar.CachedData.trans8_r5_13`, `OAI.SharpPlanar.CachedData.trans8_r5_14`, `OAI.SharpPlanar.CachedData.trans8_r5_15`, `OAI.SharpPlanar.CachedData.trans8_r5_2` and 868 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_CanonicalRows`, `PlanarPacking_Certificate_LEntries`, `PlanarPacking_Certificate_TransformedPowers10`, `PlanarPacking_Certificate_WUCert12`, `PlanarPacking_Certificate_WUCert13`, `PlanarPacking_Certificate_WUCert15`, `PlanarPacking_Certificate_WUCert16`, `PlanarPacking_Certificate_WUCert19`, `PlanarPacking_Certificate_WUCert21`, `PlanarPacking_Certificate_WUCert24`, `PlanarPacking_Certificate_WUCert25`, `PlanarPacking_Certificate_WUCert27`, `PlanarPacking_Certificate_WUCert28`, `PlanarPacking_Certificate_WUCert31`, `PlanarPacking_Certificate_WUCert33`, `PlanarPacking_Certificate_WUCert36`, `PlanarPacking_Certificate_WUCert37`, `PlanarPacking_Certificate_WUCert39`, `PlanarPacking_Certificate_WUCert40`, `PlanarPacking_Certificate_WUCert43`, `PlanarPacking_Certificate_WUCert45`, `PlanarPacking_Certificate_WUCert48`, `PlanarPacking_Certificate_WUCert49`, `PlanarPacking_Certificate_WUCert51`, `PlanarPacking_Certificate_WUCert52`, `PlanarPacking_Certificate_WUCert55`, `PlanarPacking_Certificate_WUCert57`, `PlanarPacking_Certificate_WUCert60`, `PlanarPacking_Certificate_WUCert61`, `PlanarPacking_Certificate_WUCert63`, `PlanarPacking_Certificate_WUCert64`, `PlanarPacking_Certificate_WUCert67`, `PlanarPacking_Certificate_WUCert69`, `PlanarPacking_Certificate_WUCert7`, `PlanarPacking_Certificate_WUCert72`, `PlanarPacking_Certificate_WUCert73`, `PlanarPacking_Certificate_WUCert75`, `PlanarPacking_Certificate_WUCert76`, `PlanarPacking_Certificate_WUCert79`, `PlanarPacking_Certificate_WUCert81`, `PlanarPacking_Certificate_WUCert84`, `PlanarPacking_Certificate_WUCert85`, `PlanarPacking_Certificate_WUCert87`, `PlanarPacking_Certificate_WUCert88`, `PlanarPacking_Certificate_WUCert9`, `PlanarPacking_Certificate_WUCert91`, `PlanarPacking_Certificate_WUCert93`, `PlanarPacking_Certificate_WUCert96`, `PlanarPacking_Certificate_WUCert97`, `PlanarPacking_Certificate_WUCert99`, `PlanarPacking_FiniteFull`, `PlanarPacking_FiniteInverse`, `PlanarPacking_FiniteSplit`, `PlanarPacking_FiniteTail`, `PlanarPacking_FiniteU`, `PlanarPacking_MatrixInverse`.
--
--   **Imports.** It imports the bundles `OAIQ098E006`, `OAIQ098E031` and `OAIQ098E032` of this split; the published statements `OAI.SharpPlanar.Numerical.defectminus_lt_one_e`, `OAI.SharpPlanar.Numerical.defectplus_lt_one_e` and `OAI.SharpPlanar.approximate_inverse_bijective_e`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E126`; the statements `OAI.SharpPlanar.Numerical.U28.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U28.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U28.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U28.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U28.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U28.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U31.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U31.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U33.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U33.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U33.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U33.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U36.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U36.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U36.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U36.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U36.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U36.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U37.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U37.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U37.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U39.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U39.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U39.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U40.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U40.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U40.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U40.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U43.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U43.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U43.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U45.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U45.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U45.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U48.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U48.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U49.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U49.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U51.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U51.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U51.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U51.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U51.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U51.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U52.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U52.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U52.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U52.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U52.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U52.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U55.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U55.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U55.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U57.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U57.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U60.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U60.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U60.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U60.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U60.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U60.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U61.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U61.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U61.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U61.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U61.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U61.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U63.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U63.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U64.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U64.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U67.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U67.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U67.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U67.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U67.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U67.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U69.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U69.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U69.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U69.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U69.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U69.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U72.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U72.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U73.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U73.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U75.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U75.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U75.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U75.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U75.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U75.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U76.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U76.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U76.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U76.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U76.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U76.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U79.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U79.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U79.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U7.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U7.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U7.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U81.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U81.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U84.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U84.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U84.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U84.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U84.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U84.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U85.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U85.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U85.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U85.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U85.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U85.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U87.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U87.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U88.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U88.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U88.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U88.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U91.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U91.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U91.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U91.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U91.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U91.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U93.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U93.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U93.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U93.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U93.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U93.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U96.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U96.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U96.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U96.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U97.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U97.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U97.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U99.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U99.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U99.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U99.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U99.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U99.wuplus_column_e`, `OAI.SharpPlanar.Numerical.centralV_norm_e`, `OAI.SharpPlanar.Numerical.lentry0_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry3_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_5_contains_e`, `OAI.SharpPlanar.atomL_nonneg_e`, `OAI.SharpPlanar.atomicCoefficient_norm_e`, `OAI.SharpPlanar.dampingCap_pos_e`, `OAI.SharpPlanar.decay_pieceBase_e`, `OAI.SharpPlanar.endpoint_kernel_bounds_e`, `OAI.SharpPlanar.kernelMoment_endpoint_bound_e`, `OAI.SharpPlanar.kernelMoment_segment_bound_e`, `OAI.SharpPlanar.lambdaCap_nonneg_e`, `OAI.SharpPlanar.massRational_nonneg_e`, `OAI.SharpPlanar.pieceBase_contains_e`, `OAI.SharpPlanar.pieceBase_pos_e`, `OAI.SharpPlanar.pieceL_nonneg_e`, `OAI.SharpPlanar.pieceMass_le_e`, `OAI.SharpPlanar.pieceMass_nonneg_e`, `OAI.SharpPlanar.piece_damping_bound_e`, `OAI.SharpPlanar.piece_kernel_bounds_e`, `OAI.SharpPlanar.piece_secant_bound_e`, `OAI.SharpPlanar.segmentEnvelope_integral_bound_e`, `OAI.SharpPlanar.segment_exp_integral_bound_e`, `OAI.SharpPlanar.sharp_atomic_bound_e`, `OAI.SharpPlanar.slopeCap_nonneg_e` and `OAI.SharpPlanar.zCap_nonneg_e`; the proofs of `OAI.SharpPlanar.Numerical.U28.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U28.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U28.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U28.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U36.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U36.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U39.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U43.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U45.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U51.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U51.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U52.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U52.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U60.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U60.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U61.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U61.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U63.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U67.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U67.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U69.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U69.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U75.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U75.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U76.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U76.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U84.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U84.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U85.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U85.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U87.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U91.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U91.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U93.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U93.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U99.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U99.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.centralV_norm_e`, `OAI.SharpPlanar.Numerical.lentry10_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry3_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_0_contains_e`, `OAI.SharpPlanar.atomL_nonneg_e`, `OAI.SharpPlanar.atomicCoefficient_norm_e`, `OAI.SharpPlanar.dampingCap_pos_e`, `OAI.SharpPlanar.decay_pieceBase_e`, `OAI.SharpPlanar.endpoint_kernel_bounds_e`, `OAI.SharpPlanar.kernelMoment_endpoint_bound_e`, `OAI.SharpPlanar.kernelMoment_segment_bound_e`, `OAI.SharpPlanar.lambdaCap_nonneg_e`, `OAI.SharpPlanar.massRational_nonneg_e`, `OAI.SharpPlanar.pieceBase_contains_e`, `OAI.SharpPlanar.pieceBase_pos_e`, `OAI.SharpPlanar.pieceL_nonneg_e`, `OAI.SharpPlanar.pieceMass_le_e`, `OAI.SharpPlanar.pieceMass_nonneg_e`, `OAI.SharpPlanar.piece_damping_bound_e`, `OAI.SharpPlanar.piece_kernel_bounds_e`, `OAI.SharpPlanar.piece_secant_bound_e`, `OAI.SharpPlanar.segmentEnvelope_integral_bound_e`, `OAI.SharpPlanar.segment_exp_integral_bound_e`, `OAI.SharpPlanar.sharp_atomic_bound_e`, `OAI.SharpPlanar.slopeCap_nonneg_e` and `OAI.SharpPlanar.zCap_nonneg_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E006
import Definitions.Def_OAIQ098E031
import Definitions.Def_OAIQ098E032
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_lt_one_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_lt_one_e
import Theorems.Thm_OAI_SharpPlanar_approximate_inverse_bijective_e

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


noncomputable def lambdaCap : Fin 7 → ℝ := ![2887/1000,2665/1000,2218/1000,1804/1000,1486/1000,1250/1000,1073/1000]
noncomputable def zCap : Fin 7 → ℝ := ![2934/1000,2713/1000,2269/1000,1859/1000,1548/1000,1320/1000,1151/1000]
noncomputable def dampingCap : Fin 7 → ℝ := ![2933/1000,2440/1000,1567/1000,900/1000,482/1000,224/1000,597/10000]
noncomputable def slopeCap : Fin 6 → ℝ := ![0,48/10,317/100,1946/1000,1217/1000,792/1000]

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def pieceMass (j : Fin 6) (s : ℝ) : ℝ :=
  if slopeCap j*s=0 then 1/6 else min (1/6) (1/(Real.pi*slopeCap j*s))
noncomputable def pieceL (j : Fin 6) (s : ℝ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*pieceMass j s
noncomputable def atomMass : Fin 7 → ℝ := ![5,4,4,4,2,4,2]
noncomputable def atomL (j : Fin 7) (s : ℝ) : ℝ :=
  atomMass j*lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)
noncomputable def segmentEnvelope (j : Fin 6) (ell : ℕ) (s t : ℝ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*(Real.pi*zCap ⟨j.val,by omega⟩)^ell *
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
    Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def atomicCoefficient (j : Fin 7) : ℂ := if j.val=0 then Pcoeff 0 else 2*Pcoeff j.val

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def rowTailNorm (x : X) (N : ℕ) : ℝ :=
  ∑' n : {n : Node // N<n.val}, (|x (n.val,false)|+|x (n.val,true)|)

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def rowQLower (n : ℕ) : ℝ :=
  if n%12=0 ∨ n%12=4 then 32898/10000 else
  if n%12=1 ∨ n%12=3 then 17629/10000 else 24555/1000
noncomputable def rowDUpper (n : ℕ) : ℝ :=
  if n%12=0 ∨ n%12=4 then 21162/10000 else
  if n%12=1 ∨ n%12=3 then 8260/10000 else 2214/10000

end SharpPlanar

namespace SharpPlanar
open IntegerBasis
noncomputable def pieceBase : Fin 6 → ℝ := ![469/1000000,7279/1000000,59165/1000000,219974/1000000,494744/1000000,828986/1000000]

noncomputable def massRational (j : Fin 6) (n : ℕ) : ℝ :=
  if slopeCap j*(n:ℝ)=0 then 1/6 else min (1/6) (1/((314159/100000:ℝ)*slopeCap j*n))
end SharpPlanar

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
noncomputable def trans8_r3_2 : Fin 16 → CBox := ![⟨⟨3314697650489667188564920,3314697650489667190718504⟩,⟨2118679434595321923363460,2118679434595321925516388⟩⟩,⟨⟨3270337234195545113285993,3270337234195545115391324⟩,⟨2042326734581679343883588,2042326734581679345988276⟩⟩,⟨⟨3224732315473300106280821,3224732315473300108337465⟩,⟨1965815418161197047616585,1965815418161197049672602⟩⟩,⟨⟨3177916172565592255814645,3177916172565592257822302⟩,⟨1889286921983407489991657,1889286921983407491998700⟩⟩,⟨⟨3129925334936327849346267,3129925334936327851304638⟩,⟨1812880219986837756695427,1812880219986837758653199⟩⟩,⟨⟨3080799564608911908984404,3080799564608911910893341⟩,⟨1736731435981524009467617,1736731435981524011375970⟩⟩,⟨⟨3030581817205670439355696,3030581817205670441215044⟩,⟨1660973469874923004246105,1660973469874923006104885⟩⟩,⟨⟨2979318182785177877624300,2979318182785177879434045⟩,⟨1585735639046944964942550,1585735639046944966751744⟩⟩,⟨⟨2927057806727417317614936,2927057806727417319375046⟩,⟨1511143336318121746301843,1511143336318121748061419⟩⟩,⟨⟨2873852791067538696239345,2873852791067538697949954⟩,⟨1437317705883838333112402,1437317705883838334822494⟩⟩,⟨⟨2819758076826199973548450,2819758076826199975209662⟩,⟨1364375338507328815274973,1364375338507328816935686⟩⟩,⟨⟨2764831308026846056037650,2764831308026846057649719⟩,⟨1292427987175098046886905,1292427987175098048498492⟩⟩,⟨⟨2709132678226610164982253,2709132678226610166545391⟩,⟨1221582304320998126421601,1221582304320998127984275⟩⟩,⟨⟨2652724760516677076030857,2652724760516677077545452⟩,⟨1151939601619876584436047,1151939601619876585950197⟩⟩,⟨⟨2595672322068856922681114,2595672322068856924147499⟩,⟨1083595633239120749520976,1083595633239120750986935⟩⟩,⟨⟨2538042124416787567327344,2538042124416787568746012⟩,⟨1016640403317234034285322,1016640403317234035703581⟩⟩]
noncomputable def trans8_r3_3 : Fin 16 → CBox := ![⟨⟨2479902710761703959478532,2479902710761703960849903⟩,⟨951157998313557153471787,951157998313557154842770⟩⟩,⟨⟨2421324181683270062953652,2421324181683270064278338⟩,⟨887226444743224844607362,887226444743224845931678⟩⟩,⟨⟨2362377960714851172661120,2362377960714851173939651⟩,⟨824917592677325250897358,824917592677325252175538⟩⟩,⟨⟨2303136551309209860411789,2303136551309209861644855⟩,⟨764297025250959469002711,764297025250959470235446⟩⟩,⟨⟨2243673286774451229832338,2243673286774451231020542⟩,⟨705423994282484236806052,705423994282484237993944⟩⟩,⟨⟨2184062074800756965011451,2184062074800756966155579⟩,⟨648351381966699303540787,648351381966699304684622⟩⟩,⟨⟨2124377138225791158301156,2124377138225791159401898⟩,⟨593125688464176566487303,593125688464176567587772⟩⟩,⟨⟨2064692753700518584773641,2064692753700518585831842⟩,⟨539787045069399219998910,539787045069399221056858⟩⟩,⟨⟨2005082989917559389990645,2005082989917559391007044⟩,⟨488369252502967876599582,488369252502967877615747⟩⟩,⟨⟨1945621447051250873004900,1945621447051250873980421⟩,⟨438899843738910451231165,438899843738910452206472⟩⟩,⟨⟨1886380999032559364782498,1886380999032559365717951⟩,⟨391400170648157068579076,391400170648157069514333⟩⟩,⟨⟨1827433540243266350683768,1827433540243266351580110⟩,⟨345885513614532293424029,345885513614532294320195⟩⟩,⟨⟨1768849738162942546171450,1768849738162942547029519⟩,⟨302365213161153692349231,302365213161153693207143⟩⟩,⟨⟨1710698793439731572888751,1710698793439731573709560⟩,⟨260842822513833567466915,260842822513833568287586⟩⟩,⟨⟨1653048208782604359600157,1653048208782604360384594⟩,⟨221316279924821260410406,221316279924821261194723⟩⟩,⟨⟨1595963567989324451884539,1595963567989324452633629⟩,⟨183778099485784973894262,183778099485784974643250⟩⟩]
noncomputable def trans8_r3_4 : Fin 16 → CBox := ![⟨⟨1539508326331776637164584,1539508326331776637879222⟩,⟨148215579074020910548456,148215579074020911263009⟩⟩,⟨⟨1483743613419525545676808,1483743613419525546358056⟩,⟨114611024001110401296294,114611024001110401977477⟩⟩,⟨⟨1428728049554520296307546,1428728049554520296956332⟩,⟨82941984869143151198753,82941984869143151847490⟩⟩,⟨⟨1374517576475831525065889,1374517576475831525683268⟩,⟨53181508086605788840752,53181508086605789458099⟩⟩,⟨⟨1321165303274324390437801,1321165303274324391024690⟩,⟨25298397454412891949898,25298397454412892536772⟩⟩,⟨⟨1268721368134389444366729,1268721368134389444924770⟩,⟨(-742514797462648654622),(-742514797462648096580)⟩⟩,⟨⟨1217232816434441890984303,1217232816434441891532626⟩,⟨(-24980089160626982869753),(-24980089160626982321414)⟩⟩,⟨⟨1166743495611030592206881,1166743495611030592745410⟩,⟨(-47456593830680544097752),(-47456593830680543559194)⟩⟩,⟨⟨1117293967064233108816086,1117293967064233109344616⟩,⟨(-68217415161008394338702),(-68217415161008393810131)⟩⟩,⟨⟨1068921435255691767414712,1068921435255691767933213⟩,⟨(-87310765211305277153960),(-87310765211305276635408)⟩⟩,⟨⟨1021659694026273909586648,1021659694026273910094954⟩,⟨(-104787387986967134595645),(-104787387986967134087278)⟩⟩,⟨⟨975539090038977641107201,975539090038977641605290⟩,⟨(-120700265927695232246336),(-120700265927695231748178)⟩⟩,⟨⟨930586503135357486926134,930586503135357487413848⟩,⟨(-135104328155840180401794),(-135104328155840179914003)⟩⟩,⟨⟨886825343281352124183066,886825343281352124660426⟩,⟨(-148056161937770533771755),(-148056161937770533294313)⟩⟩,⟨⟨844275563671824773539829,844275563671824774006718⟩,⟨(-159613728745570787203224),(-159613728745570786736247)⟩⟩,⟨⟨802953689463160503491967,802953689463160503948414⟩,⟨(-169836086232411167052585),(-169836086232411166596046)⟩⟩]
noncomputable def trans8_r3_5 : Fin 16 → CBox := ![⟨⟨762872861510600520769591,762872861510600521215482⟩,⟨(-178783117353800120744236),(-178783117353800120298251)⟩⟩,⟨⟨724042894402235402892122,724042894402235403327535⟩,⟨(-186515267779492093522321),(-186515267779492093086811)⟩⟩,⟨⟨686470348005234170272069,686470348005234170696935⟩,⟨(-193093292647978737509407),(-193093292647978737084443)⟩⟩,⟨⟨650158611672361456850225,650158611672361457264624⟩,⟨(-198578013618169627241168),(-198578013618169626826669)⟩⟩,⟨⟨615108000198437113217337,615108000198437113621205⟩,⟨(-203030087072014478815766),(-203030087072014478411798)⟩⟩,⟨⟨581315860567326407049836,581315860567326407443297⟩,⟨(-206509784218384877770231),(-206509784218384877376670)⟩⟩,⟨⟨548776688490419406295881,548776688490419406678911⟩,⟨(-209076783743467720697017),(-209076783743467720313889)⟩⟩,⟨⟨517482253707371983567088,517482253707371983939814⟩,⟨(-210789977547158964512523),(-210789977547158964139699)⟩⟩,⟨⟨487421732999050346688159,487421732999050347050557⟩,⟨(-211707289999395072167433),(-211707289999395071804939)⟩⟩,⟨⟨458581849850967963244662,458581849850967963596903⟩,⟨(-211885511045898083714953),(-211885511045898083362618)⟩⟩,⟨⟨430947019702765097870194,430947019702765098212296⟩,⟨(-211380143390274568775731),(-211380143390274568433537)⟩⟩,⟨⟨404499499725114968802523,404499499725114969134655⟩,⟨(-210245263879585925332421),(-210245263879585925000199)⟩⟩,⟨⟨379219542079432840872470,379219542079432841194650⟩,⟨(-208533399124128927253701),(-208533399124128926931435)⟩⟩,⟨⟨355085549637436822022729,355085549637436822335161⟩,⟨(-206295415289900798751300),(-206295415289900798438784)⟩⟩,⟨⟨332074233166426851337888,332074233166426851640626⟩,⟨(-203580421914675551370027),(-203580421914675551067209)⟩⟩,⟨⟨310160769021528355816878,310160769021528356110123⟩,⟨(-200435689516320497192318),(-200435689516320496898996)⟩⟩]
noncomputable def trans8_r3_6 : Fin 16 → CBox := ![⟨⟨289318956427466764509088,289318956427466764792887⟩,⟨(-196906580685392955937886),(-196906580685392955654014)⟩⟩,⟨⟨269521373479045118055716,269521373479045118330307⟩,⟨(-193036494283561054202099),(-193036494283561053927438)⟩⟩,⟨⟨250739531040713876734093,250739531040713876999560⟩,⟨(-188866822305296742274618),(-188866822305296742009084)⟩⟩,⟨⟨232944023780760626947321,232944023780760627203888⟩,⟨(-184436918902825058024595),(-184436918902825057767964)⟩⟩,⟨⟨216104677634013413896369,216104677634013414144117⟩,⟨(-179784081023637304518473),(-179784081023637304270664)⟩⟩,⟨⟨200190693047853379419043,200190693047853379658223⟩,⟨(-174943540066069798782459),(-174943540066069798543223)⟩⟩,⟨⟨185170783429089128722602,185170783429089128953322⟩,⟨(-169948463921526024208421),(-169948463921526023977648)⟩⟩,⟨⟨171013308273193111798096,171013308273193112020595⟩,⟨(-164829968741822801216871),(-164829968741822800994322)⟩⟩,⟨⟨157686400521899560394962,157686400521899560609337⟩,⟨(-159617139746751530867333),(-159617139746751530652911)⟩⟩,⟨⟨145158087759604258556698,145158087759604258763215⟩,⟨(-154337060370085948250333),(-154337060370085948043773)⟩⟩,⟨⟨133396406922813724916622,133396406922813725115405⟩,⟨(-149014849031706746813677),(-149014849031706746614854)⟩⟩,⟨⟨122369512259529783569149,122369512259529783760445⟩,⟨(-143673702818971285175463),(-143673702818971284984130)⟩⟩,⟨⟨112045776336432711581586,112045776336432711765509⟩,⟨(-138334947361611290777288),(-138334947361611290593331)⟩⟩,⟨⟨102393883950596045626469,102393883950596045803283⟩,⟨(-133018092190934454879932),(-133018092190934454703087)⟩⟩,⟨⟨93382918858830967365231,93382918858830967535070⟩,⟨(-127740890885548056893392),(-127740890885548056723524)⟩⟩,⟨⟨84982443291270116697925,84982443291270116861036⟩,⟨(-122519405321800890901978),(-122519405321800890738842)⟩⟩]
noncomputable def trans8_r3_7 : Fin 16 → CBox := ![⟨⟨77162570266162536041359,77162570266162536197859⟩,⟨(-117368073367222079936903),(-117368073367222079780379)⟩⟩,⟨⟨69894028769816858675883,69894028769816858826036⟩,⟨(-112299779378977673471950),(-112299779378977673321776)⟩⟩,⟨⟨63148221909002730925118,63148221909002731069062⟩,⟨(-107325926896317245151761),(-107325926896317245007798)⟩⟩,⟨⟨56897278182753884461063,56897278182753884599037⟩,⟨(-102456512945690636659128),(-102456512945690636521137)⟩⟩,⟨⟨51114096056310863101782,51114096056310863233911⟩,⟨(-97700203409230762489741),(-97700203409230762357598)⟩⟩,⟨⟨45772382051843177540846,45772382051843177667377⟩,⟨(-93064408941181546572085),(-93064408941181546445541)⟩⟩,⟨⟨40846682598588500674291,40846682598588500795362⟩,⟨(-88555360952172729221683),(-88555360952172729100601)⟩⟩,⟨⟨36312409909169292354949,36312409909169292470786⟩,⟨(-84178187217593979379283),(-84178187217593979263436)⟩⟩,⟨⟨32145862169160617796079,32145862169160617906803⟩,⟨(-79936986703307733823041),(-79936986703307733712308)⟩⟩,⟨⟨28324238343585947765996,28324238343585947871842⟩,⟨(-75834903239194338871447),(-75834903239194338765595)⟩⟩,⟨⟨24825647917039265318132,24825647917039265419232⟩,⟨(-71874197708200271291042),(-71874197708200271189936)⟩⟩,⟨⟨21629115893726856693373,21629115893726856789938⟩,⟨(-68056318455343254908918),(-68056318455343254812349)⟩⟩,⟨⟨18714583390068155326487,18714583390068155418634⟩,⟨(-64381969657228106461289),(-64381969657228106369139)⟩⟩,⟨⟨16062904155788065578300,16062904155788065666242⟩,⟨(-60851177427784606224656),(-60851177427784606136711)⟩⟩,⟨⟨13655837359884496306829,13655837359884496390691⟩,⟨(-57463353469923940972275),(-57463353469923940888411)⟩⟩,⟨⟨11476036975687063124701,11476036975687063204675⟩,⟨(-54217356115423672092115),(-54217356115423672012141)⟩⟩]
noncomputable def trans8_r3_8 : Fin 16 → CBox := ![⟨⟨9507038094666843401906,9507038094666843478098⟩,⟨(-51111548626422885991545),(-51111548626422885915353)⟩⟩,⟨⟨7733240491948322237478,7733240491948322310084⟩,⟨(-48143854661298535817665),(-48143854661298535745061)⟩⟩,⟨⟨6139889757850720875474,6139889757850720944607⟩,⟨(-45311810835288647260177),(-45311810835288647191045)⟩⟩,⟨⟨4713056299483266198623,4713056299483266264457⟩,⟨(-42612616331942858873586),(-42612616331942858807754)⟩⟩,⟨⟨3439612504670656540076,3439612504670656602709⟩,⟨(-40043179545256288962835),(-40043179545256288900205)⟩⟩,⟨⟨2307208347518239425869,2307208347518239485474⟩,⟨(-37600161754143740830823),(-37600161754143740771221)⟩⟩,⟨⟨1304245700960682307418,1304245700960682364096⟩,⟨(-35280017850724994969101),(-35280017850724994912426)⟩⟩,⟨⟨419851606883097854832,419851606883097908736⟩,⟨(-33079034161726195822767),(-33079034161726195768867)⟩⟩,⟨⟨(-356149260941406095727),(-356149260941406044511)⟩,⟨(-30993363418183571951598),(-30993363418183571900386)⟩⟩,⟨⟨(-1033262721602227522418),(-1033262721602227473737)⟩,⟨(-29019056942607034692967),(-29019056942607034644291)⟩⟩,⟨⟨(-1620353595972613758048),(-1620353595972613711812)⟩,⟨(-27152094134880327554231),(-27152094134880327508000)⟩⟩,⟨⟨(-2125674412333066826495),(-2125674412333066782571)⟩,⟨(-25388409348511734712977),(-25388409348511734669058)⟩⟩,⟨⟨(-2556894137201092335022),(-2556894137201092293333)⟩,⟨(-23723916257485968100091),(-23723916257485968058406)⟩⟩,⟨⟨(-2921126775638316214904),(-2921126775638316175319)⟩,⟨(-22154529820993576020579),(-22154529820993575980998)⟩⟩,⟨⟨(-3224959700750022540025),(-3224959700750022502467)⟩,⟨(-20676185958825833093599),(-20676185958825833056045)⟩⟩,⟨⟨(-3474481587111507362853),(-3474481587111507327206)⟩,⟨(-19284859054322572939046),(-19284859054322572903404)⟩⟩]
noncomputable def trans8_r3_9 : Fin 16 → CBox := ![⟨⟨(-3675309837362441772742),(-3675309837362441738942)⟩,⟨(-17976577404553389064916),(-17976577404553389031121)⟩⟩,⟨⟨(-3832617405130509818210),(-3832617405130509786142)⟩,⟨(-16747436739006714429188),(-16747436739006714397124)⟩⟩,⟨⟨(-3951158930717860499169),(-3951158930717860468706)⟩,⟨(-15593611928564858024100),(-15593611928564857993642)⟩⟩,⟨⟨(-4035296118559758550191),(-4035296118559758521244)⟩,⟨(-14511367006063947415847),(-14511367006063947386903)⟩⟩,⟨⟨(-4089022297307303680334),(-4089022297307303652852)⟩,⟨(-13497063618382067346464),(-13497063618382067318987)⟩⟩,⟨⟨(-4115986114469166003008),(-4115986114469165976903)⟩,⟨(-12547168027870238048955),(-12547168027870238022854)⟩⟩,⟨⟨(-4119514327854940224205),(-4119514327854940199427)⟩,⟨(-11658256778139318744814),(-11658256778139318720039)⟩⟩,⟨⟨(-4102633665588080515595),(-4102633665588080492067)⟩,⟨(-10827021135837353205441),(-10827021135837353181916)⟩⟩,⟨⟨(-4068091735200813241585),(-4068091735200813219264)⟩,⟨(-10050270416187439547780),(-10050270416187439525463)⟩⟩,⟨⟨(-4018376970295649130660),(-4018376970295649109471)⟩,⟨(-9324934295791830543381),(-9324934295791830522195)⟩⟩,⟨⟨(-3955737610473294474166),(-3955737610473294454066)⟩,⟨(-8648064211624009915820),(-8648064211624009895723)⟩⟩,⟨⟨(-3882199716705638550549),(-3882199716705638531472)⟩,⟨(-8016833940301487637190),(-8016833940301487618116)⟩⟩,⟨⟨(-3799584230100560366880),(-3799584230100560348791)⟩,⟨(-7428539446726595378543),(-7428539446726595360457)⟩⟩,⟨⟨(-3709523087091982187437),(-3709523087091982170272)⟩,⟨(-6880598086063202730680),(-6880598086063202713518)⟩⟩,⟨⟨(-3613474408526514987764),(-3613474408526514971487)⟩,⟨(-6370547237840572307749),(-6370547237840572291475)⟩⟩,⟨⟨(-3512736783942283343108),(-3512736783942283327647)⟩,⟨(-5896042445792166578826),(-5896042445792166563368)⟩⟩]
noncomputable def trans8_r3_10 : Fin 16 → CBox := ![⟨⟨(-3408462675582996813712),(-3408462675582996799031)⟩,⟨(-5454855131891979116767),(-5454855131891979102088)⟩⟩,⟨⟨(-3301670969399184511557),(-3301670969399184497605)⟩,⟨(-5044869947983181457314),(-5044869947983181443364)⟩⟩,⟨⟨(-3193258702497537994451),(-3193258702497537981201)⟩,⟨(-4664081823437512339729),(-4664081823437512326481)⟩⟩,⟨⟨(-3084011998247511603165),(-3084011998247511590574)⟩,⟨(-4310592762467785301996),(-4310592762467785289407)⟩⟩,⟨⟨(-2974616241580461425266),(-2974616241580461413312)⟩,⟨(-3982608440064287775956),(-3982608440064287764003)⟩⟩,⟨⟨(-2865665527958795579725),(-2865665527958795568365)⟩,⟨(-3678434641058381127900),(-3678434641058381116542)⟩⟩,⟨⟨(-2757671420088045338823),(-2757671420088045328035)⟩,⟨(-3396473582548866340399),(-3396473582548866329614)⟩⟩,⟨⟨(-2651071046729415496967),(-2651071046729415486715)⟩,⟨(-3135220155870461589182),(-3135220155870461578933)⟩⟩,⟨⟨(-2546234577978755162442),(-2546234577978755152710)⟩,⟨(-2893258120447421378804),(-2893258120447421369073)⟩⟩,⟨⟨(-2443472111142902498438),(-2443472111142902489188)⟩,⟨(-2669256278264193766730),(-2669256278264193757482)⟩⟩,⟨⟨(-2343040000897128715002),(-2343040000897128706217)⟩,⟨(-2461964654301581313788),(-2461964654301581305004)⟩⟩,⟨⟨(-2245146666777199901616),(-2245146666777199893266)⟩,⟨(-2270210705131219757655),(-2270210705131219749306)⟩⟩,⟨⟨(-2149957910273716857845),(-2149957910273716849914)⟩,⟨(-2092895574931259406926),(-2092895574931259398996)⟩⟩,⟨⟨(-2057601772880237566264),(-2057601772880237558724)⟩,⟨(-1928990415478030740475),(-1928990415478030732936)⟩⟩,⟨⟨(-1968172965423607274546),(-1968172965423607267382)⟩,⟨(-1777532784176736195065),(-1777532784176736187902)⟩⟩,⟨⟨(-1881736897896322701464),(-1881736897896322694651)⟩,⟨(-1637623131912066974264),(-1637623131912066967453)⟩⟩]
noncomputable def trans8_r3_11 : Fin 16 → CBox := ![⟨⟨(-1798333337836112173984),(-1798333337836112167512)⟩,⟨(-1508421390419262249510),(-1508421390419262243038)⟩⟩,⟨⟨(-1717979724074814176762),(-1717979724074814170604)⟩,⟨(-1389143666988826443011),(-1389143666988826436855)⟩⟩,⟨⟨(-1640674161422859950109),(-1640674161422859944255)⟩,⟨(-1279059052614569422822),(-1279059052614569416969)⟩⟩,⟨⟨(-1566398120581251926415),(-1566398120581251920844)⟩,⟨(-1177486548165039165036),(-1177486548165039159466)⟩⟩,⟨⟨(-1495118866292269910312),(-1495118866292269905014)⟩,⟨(-1083792111792676965731),(-1083792111792676960434)⟩⟩,⟨⟨(-1426791635464066182682),(-1426791635464066177631)⟩,⟨(-997385829582880596594),(-997385829582880591545)⟩⟩,⟨⟨(-1361361585742207042576),(-1361361585742207037764)⟩,⟨(-917719210376314258474),(-917719210376314253662)⟩⟩,⟨⟨(-1298765533761103593496),(-1298765533761103588906)⟩,⟨(-844282604762032397132),(-844282604762032392543)⟩⟩,⟨⟨(-1238933501096917214019),(-1238933501096917209646)⟩,⟨(-776602747426230301841),(-776602747426230297467)⟩⟩,⟨⟨(-1181790084766542259331),(-1181790084766542255157)⟩,⟨(-714240421341885453109),(-714240421341885448936)⟩⟩,⟨⟨(-1127255667979226819972),(-1127255667979226815991)⟩,⟨(-656788241688706751558),(-656788241688706747578)⟩⟩,⟨⟨(-1075247485751906451278),(-1075247485751906447477)⟩,⟨(-603868556891522642967),(-603868556891522639167)⟩⟩,⟨⟨(-1025680558949153306218),(-1025680558949153302592)⟩,⟨(-555131463749774963149),(-555131463749774959523)⟩⟩,⟨⟨(-978468509305775754714),(-978468509305775751250)⟩,⟨(-510252933292837623093),(-510252933292837619629)⟩⟩,⟨⟨(-933524267035853700424),(-933524267035853697116)⟩,⟨(-468933043727597586303),(-468933043727597582994)⟩⟩,⟨⟨(-890760681727077089701),(-890760681727077086538)⟩,⟨(-430894316638738065967),(-430894316638738062804)⟩⟩]
noncomputable def trans8_r3_12 : Fin 16 → CBox := ![⟨⟨(-850091046363863073672),(-850091046363863070651)⟩,⟨(-395880152451543690424),(-395880152451543687403)⟩⟩,⟨⟨(-811429543516604506432),(-811429543516604503541)⟩,⟨(-363653361065373277401),(-363653361065373274511)⟩⟩,⟨⟨(-774691621976908362461),(-774691621976908359697)⟩,⟨(-333994783507257294134),(-333994783507257291370)⟩⟩,⟨⟨(-739794311408852933616),(-739794311408852930969)⟩,⟨(-306702000433875122732),(-306702000433875120085)⟩⟩,⟨⟨(-706656481922894421946),(-706656481922894419413)⟩,⟨(-281588123321401756177),(-281588123321401753644)⟩⟩,⟨⟨(-675199054860635251045),(-675199054860635248618)⟩,⟨(-258480664221767450897),(-258480664221767448470)⟩⟩,⟨⟨(-645345170503602902483),(-645345170503602900158)⟩,⟨(-237220480026545117770),(-237220480026545115445)⟩⟩,⟨⟨(-617020317885720754953),(-617020317885720752723)⟩,⟨(-217660787262162041681),(-217660787262162039451)⟩⟩,⟨⟨(-590152431395424964753),(-590152431395424962616)⟩,⟨(-199666243538992255196),(-199666243538992253058)⟩⟩,⟨⟨(-564671958397471337057),(-564671958397471335005)⟩,⟨(-183112091889043228223),(-183112091889043226171)⟩⟩,⟨⟨(-540511901684422107482),(-540511901684422105512)⟩,⟨(-167883364349655117657),(-167883364349655115688)⟩⟩,⟨⟨(-517607840181628352297),(-517607840181628350404)⟩,⟨(-153874141281439820275),(-153874141281439818382)⟩⟩,⟨⟨(-495897930975258616207),(-495897930975258614389)⟩,⟨(-140986863045442897104),(-140986863045442895287)⟩⟩,⟨⟨(-475322895408620311139),(-475322895408620309391)⟩,⟨(-129131690805319835079),(-129131690805319833331)⟩⟩,⟨⟨(-455825991695766773014),(-455825991695766771332)⟩,⟨(-118225913363526846694),(-118225913363526845012)⟩⟩,⟨⟨(-437352976231318012513),(-437352976231318010893)⟩,⟨(-108193397084704677044),(-108193397084704675424)⟩⟩]
noncomputable def trans8_r3_13 : Fin 16 → CBox := ![⟨⟨(-419852055529744396063),(-419852055529744394504)⟩,⟨(-98964076103352583457),(-98964076103352581898)⟩⟩,⟨⟨(-403273830504333340168),(-403273830504333338664)⟩,⟨(-90473480155502576755),(-90473480155502575252)⟩⟩,⟨⟨(-387571234594015303256),(-387571234594015301807)⟩,⟨(-82662297514530090401),(-82662297514530088952)⟩⟩,⟨⟨(-372699467063578890123),(-372699467063578888724)⟩,⟨(-75475970648743792392),(-75475970648743790993)⟩⟩,⟨⟨(-358615922638046749925),(-358615922638046748575)⟩,⟨(-68864322352384324661),(-68864322352384323311)⟩⟩,⟨⟨(-345280118483685740132),(-345280118483685738828)⟩,⟨(-62781210231647545623),(-62781210231647544318)⟩⟩,⟨⟨(-332653619414939243008),(-332653619414939241747)⟩,⟨(-57184207552955199417),(-57184207552955198156)⟩⟩,⟨⟨(-320699962087230007206),(-320699962087230005986)⟩,⟨(-52034308581639849420),(-52034308581639848200)⟩⟩,⟨⟨(-309384578828901556187),(-309384578828901555007)⟩,⟨(-47295656655287131942),(-47295656655287130762)⟩⟩,⟨⟨(-298674721670436134783),(-298674721670436133639)⟩,⟨(-42935293347052916264),(-42935293347052915121)⟩⟩,⟨⟨(-288539387044474210770),(-288539387044474209662)⟩,⟨(-38922927180272555999),(-38922927180272554891)⟩⟩,⟨⟨(-278949241555104764895),(-278949241555104763820)⟩,⟨(-35230720456582965035),(-35230720456582963959)⟩⟩,⟨⟨(-269876549148507366089),(-269876549148507365046)⟩,⟨(-31833092855608971581),(-31833092855608970538)⟩⟩,⟨⟨(-261295099958483934024),(-261295099958483933011)⟩,⟨(-28706540555083872153),(-28706540555083871139)⟩⟩,⟨⟨(-253180141048961699057),(-253180141048961698072)⟩,⟨(-25829469706172003562),(-25829469706172002577)⟩⟩,⟨⟨(-245508309230481355778),(-245508309230481354819)⟩,⟨(-23182043179855698565),(-23182043179855697606)⟩⟩]
noncomputable def trans8_r3_14 : Fin 16 → CBox := ![⟨⟨(-238257566088365168258),(-238257566088365167326)⟩,⟨(-20746039576678031138),(-20746039576678030206)⟩⟩,⟨⟨(-231407135326102045613),(-231407135326102044705)⟩,⟨(-18504723564050410898),(-18504723564050409989)⟩⟩,⟨⟨(-224937442497954051976),(-224937442497954051090)⟩,⟨(-16442726672906949376),(-16442726672906948491)⟩⟩,⟨⟨(-218830057179392295235),(-218830057179392294371)⟩,⟨(-14545937748891353762),(-14545937748891352897)⟩⟩,⟨⟨(-213067637602264454553),(-213067637602264453710)⟩,⟨(-12801402312678961258),(-12801402312678960415)⟩⟩,⟨⟨(-207633877763177000941),(-207633877763177000116)⟩,⟨(-11197230139652295421),(-11197230139652294597)⟩⟩,⟨⟨(-202513456998075936125),(-202513456998075935320)⟩,⟨(-9722510421150818744),(-9722510421150817938)⟩⟩,⟨⟨(-197691992003099117451),(-197691992003099116662)⟩,⟨(-8367233918091940552),(-8367233918091939763)⟩⟩,⟨⟨(-193155991271151722521),(-193155991271151721749)⟩,⟨(-7122221563096850974),(-7122221563096850202)⟩⟩,⟨⟨(-188892811905054608364),(-188892811905054607606)⟩,⟨(-5979059009534669034),(-5979059009534668277)⟩⟩,⟨⟨(-184890618761290974268),(-184890618761290973525)⟩,⟨(-4930036665301242332),(-4930036665301241590)⟩⟩,⟨⟨(-181138345873112562633),(-181138345873112561903)⟩,⟨(-3968094785849701038),(-3968094785849700308)⟩⟩,⟨⟨(-177625660097868180506),(-177625660097868179790)⟩,⟨(-3086773235158376502),(-3086773235158375786)⟩⟩,⟨⟨(-174342926930710979969),(-174342926930710979265)⟩,⟨(-2280165555122158018),(-2280165555122157314)⟩⟩,⟨⟨(-171281178425172047263),(-171281178425172046570)⟩,⟨(-1542877013444058416),(-1542877013444057723)⟩⟩,⟨⟨(-168432083160318998991),(-168432083160318998308)⟩,⟨(-869986327636831063),(-869986327636830379)⟩⟩]
noncomputable def trans8_r4_0 : Fin 16 → CBox := ![⟨⟨1070467998137550993379625040,1070467998137550997836572492⟩,⟨(-3408355754280343974725812511),(-3408355754280343970268242029)⟩⟩,⟨⟨1069008081094271600771550427,1069008081094271605227226269⟩,⟨(-3407376385932809355439299735),(-3407376385932809350983001600)⟩⟩,⟨⟨1066090979666289266108549598,1066090979666289270561674782⟩,⟨(-3405417454156153107456962815),(-3405417454156153103003216814)⟩⟩,⟨⟨1061722153604830035149315724,1061722153604830039598612821⟩,⟨(-3402478573764827068029922241),(-3402478573764827063580006536)⟩⟩,⟨⟨1055909778627263152421638264,1055909778627263156865832202⟩,⟨(-3398559179395314324904819175),(-3398559179395314320460009571)⟩⟩,⟨⟨1048664729740783625272061637,1048664729740783629709880525⟩,⟨(-3393658540322109642192786175),(-3393658540322109637754355288)⟩⟩,⟨⟨1040000559032620204312147879,1040000559032620208742323688⟩,⟨(-3387775780076469919734726282),(-3387775780076469915303942864)⟩⟩,⟨⟨1029933467948890901775312394,1029933467948890906196582070⟩,⟨(-3380909900752295796345927785),(-3380909900752295791924055602)⟩⟩,⟨⟨1018482274090299586995195068,1018482274090299591406300568⟩,⟨(-3373059811855640684262537380),(-3373059811855640679850835183)⟩⟩,⟨⟨1005668372559288576938203425,1005668372559288581337893908⟩,⟨(-3364224363527170561544832590),(-3364224363527170557144551914)⟩⟩,⟨⟨991515691900092961457190817,991515691900092965844221200⟩,⟨(-3354402383940550353990312760),(-3354402383940550349602699376)⟩⟩,⟨⟨976050644680436569085432749,976050644680436573458567772⟩,⟨(-3343592720654341669309379554),(-3343592720654341664935669396)⟩⟩,⟨⟨959302072771414506092652096,959302072771414510450662208⟩,⟨(-3331794285670689851091188183),(-3331794285670689846732611464)⟩⟩,⟨⟨941301187390463472539794559,941301187390463476881463803⟩,⟨(-3319006103930980046987192050),(-3319006103930980042644965375)⟩⟩,⟨⟨922081503981261140378713163,922081503981261144702830825⟩,⟨(-3305227364956872386494643342),(-3305227364956872382169978060)⟩⟩,⟨⟨901678772013943905424440639,901678772013943909729813177⟩,⟨(-3290457477324800982796983652),(-3290457477324800978491073921)⟩⟩]
noncomputable def trans8_r4_1 : Fin 16 → CBox := ![⟨⟨880130899799203464264357058,880130899799203468549794163⟩,⟨(-3274696125643250722534524408),(-3274696125643250718248561139)⟩⟩,⟨⟨857477874420622662839694865,857477874420622667104030117⟩,⟨(-3257943329685014431875602615),(-3257943329685014427610752811)⟩⟩,⟨⟨833761676901035869290424919,833761676901035873532492721⟩,⟨(-3240199505311279538433586576),(-3240199505311279534191016400)⟩⟩,⟨⟨809026192730734628167256508,809026192730734632385919602⟩,⟨(-3221465526810889551455112437),(-3221465526810889547235959690)⟩⟩,⟨⟨783317117897961200567549881,783317117897961204761667344⟩,⟨(-3201742790266555997363996500),(-3201742790266555993169402631)⟩⟩,⟨⟨756681860575306105712304330,756681860575306109880774333⟩,⟨(-3181033277550237429401680814),(-3181033277550237425232748155)⟩⟩,⟨⟨729169438629305973185442671,729169438629305977327154986⟩,⟨(-3159339620542421891672548679),(-3159339620542421887530387939)⟩⟩,⟨⟨700830373134669735433296138,700830373134669739547184567⟩,⟨(-3136665165164706879541821088),(-3136665165164706875427498921)⟩⟩,⟨⟨671716578089079336384743172,671716578089079340469725170⟩,⟨(-3113014034811915989031498824),(-3113014034811915984946098213)⟩⟩,⟨⟨641881246539340993903235904,641881246539340997958290130⟩,⟨(-3088391192769063624555354855),(-3088391192769063620499897548)⟩⟩,⟨⟨611378733344720750428624572,611378733344720754452705946⟩,⟨(-3062802503199807324486587504),(-3062802503199807320462118967)⟩⟩,⟨⟨580264434818491067393353182,580264434818491071385481396⟩,⟨(-3036254790296629437927305488),(-3036254790296629433934806384)⟩⟩,⟨⟨548594665503943065659506178,548594665503943069618666763⟩,⟨(-3008755895188872565224989348),(-3008755895188872561265474483)⟩⟩,⟨⟨516426532356273934532986816,516426532356273938458253365⟩,⟨(-2980314730212911043620420242),(-2980314730212911039694816325)⟩⟩,⟨⟨483817806616726849011384733,483817806616726852901786566⟩,⟨(-2950941330159156326289632912),(-2950941330159156322398910904)⟩⟩,⟨⟨450826793680021760219165640,450826793680021764073822776⟩,⟨(-2920646900123237418201677457),(-2920646900123237414346717586)⟩⟩]
noncomputable def trans8_r4_2 : Fin 16 → CBox := ![⟨⟨417512201270345449881574811,417512201270345453699547322⟩,⟨(-2889443859603525968943247203),(-2889443859603525965124989622)⟩⟩,⟨⟨383933006254840604355277262,383933006254840608135750317⟩,⟨(-2857345882504133728408414282),(-2857345882504133724627674013)⟩⟩,⟨⟨350148320436516379775393411,350148320436516383517479408⟩,⟨(-2824367932721529494870262524),(-2824367932721529491127927334)⟩⟩,⟨⟨316217255680665867837502371,316217255680665871540435237⟩,⟨(-2790526295013922186007771359),(-2790526295013922182304607455)⟩⟩,⟨⟨282198788740087988690521420,282198788740087992353446339⟩,⟨(-2755838600875442208885773865),(-2755838600875442205222636173)⟩⟩,⟨⟨248151626154542940110526333,248151626154542943732750857⟩,⟨(-2720323849161818257790061722),(-2720323849161818254167642762)⟩⟩,⟨⟨214134069608794363527512965,214134069608794367108240515⟩,⟨(-2684002421240572073430097682),(-2684002421240572069849194084)⟩⟩,⟨⟨180203882141184725020759955,180203882141184728559350734⟩,⟨(-2646896090466608663050527771),(-2646896090466608659511779347)⟩⟩,⟨⟨146418155600835162804571048,146418155600835166300258095⟩,⟨(-2609028025813321669674319802),(-2609028025813321666178493505)⟩⟩,⟨⟨112833179756145848780470362,112833179756145852232699977⟩,⟨(-2570422789519809791959948561),(-2570422789519809788507598047)⟩⟩,⟨⟨79504313460194153368841087,79504313460194156776914876⟩,⟨(-2531106328646347029086976171),(-2531106328646347025678799768)⟩⟩,⟨⟨46485858279790989495775894,46485858279790992859190846⟩,⟨(-2491105960462694321062587398),(-2491105960462694317699088017)⟩⟩,⟨⟨13830934994276208134583279,13830934994276211452672055⟩,⟨(-2450450351627001661145126938),(-2450450351627001657826971793)⟩⟩,⟨⟨(-18408636632461341094105836),(-18408636632461337821753920)⟩,⟨(-2409169491146739278013110131),(-2409169491146739274740709751)⟩⟩,⟨⟨(-50182454407825352689176570),(-50182454407825349463155746)⟩,⟨(-2367294657147118928251794728),(-2367294657147118925025743163)⟩⟩,⟨⟨(-81441646201897615921115167),(-81441646201897612741783318)⟩,⟨(-2324858377506621388683265846),(-2324858377506621385503920770)⟩⟩]
noncomputable def trans8_r4_3 : Fin 16 → CBox := ![⟨⟨(-112138977990703924260084241),(-112138977990703921128012395)⟩,⟨(-2281894384453329607640608596),(-2281894384453329604508540802)⟩⟩,⟨⟨(-142228957078427205005067789),(-142228957078427201920507782)⟩,⟨(-2238437563249571736311960666),(-2238437563249571733227421729)⟩⟩,⟨⟨(-171667930138445150743293206),(-171667930138445147706730414)⟩,⟨(-2194523895125696234632437980),(-2194523895125696231595912989)⟩⟩,⟨⟨(-200414175727947425442037725),(-200414175727947422453679354)⟩,⟨(-2150190394656424439788435146),(-2150190394656424436800131000)⟩⟩,⟨⟨(-228427990947803919352862317),(-228427990947803916413168325)⟩,⟨(-2105475041804948082777701982),(-2105475041804948079838078302)⟩⟩,⟨⟨(-255671771938265362712994332),(-255671771938265359822064563)⟩,⟨(-2060416708890557112132798089),(-2060416708890557109241954365)⟩⟩,⟨⟨(-282110087921919244703718264),(-282110087921919241861926113)⟩,⟨(-2015055082764898425961229794),(-2015055082764898423119539040)⟩⟩,⟨⟨(-307709748528019440734320527),(-307709748528019437941719945)⟩,⟨(-1969430582509786569191924119),(-1969430582509786566399439892)⟩⟩,⟨⟨(-332439864156763168007779659),(-332439864156763165264730071)⟩,⟨(-1923584272995628742882459800),(-1923584272995628740139541100)⟩⟩,⟨⟨(-356271899168194152121814865),(-356271899168194149428250198)⟩,⟨(-1877557774663813488455031959),(-1877557774663813485761612283)⟩⟩,⟨⟨(-379179717708041408264564627),(-379179717708041405620744984)⟩,⟨(-1831393169918680769797324065),(-1831393169918680767153663055)⟩⟩,⟨⟨(-401139622011819692869762890),(-401139622011819690275589757)⟩,⟨(-1785132906534788623586623780),(-1785132906534788620992622457)⟩⟩,⟨⟨(-422130383058767884584569368),(-422130383058767882040286708)⟩,⟨(-1738819698502979279713247838),(-1738819698502979277169149670)⟩⟩,⟨⟨(-442133263478520300009139402),(-442133263478520297514532568)⟩,⟨(-1692496424754101562457086735),(-1692496424754101559962676588)⟩⟩,⟨⟨(-461132032645616970432593846),(-461132032645616967987810320)⟩,⟨(-1646206026212058202091490041),(-1646206026212058199646914870)⟩⟩,⟨⟨(-479112973929875959630437472),(-479112973929875957235230444)⟩,⟨(-1599991401638025019423166854),(-1599991401638025017028179338)⟩⟩]
noncomputable def trans8_r4_4 : Fin 16 → CBox := ![⟨⟨(-496064884104079083495627655),(-496064884104079081150145525)⟩,⟨(-1553895302735160171803952789),(-1553895302735160169458700777)⟩⟩,⟨⟨(-511979064944160038867532020),(-511979064944160036571398917)⟩,⟨(-1507960228987830692067356258),(-1507960228987830689771463353)⟩⟩,⟨⟨(-526849307090923645818193746),(-526849307090923643571447344)⟩,⟨(-1462228322711294500731387289),(-1462228322711294498484890597)⟩⟩,⟨⟨(-540671866276055560213886231),(-540671866276055558016139040)⟩,⟨(-1416741264786872646156120425),(-1416741264786872643958631917)⟩⟩,⟨⟨(-553445432048590282453373345),(-553445432048590280304659135)⟩,⟨(-1371540171553932378090772659),(-1371540171553932375942325518)⟩⟩,⟨⟨(-565171089170878167408242217),(-565171089170878165308056586)⟩,⟨(-1326665493323500501191926886),(-1326665493323500499092016170)⟩⟩,⟨⟨(-575852271885217557650426690),(-575852271885217555598702471)⟩,⟨(-1282156914969082021253249496),(-1282156914969082019201807448)⟩⟩,⟨⟨(-585494711283487587953450475),(-585494711283487585949670342)⟩,⟨(-1238053259038334924864509818),(-1238053259038334922861018565)⟩⟩,⟨⟨(-594106376042127254349562285),(-594106376042127252393673641)⟩,⟨(-1194392391814730966705898574),(-1194392391814730964750304918)⟩⟩,⟨⟨(-601697406813460522455570334),(-601697406813460520546929801)⟩,⟨(-1151211132741316357963370152),(-1151211132741316356055030181)⟩⟩,⟨⟨(-608280044591477707798952158),(-608280044591477705937394779)⟩,⟨(-1108545167599295128936316829),(-1108545167599295127075064992)⟩⟩,⟨⟨(-613868553395572510505674421),(-613868553395572508690566794)⟩,⟨(-1066428965812528738944703873),(-1066428965812528737129906239)⟩⟩,⟨⟨(-618479137639236183679390814),(-618479137639236181906195603)⟩,⟨(-1024895702225331404812792443),(-1024895702225331403039906836)⟩⟩,⟨⟨(-622129854572172920616262525),(-622129854572172918884107257)⟩,⟨(-983977183675309692718810944),(-983977183675309690986964224)⟩⟩,⟨⟨(-624840522203585875784408825),(-624840522203585874093211937)⟩,⟨(-943703780655628786345724580),(-943703780655628784654834742)⟩⟩,⟨⟨(-626632623131369372984917740),(-626632623131369371334115878)⟩,⟨(-904104364332180184111408492),(-904104364332180182460911825)⟩⟩]
noncomputable def trans8_r4_5 : Fin 16 → CBox := ![⟨⟨(-627529204716524827087176940),(-627529204716524825476724866)⟩,⟨(-865206249150880528055123919),(-865206249150880526444974753)⟩⟩,⟨⟨(-627554776054208594037974372),(-627554776054208592467188600)⟩,⟨(-827035141238961731566085340),(-827035141238961729995599874)⟩⟩,⟨⟨(-626735202202350851369142668),(-626735202202350849837867460)⟩,⟨(-789615092771838449443827897),(-789615092771838447912850002)⟩⟩,⟨⟨(-625097596135706357792885345),(-625097596135706356300472970)⟩,⟨(-752968462444185272677316030),(-752968462444185271185197676)⟩⟩,⟨⟨(-622670208897480772661604329),(-622670208897480771207925209)⟩,⟨(-717115882150451154160270065),(-717115882150451152706881303)⟩⟩,⟨⟨(-619482318422310134940435462),(-619482318422310133524742852)⟩,⟨(-682076229946412166109268116),(-682076229946412164693861947)⟩⟩,⟨⟨(-615564117503365900503996185),(-615564117503365899126067759)⟩,⟨(-647866609329744889953627176),(-647866609329744888575980944)⟩⟩,⟨⟨(-610946601372743034192231180),(-610946601372743032851349355)⟩,⟨(-614502334844218227623140256),(-614502334844218226282536149)⟩⟩,⟨⟨(-605661455358112738246885441),(-605661455358112736942873814)⟩,⟨(-581996923979173561462303662),(-581996923979173560158564967)⟩⟩,⟨⟨(-599740943069951897312655811),(-599740943069951896044689509)⟩,⟨(-550362095303708202890997680),(-550362095303708201623299344)⟩⟩,⟨⟨(-593217795562583685607462855),(-593217795562583684375261794)⟩,⟨(-519607772743603297136334521),(-519607772743603295904396194)⟩⟩,⟨⟨(-586125101898880620311909137),(-586125101898880619114701620)⟩,⟨(-489742095878743588486272622),(-489742095878743587289322452)⟩⟩,⟨⟨(-578496201532911384249136482),(-578496201532911383086679105)⟩,⟨(-460771436109750393375737392),(-460771436109750392213531734)⟩⟩,⟨⟨(-570364578907189654316930695),(-570364578907189653188366913)⟩,⟨(-432700418514965937091039836),(-432700418514965935962722033)⟩⟩,⟨⟨(-561763760641654273886292499),(-561763760641654272791294305)⟩,⟨(-405531949192948204571550363),(-405531949192948203476792215)⟩⟩,⟨⟨(-552727215670234930205135572),(-552727215670234929142893354)⟩,⟨(-379267247861406960261123121),(-379267247861406959199114928)⟩⟩]
noncomputable def trans8_r4_6 : Fin 16 → CBox := ![⟨⟨(-543288258658006271804193846),(-543288258658006270774438915)⟩,⟨(-353905885461163930466576387),(-353905885461163929437049285)⟩⟩,⟨⟨(-533479957007685449823205995),(-533479957007685448825033917)⟩,⟨(-329445826493366801545972477),(-329445826493366800548021993)⟩⟩,⟨⟨(-523335041738770140179906250),(-523335041738770139212951475)⟩,⟨(-305883475799923652026702511),(-305883475799923651059962971)⟩⟩,⟨⟨(-512885822496138660625666128),(-512885822496138659689097382)⟩,⟨(-283213729481029695290830797),(-283213729481029694354470903)⟩⟩,⟨⟨(-502164106917637266811140741),(-502164106917637265904637949)⟩,⟨(-261430029629791442920047943),(-261430029629791442013747517)⟩⟩,⟨⟨(-491201124562260741701779366),(-491201124562260740824443998)⟩,⟨(-240524422552355846619568932),(-240524422552355845742429465)⟩⟩,⟨⟨(-480027455572190107787759345),(-480027455572190106938378400)⟩,⟨(-220487620132646479424619370),(-220487620132646478575422203)⟩⟩,⟨⟨(-468672964213383581568018953),(-468672964213383580745508077)⟩,⟨(-201309063993800032996776434),(-201309063993800032174435684)⟩⟩,⟨⟨(-457166737410818743366107983),(-457166737410818742570194313)⟩,⟨(-182976992103671197797205718),(-182976992103671197001448982)⟩⟩,⟨⟨(-445537028366045795891453978),(-445537028366045795121281209)⟩,⟨(-165478507469301964817847031),(-165478507469301964047818566)⟩⟩,⟨⟨(-433811205316618184135785614),(-433811205316618183390999867)⟩,⟨(-148799648564985593604352866),(-148799648564985592859699264)⟩⟩,⟨⟨(-422015705469394735122854150),(-422015705469394734402678051)⟩,⟨(-132925461140433265751107702),(-132925461140433265031052127)⟩⟩,⟨⟨(-410175994112825045376680153),(-410175994112825044680810389)⟩,⟨(-117840071059495368657352016),(-117840071059495367961591613)⟩⟩,⟨⟨(-398316528887295292666149903),(-398316528887295291993757125)⟩,⟨(-103526757825808344749029308),(-103526757825808344076735260)⟩⟩,⟨⟨(-386460729167572089548252300),(-386460729167572088898972970)⟩,⟨(-89968028459528524516878070),(-89968028459528523867687296)⟩⟩,⟨⟨(-374630950487472513076248957),(-374630950487472512449321521)⟩,⟨(-77145691398861549613114883),(-77145691398861548986266332)⟩⟩]
noncomputable def trans8_r4_7 : Fin 16 → CBox := ![⟨⟨(-362848463914231287610954244),(-362848463914231287006083529)⟩,⟨(-65040930111275220948851117),(-65040930111275220344050059)⟩⟩,⟨⟨(-351133440258740024613107975),(-351133440258740024029471684)⟩,⟨(-53634376111961730779483317),(-53634376111961730195907946)⟩⟩,⟨⟨(-339504938987993193862886298),(-339504938987993193300119308)⟩,⟨(-42906181101152062230701069),(-42906181101152061667986699)⟩⟩,⟨⟨(-327980901687771517164068411),(-327980901687771516621435532)⟩,⟨(-32836087947135074065536117),(-32836087947135073522948016)⟩⟩,⟨⟨(-316578149906891575739124549),(-316578149906891575216313506)⟩,⟨(-23403500258146505637833140),(-23403500258146505115059451)⟩⟩,⟨⟨(-305312387199301817999284195),(-305312387199301817495523518)⟩,⟨(-14587550303516222377113536),(-14587550303516221873383228)⟩⟩,⟨⟨(-294198205166946513105126014),(-294198205166946512620056276)⟩,⟨(-6367165062441597399411451),(-6367165062441596914365500)⟩⟩,⟨⟨(-283249093294672860946346602),(-283249093294672860479109708)⟩,⟨1278869802662768021551600,1278869802662768488770814⟩⟩,⟨⟨(-272477452358530808291680051),(-272477452358530807841260466)⟩,⟨8371848232256049618649703,8371848232256050069057028⟩⟩,⟨⟨(-261894611180604996148915874),(-261894611180604995714631144)⟩,⟨14933084479886425171555294,14933084479886425605832812⟩⟩,⟨⟨(-251510846497005614305405807),(-251510846497005613886966787)⟩,⟨20983856391725285821059943,20983856391725286239496450⟩⟩,⟨⟨(-241335405700799466294519057),(-241335405700799465891321950)⟩,⟨26545351381111981776470558,26545351381111982179669508⟩⟩,⟨⟨(-231376532218442487623285228),(-231376532218442487235089471)⟩,⟨31638615204417585982823909,31638615204417586371025537⟩⟩,⟨⟨(-221641493276627935573892398),(-221641493276627935200065764)⟩,⟨36284503625400960420431550,36284503625400960794267767⟩⟩,⟨⟨(-212136609816328409589986061),(-212136609816328409230248599)⟩,⟨40503637036463053482658348,40503637036463053842408802⟩⟩,⟨⟨(-202867288312113973772229094),(-202867288312113973426013977)⟩,⟨44316358086917393111426859,44316358086917393457658090⟩⟩]
noncomputable def trans8_r4_8 : Fin 16 → CBox := ![⟨⟨(-193838054257494433116545001),(-193838054257494432783633357)⟩,⟨47742692350688712457927394,47742692350688712790857986⟩⟩,⟨⟨(-185052587080976087817753327),(-185052587080976087497541320)⟩,⟨50802312048820624482260292,50802312048820624802493827⟩⟩,⟨⟨(-176513756262651264802295169),(-176513756262651264494516252)⟩,⟨53514502825900497748879952,53514502825900498056682717⟩⟩,⟨⟨(-168223658427357255901622946),(-168223658427357255605751291)⟩,⟨55898133564068363840245011,55898133564068364136142601⟩⟩,⟨⟨(-160183655197651125650986963),(-160183655197651125366802042)⟩,⟨57971629203729800870138117,57971629203729801154350819⟩⟩,⟨⟨(-152394411597946863554053715),(-152394411597946863281011577)⟩,⟨59752946526493063547307079,59752946526493063820378640⟩⟩,⟨⟨(-144855934810048751132393910),(-144855934810048750870244697)⟩,⟨61259552843240901915600295,61259552843240902177780358⟩⟩,⟨⟨(-137567613089886294319382927),(-137567613089886294067644182)⟩,⟨62508407518660189211067847,62508407518660189462838687⟩⟩,⟨⟨(-130528254665408752544518461),(-130528254665408752302993512)⟩,⟨63515946253010609233548147,63515946253010609475106236⟩⟩,⟨⟨(-123736126446229572875279640),(-123736126446229572643462436)⟩,⟨64298068032430801064812502,64298068032430801296663740⟩⟩,⟨⟨(-117188992386623391490860722),(-117188992386623391268520371)⟩,⟨64870124650661119453873326,64870124650661119676248429⟩⟩,⟨⟨(-110884151354774001065193928),(-110884151354774000851892456)⟩,⟨65246912697702640430071202,65246912697702640643408008⟩⟩,⟨⟨(-104818474372657601946660627),(-104818474372657601742208733)⟩,⟨65442667904620350990822084,65442667904620351195309736⟩⟩,⟨⟨(-98988441102532650781961670),(-98988441102532650585910728)⟩,⟨65471061728415339410125093,65471061728415339606212106⟩⟩,⟨⟨(-93390175467611201543508450),(-93390175467611201355647963)⟩,⟨65345200056610193178012471,65345200056610193365909204⟩⟩,⟨⟨(-88019480306027372630549120),(-88019480306027372450366614)⟩,⟨65077623907881512469340114,65077623907881512649558811⟩⟩]
noncomputable def trans8_r4_9 : Fin 16 → CBox := ![⟨⟨(-82871870968622475345270342),(-82871870968622475172368855)⟩,⟨64680312002695768753551045,64680312002695768926488272⟩⟩,⟨⟨(-77942607782265138565161642),(-77942607782265138399156294)⟩,⟨64164685076417174856948672,64164685076417175022989266⟩⟩,⟨⟨(-73226727311356148206393659),(-73226727311356148047120809)⟩,⟨63541611806712137363059235,63541611806712137522366759⟩⟩,⟨⟨(-68719072360775476568445797),(-68719072360775476415578518)⟩,⟨62821416227224117531906970,62821416227224117684808317⟩⟩,⟨⟨(-64414320673763078716686377),(-64414320673763078570095103)⟩,⟨62013886500382406553460348,62013886500382406700085014⟩⟩,⟨⟨(-60307012288041655585088079),(-60307012288041655444437114)⟩,⟨61128284923783333179783511,61128284923783333320467172⟩⟩,⟨⟨(-56391575522851060417849794),(-56391575522851060282992116)⟩,⟨60173359046786130863609353,60173359046786130998498982⟩⟩,⟨⟨(-52662351578438750643575797),(-52662351578438750514220296)⟩,⟨59157353776740511380889378,59157353776740511510276071⟩⟩,⟨⟨(-49113617737912965535192561),(-49113617737912965411230044)⟩,⟨58088024357550947801707513,58088024357550947925700413⟩⟩,⟨⟨(-45739609169195159536145361),(-45739609169195159417271158)⟩,⟨56972650107025924092731592,56972650107025924211635373⟩⟩,⟨⟨(-42534539332091138083465905),(-42534539332091137969549435)⟩,⟨55818048803601748490958448,55818048803601748604903659⟩⟩,⟨⟨(-39492619002227029319293092),(-39492619002227029210077265)⟩,⟨54630591617513810354495107,54630591617513810463738841⟩⟩,⟨⟨(-36608073929762288015233372),(-36608073929762287910616448)⟩,⟨53416218486258716306255853,53416218486258716410899823⟩⟩,⟨⟨(-33875161156397552948649640),(-33875161156397552848368977)⟩,⟨52180453839195734711778812,52180453839195734812085674⟩⟩,⟨⟨(-31288184019244785420699179),(-31288184019244785324640075)⟩,⟨50928422581324719013174265,50928422581324719109258704⟩⟩,⟨⟨(-28841505874628999257210347),(-28841505874628999165147424)⟩,⟨49664866251601899266713324,49664866251601899358800733⟩⟩]
noncomputable def trans8_r4_10 : Fin 16 → CBox := ![⟨⟨(-26529562578856853184420261),(-26529562578856853096107456)⟩,⟨48394159276569001101095858,48394159276569001189431951⟩⟩,⟨⟨(-24346873766432351074959516),(-24346873766432350990154261)⟩,⟨47120325245532274354165007,47120325245532274438992370⟩⟩,⟨⟨(-22288052969141581858162297),(-22288052969141581776778045)⟩,⟨45847053138996362980285539,45847053138996363061690748⟩⟩,⟨⟨(-20347816621886918732794957),(-20347816621886918654647511)⟩,⟨44577713447496770560641264,44577713447496770638808565⟩⟩,⟨⟨(-18520992003148506631222060),(-18520992003148506556247545)⟩,⟨43315374123350358637833462,43315374123350358712826753⟩⟩,⟨⟨(-16802524159510995942335997),(-16802524159510995870344870)⟩,⟨42062816313125415094986187,42062816313125415166995066⟩⟩,⟨⟨(-15187481864841467398772201),(-15187481864841467329689558)⟩,⟨40822549823794072262951978,40822549823794072332051377⟩⟩,⟨⟨(-13671062665466492795087801),(-13671062665466492728753052)⟩,⟨39596828280546101545151807,39596828280546101611502365⟩⟩,⟨⟨(-12248597063099155509212801),(-12248597063099155445575757)⟩,⟨38387663939093303718711305,38387663939093303782363235⟩⟩,⟨⟨(-10915551887337906096511250),(-10915551887337906035402228)⟩,⟨37196842119959788375099341,37196842119959788436222375⟩⟩,⟨⟨(-9667532909325804392388031),(-9667532909325804333742807)⟩,⟨36025935236720221570251650,36025935236720221628910042⟩⟩,⟨⟨(-8500286747648370190371150),(-8500286747648370134050473)⟩,⟨34876316394403218198652088,34876316394403218254985133⟩⟩,⟨⟨(-7409702116787994378423631),(-7409702116787994324342374)⟩,⟨33749172538310699868958042,33749172538310699923050775⟩⟩,⟨⟨(-6391810467469212212827292),(-6391810467469212160777794)⟩,⟨32645517137308950313419535,32645517137308950365479480⟩⟩,⟨⟨(-5442786067047990466374203),(-5442786067047990416309433)⟩,⟨31566202389218324963896847,31566202389218325013971092⟩⟩,⟨⟨(-4558945566744576006336741),(-4558945566744575958143373)⟩,⟨30511930939263315472439018,30511930939263315520640955⟩⟩]
noncomputable def trans8_r4_11 : Fin 16 → CBox := ![⟨⟨(-3736747101017473161550584),(-3736747101017473115201860)⟩,⟨29483267105642128501919109,29483267105642128548275546⟩⟩,⟨⟨(-2972788962748760672335923),(-2972788962748760627709258)⟩,⟨28480647609136120662194562,28480647609136120706828147⟩⟩,⟨⟨(-2263807896180056099257168),(-2263807896180056056312914)⟩,⟨27504391806306987848851552,27504391806306987891801979⟩⟩,⟨⟨(-1606677047724575002655916),(-1606677047724574961295976)⟩,⟨26554711428227654145660520,26554711428227654187025939⟩⟩,⟨⟨(-998403612903207853720609),(-998403612903207813919691)⟩,⟨25631719828866755969782799,25631719828866756009588546⟩⟩,⟨⟨(-436126215729312015504909),(-436126215729311977160423)⟩,⟨24735440749203014571719540,24735440749203014610068252⟩⟩,⟨⟨82887945085400418832239,82887945085400455753416⟩,⟨23865816604892147302597066,23865816604892147339521906⟩⟩,⟨⟨561246150697653863158205,561246150697653898740780⟩,⟨23022716306853613905560605,23022716306853613941146322⟩⟩,⟨⟨1001433387031949617783655,1001433387031949652044993⟩,⟨22205942625496426555960922,22205942625496426590224914⟩⟩,⟨⟨1405815711525793986740807,1405815711525794019772839⟩,⟨21415239110472000890639773,21415239110472000923674011⟩⟩,⟨⟨1776643735163733827204847,1776643735163733859035009⟩,⟨20650296578837521427040083,20650296578837521458872033⟩⟩,⟨⟨2116056195138819721698015,2116056195138819752399286⟩,⟨19910759185345752400445690,19910759185345752431148364⟩⟩,⟨⟨2426083595333166148786535,2426083595333166178374782⟩,⟨19196230089257029792229946,19196230089257029821819239⟩⟩,⟨⟨2708651893612075999265485,2708651893612076027817759⟩,⟨18506276732606778873143575,18506276732606778901696566⟩⟩,⟨⟨2965586216672257569778270,2965586216672257597317075⟩,⟨17840435745267750568271578,17840435745267750595810798⟩⟩,⟨⟨3198614584868552677387635,3198614584868552703975781⟩,⟨17198217492430594339622346,17198217492430594366210629⟩⟩]
noncomputable def trans8_r4_12 : Fin 16 → CBox := ![⟨⟨3409371631060870466078979,3409371631060870491725478⟩,⟨16579110280299546206368542,16579110280299546232014924⟩⟩,⟨⟨3599402299070161016239034,3599402299070161041013832⟩,⟨15982584235871832117635819,15982584235871832142410266⟩⟩,⟨⟨3770165508806599235680469,3770165508806599259601855⟩,⟨15408094876649501923259229,15408094876649501947180049⟩⟩,⟨⟨3923037776532802973803596,3923037776532802996925581⟩,⟨14855086386030112976064764,14855086386030112999185987⟩⟩,⟨⟨4059316780048719510159502,4059316780048719532491039⟩,⟨14322994609946894665605167,14322994609946894687935765⟩⟩,⟨⟨4180224859832273765574962,4180224859832273787173867⟩,⟨13811249790088259264162293,13811249790088259285760095⟩⟩,⟨⟨4286912448341059287427799,4286912448341059308308769⟩,⟨13319279048728863447878052,13319279048728863468757774⟩⟩,⟨⟨4380461420775872665955884,4380461420775872686165389⟩,⟨12846508639857504049805468,12846508639857504070013593⟩⟩,⟨⟨4461888361627809772830362,4461888361627809792372674⟩,⟨12392365980898126867515454,12392365980898126887056267⟩⟩,⟨⟨4532147742278428734275981,4532147742278428753203355⟩,⟨11956281478895848687301007,11956281478895848706226774⟩⟩,⟨⟨4592135005798959497885247,4592135005798959516209359⟩,⟨11537690164586382614676247,11537690164586382632998657⟩⟩,⟨⟨4642689555901819508047425,4642689555901819525808293⟩,⟨11136033147290392929072017,11136033147290392946831096⟩⟩,⟨⟨4684597647738143259421722,4684597647738143276623408⟩,⟨10750758903079407052743934,10750758903079407069943757⟩⟩,⟨⟨4718595178911216162922662,4718595178911216179608818⟩,⟨10381324408151848867405168,10381324408151848884089392⟩⟩,⟨⟨4745370379690345724857971,4745370379690345741037739⟩,⟨10027196128840962888214325,10027196128840962904392102⟩⟩,⟨⟨4765566401965651840459404,4765566401965651856167324⟩,⟨9687850879154884075302408,9687850879154884091008285⟩⟩]
noncomputable def trans8_r4_13 : Fin 16 → CBox := ![⟨⟨4779783806984444792968535,4779783806984444808204670⟩,⟨9362776556226479301567676,9362776556226479316801725⟩⟩,⟨⟨4788582952357269399277311,4788582952357269414081991⟩,⟨9051472763530062423001491,9051472763530062437804047⟩⟩,⟨⟨4792486279219336194522847,4792486279219336208903117⟩,⟨8753451331206516326057813,8753451331206516340435927⟩⟩,⟨⟨4791980500783943882293030,4791980500783943896278779⟩,⟨8468236742330245350894717,8468236742330245364878283⟩⟩,⟨⟨4787518693831605799769650,4787518693831605813361599⟩,⟨8195366473452906272819615,8195366473452906286409360⟩⟩,⟨⟨4779522294944867307867992,4779522294944867321099553⟩,⟨7934391257271895875966476,7934391257271895889195815⟩⟩,⟨⟨4768383003527120239924649,4768383003527120252801130⟩,⟨7684875274797693699867522,7684875274797693712741768⟩⟩,⟨⟨4754464593836888571067375,4754464593836888583614757⟩,⟨7446396283934691751771430,7446396283934691764316567⟩⟩,⟨⟨4738104638429792078395874,4738104638429792090612131⟩,⟨7218545690946167902455985,7218545690946167914669991⟩⟩,⟨⟨4719616145531309637264018,4719616145531309649180171⟩,⟨7000928570846432699192420,7000928570846432711106318⟩⟩,⟨⟨4699289112967072445642727,4699289112967072457262669⟩,⟨6793163642352553821578883,6793163642352553833196570⟩⟩,⟨⟨4677392001356118930795482,4677392001356118942141905⟩,⟨6594883202634907726083348,6594883202634907737427516⟩⟩,⟨⟨4654173129328619355231153,4654173129328619366302556⟩,⟨6405733026730427676800497,6405733026730427687869650⟩⟩,⟨⟨4629861993565191014260432,4629861993565191025082973⟩,⟨6225372236124966311286842,6225372236124966322107138⟩⟩,⟨⟨4604670516472114284977086,4604670516472114295553509⟩,⟨6053473140671691991924898,6053473140671692002499083⟩⟩,⟨⟨4578794224307443007475381,4578794224307443017825636⟩,⟨5889721057690797637106421,5889721057690797647454445⟩⟩]
noncomputable def trans8_r4_14 : Fin 16 → CBox := ![⟨⟨4552413358558975067342082,4552413358558975077462080⟩,⟨5733814111791822550660289,5733814111791822560778068⟩⟩,⟨⟨4525693923347985235221570,4525693923347985245136547⟩,⟨5585463018673287371350814,5585463018673287381263582⟩⟩,⟨⟨4498788671594078410182681,4498788671594078419894466⟩,⟨5444390855884758957477959,5444390855884758967187547⟩⟩,⟨⟨4471838032627937794407097,4471838032627937803933354⟩,⟨5310332823283470599234999,5310332823283470608759070⟩⟩,⟨⟨4444970983881447231892821,4444970983881447241230623⟩,⟨5183035995680744328393717,5183035995680744337729347⟩⟩,⟨⟨4418305869219879464212785,4418305869219879473383263⟩,⟨5062259069952173007076944,5062259069952173016245263⟩⟩,⟨⟨4391951166409677517202834,4391951166409677526207093⟩,⟨4947772108679261701593184,4947772108679261710595297⟩⟩,⟨⟨4366006206138830036185301,4366006206138830045039127⟩,⟨4839356282198414550735758,4839356282198414559587451⟩⟩,⟨⟨4340561844925873068260734,4340561844925873076959420⟩,⟨4736803610755178618557588,4736803610755178627254157⟩⟩,⟨⟨4315701094168969993367299,4315701094168970001931424⟩,⟨4639916708296899858264413,4639916708296899866826434⟩⟩,⟨⟨4291499707499071852156384,4291499707499071860586495⟩,⟨4548508529284779789575121,4548508529284779798003143⟩⟩,⟨⟨4268026728511505284377137,4268026728511505292687482⟩,⟨4462402119766112913424102,4462402119766112921732369⟩⟩,⟨⟨4245345000859061876814415,4245345000859061885001177⟩,⟨4381430373818603265661520,4381430373818603273846220⟩⟩,⟨⟨4223511642597287049957252,4223511642597287058038222⟩,⟨4305435796360477423597883,4305435796360477431676802⟩⟩,⟨⟨4202578486579638457060593,4202578486579638465035901⟩,⟨4234270273212011983663852,4234270273212011991637123⟩⟩,⟨⟨4182592488606891234549558,4182592488606891242432215⟩,⟨4167794849195467544753670,4167794849195467552634301⟩⟩]
noncomputable def trans8_r4_15 : Fin 16 → CBox := ![⟨⟨4163596104941941034893143,4163596104941941042677482⟩,⟨4105879514970672454533282,4105879514970672462315610⟩⟩,⟨⟨4145627640708273295131272,4145627640708273302835485⟩,⟨4048403003222045939491539,4048403003222045947193751⟩⟩,⟨⟨4128721570598057483520803,4128721570598057491144735⟩,⟨3995252594739124991332241,3995252594739124998954184⟩⟩,⟨⟨4112908833224272045323780,4112908833224272052879459⟩,⟨3946323934866111982834717,3946323934866111990388415⟩⟩,⟨⟨4098217100360612219259605,4098217100360612226742700⟩,⟨3901520860736056687328649,3901520860736056694809773⟩⟩,⟨⟨4084671022223284042361666,4084671022223284049787909⟩,⟨3860755239651510491819076,3860755239651510499243357⟩⟩,⟨⟨4072292449860214771840037,4072292449860214779209098⟩,⟨3823946818925342514379142,3823946818925342521746250⟩⟩,⟨⟨4061100635625752753788573,4061100635625752761111729⟩,⟨3791023087452404291081917,3791023087452404298403127⟩⟩,⟨⟨4051112412632600684663609,4051112412632600691935132⟩,⟨3761919149244405314874643,3761919149244405322144229⟩⟩,⟨⟨4042342353987512427186981,4042342353987512434423229⟩,⟨3736577609126265377639143,3736577609126265384873459⟩⟩,⟨⟨4034802912533149909117105,4034802912533149916317677⟩,⟨3714948470761905740676111,3714948470761905747874756⟩⟩,⟨⟨4028504541735388213278595,4028504541735388220454219⟩,⟨3696989047150508004501840,3696989047150508011675542⟩⟩,⟨⟨4023455798273201442272975,4023455798273201449419067⟩,⟨3682663883710298475555516,3682663883710298482699691⟩⟩,⟨⟨4019663426806971882497256,4019663426806971889628537⟩,⟨3671944694045509898800883,3671944694045509905930250⟩⟩,⟨⟨4017132427320540019018941,4017132427320540026135036⟩,⟨3664810308472945184939722,3664810308472945192053906⟩⟩,⟨⟨4015866105352441779198394,4015866105352441786309672⟩,⟨3661246635367141870745795,3661246635367141877855162⟩⟩]
noncomputable def trans8_r4 : Fin 16 → Fin 16 → CBox := ![trans8_r4_0,trans8_r4_1,trans8_r4_2,trans8_r4_3,trans8_r4_4,trans8_r4_5,trans8_r4_6,trans8_r4_7,trans8_r4_8,trans8_r4_9,trans8_r4_10,trans8_r4_11,trans8_r4_12,trans8_r4_13,trans8_r4_14,trans8_r4_15]
noncomputable def trans8_r5_0 : Fin 16 → CBox := ![⟨⟨(-181983256820125019599337860756),(-181983256820125019444657560749)⟩,⟨128252827677630451469122659863,128252827677630451623887463075⟩⟩,⟨⟨(-181904094476039445339613771447),(-181904094476039445184946424271)⟩,⟨128268523863427011164272067429,128268523863427011319023895554⟩⟩,⟨⟨(-181745823184671930168535598206),(-181745823184671930013894430244)⟩,⟨128299838747098851855596597232,128299838747098852010322201524⟩⟩,⟨⟨(-181508549769037322951764324567),(-181508549769037322797162573701)⟩,⟨128346617545539348746675785699,128346617545539348901361905894⟩⟩,⟨⟨(-181192434536708094708070572047),(-181192434536708094553521499789)⟩,⟨128408628565556939006608280868,128408628565556939161241633038⟩⟩,⟨⟨(-180797691366164525745028599032),(-180797691366164525590545491357)⟩,⟨128485563780596892717406419039,128485563780596892871973694759⟩⟩,⟨⟨(-180324587819752277117488418706),(-180324587819752276963084602889)⟩,⟨128577039597969291842113186445,128577039597969291996601035937⟩⟩,⟨⟨(-179773445281396977053921537245),(-179773445281396976899610371185)⟩,⟨128682597815095464062424000955,128682597815095464216819043760⟩⟩,⟨⟨(-179144639116781277361357545197),(-179144639116781277207152454799)⟩,⟨128801706762911823784127072395,128801706762911823938415859976⟩⟩,⟨⟨(-178438598853257839942993540337),(-178438598853257839788907977255)⟩,⟨128933762634195979653415255304,128933762634195979807584313309⟩⟩,⟨⟨(-177655808376354238525937157382),(-177655808376354238371984677939)⟩,⟨129078090994205021438491060126,129078090994205021592526809440⟩⟩,⟨⟨(-176796806139325091612855451697),(-176796806139325091459049616538)⟩,⟨129233948470640099466899755334,129233948470640099620788612449⟩⟩,⟨⟨(-175862185381825103849363640345),(-175862185381825103695718181566)⟩,⟨129400524619574820789273565428,129400524619574820943001775256⟩⟩,⟨⟨(-174852594353416238118714389315),(-174852594353416237965242983721)⟩,⟨129576943963607742546477068607,129576943963607742700030931302⟩⟩,⟨⟨(-173768736537285043983266013598),(-173768736537285043829982588339)⟩,⟨129762268198121556947263211582,129762268198121557100628776786⟩⟩,⟨⟨(-172611370869234215631075659925),(-172611370869234215477994029465)⟩,⟨129955498561153729768925387948,129955498561153729922088817958⟩⟩]
noncomputable def trans8_r5_1 : Fin 16 → CBox := ![⟨⟨(-171381311946727633375800136265),(-171381311946727633222934494501)⟩,⟨130155578362005760236375568546,130155578362005760389322646015⟩⟩,⟨⟨(-170079430222512240549890858672),(-170079430222512240397255126489)⟩,⟨130361395663341352705214559394,130361395663341352857931340007⟩⟩,⟨⟨(-168706652177114791758303051019),(-168706652177114791605911671177)⟩,⟨130571786111148204809516229226,130571786111148204961988246535⟩⟩,⟨⟨(-167263960464318325817241362299),(-167263960464318325665108412875)⟩,⟨130785535906564497097052566865,130785535906564497249265719164⟩⟩,⟨⟨(-165752394023563583384826306204),(-165752394023563583232966601876)⟩,⟨131001384913200291136880841616,131001384913200291288820290275⟩⟩,⟨⟨(-164173048153095782530822496916),(-164173048153095782379250179107)⟩,⟨131218029893216783693406712738,131218029893216783845058292550⟩⟩,⟨⟨(-162527074537588315838488024502),(-162527074537588315687218197037)⟩,⟨131434127865063701944050204240,131434127865063702095398787210⟩⟩,⟨⟨(-160815681223923016408502796798),(-160815681223923016257549772492)⟩,⟨131648299575418136509019150517,131648299575418136660050399882⟩⟩,⟨⟨(-159040132538792472242519724499),(-159040132538792472091899113233)⟩,⟨131859133077517969737586536751,131859133077517969888284818192⟩⟩,⟨⟨(-157201748941814095580478415087),(-157201748941814095430204494561)⟩,⟨132065187407741033805268910600,132065187407741033955619922414⟩⟩,⟨⟨(-155301906807908747894869495487),(-155301906807908747744958160793)⟩,⟨132264996351948582474480272364,132264996351948582624468094876⟩⟩,⟨⟨(-153342038132798973963023229604),(-153342038132798973813488957996)⟩,⟨132457072292790019854442042383,132457072292790020004052174234⟩⟩,⟨⟨(-151323630155623415503036612668),(-151323630155623415353895931037)⟩,⟨132639910128856612368106944110,132639910128856612517322833615⟩⟩,⟨⟨(-149248224892844671541582420063),(-149248224892844671392849653740)⟩,⟨132811991256276696720324344435,132811991256276696869131642234⟩⟩,⟨⟨(-147117418577847469765053083050),(-147117418577847469616745035491)⟩,⟨132971787603065325312711316090,132971787603065325461093193903⟩⟩,⟨⟨(-144932861000882033630172453661),(-144932861000882033482303652201)⟩,⟨133117765706279047574260412988,133117765706279047722202319471⟩⟩]
noncomputable def trans8_r5_2 : Fin 16 → CBox := ![⟨⟨(-142696254744303296834010071651),(-142696254744303296686598158397)⟩,⟨133248390821783334355101004408,133248390821783334502585272478⟩⟩,⟨⟨(-140409354308389250973545778116),(-140409354308389250826604898924)⟩,⟨133362131056217761284068982239,133362131056217761431081442325⟩⟩,⟨⟨(-138073965123390132583499058204),(-138073965123390132437047015240)⟩,⟨133457461510544236756767519231,133457461510544236903290344356⟩⟩,⟨⟨(-135691942443863078921109102426),(-135691942443863078775160319460)⟩,⟨133532868424388051130395607939,133532868424388051276414350762⟩⟩,⟨⟨(-133265190121782823930809007585),(-133265190121782823785382247711)⟩,⟨133586853310232081137886410300,133586853310232081283382282912⟩⟩,⟨⟨(-130795659255386284695884317456),(-130795659255386284550993445549)⟩,⟨133617937066402823668634181639,133617937066402823813593296115⟩⟩,⟨⟨(-128285346711205627784203946396),(-128285346711205627639867824195)⟩,⟨133624664057694727975850135718,133624664057694728120253605875⟩⟩,⟨⟨(-125736293517268537930879597950),(-125736293517268537787112354792)⟩,⟨133605606152418157856368559512,133605606152418158000202233316⟩⟩,⟨⟨(-123150583125993688482689261861),(-123150583125993688339511016024)⟩,⟨133559366704627783533786965591,133559366704627783677030700439⟩⟩,⟨⟨(-120530339545881407505102737630),(-120530339545881407362526669022)⟩,⟨133484584470293724858717982801,133484584470293725001358576928⟩⟩,⟨⟨(-117877725341691650985305060352),(-117877725341691650843351118208)⟩,⟨133379937446218685488202949235,133379937446218685630220429770⟩⟩,⟨⟨(-115194939503410882459385074716),(-115194939503410882318066863282)⟩,⟨133244146620581853633877880442,133244146620581853775258621802⟩⟩,⟨⟨(-112484215184933416667673225086),(-112484215184933416527012043820)⟩,⟨133075979624105584831637154280,133075979624105584972359833721⟩⟩,⟨⟨(-109747817314018178434150518996),(-109747817314018178294158801611)⟩,⟨132874254270994761926983673982,132874254270994762067035837585⟩⟩,⟨⟨(-106988040075725500129900909715),(-106988040075725499990599681963)⟩,⟨132637841978992019052524835728,132637841978992019191885435424⟩⟩,⟨⟨(-104207204272187267970269560722),(-104207204272187267831671643599)⟩,⟨132365671058125314631489947413,132365671058125314770146142782⟩⟩]
noncomputable def trans8_r5_3 : Fin 16 → CBox := ![⟨⟨(-101407654562214073755434740626),(-101407654562214073617562945890)⟩,⟨132056729857998048791221331994,132056729857998048929150289465⟩⟩,⟨⟨(-98591756584891604589228970546),(-98591756584891604452094348468)⟩,⟨131710069763786247708736866878,131710069763786247845927518290⟩⟩,⟨⟨(-95761893971961821790749866277),(-95761893971961821654374464252)⟩,⟨131324808031462275123555657571,131324808031462275259985935097⟩⟩,⟨⟨(-92920465254419016588353219644),(-92920465254419016452748793140)⟩,⟨130900130453159853465562808298,130900130453159853601220939522⟩⟩,⟨⟨(-90069880669373040412894231497),(-90069880669373040278084606492)⟩,⟨130435293844030430223905258649,130435293844030430358767397970⟩⟩,⟨⟨(-87212558873838349237101214564),(-87212558873838349103096191902)⟩,⟨129929628342415422194649755672,129929628342415422328706087115⟩⟩,⟨⟨(-84350923572694454148608409095),(-84350923572694454015430960845)⟩,⟨129382539515671685786016132933,129382539515671685919243666469⟩⟩,⟨⟨(-81487400068627457295356034002),(-81487400068627457163016553402)⟩,⟨128793510264537529224567126457,128793510264537529356955454946⟩⟩,⟨⟨(-78624411742400161554246244259),(-78624411742400161422770031234)⟩,⟨128162102519512293590335152849,128162102519512293721858959385⟩⟩,⟨⟨(-75764376472306448498441648582),(-75764376472306448367836371498)⟩,⟨127487958723342333703601687250,127487958723342333834253291786⟩⟩,⟨⟨(-72909703002141005705395021310),(-72909703002141005575656798301)⟩,⟨126770803094358237317619000906,126770803094358237447402216335⟩⟩,⟨⟨(-70062787267454964525367056976),(-70062787267454964396293923374)⟩,⟨126010442666090207222564798762,126010442666090207351681172071⟩⟩,⟨⟨(-67226008690268647991628828278),(-67226008690268647863246897340)⟩,⟨125206768099298342407345762428,125206768099298342535769175893⟩⟩,⟨⟨(-64401726452771662897168866649),(-64401726452771662769484243767)⟩,⟨124359754263289517450099143083,124359754263289517577823492935⟩⟩,⟨⟨(-61592275760855430188897649624),(-61592275760855430061935225822)⟩,⟨123469460584149889385942061645,123469460584149889512942455753⟩⟩,⟨⟨(-58799964108591575959455718295),(-58799964108591575833222841747)⟩,⟨122536031158298775375069246113,122536031158298775501338340449⟩⟩]
noncomputable def trans8_r5_4 : Fin 16 → CBox := ![⟨⟨(-56027067554989274391529318121),(-56027067554989274266054352424)⟩,⟨121559694630562574658558835894,121559694630562574784068268185⟩⟩,⟨⟨(-53275827024533765118089490712),(-53275827024533764993376174662)⟩,⟨120540763836773217278668807155,120540763836773217403414846296⟩⟩,⟨⟨(-50548444643125245922580867456),(-50548444643125245798655326021)⟩,⟨119479635211710820458496962254,119479635211710820582453488163⟩⟩,⟨⟨(-47847080121100831722016986129),(-47847080121100831598884967246)⟩,⟨118376787964031198647887792683,118376787964031198771049067483⟩⟩,⟨⟨(-45173847195031228484555774503),(-45173847195031228362246572577)⟩,⟨117232783020641869266747960690,117232783020641869389084697466⟩⟩,⟨⟨(-42530810139937455491362761257),(-42530810139937455369878550407)⟩,⟨116048261743811395917462358858,116048261743811396038972396898⟩⟩,⟨⟨(-39919980363470933164825004404),(-39919980363470933044192913574)⟩,⟨114823944425112418537127442170,114823944425112418657783663460⟩⟩,⟨⟨(-37343313093442428633279253844),(-37343313093442428513503121824)⟩,⟨113560628561104595189739548306,113560628561104595309538129843⟩⟩,⟨⟨(-34802704169871934768114608263),(-34802704169871934649225655112)⟩,⟨112259186916455962641397266950,112259186916455962760307002130⟩⟩,⟨⟨(-32299986952463096641139884670),(-32299986952463096523137163454)⟩,⟨110920565380975957776262072363,110920565380975957894283927141⟩⟩,⟨⟨(-29836929354083167658849339991),(-29836929354083167541760717546)⟩,⟨109545780627786606107631336681,109545780627786606224737461076⟩⟩,⟨⟨(-27415231010453879481052381393),(-27415231010453879364879493956)⟩,⟨108135917580586311739843439473,108135917580586311856032218385⟩⟩,⟨⟨(-25036520595831572874723332731),(-25036520595831572759497725298)⟩,⟨106692126698659493939182694452,106692126698659494054422602300⟩⟩,⟨⟨(-22702353293978306603849754112),(-22702353293978306489568409572)⟩,⟨105215621088951338163129043989,105215621088951338277423121834⟩⟩,⟨⟨(-20414208433201593572732598422),(-20414208433201593459423828771)⟩,⟨103707673455156629440567722520,103707673455156629553887680859⟩⟩,⟨⟨(-18173487293671361691822108372),(-18173487293671361579485081427)⟩,⟨102169612894361640431534835680,102169612894361640543881532621⟩⟩]
noncomputable def trans8_r5_5 : Fin 16 → CBox := ![⟨⟨(-15981511094611440855225098842),(-15981511094611440743893071696)⟩,⟨100602821552325168470854822235,100602821552325168582195025569⟩⟩,⟨⟨(-13839519168312346757184893994),(-13839519168312346646850825908)⟩,⟨99008731148986078179624098967,99008731148986078289964877797⟩⟩,⟨⟨(-11748667327225629498811849640),(-11748667327225629389504182721)⟩,⟨97388819386237363504644662317,97388819386237363613957602199⟩⟩,⟨⟨(-9710026429681075725705373789),(-9710026429681075617420584296)⟩,⟨95744606250408302817737923796,95744606250408302926026578457⟩⟩,⟨⟨(-7724581149020304865042784999),(-7724581149020304757813472267)⟩,⟨94077650222244522562597466965,94077650222244522669829267022⟩⟩,⟨⟨(-5793228950167679015795947219),(-5793228950167678909612912438)⟩,⟨92389544407468778025016196456,92389544407468778131200372533⟩⟩,⟨⟨(-3916779276866012204152350295),(-3916779276866012099043849289)⟩,⟨90681912601241378358417366371,90681912601241378463525694850⟩⟩,⟨⟨(-2095952951994515832977204806),(-2095952951994515728936838658)⟩,⟨88956405300017119735747640564,88956405300017119839786553547⟩⟩,⟨⟨(-331381792564061434129427847),(-331381792564061331190903610)⟩,⟨87214695674414367775548813161,87214695674414367878484637908⟩⟩,⟨⟨1376391559845430420835870770,1376391559845430522686169866⟩,⟨85458475516770908971423916485,85458475516770909073270304130⟩⟩,⟨⟨3026913593274411689530076119,3026913593274411790264400630⟩,⟨83689451177060076247116602474,83689451177060076347845839561⟩⟩,⟨⟨4619819665101627622936295112,4619819665101627722564041267⟩,⟨81909339500779499979510688456,81909339500779500079132206626⟩⟩,⟨⟨6154833529019524029165662232,6154833529019524127654486366⟩,⟨80119863782304046599833798657,80119863782304046698315292080⟩⟩,⟨⟨7631766651813549927156890946,7631766651813550024522739933⟩,⟨78322749747014834180864141870,78322749747014834278221593326⟩⟩,⟨⟨9050517323294951920558481797,9050517323294952016774413001⟩,⟨76519721575278754438359400823,76519721575278754534565906574⟩⟩,⟨⟨10411069563521348488306842156,10411069563521348583385315171⟩,⟨74712497981059117046272772460,74712497981059117141340828707⟩⟩]
noncomputable def trans8_r5_6 : Fin 16 → CBox := ![⟨⟨11713491832201431657556995384,11713491832201431751464726760⟩,⟨72902788357589627131285483591,72902788357589627225181847508⟩⟩,⟨⟨12957935545915585319803090741,12957935545915585412561018061⟩,⟨71092289002142988895324175820,71092289002142988988069821230⟩⟩,⟨⟨14144633409489227653027477781,14144633409489227744609749383⟩,⟨69282679431474378596273340400,69282679431474378687842456505⟩⟩,⟨⟨15273897568526677571667007076,15273897568526677662089141674⟩,⟨67475618799021515702184921857,67475618799021515792593064124⟩⟩,⟨⟨16346117590746937308746690586,16346117590746937397977859449⟩,⟨65672742424400016482855475384,65672742424400016572071857268⟩⟩,⟨⟨17361758284355850063706316329,17361758284355850151769244135⟩,⟨63875658445148321034802073273,63875658445148321122849455227⟩⟩,⟨⟨18321357362238777404031988569,18321357362238777490902158179⟩,⟨62085944600054148633223596413,62085944600054148720077503153⟩⟩,⟨⟨19225522961261677172113183585,19225522961261677257809109602⟩,⟨60305145152737763651773266181,60305145152737763737452248194⟩⟩,⟨⟨20074931026423983011902485154,20074931026423983096474177666⟩,⟨58534767963480106309197369838,58534767963480106393751450330⟩⟩,⟨⟨20870322570012040980539595296,20870322570012041064039933229⟩,⟨56776281716569988649519980739,56776281716569988733002065860⟩⟩,⟨⟨21612500816255423053038305816,21612500816255423135441577678⟩,⟨55031113309708126477047337407,55031113309708126559431761452⟩⟩,⟨⟨22302328242288922022085733880,22302328242288922103410670580⟩,⟨53300645411250914647708487097,53300645411250914729014018727⟩⟩,⟨⟨22940723526469487485015128991,22940723526469487565230564982⟩,⟨51586214190307761623048499307,51586214190307761703244019246⟩⟩,⟨⟨23528658415289181004479857254,23528658415289181083612162349⟩,⟨49889107223926719081506261878,49889107223926719160618174931⟩⟩,⟨⟨24067154520262145543462356219,24067154520262145621487309537⟩,⟨48210561584818318166817754877,48210561584818318244821884343⟩⟩,⟨⟨24557280056245675531174319640,24557280056245675608113359539⟩,⟨46551762112281176187807463138,46551762112281176264725281721⟩⟩]
noncomputable def trans8_r5_7 : Fin 16 → CBox := ![⟨⟨25000146532683150189369854859,25000146532683150265191224328⟩,⟨44913839868209234459397872799,44913839868209234535197668399⟩⟩,⟨⟨25396905409230592379540949000,25396905409230592454275844891⟩,⟨43297870779283517627053744465,43297870779283517701766744516⟩⟩,⟨⟨25748744727149994151985096109,25748744727149994225610958437⟩,⟨41704874465685048613500554084,41704874465685048687104240382⟩⟩,⟨⟨26056885727722669609080779388,26056885727722669681621559468⟩,⟨40135813255913860302059402171,40135813255913860374577756332⟩⟩,⟨⟨26322579468756407709565466299,26322579468756407780992874169⟩,⟨38591591386565607766563850150,38591591386565607837968624167⟩⟩,⟨⟨26547103450033028684965141629,26547103450033028755311010867⟩,⟨37073054385205616698446349177,37073054385205616768769403116⟩⟩,⟨⟨26731758258270280345909542361,26731758258270280415153084093⟩,⟨35580988633793618115966853456,35580988633793618185187437169⟩⟩,⟨⟨26877864241856263371746558266,26877864241856263439914002173⟩,⟨34116121109454010941528243408,34116121109454011009672612389⟩⟩,⟨⟨26986758225258381063018420127,26986758225258381130128243104⟩,⟨32679119298759121144203509053,32679119298759121211290856141⟩⟩,⟨⟨27059790272614994394508185712,27059790272614994460610757399⟩,⟨31270591281099196630209767291,31270591281099196696290686830⟩⟩,⟨⟨27098320509589521299903205108,27098320509589521364977499885⟩,⟨29891085976155135303612591686,29891085976155135368666056989⟩⟩,⟨⟨27103716012106787562869574328,27103716012106787626941829218⟩,⟨28541093549970260363646535390,28541093549970260427698769731⟩⟩,⟨⟨27077347770103271881393270001,27077347770103271944436452480⟩,⟨27221045973637620880593065615,27221045973637620943617035311⟩⟩,⟨⟨27020587733909839350926187653,27020587733909839412974474438⟩,⟨25931317728180808536793841676,25931317728180808598823706788⟩⟩,⟨⟨26934805950351043307572733499,26934805950351043368606883513⟩,⟨24672226648810353983459696515,24672226648810354044476211502⟩⟩,⟨⟨26821367795092555030943752001,26821367795092555090991792397⟩,⟨23444034901385317710892595485,23444034901385317770923771544⟩⟩]
noncomputable def trans8_r5_8 : Fin 16 → CBox := ![⟨⟨26681631307201231250253444318,26681631307201231309287769392⟩,⟨22246950083601349439246242240,22246950083601349498264469680⟩⟩,⟨⟨26516944631304220281783509902,26516944631304220339842363543⟩,⟨21081126443162598690286749500,21081126443162598748330253275⟩⟩,⟨⟨26328643572147777140674455908,26328643572147777197740406142⟩,⟨19946666204975478018034400066,19946666204975478075085740799⟩⟩,⟨⟨26118049265766489920410616500,26118049265766489976513167291⟩,⟨18843620999227196346615818929,18843620999227196402704483036⟩⟩,⟨⟨25886465970882721628915214269,25886465970882721684030794019⟩,⟨17771993382080715902286465961,17771993382080715957388874503⟩⟩,⟨⟨25635178983567454023122614239,25635178983567454077288508662⟩,⟨16731738440629612468410836893,16731738440629612522564256059⟩⟩,⟨⟨25365452677610477016674854102,25365452677610477069875408084⟩,⟨15722765473710265430745151420,15722765473710265483933916262⟩⟩,⟨⟨25078528672472959065078204712,25078528672472959117344084081⟩,⟨14744939740163676134895747534,14744939740163676187150505361⟩⟩,⟨⟨24775624130131670395719750147,24775624130131670447027262141⟩,⟨13798084266173605476744964951,13798084266173605528042013614⟩⟩,⟨⟨24457930181574157100206457830,24457930181574157150595793720⟩,⟨12881981703380036396093358577,12881981703380036446472869019⟩⟩,⟨⟨24126610483170447509703937644,24126610483170447559161163067⟩,⟨11996376229575430755763516050,11996376229575430805211542174⟩⟩,⟨⟨23782799902631692097179550255,23782799902631692145736153898⟩,⟨11140975483933932829716928197,11140975483933932878264939804⟩⟩,⟨⟨23427603333771576128438213448,23427603333771576176074071068⟩,⟨10315452528898505355827169899,10315452528898505403455031213⟩⟩,⟨⟨23062094638814277522565446315,23062094638814277569319484944⟩,⟨9519447831055782479864097156,9519447831055782526610715325⟩⟩,⟨⟨22687315716544838048705548467,22687315716544838094565455185⟩,⟨8752571253560901780154461241,8752571253560901826007510238⟩⟩,⟨⟨22304275694175527804843778274,22304275694175527849841540281⟩,⟨8014404052932370589111930679,8014404052932370634103378998⟩⟩]
noncomputable def trans8_r5_9 : Fin 16 → CBox := ![⟨⟨21913950240406349497803753571,21913950240406349541918579930⟩,⟨7304500873317706001930804521,7304500873317706046039848607⟩⟩,⟨⟨21517280996790273884566451035,21517280996790273927839883084⟩,⟨6622391731631698736214406707,6622391731631698779482568396⟩⟩,⟨⟨21115175124174930995475821482,21115175124174931037897057576⟩,⟨5967583987288202020591922624,5967583987288202063008386289⟩⟩,⟨⟨20708504960682903521893389145,20708504960682903563494585611⟩,⟨5339564290580847865944623949,5339564290580847907541527877⟩⟩,⟨⟨20298107787412873835426768565,20298107787412873876190969496⟩,⟨4737800504115567989895972791,4737800504115568030656347359⟩⟩,⟨⟨19884785697793860243104104880,19884785697793860283070435274⟩,⟨4161743592055799063440639502,4161743592055799103403591567⟩⟩,⟨⟨19469305566304645383105630261,19469305566304645422264656644⟩,⟨3610829472307381295022522144,3610829472307381334178603835⟩⟩,⟨⟨19052399112080071217171844191,19052399112080071255555599551⟩,⟨3084480827142075347025035858,3084480827142075385406263185⟩⟩,⟨⟨18634763052764798595427722288,18634763052764798633018825462⟩,⟨2582108868134058484160663448,2582108868134058521749641200⟩⟩,⟨⟨18217059343842889724057031829,18217059343842889760896100932⟩,⟨2103115051660535753000657290,2103115051660535789837986784⟩⟩,⟨⟨17799915498567502383640340444,17799915498567502419719169899⟩,⟨1646892741593631693338084752,1646892741593631729415546002⟩⟩,⟨⟨17383924983538279129535884435,17383924983538279164886100314⟩,⟨1212828816184034785309346039,1212828816184034820658549514⟩⟩,⟨⟨16969647684923739471567358563,16969647684923739506174717404⟩,⟨800305216505587521603421447,800305216505587556210109500⟩⟩,⟨⟨16557610440301090283771711056,16557610440301090317674275126⟩,⟨408700434192408480350018417,408700434192408514252238333⟩⟩,⟨⟨16148307631085210168820074361,16148307631085210202010708954⟩,⟨37390936554585503102190403,37390936554585536292793380⟩⟩,⟨⟨15742201830540899682235064285,15742201830540899714863931915⟩,⟨(-314247472496490403017475028),(-314247472496490370388341476)⟩⟩]
noncomputable def trans8_r5_10 : Fin 16 → CBox := ![⟨⟨15339724502416508593145986287,15339724502416508625206123425⟩,⟨(-646838356947818624270064084),(-646838356947818592209379791)⟩⟩,⟨⟨14941276745301379002808525218,14941276745301379034334166568⟩,⟨(-961003419521893012737707833),(-961003419521892981211253352)⟩⟩,⟨⟨14547230077892755147070690058,14547230077892755178050136552⟩,⟨(-1257361339454361961184896970),(-1257361339454361930204386855)⟩⟩,⟨⟨14157927260458446213087771507,14157927260458446243546285282⟩,⟨(-1536526677520132520374926811),(-1536526677520132489915113001)⟩⟩,⟨⟨13773683147898101878118351015,13773683147898101908038364304⟩,⟨(-1799108848335325120152212578),(-1799108848335325090230677876)⟩⟩,⟨⟨13394785569936972684849810155,13394785569936972714263014261⟩,⟨(-2045711159697441409419761611),(-2045711159697441380004827338)⟩⟩,⟨⟨13021496234129977766364682710,13021496234129977795260424499⟩,⟨(-2276929918477031341088107065),(-2276929918477031312190440374)⟩⟩,⟨⟨12654051647509297967415067441,12654051647509297995818388947⟩,⟨(-2493353602341439890253935054),(-2493353602341439861848505582)⟩⟩,⟨⟨12292664052874078123370155927,12292664052874078151262793260⟩,⟨(-2695562096375159191388334456),(-2695562096375159163493419920)⟩⟩,⟨⟨11937522375894710088217963542,11937522375894710115633012668⟩,⟨(-2884125993462071783935662514),(-2884125993462071756518176954)⟩⟩,⟨⟨11588793179385165127548561418,11588793179385165154476310584⟩,⟨(-3059605957112497265503790708),(-3059605957112497238573458404)⟩⟩,⟨⟨11246621621283580197492869593,11246621621283580223957956727⟩,⟨(-3222552145252395444149418909),(-3222552145252395417681611339)⟩⟩,⟨⟨10911132413072456403723335020,10911132413072456429710262964⟩,⟨(-3373503693343183631738212046),(-3373503693343183605748438734)⟩⟩,⟨⟨10582430775564133742272731160,10582430775564133767812201102⟩,⟨(-3512988255068152863392636530),(-3512988255068152837850204083)⟩⟩,⟨⟨10260603389173458516158956989,10260603389173458541242081852⟩,⟨(-3641521598705093028217791390),(-3641521598705093003131597954)⟩⟩,⟨⟨9945719335996617629280385276,9945719335996617653931255611⟩,⟨(-3759607257204059797946953427),(-3759607257204059773292915779)⟩⟩]
noncomputable def trans8_r5_11 : Fin 16 → CBox := ![⟨⟨9637831031211904440225131464,9637831031211904464426976861⟩,⟨(-3867736229903768277067470041),(-3867736229903768252862369896)⟩⟩,⟨⟨9336975141513702076626798076,9336975141513702100411785262⟩,⟨(-3966386733749350338487515229),(-3966386733749350314699191313)⟩⟩,⟨⟨9043173488484293108193106961,9043173488484293131553075343⟩,⟨(-4056024001817582525451180311),(-4056024001817582502087802897)⟩⟩,⟨⟨8756433934998374639499134070,8756433934998374662457493029⟩,⟨(-4137100126912551548368175697),(-4137100126912551525406340866)⟩⟩,⟨⟨8476751252941595670774901473,8476751252941595693317832683⟩,⟨(-4210053947964408912045874124),(-4210053947964408889499410022)⟩⟩,⟨⟨8204107970706334611283603652,8204107970706334633440225140⟩,⟨(-4275310976945678067514032933),(-4275310976945678045353825363)⟩⟩,⟨⟨7938475199104669448650342845,7938475199104669470413112791⟩,⟨(-4333283364012795362558034846),(-4333283364012795340791634018)⟩⟩,⟨⟨7679813434509505313450962981,7679813434509505334842521498⟩,⟨(-4384369898584450843215865218),(-4384369898584450821820634844)⟩⟩,⟨⟨7428073338199630299615079676,7428073338199630320620611523⟩,⟨(-4428956044082095898338574987),(-4428956044082095877329339233)⟩⟩,⟨⟨7183196491042656987379504083,7183196491042657008028912339⟩,⟨(-4467414004080945328941607632),(-4467414004080945308288465381)⟩⟩,⟨⟨6945116122801028768905641663,6945116122801028789191918440⟩,⟨(-4500102817651164812978849978),(-4500102817651164792688816337)⟩⟩,⟨⟨6713757815490246775849295840,6713757815490246795794231992⟩,⟨(-4527368481707948792048994451),(-4527368481707948772100280976)⟩⟩,⟨⟨6489040180354987389546192103,6489040180354987409137275616⟩,⟨(-4549544098235115742369780628),(-4549544098235115722774906964)⟩⟩,⟨⟨6270875508157673689923401457,6270875508157673709187816116⟩,⟨(-4566950044298948394401999447),(-4566950044298948375133782649)⟩⟩,⟨⟨6059170392595234393010284415,6059170392595234411941468126⟩,⟨(-4579894162826573881443861629),(-4579894162826573862508869964)⟩⟩,⟨⟨5853826326773180837382700433,5853826326773180856001554200⟩,⟨(-4588671972185521923524707518),(-4588671972185521904902041198)⟩⟩]
noncomputable def trans8_r5_12 : Fin 16 → CBox := ![⟨⟨5654740272771755144188004157,5654740272771755162480411382⟩,⟨(-4593566892667550588038962212),(-4593566892667550569742744924)⟩⟩,⟨⟨5461805204436794540179729312,5461805204436794558174010918⟩,⟨(-4594850488049747780505556079),(-4594850488049747762507466210)⟩⟩,⟨⟨5274910623618203003191373032,5274910623618203020881349011⟩,⟨(-4592782720478689697350959028),(-4592782720478689679657181841)⟩⟩,⟨⟨5093943050161644353146797346,5093943050161644370552442688⟩,⟨(-4587612216998482519341674479),(-4587612216998482501932235215)⟩⟩,⟨⟨4918786486034426909752508720,4918786486034426926862302607⟩,⟨(-4579576546120279760689024282),(-4579576546120279743575449652)⟩⟩,⟨⟨4749322854034725168218557073,4749322854034725185057604221⟩,⟨(-4568902502908836735510008097),(-4568902502908836718667192140)⟩⟩,⟨⟨4585432411594491363524717523,4585432411594491380087150269⟩,⟨(-4555806401140350815181119820),(-4555806401140350798614934663)⟩⟩,⟨⟨4426994140240885004454253826,4426994140240885020759123573⟩,⟨(-4540494371164790663704863360),(-4540494371164790647396257029)⟩⟩,⟨⟨4273886111329046734496436210,4273886111329046750531023280⟩,⟨(-4523162662184722619007932424),(-4523162662184722602969630109)⟩⟩,⟨⟨4125985828700835810270041389,4125985828700835826060032495⟩,⟨(-4503997947740914933786429480),(-4503997947740914917992742153)⟩⟩,⟨⟨3983170548960022907773744596,3983170548960022923313538259⟩,⟨(-4483177633272391379667519566),(-4483177633272391364124052495)⟩⟩,⟨⟨3845317580084677002742124150,3845317580084677018049850325⟩,⟨(-4460870164694798465964608380),(-4460870164694798450653230402)⟩⟩,⟨⟨3712304559122409411366604053,3712304559122409426431472054⟩,⟨(-4437235337015661219766895890),(-4437235337015661204698402290)⟩⟩,⟨⟨3584009709734047387089997611,3584009709734047401935068865⟩,⟨(-4412424602078078477828495516),(-4412424602078078462979822287)⟩⟩,⟨⟨3460312080366514213003111044,3460312080366514227626212849⟩,⟨(-4386581374595427612308558710),(-4386581374595427597681914655)⟩⟩,⟨⟨3341091763846503165602817105,3341091763846503180026324202⟩,⟨(-4359841335708517331273524012),(-4359841335708517316846584917)⟩⟩]
noncomputable def trans8_r5_13 : Fin 16 → CBox := ![⟨⟨3226230099193258102793146073,3226230099193258117004231177⟩,⟨(-4332332733363180261316325909),(-4332332733363180247101919171)⟩⟩,⟨⟨3115609856451719355669770378,3115609856451719369692160220⟩,⟨(-4304176678870395486281456103),(-4304176678870395472255847673)⟩⟩,⟨⟨3009115405346760617748354067,3009115405346760631576493863⟩,⟨(-4275487439072561138477571047),(-4275487439072561124646314384)⟩⟩,⟨⟨2906632868555524628956184925,2906632868555524642606146750⟩,⟨(-4246372723598408092421245559),(-4246372723598408078768263039)⟩⟩,⟨⟨2808050260388248836608823562,2808050260388248850069982345⟩,⟨(-4216933966745189360993336260),(-4216933966745189347529252626)⟩⟩,⟨⟨2713257611658734141961578017,2713257611658734155254856513⟩,⟨(-4187266603580147962029974772),(-4187266603580147948733860982)⟩⟩,⟨⟨2622147081514017693994687264,2622147081514017707114712392⟩,⟨(-4157460339903829737744153551),(-4157460339903829724621381409)⟩⟩,⟨⟨2534613056979121177593111484,2534613056979121190555208453⟩,⟨(-4127599415765555176244639031),(-4127599415765555163279878302)⟩⟩,⟨⟨2450552240957204542836991725,2450552240957204555629223251⟩,⟨(-4097762862266299866664048130),(-4097762862266299853869236027)⟩⟩,⟨⟨2369863729408295171390713452,2369863729408295184034769716⟩,⟨(-4068024751426375358740284211),(-4068024751426375346093724569)⟩⟩,⟨⟨2292449078411205384015646453,2292449078411205396506320505⟩,⟨(-4038454438934682361907438238),(-4038454438934682349414336805)⟩⟩,⟨⟨2218212361793505766257821511,2218212361793505778609725875⟩,⟨(-4009116799632969409065720529),(-4009116799632969396711460242)⟩⟩,⟨⟨2147060219993684176684192460,2147060219993684188887108228⟩,⟨(-3980072455622525506776931423),(-3980072455622525494571730856)⟩⟩,⟨⟨2078901900798073927234800168,2078901900798073939308144228⟩,⟨(-3951377996912126974959392060),(-3951377996912126962883829160)⟩⟩,⟨⟨2013649292572950220845332835,2013649292572950232784042785⟩,⟨(-3923086194554916388040928639),(-3923086194554916376100064687)⟩⟩,⟨⟨1951216950589529640534121418,1951216950589529652352150155⟩,⟨(-3895246206248291519480605077),(-3895246206248291507660483080)⟩⟩]
noncomputable def trans8_r5_14 : Fin 16 → CBox := ![⟨⟨1891522117016609046424360820,1891522117016609058109651881⟩,⟨(-3867903774394906128238929527),(-3867903774394906116551605945)⟩⟩,⟨⟨1834484735132381225334963559,1834484735132381236908287705⟩,⟨(-3841101416644618371348847498),(-3841101416644618359773546574)⟩⟩,⟨⟨1780027458283686760592514506,1780027458283686772048950836⟩,⟨(-3814878608956756082592603769),(-3814878608956756071134245369)⟩⟩,⟨⟨1728075654097715030250713683,1728075654097715041603595624⟩,⟨(-3789271961239493190709765464),(-3789271961239493179355012467)⟩⟩,⟨⟨1678557404428051045609927998,1678557404428051056849326961⟩,⟨(-3764315385638541979718916682),(-3764315385638541968477697399)⟩⟩,⟨⟨1631403501494067325828007548,1631403501494067336972086266⟩,⟨(-3740040257560856556148268212),(-3740040257560856545002415662)⟩⟩,⟨⟨1586547440650059204011403297,1586547440650059215055368644⟩,⟨(-3716475569530708963707438117),(-3716475569530708952661744467)⟩⟩,⟨⟨1543925410198286083217942591,1543925410198286094174568567⟩,⟨(-3693648077985435802920892297),(-3693648077985435791962580206)⟩⟩,⟨⟨1503476278638269067350762831,1503476278638269078208688865⟩,⟨(-3671582443126454103358249649),(-3671582443126454092498679649)⟩⟩,⟨⟨1465141579723357071137659526,1465141579723357081916078080⟩,⟨(-3650301361947903427244470564),(-3650301361947903416464446107)⟩⟩,⟨⟨1428865495674750576541329686,1428865495674750587235579331⟩,⟨(-3629825694570577939541116629),(-3629825694570577928845298259)⟩⟩,⟨⟨1394594838882898364610602835,1394594838882898375232942431⟩,⟨(-3610174584012756611077442309),(-3610174584012756600453568127)⟩⟩,⟨⟨1362279032406484119400330161,1362279032406484129941024338⟩,⟨(-3591365569532208636332010637),(-3591365569532208625789815805)⟩⟩,⟨⟨1331870089560116145054678693,1331870089560116155530920649⟩,⟨(-3573414693675128769072743549),(-3573414693675128758595031307)⟩⟩,⟨⟨1303322592863337466095964607,1303322592863337476503221134⟩,⟨(-3556336603168125037829875076),(-3556336603168125027421177812)⟩⟩,⟨⟨1276593672605692188070372198,1276593672605692198420444117⟩,⟨(-3540144643788717687732604220),(-3540144643788717677381118323)⟩⟩]
noncomputable def trans8_r5_15 : Fin 16 → CBox := ![⟨⟨1251642985265318507705700580,1251642985265318517986941029⟩,⟨(-3524850949348188633858962689),(-3524850949348188623576335082)⟩⟩,⟨⟨1228432692001885358449235720,1228432692001885368680449827⟩,⟨(-3510466524918117504541792234),(-3510466524918117494309214243)⟩⟩,⟨⟨1206927437428639806174003119,1206927437428639816350799390⟩,⟨(-3497001324428622632068776670),(-3497001324428622621890639019)⟩⟩,⟨⟨1187094328852873071689415542,1187094328852873081823176159⟩,⟨(-3484464322762259077656467594),(-3484464322762259067521385520)⟩⟩,⟨⟨1168902916159227584037620951,1168902916159227594118732469⟩,⟨(-3472863582462773778920202201),(-3472863582462773768837788998)⟩⟩,⟨⟨1152325172495935273983069098,1152325172495935284028038530⟩,⟨(-3462206315172539922692789276),(-3462206315172539912646534824)⟩⟩,⟨⟨1137335475910274634490492552,1137335475910274644495072338⟩,⟨(-3452498937906545412544013018),(-3452498937906545402538164145)⟩⟩,⟨⟨1123910592066234170528417334,1123910592066234180503625307⟩,⟨(-3443747124264347666892974674),(-3443747124264347656916511122)⟩⟩,⟨⟨1112029658164543336680249157,1112029658164543346615548634⟩,⟨(-3435955850674480030379310800),(-3435955850674480020442769141)⟩⟩,⟨⟨1101674168172847131782159123,1101674168172847141696045613⟩,⟨(-3429129437758452272821536272),(-3429129437758452262906417712)⟩⟩,⟨⟨1092827959461823279857184967,1092827959461823289745388443⟩,⟨(-3423271586893774994343660553),(-3423271586893774984454234450)⟩⟩,⟨⟨1085477200931435593791676468,1085477200931435603664703950⟩,⟨(-3418385412047398987304915774),(-3418385412047398977430672837)⟩⟩,⟨⟨1079610382700246271593348761,1079610382700246281441460248⟩,⟨(-3414473466942637375162766469),(-3414473466942637365313446634)⟩⟩,⟨⟨1075218307419734668261641155,1075218307419734678100764363⟩,⟨(-3411537767614070429073580110),(-3411537767614070419233252826)⟩⟩,⟨⟨1072294083264850459332379563,1072294083264850469158423993⟩,⟨(-3409579810396158461108755168),(-3409579810396158451281510271)⟩⟩,⟨⟨1070833118641523981186641155,1070833118641523991009833607⟩,⟨(-3408600585382343775208381405),(-3408600585382343765383989891)⟩⟩]
noncomputable def trans8_r5 : Fin 16 → Fin 16 → CBox := ![trans8_r5_0,trans8_r5_1,trans8_r5_2,trans8_r5_3,trans8_r5_4,trans8_r5_5,trans8_r5_6,trans8_r5_7,trans8_r5_8,trans8_r5_9,trans8_r5_10,trans8_r5_11,trans8_r5_12,trans8_r5_13,trans8_r5_14,trans8_r5_15]
end SharpPlanar.CachedData

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
noncomputable def lentry0_0 : RBox := ⟨386164739228853845759773052,386164739228853847338729471⟩
noncomputable def lentry6_0 : RBox := ⟨(-428037821451401034679013730),(-428037821451401027790023895)⟩
noncomputable def lentry1_0 : RBox := ⟨49064967585188068869174563,49064967585188069987341210⟩
noncomputable def lentry7_0 : RBox := ⟨(-596386320756599937937491488),(-596386320756599933047674875)⟩
noncomputable def lentry2_0 : RBox := ⟨349955633020704232195660108,349955633020704238293079170⟩
noncomputable def lentry8_0 : RBox := ⟨1156450605893201085971615858,1156450605893201123879614487⟩
noncomputable def lentry3_0 : RBox := ⟨(-497900663495165887403278912),(-497900663495165876692203228)⟩
noncomputable def lentry9_0 : RBox := ⟨726695844980284058022282278,726695844980284110485485687⟩
noncomputable def lentry4_0 : RBox := ⟨(-129722376498730229479424854),(-129722376498730219846221208)⟩
noncomputable def lentry10_0 : RBox := ⟨735342424357373673845647416,735342424357373720939652077⟩
noncomputable def lentry5_0 : RBox := ⟨5192157766382216813328101,5192157766382221815251673⟩
noncomputable def lentry11_0 : RBox := ⟨(-373604188084837902044523338),(-373604188084837871188935056)⟩
noncomputable def lentry0_3 : RBox := ⟨1237841529233122015925964342,1237841529233122021272149662⟩
noncomputable def lentry6_3 : RBox := ⟨(-10884852847347014469371491535),(-10884852847347014445864444233)⟩
noncomputable def lentry1_3 : RBox := ⟨(-945531822378341432500259730),(-945531822378341427352180742)⟩
noncomputable def lentry7_3 : RBox := ⟨(-4465708184822282113792278974),(-4465708184822282091488397712)⟩
noncomputable def lentry2_3 : RBox := ⟨4605024524144134428523673830,4605024524144134467976903087⟩
noncomputable def lentry8_3 : RBox := ⟨9348829383490770441808543,9348829383491012494286692⟩
noncomputable def lentry3_3 : RBox := ⟨(-4308649990873823136416589661),(-4308649990873823060803451595)⟩
noncomputable def lentry9_3 : RBox := ⟨26226240502596733865099430434,26226240502596734231105827117⟩
noncomputable def lentry4_3 : RBox := ⟨1369022879160941407076210245,1369022879160941487324115228⟩
noncomputable def lentry10_3 : RBox := ⟨15723242855704063078702190943,15723242855704063465727922119⟩
noncomputable def lentry5_3 : RBox := ⟨(-1289552013974452050024155783),(-1289552013974452005347604255)⟩
noncomputable def lentry11_3 : RBox := ⟨(-1539994406308444939497564809),(-1539994406308444667344235719)⟩
noncomputable def lentry0_1 : RBox := ⟨486118439120750072856567422,486118439120750074559192952⟩
noncomputable def lentry6_1 : RBox := ⟨257993788917541150498000107,257993788917541157888863267⟩
noncomputable def lentry1_1 : RBox := ⟨119087850140090609779608152,119087850140090611010500019⟩
noncomputable def lentry7_1 : RBox := ⟨(-663777977784782234746612750),(-663777977784782229394005574)⟩
noncomputable def lentry2_1 : RBox := ⟨358967247032856833332163871,358967247032856840141352766⟩
noncomputable def lentry8_1 : RBox := ⟨1619108661149769913016706898,1619108661149769955303200794⟩
noncomputable def lentry3_1 : RBox := ⟨(-579591941864548585450896356),(-579591941864548573447403574)⟩
noncomputable def lentry9_1 : RBox := ⟨377184322890016097180070227,377184322890016155875518461⟩
noncomputable def lentry4_1 : RBox := ⟨(-195228355766339276704702654),(-195228355766339265841016551)⟩
noncomputable def lentry10_1 : RBox := ⟨710843065811023928625760408,710843065811023981701947655⟩
noncomputable def lentry5_1 : RBox := ⟨25977920002013968828483999,25977920002013974478303761⟩
noncomputable def lentry11_1 : RBox := ⟨(-467966495451986099247977206),(-467966495451986064390183177)⟩
noncomputable def lentry0_4 : RBox := ⟨2125600111687210926303952134,2125600111687210932405875170⟩
noncomputable def lentry6_4 : RBox := ⟨(-11139267443296261033356468182),(-11139267443296261006716194412)⟩
noncomputable def lentry1_4 : RBox := ⟨(-780891265784406832000933468),(-780891265784406826200208949)⟩
noncomputable def lentry7_4 : RBox := ⟨(-5743618610332307669422004880),(-5743618610332307644322228913)⟩
noncomputable def lentry2_4 : RBox := ⟨5321012643203737848682181032,5321012643203737892803135677⟩
noncomputable def lentry8_4 : RBox := ⟨2776571492109706045337114003,2776571492109706316069623773⟩
noncomputable def lentry3_4 : RBox := ⟨(-5389978260281014816719222713),(-5389978260281014732262209926)⟩
noncomputable def lentry9_4 : RBox := ⟨27368681932658456888679605519,27368681932658457297208750387⟩
noncomputable def lentry4_4 : RBox := ⟨1046331030113728873277846982,1046331030113728962453513129⟩
noncomputable def lentry10_4 : RBox := ⟨17181475429765936689474771825,17181475429765937119960748674⟩
noncomputable def lentry5_4 : RBox := ⟨(-1259566801050796385474280065),(-1259566801050796335904409976)⟩
noncomputable def lentry11_4 : RBox := ⟨(-2380512632259958830256652294),(-2380512632259958528106206527)⟩
noncomputable def lentry0_2 : RBox := ⟨485328626881395931714985849,485328626881395932971229801⟩
noncomputable def lentry6_2 : RBox := ⟨767399171832372983257164636,767399171832372988906161653⟩
noncomputable def lentry1_2 : RBox := ⟨159432915114858452138511907,159432915114858453113123532⟩
noncomputable def lentry7_2 : RBox := ⟨(-644392944651544272181557039),(-644392944651544267855959278)⟩
noncomputable def lentry2_2 : RBox := ⟨344129241302690651571586296,344129241302690657533194559⟩
noncomputable def lentry8_2 : RBox := ⟨1856497232206901564546533917,1856497232206901601841142359⟩
noncomputable def lentry3_2 : RBox := ⟨(-607660233060482493251090964),(-607660233060482482498102625)⟩
noncomputable def lentry9_2 : RBox := ⟨109451628144957371825678763,109451628144957424719076512⟩
noncomputable def lentry4_2 : RBox := ⟨(-232443036487199701392321254),(-232443036487199691183528398)⟩
noncomputable def lentry10_2 : RBox := ⟨667100822413377830267050569,667100822413377880297221997⟩
noncomputable def lentry5_2 : RBox := ⟨39065964993206543259829543,39065964993206548649635729⟩
noncomputable def lentry11_2 : RBox := ⟨(-515958726858467410477971212),(-515958726858467377164471438)⟩
noncomputable def lentry0_5 : RBox := ⟨2615176994895548135832210442,2615176994895548142063566693⟩
noncomputable def lentry6_5 : RBox := ⟨(-10633079943167156175729829310),(-10633079943167156148566371119)⟩
noncomputable def lentry1_5 : RBox := ⟨(-641704209447256286883620943),(-641704209447256281007240349)⟩
noncomputable def lentry7_5 : RBox := ⟨(-6401538002129311513332102913),(-6401538002129311487912931512)⟩
noncomputable def lentry2_5 : RBox := ⟨5673870684468758906815253281,5673870684468758951656584385⟩
noncomputable def lentry8_5 : RBox := ⟨4515061100882060574473274188,4515061100882060849421864762⟩
noncomputable def lentry3_5 : RBox := ⟨(-5984619825577872881362402157),(-5984619825577872795340231432)⟩
noncomputable def lentry9_5 : RBox := ⟨27617495594282279521247988788,27617495594282279936739730868⟩
noncomputable def lentry4_5 : RBox := ⟨832688775810658666830659423,832688775810658757889595712⟩
noncomputable def lentry10_5 : RBox := ⟨17872500092793652677529018879,17872500092793653116898410653⟩
noncomputable def lentry5_5 : RBox := ⟨(-1227193748716980633078098857),(-1227193748716980582381799584)⟩
noncomputable def lentry11_5 : RBox := ⟨(-2872552850724879556441069579),(-2872552850724879247571465752)⟩
noncomputable def lEntries : Matrix (Fin 12) (Fin 6) RBox := ![![lentry0_0,lentry0_1,lentry0_2,lentry0_3,lentry0_4,lentry0_5],
![lentry1_0,lentry1_1,lentry1_2,lentry1_3,lentry1_4,lentry1_5],
![lentry2_0,lentry2_1,lentry2_2,lentry2_3,lentry2_4,lentry2_5],
![lentry3_0,lentry3_1,lentry3_2,lentry3_3,lentry3_4,lentry3_5],
![lentry4_0,lentry4_1,lentry4_2,lentry4_3,lentry4_4,lentry4_5],
![lentry5_0,lentry5_1,lentry5_2,lentry5_3,lentry5_4,lentry5_5],
![lentry6_0,lentry6_1,lentry6_2,lentry6_3,lentry6_4,lentry6_5],
![lentry7_0,lentry7_1,lentry7_2,lentry7_3,lentry7_4,lentry7_5],
![lentry8_0,lentry8_1,lentry8_2,lentry8_3,lentry8_4,lentry8_5],
![lentry9_0,lentry9_1,lentry9_2,lentry9_3,lentry9_4,lentry9_5],
![lentry10_0,lentry10_1,lentry10_2,lentry10_3,lentry10_4,lentry10_5],
![lentry11_0,lentry11_1,lentry11_2,lentry11_3,lentry11_4,lentry11_5]]
end SharpPlanar.Numerical

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
noncomputable def entry5_1 : RBox := ⟨(-132961498390156263788907228999),(-132961498390156262791306714514)⟩
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
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
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
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
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
end SharpPlanar.Numerical.U99

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

noncomputable def certifiedEquiv (A W : E →L[ℝ] E) (h : ‖1-W*A‖ < 1) : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective A.toLinearMap (approximate_inverse_bijective_e A W h)).toContinuousLinearEquiv
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
noncomputable def inversePlusEquiv : L1Finite (Fin 6) ≃L[ℝ] L1Finite (Fin 6) :=
  (certifiedEquiv (matrixL1 Aplus) (matrixL1 Wplus) defectplus_lt_one_e).symm
noncomputable def inverseMinusEquiv : L1Finite (Fin 6) ≃L[ℝ] L1Finite (Fin 6) :=
  (certifiedEquiv (matrixL1 Aminus) (matrixL1 Wminus) defectminus_lt_one_e).symm
end SharpPlanar.Numerical

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
noncomputable def l1Left (x : L1Finite (ι ⊕ κ)) : L1Finite ι :=
  WithLp.toLp 1 (fun i => x (Sum.inl i))
noncomputable def l1Right (x : L1Finite (ι ⊕ κ)) : L1Finite κ :=
  WithLp.toLp 1 (fun i => x (Sum.inr i))
end
end SharpPlanar

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
noncomputable def tailScalar (x : X) (N : ℕ) : ℝ :=
  ∑' k : Node × Bool, if N<k.1.val then |x k| else 0
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exterior coupling in the finite interpolation system

Column estimates control the coupling between the central and exterior coordinates.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable def Umat : Matrix (Fin 6) (Fin 48 × Fin 2) ℝ := fun i j => S (columnVector (eNode j.1) (decide (j.2.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical

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
noncomputable def centralV (neg : Bool) : L1Finite (Fin 6) →L[ℝ] L1Finite (Fin 6) :=
  if neg then inverseMinusEquiv.toContinuousLinearMap else inversePlusEquiv.toContinuousLinearMap
end SharpPlanar.Numerical

end OAI
end


