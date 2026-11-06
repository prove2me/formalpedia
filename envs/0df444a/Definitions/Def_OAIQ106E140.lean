-- Prove2me | Definitions.Def_OAIQ106E140
-- name    : OAIQ106E140
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T02:46:43.332491+00:00
-- url     : https://prove2.me/theorems/986d0b3a-9732-4fef-b325-4fc3f4950a7d
-- title:
--   Definitions bundle OAIQ106E140 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1428 declarations of OpenAI's Lean: 1426 definitions, 1 inductive type or structure and 1 theorem. The definitions and types are `OAI.MUB6.Certificate.PairData.pairMerged211`, `OAI.MUB6.Certificate.PairData.pairMerged212`, `OAI.MUB6.Certificate.PairData.pairMerged213`, `OAI.MUB6.Certificate.PairData.pairMerged214`, `OAI.MUB6.Certificate.PairData.pairMerged215`, `OAI.MUB6.Certificate.PairData.pairMerged216`, `OAI.MUB6.Certificate.PairData.pairMerged217`, `OAI.MUB6.Certificate.PairData.pairMerged218`, `OAI.MUB6.Certificate.PairData.pairMerged219`, `OAI.MUB6.Certificate.PairData.pairMerged220`, `OAI.MUB6.Certificate.PairData.pairMerged221`, `OAI.MUB6.Certificate.PairData.pairMerged222`, `OAI.MUB6.Certificate.PairData.pairMerged223`, `OAI.MUB6.Certificate.PairData.pairMerged224`, `OAI.MUB6.Certificate.PairData.pairMerged225`, `OAI.MUB6.Certificate.PairData.pairMerged226`, `OAI.MUB6.Certificate.PairData.pairMerged227`, `OAI.MUB6.Certificate.PairData.pairMerged228`, `OAI.MUB6.Certificate.PairData.pairMerged229`, `OAI.MUB6.Certificate.PairData.pairMerged23`, `OAI.MUB6.Certificate.PairData.pairMerged230`, `OAI.MUB6.Certificate.PairData.pairMerged231`, `OAI.MUB6.Certificate.PairData.pairMerged232`, `OAI.MUB6.Certificate.PairData.pairMerged233`, `OAI.MUB6.Certificate.PairData.pairMerged234`, `OAI.MUB6.Certificate.PairData.pairMerged235`, `OAI.MUB6.Certificate.PairData.pairMerged236`, `OAI.MUB6.Certificate.PairData.pairMerged237`, `OAI.MUB6.Certificate.PairData.pairMerged238`, `OAI.MUB6.Certificate.PairData.pairMerged239`, `OAI.MUB6.Certificate.PairData.pairMerged24`, `OAI.MUB6.Certificate.PairData.pairMerged240`, `OAI.MUB6.Certificate.PairData.pairMerged241`, `OAI.MUB6.Certificate.PairData.pairMerged242`, `OAI.MUB6.Certificate.PairData.pairMerged243`, `OAI.MUB6.Certificate.PairData.pairMerged244`, `OAI.MUB6.Certificate.PairData.pairMerged245`, `OAI.MUB6.Certificate.PairData.pairMerged246`, `OAI.MUB6.Certificate.PairData.pairMerged247`, `OAI.MUB6.Certificate.PairData.pairMerged248` and 1387 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Fourier_Dichotomy`, `MutuallyUnbiased_Matrix_Hadamard`, `MutuallyUnbiased_Moments_Moments`, `MutuallyUnbiased_PairData_Data`, `MutuallyUnbiased_PairMerge_Block0`, `MutuallyUnbiased_PairMerge_Block1`, `MutuallyUnbiased_PairMerge_Block10`, `MutuallyUnbiased_PairMerge_Block11`, `MutuallyUnbiased_PairMerge_Block2`, `MutuallyUnbiased_PairMerge_Block3`, `MutuallyUnbiased_PairMerge_Block6`, `MutuallyUnbiased_PairMerge_Block7`, `MutuallyUnbiased_PairMerge_Block8`, `MutuallyUnbiased_PairMerge_Block9`, `MutuallyUnbiased_PairMoments_PairCharges`, `MutuallyUnbiased_PairPolynomial_Grid`, `MutuallyUnbiased_PairPolynomial_Terms`, `MutuallyUnbiased_PairSemantics_Boundary0`, `MutuallyUnbiased_PairSemantics_Boundary1`, `MutuallyUnbiased_PairSemantics_Boundary10`, `MutuallyUnbiased_PairSemantics_Boundary11`, `MutuallyUnbiased_PairSemantics_Boundary12`, `MutuallyUnbiased_PairSemantics_Boundary13`, `MutuallyUnbiased_PairSemantics_Boundary14`, `MutuallyUnbiased_PairSemantics_Boundary15`, `MutuallyUnbiased_PairSemantics_Boundary16`, `MutuallyUnbiased_PairSemantics_Boundary2`, `MutuallyUnbiased_PairSemantics_Boundary3`, `MutuallyUnbiased_PairSemantics_Boundary4`, `MutuallyUnbiased_PairSemantics_Boundary5`, `MutuallyUnbiased_PairSemantics_Boundary6`, `MutuallyUnbiased_PairSemantics_Boundary7`, `MutuallyUnbiased_PairSemantics_Boundary8`, `MutuallyUnbiased_PairSemantics_Boundary9`, `MutuallyUnbiased_PairTargets_Data`, `MutuallyUnbiased_PairTargets_IntegerTerms`, `MutuallyUnbiased_TaoCertificate_Merge0`, `MutuallyUnbiased_TaoCertificate_Merge1`, `MutuallyUnbiased_TaoCertificate_Merge12`, `MutuallyUnbiased_TaoCertificate_Merge13`, `MutuallyUnbiased_TaoCertificate_Merge14`, `MutuallyUnbiased_TaoCertificate_Merge15`, `MutuallyUnbiased_TaoCertificate_Merge16`, `MutuallyUnbiased_TaoCertificate_Merge17`, `MutuallyUnbiased_TaoCertificate_Merge18`, `MutuallyUnbiased_TaoCertificate_Merge19`, `MutuallyUnbiased_TaoCertificate_Merge2`, `MutuallyUnbiased_TaoCertificate_Merge20`, `MutuallyUnbiased_TaoCertificate_Merge21`, `MutuallyUnbiased_TaoCertificate_Merge22`, `MutuallyUnbiased_TaoCertificate_Merge23`, `MutuallyUnbiased_TaoCertificate_Merge24`, `MutuallyUnbiased_TaoCertificate_Merge25`, `MutuallyUnbiased_TaoCertificate_Merge26`, `MutuallyUnbiased_TaoCertificate_Merge27`, `MutuallyUnbiased_TaoCertificate_Merge28`, `MutuallyUnbiased_TaoCertificate_Merge29`, `MutuallyUnbiased_TaoCertificate_Merge3`, `MutuallyUnbiased_TaoCertificate_Merge30`, `MutuallyUnbiased_TaoCertificate_Merge31`, `MutuallyUnbiased_TaoCertificate_Merge32`, `MutuallyUnbiased_TaoCertificate_Merge33`, `MutuallyUnbiased_TaoCertificate_Merge34`, `MutuallyUnbiased_TaoCertificate_Merge35`, `MutuallyUnbiased_TaoCertificate_Merge36`, `MutuallyUnbiased_Tao_TaoSparse`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundle `OAIQ106E000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E154`, `OAIQ106E156`, `OAIQ106E157`, `OAIQ106E158`, `OAIQ106E159`, `OAIQ106E162`, `OAIQ106E164` and `OAIQ106E167`; the statements `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5167_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5168_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5169_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5292_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5386_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5388_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5416_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5417_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5433_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5434_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5435_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5476_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5482_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5483_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5485_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E000

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

def difference (i j : Coord) : Charge := Pi.single i 1 - Pi.single j 1

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite injective moments of Section 2 of the exact companion.
Both orientations are retained with weight 1/2, including when H = Hᵀ. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- Equation (pair-average), with the two orientations counted separately. -/
def pairAverage (H : CMatrix) (F : CMatrix → ℝ) : ℝ :=
  average (fun π : Equiv.Perm Coord =>
    (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

def qCross : Charge := ![2, 0, 0, -2, 0, 0]
def qSame : Charge := ![2, -2, 0, 0, 0, 0]
def pairW : Charge := ![-3, -2, 0, 1, 2, 2]
def pairA : Fin 4 → Charge :=
  ![![-1, -1, 0, 0, 1, 1], ![-2, 0, 0, 0, 1, 1],
    ![-1, -1, 0, 1, 0, 1], ![-1, -1, 0, 1, 1, 0]]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Dichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def PairProductsZero (H : CMatrix) : Prop :=
  ∀ π : Equiv.Perm Coord,
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) qCross = 0 ∧
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) qSame = 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairData_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Untrusted literal certificate data. The subsequent Check modules
check the linear identities. Hadamard interpretation is separate. -/
namespace MUB6.Certificate.PairData

-- Selected source equation 0 in the original pair table.
def row0 : Integer.Sparse (Fin 271) := [(0, 9), (1, 170), (2, -25), (3, -80), (4, -160), (12, -40)]

-- Selected source equation 1 in the original pair table.
def row1 : Integer.Sparse (Fin 271) := [(0, -1), (1, -4), (5, -8), (6, 1), (27, 12)]

-- Selected source equation 2 in the original pair table.
def row2 : Integer.Sparse (Fin 271) := [(0, -1), (1, 18), (2, -8), (3, -64), (4, -32), (5, 3), (7, -16), (8, -8), (12, -24), (23, 12), (24, 24)]

-- Selected source equation 3 in the original pair table.
def row3 : Integer.Sparse (Fin 271) := [(0, -9), (1, 205), (2, -110), (3, -160), (4, -160), (5, 30), (7, -40), (8, -200), (24, 120), (29, 240)]

-- Selected source equation 4 in the original pair table.
def row4 : Integer.Sparse (Fin 271) := [(0, -4), (1, 95), (2, -25), (3, -320), (4, -160), (12, -160), (13, -80)]

-- Selected source equation 5 in the original pair table.
def row5 : Integer.Sparse (Fin 271) := [(0, -11), (1, 250), (2, -45), (3, -800), (4, -480), (12, -320), (25, 120), (26, -160)]

-- Selected source equation 6 in the original pair table.
def row6 : Integer.Sparse (Fin 271) := [(0, -9), (1, 315), (2, -70), (3, -480), (4, -400), (12, -80), (26, -80), (30, 240)]

-- Selected source equation 7 in the original pair table.
def row7 : Integer.Sparse (Fin 271) := [(0, 1), (1, -8), (2, 4), (14, 18), (17, 72), (23, -48), (25, -96), (27, 9), (29, -24), (30, -96)]

-- Selected source equation 8 in the original pair table.
def row8 : Integer.Sparse (Fin 271) := [(0, 149), (1, -1760), (2, 285), (3, 2080), (4, 2880), (12, 800), (15, 720), (20, 1440), (23, -240), (24, -720), (25, -480), (27, 180), (29, -480), (30, -960)]

-- Selected source equation 9 in the original pair table.
def row9 : Integer.Sparse (Fin 271) := [(0, -11), (1, -150), (2, 80), (3, 640), (4, 320), (12, 240), (16, 180), (17, 360), (23, -240), (27, 45), (29, -120)]

-- Selected source equation 10 in the original pair table.
def row10 : Integer.Sparse (Fin 271) := [(0, 11), (1, -890), (2, 45), (3, 1120), (4, 1080), (12, 440), (18, 360), (22, 720)]

-- Selected source equation 11 in the original pair table.
def row11 : Integer.Sparse (Fin 271) := [(0, 12), (1, -121), (2, 33), (3, 320), (4, 224), (12, 192), (15, 144), (17, 72), (23, -72), (24, -48), (25, -144), (27, 18), (29, -24), (30, -144)]

-- Selected source equation 12 in the original pair table.
def row12 : Integer.Sparse (Fin 271) := [(0, 3), (1, -65), (2, 11), (3, 80), (4, 80), (12, 20), (17, 36), (19, 36), (20, 36), (22, 36), (24, -60), (27, 9), (29, -12), (30, -48)]

-- Selected source equation 13 in the original pair table.
def row13 : Integer.Sparse (Fin 271) := [(0, 93), (1, -1715), (2, 210), (3, 2880), (4, 2400), (12, 1520), (21, 720), (22, 720), (30, -480)]

-- Selected source equation 14 in the original pair table.
def row14 : Integer.Sparse (Fin 271) := [(0, 16), (1, -315), (2, 65), (3, 960), (4, 600), (12, 360), (18, 360), (25, -240), (30, -240)]

-- Selected source equation 16 in the original pair table.
def row15 : Integer.Sparse (Fin 271) := [(0, -69), (1, -470), (2, 110), (3, 160), (4, 160), (12, 160), (17, 180), (23, -60), (27, 45), (28, 360), (29, -300)]

-- Selected source equation 17 in the original pair table.
def row16 : Integer.Sparse (Fin 271) := [(0, -11), (1, 220), (2, -250), (3, -1200), (4, -240), (5, 260), (6, -15), (7, -480), (8, -480), (12, -480), (13, -320), (34, -160), (50, 720), (51, -240)]

-- Selected source equation 18 in the original pair table.
def row17 : Integer.Sparse (Fin 271) := [(0, -32), (1, 615), (2, -60), (3, -2160), (4, -960), (5, 60), (6, -15), (12, -240), (13, -160), (26, -960), (34, -240), (54, 720)]

-- Selected source equation 19 in the original pair table.
def row18 : Integer.Sparse (Fin 271) := [(0, -7), (1, 125), (2, -70), (3, -480), (4, -160), (5, 160), (6, -20), (7, -80), (8, -160), (26, -160), (34, -80), (51, -160)]

-- Selected source equation 20 in the original pair table.
def row19 : Integer.Sparse (Fin 271) := [(0, -2), (1, 55), (2, -11), (3, -304), (4, -64), (5, 52), (6, -8), (7, -16), (8, -32), (12, -64), (13, -208), (26, -64), (34, -80), (51, -64), (53, 48), (55, 96)]

-- Selected source equation 21 in the original pair table.
def row20 : Integer.Sparse (Fin 271) := [(0, -11), (1, 215), (2, -95), (3, -720), (4, -240), (5, 160), (6, -15), (7, -240), (8, -240), (26, -240), (34, -80)]

-- Selected source equation 22 in the original pair table.
def row21 : Integer.Sparse (Fin 271) := [(0, 1), (1, 5), (3, -400), (5, 10), (7, -160), (12, -240), (13, -240), (23, 360), (25, 360), (34, -80), (53, 240)]

-- Selected source equation 23 in the original pair table.
def row22 : Integer.Sparse (Fin 271) := [(0, -7), (1, 180), (2, -15), (3, -720), (12, -360), (13, -960), (31, -80)]

-- Selected source equation 24 in the original pair table.
def row23 : Integer.Sparse (Fin 271) := [(0, -7), (1, 145), (2, -30), (3, -680), (4, -240), (12, -120), (13, -160), (26, -280), (32, 120), (33, -80)]

-- Selected source equation 25 in the original pair table.
def row24 : Integer.Sparse (Fin 271) := [(0, -19), (1, 300), (2, -75), (3, -640), (4, -480), (12, -200), (25, 240), (26, -80), (30, 480), (32, 240)]

-- Selected source equation 26 in the original pair table.
def row25 : Integer.Sparse (Fin 271) := [(0, 157), (1, -2040), (2, 585), (3, 5280), (4, 3520), (12, 2240), (13, 560), (25, -1200), (30, -2880), (32, -960), (49, 720)]

-- Selected source equation 27 in the original pair table.
def row26 : Integer.Sparse (Fin 271) := [(0, 59), (1, -575), (2, 320), (3, 1040), (4, 480), (5, -80), (7, 80), (8, 320), (12, 480), (23, -240), (25, -240), (27, 180), (29, -480), (30, -480), (32, -480), (44, 1440), (50, -480), (53, -240)]

-- Selected source equation 28 in the original pair table.
def row27 : Integer.Sparse (Fin 271) := [(0, 29), (1, -334), (2, 99), (3, 896), (4, 512), (12, 352), (13, 32), (25, -96), (26, 112), (30, -336), (32, -192), (42, 144), (44, 288)]

-- Selected source equation 29 in the original pair table.
def row28 : Integer.Sparse (Fin 271) := [(0, 128), (1, -1575), (2, 405), (3, 4480), (4, 2960), (12, 1360), (25, -960), (26, 960), (30, -1680), (42, 720), (43, 720), (44, 720), (45, 720)]

-- Selected source equation 30 in the original pair table.
def row29 : Integer.Sparse (Fin 271) := [(0, 58), (1, -605), (2, 235), (3, 1280), (4, 920), (5, -30), (7, 40), (8, 80), (12, 560), (23, -240), (24, -720), (25, -600), (27, 300), (29, -480), (30, -1200), (32, -480), (47, 360), (48, 720), (50, -360), (54, -240)]

-- Selected source equation 31 in the original pair table.
def row30 : Integer.Sparse (Fin 271) := [(0, 141), (1, -1765), (2, 580), (3, 3600), (4, 2560), (5, -60), (7, 80), (8, 160), (12, 1440), (13, 320), (23, -480), (24, -1440), (27, 600), (29, -960), (30, -1920), (46, 720), (48, 1440), (50, -720), (54, -480)]

-- Selected source equation 32 in the original pair table.
def row31 : Integer.Sparse (Fin 271) := [(0, 109), (1, -1300), (2, 565), (3, 2880), (4, 1760), (5, -120), (7, 160), (8, 320), (12, 800), (23, -480), (24, -1440), (26, 400), (27, 600), (29, -960), (30, -1200), (42, 720), (54, -480)]

-- Selected source equation 33 in the original pair table.
def row32 : Integer.Sparse (Fin 271) := [(0, 56), (1, -675), (2, 305), (3, 1760), (4, 1120), (5, -80), (7, 160), (8, 240), (12, 440), (24, -480), (26, 160), (27, 180), (29, -240), (30, -720), (44, 360), (45, 360), (50, -480), (55, -240)]

-- Selected source equation 34 in the original pair table.
def row33 : Integer.Sparse (Fin 271) := [(0, 67), (1, -1010), (2, 185), (3, 3200), (4, 960), (5, -60), (7, 80), (8, 160), (12, 1040), (13, 1200), (25, -960), (26, 640), (30, -960), (32, -960), (37, 720), (38, 1440), (53, -720)]

-- Selected source equation 35 in the original pair table.
def row34 : Integer.Sparse (Fin 271) := [(0, 8), (1, -151), (2, 109), (3, 624), (4, 192), (5, -44), (7, 48), (8, 160), (12, 96), (23, -48), (25, -96), (26, 128), (27, 36), (29, -96), (30, -192), (32, -384), (35, 144), (38, 288), (39, 288), (50, -192), (53, -240), (54, -144)]

-- Selected source equation 36 in the original pair table.
def row35 : Integer.Sparse (Fin 271) := [(0, 19), (1, -288), (2, 91), (3, 928), (4, 512), (5, -12), (7, 16), (8, 32), (12, 48), (13, 32), (26, 368), (36, 144), (39, 288), (55, -144), (56, 288)]

-- Selected source equation 37 in the original pair table.
def row36 : Integer.Sparse (Fin 271) := [(0, 37), (1, -580), (2, 255), (3, 1920), (4, 320), (5, -80), (7, 80), (8, 320), (12, 720), (13, 880), (23, -120), (26, 160), (27, 90), (29, -240), (37, 360), (39, 720), (50, -480), (53, -240), (54, -360)]

-- Selected source equation 38 in the original pair table.
def row37 : Integer.Sparse (Fin 271) := [(0, 16), (1, -255), (2, 93), (3, 896), (4, 304), (12, 384), (13, 448), (26, 112), (30, -192), (32, -192), (40, 144), (41, 288)]

-- Selected source equation 39 in the original pair table.
def row38 : Integer.Sparse (Fin 271) := [(0, 17), (1, -309), (2, 76), (3, 1008), (4, 480), (26, 528), (52, 144), (56, 144)]

-- Selected source equation 40 in the original pair table.
def row39 : Integer.Sparse (Fin 271) := [(0, 9), (1, -179), (2, 82), (3, 720), (4, 288), (5, -32), (7, 64), (8, 96), (12, 160), (13, 128), (24, -96), (26, 176), (27, 36), (29, -48), (30, -96), (32, -192), (36, 144), (38, 144), (39, 144), (41, 144), (50, -192), (54, -144), (55, -96)]

-- Selected source equation 41 in the original pair table.
def row40 : Integer.Sparse (Fin 271) := [(0, 1), (1, -145), (2, 70), (3, 1200), (4, 400), (5, -10), (7, 80), (12, 720), (14, 360), (15, 1440), (23, -840), (24, -480), (25, -840), (27, 120), (32, -480), (35, 720), (47, 720), (50, -240), (53, -240), (54, -240)]

-- Selected source equation 42 in the original pair table.
def row41 : Integer.Sparse (Fin 271) := [(0, 83), (1, -1010), (2, 145), (3, 5280), (4, 1920), (12, 1760), (13, 720), (15, 1440), (16, 720), (18, 2880), (23, -480), (24, -480), (25, -720), (27, 60), (37, 1440), (49, 720), (54, -480)]

-- Selected source equation 43 in the original pair table.
def row42 : Integer.Sparse (Fin 271) := [(0, 88), (1, -1245), (2, 255), (3, 4080), (4, 1760), (5, -20), (7, 80), (8, 80), (12, 880), (15, 720), (18, 720), (19, 1440), (21, 1440), (23, -240), (24, -1440), (25, -240), (26, 480), (27, 180), (30, -960), (36, 1440), (46, 720), (47, 720), (50, -480), (55, -480)]

-- Selected source equation 44 in the original pair table.
def row43 : Integer.Sparse (Fin 271) := [(0, 79), (1, -810), (2, 195), (3, 1040), (4, 1320), (5, -20), (7, 80), (8, 120), (12, 160), (17, 360), (20, 720), (23, -120), (24, -600), (25, -360), (26, 80), (27, 90), (29, -360), (30, -720), (43, 720), (44, 720), (47, 360), (50, -120)]

-- Selected source equation 45 in the original pair table.
def row44 : Integer.Sparse (Fin 271) := [(0, 1), (1, -25), (2, -25), (9, -100), (57, 5)]

-- Selected source equation 46 in the original pair table.
def row45 : Integer.Sparse (Fin 271) := [(0, 1), (1, -24), (2, 36), (5, -120), (6, 15), (9, -16), (27, 180), (66, 240)]

-- Selected source equation 47 in the original pair table.
def row46 : Integer.Sparse (Fin 271) := [(0, 1), (1, -25), (2, -150), (3, -240), (5, 320), (6, -30), (7, -480), (8, -480), (9, 40), (34, -160), (67, -240), (68, -80), (69, -480)]

-- Selected source equation 48 in the original pair table.
def row47 : Integer.Sparse (Fin 271) := [(0, -1), (1, 55), (2, -10), (3, -480), (5, -20), (7, -480), (9, 20), (12, -320), (13, -160), (23, 720), (34, -320), (67, -320), (68, -160), (111, 720), (112, 480)]

-- Selected source equation 49 in the original pair table.
def row48 : Integer.Sparse (Fin 271) := [(0, -9), (1, 135), (2, -160), (3, -1280), (4, -480), (5, 260), (6, -30), (7, -720), (8, -240), (9, 20), (24, 720), (26, -480), (34, -640), (51, -480), (67, -240), (68, -160), (69, -80), (113, 720), (131, 480)]

-- Selected source equation 50 in the original pair table.
def row49 : Integer.Sparse (Fin 271) := [(0, 3), (1, 105), (2, -90), (3, -1440), (5, 210), (6, -30), (7, -480), (9, 10), (12, -600), (13, -1240), (23, 360), (34, -720), (51, -480), (53, 720), (67, -120), (68, -120), (112, 360), (130, 240)]

-- Selected source equation 51 in the original pair table.
def row50 : Integer.Sparse (Fin 271) := [(0, -4), (1, 45), (2, -230), (3, -640), (4, -160), (5, 280), (6, -15), (7, -480), (8, -480), (9, 20), (24, 480), (27, -60), (50, 480), (51, -160), (67, -160), (69, -320), (111, 240), (113, 960)]

-- Selected source equation 52 in the original pair table.
def row51 : Integer.Sparse (Fin 271) := [(0, -14), (1, 65), (2, -250), (3, -320), (5, 440), (6, -45), (7, -160), (8, -800), (9, 20), (27, -60), (29, 480), (51, -160), (67, -80), (69, -400), (113, 240), (146, 960)]

-- Selected source equation 53 in the original pair table.
def row52 : Integer.Sparse (Fin 271) := [(0, -2), (1, 95), (2, -60), (3, -880), (4, -320), (5, 460), (6, -65), (7, -160), (8, -480), (9, 20), (13, -400), (24, 480), (26, -320), (34, -400), (51, -320), (54, 240), (55, 960), (67, -80), (68, -80), (69, -320), (112, 240), (131, 960)]

-- Selected source equation 54 in the original pair table.
def row53 : Integer.Sparse (Fin 271) := [(0, -1), (1, 35), (2, -140), (3, -480), (5, 265), (6, -15), (7, -600), (8, -480), (10, 180), (12, -120), (13, -160), (34, -320), (80, -60)]

-- Selected source equation 55 in the original pair table.
def row54 : Integer.Sparse (Fin 271) := [(0, -1), (1, 10), (2, -205), (3, -1200), (4, -240), (5, 680), (6, -90), (7, -480), (8, -480), (11, -240), (26, -480), (34, -1120), (51, -1200), (143, 720)]

-- Selected source equation 56 in the original pair table.
def row55 : Integer.Sparse (Fin 271) := [(0, 1), (1, -30), (2, -50), (3, -160), (5, 90), (6, -15), (7, -40), (8, -80), (12, -20), (13, -160), (34, -160), (51, -320), (80, -120), (115, -160), (132, 60), (133, 240)]

-- Selected source equation 57 in the original pair table.
def row56 : Integer.Sparse (Fin 271) := [(0, -1), (1, -10), (2, -5), (3, -480), (5, 10), (7, -240), (10, 360), (12, -240), (13, -640), (34, -320), (80, -120), (114, 360), (115, -120)]

-- Selected source equation 58 in the original pair table.
def row57 : Integer.Sparse (Fin 271) := [(0, -9), (1, 525), (2, 90), (3, -3360), (4, -1200), (5, 140), (6, -30), (7, -240), (11, -240), (12, -960), (13, -1680), (25, 720), (26, -1440), (34, -1520), (51, -240), (53, 2160), (55, 1440), (142, 480), (143, 720)]

-- Selected source equation 59 in the original pair table.
def row58 : Integer.Sparse (Fin 271) := [(0, -19), (1, 270), (2, -105), (3, -1360), (4, -560), (5, 240), (6, -40), (11, -80), (26, -640), (27, -120), (30, 480), (34, -480), (51, -400), (54, 480), (143, 240), (147, 480), (148, 480)]

-- Selected source equation 60 in the original pair table.
def row59 : Integer.Sparse (Fin 271) := [(1, 35), (2, -13), (3, -400), (4, -64), (5, 44), (6, -8), (7, -48), (12, -144), (13, -368), (26, -64), (34, -208), (51, -128), (53, 144), (55, 96), (80, -64), (115, -64), (132, 48), (133, 96)]

-- Selected source equation 64 in the original pair table.
def row60 : Integer.Sparse (Fin 271) := [(0, 7), (1, -140), (2, -465), (3, -1680), (5, 1240), (6, -160), (7, -960), (8, -960), (12, -240), (13, -1120), (34, -1520), (51, -1920), (58, 720), (59, -320), (115, -240)]

-- Selected source equation 65 in the original pair table.
def row61 : Integer.Sparse (Fin 271) := [(0, 1), (1, -5), (2, -120), (3, -480), (4, -80), (5, 240), (6, -20), (7, -480), (8, -320), (26, -160), (34, -400), (51, -160), (65, -80), (79, 240)]

-- Selected source equation 66 in the original pair table.
def row62 : Integer.Sparse (Fin 271) := [(0, 12), (1, 50), (2, -15), (3, -1760), (5, 20), (6, -5), (12, -720), (13, -2000), (26, -560), (31, -160), (32, 720), (33, -480), (34, -240), (54, 720), (59, -160), (60, 480)]

-- Selected source equation 67 in the original pair table.
def row63 : Integer.Sparse (Fin 271) := [(0, 2), (1, 6), (2, -5), (3, -256), (5, 8), (6, -1), (12, -96), (13, -224), (25, 48), (26, -64), (32, 192), (33, -32), (34, -32), (51, -32), (54, 96), (62, 48), (63, 96)]

-- Selected source equation 68 in the original pair table.
def row64 : Integer.Sparse (Fin 271) := [(0, 8), (1, 40), (2, -15), (3, -1120), (5, 60), (6, -15), (7, -160), (12, -320), (13, -800), (23, 240), (26, -480), (32, 480), (33, -320), (34, -480), (53, 480), (54, 480), (62, 240), (64, 480), (65, -160)]

-- Selected source equation 70 in the original pair table.
def row65 : Integer.Sparse (Fin 271) := [(0, 9), (1, -5), (2, -65), (3, -1440), (5, 60), (6, -5), (12, -720), (13, -2640), (26, -240), (31, -320), (33, -480), (34, -240), (51, -480), (58, 720), (59, -400), (60, 720), (115, -240)]

-- Selected source equation 71 in the original pair table.
def row66 : Integer.Sparse (Fin 271) := [(0, 1), (2, -7), (3, -144), (5, 14), (6, -2), (7, -24), (12, -48), (13, -160), (26, -24), (31, -16), (32, 72), (34, -72), (51, -48), (53, 72), (59, -16), (61, 48)]

-- Selected source equation 72 in the original pair table.
def row67 : Integer.Sparse (Fin 271) := [(0, -16), (1, 485), (2, -240), (3, -3440), (4, -1280), (5, 120), (6, -5), (7, -480), (8, -160), (12, -320), (13, -320), (25, 240), (26, -1600), (30, 480), (32, 960), (33, -400), (34, -560), (50, 480), (51, -240), (63, 240), (65, -160), (79, 480), (110, 480)]

-- Selected source equation 73 in the original pair table.
def row68 : Integer.Sparse (Fin 271) := [(1, 42), (2, -35), (3, -448), (4, -64), (5, 44), (6, -5), (7, -112), (8, -32), (12, -128), (13, -272), (26, -160), (33, -80), (34, -160), (50, 96), (51, -112), (53, 48), (63, 48), (65, -32)]

-- Selected source equation 77 in the original pair table.
def row69 : Integer.Sparse (Fin 271) := [(0, 5), (1, -73), (2, 44), (3, 160), (4, 64), (5, -15), (7, 20), (8, 40), (10, -36), (12, 56), (13, 32), (23, -120), (24, -336), (27, 123), (29, -192), (54, -192), (77, 36), (78, 72)]

-- Selected source equation 78 in the original pair table.
def row70 : Integer.Sparse (Fin 271) := [(0, 17), (1, -570), (2, 730), (3, 3040), (4, 1040), (5, -620), (6, 15), (7, 1120), (8, 1760), (12, 400), (23, -480), (24, -1440), (26, 480), (27, 600), (29, -960), (34, 160), (50, -3600), (53, -960), (54, -480), (55, -1920), (75, 720), (76, 1440), (143, -720)]

-- Selected source equation 79 in the original pair table.
def row71 : Integer.Sparse (Fin 271) := [(0, -3), (1, 20), (2, 240), (3, 560), (5, -350), (6, 20), (7, 600), (8, 520), (10, -180), (12, 180), (13, 240), (23, -60), (27, 45), (29, -120), (34, 240), (50, -480), (51, 160), (53, -240), (58, -480), (70, 180), (72, 360), (73, 360), (132, -180)]

-- Selected source equation 80 in the original pair table.
def row72 : Integer.Sparse (Fin 271) := [(0, -14), (1, 260), (2, 1255), (3, 3120), (4, 400), (5, -2280), (6, 205), (7, 3040), (8, 2720), (26, 480), (34, 2240), (51, 2320), (79, -960), (82, 720), (83, 1440), (84, 1440), (143, -720)]

-- Selected source equation 81 in the original pair table.
def row73 : Integer.Sparse (Fin 271) := [(0, -17), (1, 80), (2, 990), (3, 2880), (4, 320), (5, -1580), (6, 95), (7, 2800), (8, 2640), (10, -720), (12, 400), (13, 640), (24, -480), (27, 180), (29, -240), (34, 1440), (50, -1920), (51, 640), (55, -960), (58, -1920), (71, 720), (72, 720), (73, 720), (74, 1440), (133, -720)]

-- Selected source equation 82 in the original pair table.
def row74 : Integer.Sparse (Fin 271) := [(0, -17), (1, 280), (2, 1440), (3, 3840), (5, -2160), (6, 185), (7, 2480), (8, 2400), (12, 480), (13, 640), (34, 2400), (51, 3200), (71, 720), (73, 1440), (79, -960), (84, 2880), (133, -720)]

-- Selected source equation 83 in the original pair table.
def row75 : Integer.Sparse (Fin 271) := [(0, -3), (1, 10), (2, 950), (3, 3360), (4, 720), (5, -1240), (6, 95), (7, 1520), (8, 1600), (26, 960), (34, 960), (51, 1280), (79, -1920), (81, 720), (83, 2880), (84, 1440), (143, -1440)]

-- Selected source equation 84 in the original pair table.
def row76 : Integer.Sparse (Fin 271) := [(0, 13), (1, -580), (2, 285), (3, 4800), (4, 800), (5, -100), (7, 560), (8, 160), (10, -240), (12, 1920), (13, 1520), (23, -1920), (24, -1440), (25, -240), (27, 420), (46, 2880), (47, 1440), (49, 720), (50, -1440), (54, -960), (58, -480), (77, 720), (87, 1440)]

-- Selected source equation 85 in the original pair table.
def row77 : Integer.Sparse (Fin 271) := [(0, 8), (1, -124), (2, 37), (3, 800), (4, 352), (5, -12), (6, 1), (7, 64), (12, 592), (13, 80), (23, -96), (25, -384), (26, 128), (32, -96), (34, 64), (42, 576), (49, 144), (51, 32), (54, -96), (96, 288), (103, 144)]

-- Selected source equation 87 in the original pair table.
def row78 : Integer.Sparse (Fin 271) := [(0, 64), (1, -710), (2, 515), (3, 3760), (4, 1760), (5, -260), (6, 5), (7, 480), (8, 800), (12, 240), (23, -240), (24, -480), (26, 880), (27, 60), (30, -1680), (42, 720), (45, 1440), (50, -1440), (51, 80), (55, -960), (75, 720), (79, -480), (98, 1440), (99, 1440), (109, 1440), (143, -240)]

-- Selected source equation 88 in the original pair table.
def row79 : Integer.Sparse (Fin 271) := [(0, 6), (1, -189), (2, 83), (3, 832), (4, 368), (5, -28), (6, 2), (7, 112), (8, 16), (12, 320), (13, 96), (23, -48), (24, -48), (25, -336), (26, 128), (30, -336), (32, -336), (34, 80), (42, 288), (45, 288), (49, 144), (50, -96), (51, 64), (54, -96), (79, -96), (88, 144), (96, 144), (103, 288), (109, 288)]

-- Selected source equation 89 in the original pair table.
def row80 : Integer.Sparse (Fin 271) := [(0, -1), (1, -56), (2, 56), (3, 464), (4, 80), (5, -40), (6, 1), (7, 80), (8, 80), (10, -72), (12, 184), (13, 192), (24, -48), (26, 32), (34, 32), (37, 72), (39, 144), (50, -48), (51, 48), (54, -72), (58, -144), (70, 72), (73, 144), (87, 144), (88, 288), (94, 288), (132, -24)]

-- Selected source equation 90 in the original pair table.
def row81 : Integer.Sparse (Fin 271) := [(0, 31), (1, -362), (2, 90), (3, 768), (4, 704), (5, -20), (6, 1), (7, 32), (8, 32), (12, 144), (24, -96), (25, -240), (26, 160), (30, -768), (34, 32), (42, 288), (43, 576), (51, 32), (54, -96), (88, 288), (103, 144)]

-- Selected source equation 91 in the original pair table.
def row82 : Integer.Sparse (Fin 271) := [(0, 68), (1, -1405), (2, 540), (3, 5040), (4, 2240), (5, -180), (6, 5), (7, 880), (8, 160), (10, -240), (12, 2480), (13, 160), (23, -2160), (24, -1440), (25, -480), (26, 640), (27, 420), (30, -1440), (34, 240), (42, 2880), (51, 160), (54, -1200), (77, 720), (88, 1440), (103, 1440)]

-- Selected source equation 92 in the original pair table.
def row83 : Integer.Sparse (Fin 271) := [(0, 54), (1, -935), (2, 310), (3, 3280), (4, 1480), (5, -140), (6, 5), (7, 360), (8, 360), (12, 1080), (23, -480), (24, -120), (26, 720), (27, 30), (30, -240), (34, 80), (42, 720), (44, 1440), (50, -600), (54, -240), (55, -480), (75, 360), (97, 720), (99, 720), (143, -120)]

-- Selected source equation 93 in the original pair table.
def row84 : Integer.Sparse (Fin 271) := [(0, 4), (1, -875), (2, 605), (3, 5680), (4, 640), (5, -420), (6, 20), (7, 880), (8, 640), (10, -720), (12, 3120), (13, 3840), (23, -480), (26, 320), (32, -1920), (34, 800), (35, 720), (37, 1440), (39, 1440), (51, 640), (53, -1200), (54, -720), (58, -960), (70, 720), (73, 1440), (132, -240)]

-- Selected source equation 94 in the original pair table.
def row85 : Integer.Sparse (Fin 271) := [(0, 8), (1, -1045), (2, 155), (3, 6480), (4, 1920), (10, -720), (12, 3200), (13, 2800), (23, -480), (24, -960), (25, -720), (27, 60), (32, -1920), (49, 1440), (54, -1920), (58, -720), (77, 720), (78, 1440), (87, 720), (93, 1440)]

-- Selected source equation 95 in the original pair table.
def row86 : Integer.Sparse (Fin 271) := [(0, -7), (1, -515), (2, 435), (3, 4560), (4, 800), (5, -100), (6, 5), (7, 480), (12, 3200), (13, 3600), (25, -240), (26, 160), (32, -960), (34, 800), (40, 1440), (51, 640), (58, -720), (71, 720), (73, 1440), (87, 720), (93, 1440), (133, -720)]

-- Selected source equation 96 in the original pair table.
def row87 : Integer.Sparse (Fin 271) := [(0, -22), (1, -465), (2, 365), (3, 4880), (4, 320), (5, -180), (7, 720), (8, 320), (10, -240), (12, 2800), (13, 3920), (23, -720), (25, -240), (27, 180), (32, -960), (34, 320), (37, 1440), (50, -1920), (53, -1920), (54, -480), (58, -1680), (70, 720), (72, 1440), (87, 720), (93, 1440), (132, -720)]

-- Selected source equation 97 in the original pair table.
def row88 : Integer.Sparse (Fin 271) := [(0, 6), (1, -140), (2, 225), (3, 2560), (4, 800), (5, -260), (6, 15), (7, 1360), (8, 160), (12, 1600), (13, 1040), (23, -480), (25, -960), (26, 720), (34, 1200), (37, 1440), (40, 720), (42, 1440), (51, 560), (53, -720), (82, 720), (89, 1440), (90, 1440), (143, -240)]

-- Selected source equation 98 in the original pair table.
def row89 : Integer.Sparse (Fin 271) := [(0, 39), (1, -385), (2, 615), (3, 3600), (4, 960), (5, -740), (6, 65), (7, 720), (8, 1120), (12, 560), (13, 240), (23, -240), (26, 640), (30, -720), (32, -480), (34, 560), (43, 1440), (50, -1440), (51, 880), (53, -960), (79, -480), (88, 720), (91, 1440), (92, 1440)]

-- Selected source equation 99 in the original pair table.
def row90 : Integer.Sparse (Fin 271) := [(0, 24), (1, -795), (2, 495), (3, 4320), (4, 2000), (5, -220), (6, 10), (7, 800), (8, 160), (12, 1120), (13, 960), (25, -960), (26, 1280), (30, -1200), (32, -960), (34, 720), (37, 720), (38, 1440), (40, 1440), (45, 1440), (50, -480), (51, 640), (53, -720), (79, -480), (82, 720), (83, 1440), (88, 720), (95, 1440), (143, -720)]

-- Selected source equation 100 in the original pair table.
def row91 : Integer.Sparse (Fin 271) := [(0, 44), (1, -690), (2, 385), (3, 4960), (4, 2480), (5, -260), (6, 15), (7, 640), (8, 480), (12, 240), (13, 160), (24, -480), (26, 2160), (30, -480), (34, 320), (36, 2160), (39, 1440), (51, 160), (55, -1200), (79, -960), (81, 720), (83, 1440), (91, 1440), (99, 1440), (143, -960)]

-- Selected source equation 101 in the original pair table.
def row92 : Integer.Sparse (Fin 271) := [(0, -1), (1, -390), (2, 480), (3, 3520), (4, 1120), (5, -420), (6, 35), (7, 1200), (8, 240), (12, 880), (13, 720), (23, -240), (24, -240), (25, -480), (26, 880), (30, -720), (32, -1440), (34, 1200), (40, 720), (42, 1440), (50, -720), (51, 1120), (53, -480), (58, -480), (71, 720), (79, -480), (87, 1440), (88, 720), (95, 1440), (96, 1440), (133, -240)]

-- Selected source equation 102 in the original pair table.
def row93 : Integer.Sparse (Fin 271) := [(0, 23), (1, -385), (2, 310), (3, 1720), (4, 760), (5, -210), (6, 10), (7, 280), (8, 360), (12, 160), (13, 80), (24, -240), (25, -240), (26, 400), (30, -720), (32, -600), (34, 120), (38, 720), (41, 720), (43, 360), (51, 200), (53, -240), (55, -120), (79, -240), (83, 360), (84, 360), (89, 360), (91, 720), (92, 360), (143, -120)]

-- Selected source equation 103 in the original pair table.
def row94 : Integer.Sparse (Fin 271) := [(0, 21), (1, -255), (2, 170), (3, 880), (4, 432), (5, -88), (6, 4), (7, 80), (8, 192), (26, 288), (29, -96), (30, -96), (34, 32), (39, 288), (51, 80), (55, -96), (56, 288), (79, -96), (83, 144), (84, 144), (99, 288), (143, -48), (149, 288)]

-- Selected source equation 104 in the original pair table.
def row95 : Integer.Sparse (Fin 271) := [(0, 3), (1, -113), (2, 53), (3, 640), (4, 240), (5, -26), (6, 1), (7, 72), (8, 32), (12, 200), (13, 144), (25, -72), (26, 176), (32, -120), (34, 80), (36, 144), (37, 144), (38, 288), (39, 288), (50, -48), (51, 64), (53, -48), (54, -240), (79, -48), (82, 72), (83, 144), (86, 144), (96, 72), (143, -72)]

-- Selected source equation 105 in the original pair table.
def row96 : Integer.Sparse (Fin 271) := [(0, 7), (1, -235), (2, 111), (3, 1424), (4, 464), (5, -60), (6, 3), (7, 160), (8, 96), (12, 352), (13, 144), (23, -96), (25, -144), (26, 416), (30, -96), (32, -480), (34, 80), (35, 288), (36, 288), (38, 576), (39, 576), (51, 32), (53, -144), (54, -480), (79, -192), (81, 144), (83, 288), (85, 288), (92, 288), (143, -192)]

-- Selected source equation 106 in the original pair table.
def row97 : Integer.Sparse (Fin 271) := [(0, 11), (1, -185), (2, 160), (3, 1680), (4, 360), (5, -90), (7, 480), (8, 120), (12, 880), (13, 80), (23, -360), (24, -600), (25, -360), (27, 180), (30, -240), (32, -240), (34, 80), (47, 360), (50, -600), (53, -240), (92, 720), (97, 720)]

-- Selected source equation 107 in the original pair table.
def row98 : Integer.Sparse (Fin 271) := [(0, 21), (1, -333), (2, 124), (3, 1072), (4, 672), (5, -36), (7, 192), (8, 48), (12, 192), (23, -144), (24, -240), (25, -288), (26, 128), (27, 72), (30, -672), (34, 32), (45, 576), (46, 144), (50, -240), (53, -96), (89, 288), (98, 288)]

-- Selected source equation 108 in the original pair table.
def row99 : Integer.Sparse (Fin 271) := [(0, -18), (1, -560), (2, 555), (3, 5200), (4, 720), (5, -440), (6, 25), (7, 1200), (8, 560), (10, -720), (12, 2240), (13, 3200), (26, 640), (32, -960), (34, 1040), (36, 720), (38, 720), (39, 720), (40, 1440), (50, -960), (51, 800), (53, -480), (54, -720), (58, -960), (71, 720), (72, 720), (73, 720), (88, 1440), (94, 720), (95, 720), (133, -240)]

-- Selected source equation 128 in the original pair table.
def row100 : Integer.Sparse (Fin 271) := [(0, 4), (1, -44), (2, 7), (5, -12), (6, 3), (23, -144), (25, -144), (27, 84), (29, -144), (30, -288), (62, -96), (66, 24), (97, 432), (111, -144), (130, -48), (146, -288), (147, -144)]

-- Selected source equation 129 in the original pair table.
def row101 : Integer.Sparse (Fin 271) := [(0, 6), (1, -53), (2, 119), (3, 240), (5, -112), (6, 6), (7, 144), (8, 288), (12, 96), (13, 32), (23, -144), (27, 108), (29, -288), (34, 32), (50, -288), (53, -144), (66, 24), (111, -144), (130, -48), (146, -288)]

-- Selected source equation 130 in the original pair table.
def row102 : Integer.Sparse (Fin 271) := [(0, 37), (1, -930), (2, 975), (3, 4880), (4, 1360), (5, -840), (6, 40), (7, 1760), (8, 1920), (12, 960), (13, 480), (23, -480), (24, -1440), (26, 640), (27, 600), (29, -960), (30, -960), (34, 800), (50, -4320), (51, 320), (53, -960), (54, -480), (55, -1200), (88, 1440), (89, 720), (99, 1440), (148, -720)]

-- Selected source equation 131 in the original pair table.
def row103 : Integer.Sparse (Fin 271) := [(0, -1), (1, 110), (2, 5), (14, 2160), (23, -2400), (25, -1440), (62, -1440), (66, 60), (111, -960), (116, 1440), (130, -480), (144, 2160)]

-- Selected source equation 133 in the original pair table.
def row104 : Integer.Sparse (Fin 271) := [(0, -2), (1, -455), (2, 195), (3, 3040), (4, 720), (5, -80), (7, 480), (12, 1840), (13, 480), (15, 2160), (23, -2160), (24, -720), (25, -1440), (27, 420), (32, -1440), (34, 160), (50, -1440), (53, -1440), (62, -480), (66, 60), (111, -720), (113, -240), (124, 1440), (130, -480), (136, 2160)]

-- Selected source equation 134 in the original pair table.
def row105 : Integer.Sparse (Fin 271) := [(0, 8), (1, -30), (2, 25), (5, -12), (6, 3), (17, 432), (23, -288), (25, -624), (27, 48), (29, -144), (30, -576), (62, -96), (66, 12), (85, 432), (100, 432), (110, -432), (111, -144), (130, -96), (134, 432), (140, 288), (142, -144), (146, -48), (147, -144)]

-- Selected source equation 135 in the original pair table.
def row106 : Integer.Sparse (Fin 271) := [(0, 52), (1, -425), (2, 55), (17, 2160), (23, -1440), (25, -3600), (27, 480), (29, -960), (30, -4080), (62, -960), (97, 2160), (100, 2160), (110, -720), (145, 1440), (147, -720)]

-- Selected source equation 138 in the original pair table.
def row107 : Integer.Sparse (Fin 271) := [(0, -9), (1, -845), (2, 530), (3, 6960), (5, -160), (7, 960), (12, 3440), (13, 4560), (16, 2160), (23, -2880), (27, 540), (34, 320), (37, 4320), (50, -2880), (53, -2880), (54, -1440), (66, 60), (111, -720), (112, -240), (120, 2160), (121, 1440), (130, -480)]

-- Selected source equation 139 in the original pair table.
def row108 : Integer.Sparse (Fin 271) := [(0, 101), (1, -2045), (2, 420), (3, 8560), (4, 3280), (5, -20), (7, 240), (12, 2640), (13, 480), (18, 2160), (23, -1440), (24, -1440), (25, -1440), (26, 1760), (27, 240), (30, -1440), (32, -1440), (34, 160), (42, 4320), (46, 2160), (50, -240), (54, -1440), (62, -480), (123, 1440)]

-- Selected source equation 140 in the original pair table.
def row109 : Integer.Sparse (Fin 271) := [(0, 149), (1, -2280), (2, 265), (3, 6960), (4, 5280), (5, -40), (7, 480), (12, 1200), (13, 320), (23, -1440), (24, -1440), (25, -3600), (26, 2400), (27, 240), (30, -3600), (34, 560), (43, 4320), (54, -2160), (62, -480), (100, 2160), (110, -720)]

-- Selected source equation 144 in the original pair table.
def row110 : Integer.Sparse (Fin 271) := [(0, 32), (1, -25), (2, 95), (5, -60), (14, 1080), (17, 2160), (23, -1920), (25, -2880), (27, 480), (29, -720), (30, -2160), (62, -240), (100, 2160), (110, -720), (111, -480), (116, 720), (134, 4320), (144, 2160)]

-- Selected source equation 145 in the original pair table.
def row111 : Integer.Sparse (Fin 271) := [(0, 31), (1, -354), (2, 141), (3, 704), (4, 384), (5, -24), (12, 320), (13, 64), (15, 432), (20, 864), (23, -144), (24, -432), (27, 180), (29, -288), (50, -288), (51, 96), (113, -192), (124, 288), (136, 864), (138, 1728)]

-- Selected source equation 146 in the original pair table.
def row112 : Integer.Sparse (Fin 271) := [(0, 23), (1, -885), (2, 210), (3, 3840), (4, 1200), (12, 1840), (13, 960), (16, 1080), (17, 2160), (23, -1080), (26, 480), (34, 240), (37, 1080), (39, 2160), (50, -720), (51, 240), (54, -1800), (112, -480), (120, 2160), (121, 720), (126, 4320)]

-- Selected source equation 147 in the original pair table.
def row113 : Integer.Sparse (Fin 271) := [(0, -1), (1, -11), (2, 21), (5, -24), (6, 3), (17, 216), (23, -72), (25, -96), (27, 90), (28, 432), (29, -360), (30, -144), (134, 432), (140, 144), (146, -96), (150, 864)]

-- Selected source equation 150 in the original pair table.
def row114 : Integer.Sparse (Fin 271) := [(0, 3), (1, -290), (2, 165), (3, 2080), (4, 640), (5, -60), (7, 320), (12, 1120), (15, 1440), (23, -1680), (24, -1440), (25, -1200), (27, 360), (32, -480), (47, 1440), (50, -480), (54, -960), (66, 60), (111, -480), (113, -480), (117, 1440), (131, -480), (136, 1440), (144, 720)]

-- Selected source equation 151 in the original pair table.
def row115 : Integer.Sparse (Fin 271) := [(0, 17), (1, -725), (2, 260), (3, 4720), (4, 1120), (5, -120), (7, 640), (12, 2000), (13, 560), (16, 720), (23, -2880), (24, -1920), (27, 540), (46, 2880), (50, -960), (54, -1920), (66, 60), (111, -240), (112, -720), (113, -480), (120, 2160), (136, 1440)]

-- Selected source equation 152 in the original pair table.
def row116 : Integer.Sparse (Fin 271) := [(0, 9), (1, -160), (2, 40), (3, 1160), (4, 440), (5, -5), (7, 60), (12, 780), (13, 80), (23, -120), (25, -660), (26, 200), (32, -360), (37, 180), (42, 720), (49, 180), (53, -60), (63, -120), (101, 360)]

-- Selected source equation 153 in the original pair table.
def row117 : Integer.Sparse (Fin 271) := [(0, 47), (1, -1150), (2, 350), (3, 4640), (4, 2480), (5, -120), (6, 5), (7, 240), (8, 160), (12, 1120), (21, 1440), (23, -480), (24, -960), (25, -240), (26, 720), (27, 360), (30, -1680), (32, -480), (34, 160), (42, 720), (46, 1440), (47, 720), (50, -2880), (51, 240), (53, -480), (55, -1200), (89, 720), (129, 1440), (139, 1440), (148, -240)]

-- Selected source equation 156 in the original pair table.
def row118 : Integer.Sparse (Fin 271) := [(0, 9), (1, -206), (2, 31), (3, 1088), (4, 432), (5, -4), (7, 48), (12, 464), (13, 144), (18, 288), (23, -240), (24, -288), (25, -144), (26, 32), (27, 36), (32, -96), (34, 32), (46, 288), (47, 144), (49, 432), (50, -48), (54, -384), (103, 144), (127, 288)]

-- Selected source equation 157 in the original pair table.
def row119 : Integer.Sparse (Fin 271) := [(0, 32), (1, -825), (2, 235), (3, 4960), (4, 1760), (12, 3520), (13, 1440), (25, -1920), (26, 400), (32, -1440), (33, 160), (40, 720), (42, 2880), (49, 1440), (104, 720), (106, 1440)]

-- Selected source equation 158 in the original pair table.
def row120 : Integer.Sparse (Fin 271) := [(0, 29), (1, -340), (2, 105), (3, 1560), (4, 760), (12, 440), (13, 440), (26, 320), (30, -540), (32, -360), (33, 160), (41, 360), (43, 360), (44, 360), (105, 180), (107, 360), (108, 360)]

-- Selected source equation 161 in the original pair table.
def row121 : Integer.Sparse (Fin 271) := [(0, 116), (1, -1215), (2, 325), (3, 3200), (4, 2000), (5, -60), (7, 240), (8, 160), (12, 800), (13, 160), (22, 1440), (26, 480), (30, -2880), (34, 160), (42, 1440), (45, 1440), (46, 720), (48, 1440), (50, -1680), (55, -240), (89, 720), (99, 1440), (135, 1440), (148, -720)]

-- Selected source equation 162 in the original pair table.
def row122 : Integer.Sparse (Fin 271) := [(0, 29), (1, -1090), (2, 335), (3, 4880), (4, 2000), (12, 2080), (13, 1200), (25, -2880), (26, 800), (30, -2160), (32, -2400), (33, 320), (37, 720), (38, 1440), (42, 1440), (45, 1440), (49, 1440), (53, -720), (63, -720), (101, 720), (102, 1440), (105, 720), (106, 1440)]

-- Selected source equation 165 in the original pair table.
def row123 : Integer.Sparse (Fin 271) := [(0, 21), (1, -1115), (2, 610), (3, 5520), (4, 2560), (5, -220), (7, 320), (8, 640), (12, 2160), (13, 1360), (15, 1440), (23, -720), (24, -1440), (25, -960), (27, 360), (30, -1920), (32, -2400), (38, 2880), (41, 2880), (50, -2880), (54, -960), (55, -2400), (63, -480), (66, 60), (89, 1440), (101, 1440), (111, -240), (112, -240), (113, -480), (120, 720), (124, 1440), (125, 1440), (131, -480), (148, -480)]

-- Selected source equation 166 in the original pair table.
def row124 : Integer.Sparse (Fin 271) := [(0, 37), (1, -406), (2, 139), (3, 1216), (4, 704), (12, 384), (13, 16), (25, -144), (26, 224), (30, -576), (32, -96), (33, 32), (42, 288), (44, 576), (45, 576), (49, 144), (105, 288), (106, 288)]

-- Selected source equation 167 in the original pair table.
def row125 : Integer.Sparse (Fin 271) := [(0, 126), (1, -2265), (2, 305), (3, 7920), (4, 5120), (5, -20), (7, 240), (12, 2320), (21, 1440), (23, -1200), (24, -1440), (25, -2640), (26, 2000), (27, 180), (30, -1680), (32, -480), (34, 160), (42, 2160), (43, 4320), (46, 720), (47, 1440), (50, -240), (54, -1920), (103, 720), (104, 1440), (129, 1440)]

-- Selected source equation 168 in the original pair table.
def row126 : Integer.Sparse (Fin 271) := [(0, 39), (1, -1590), (2, 670), (3, 8160), (4, 2720), (5, -100), (6, 5), (7, 160), (8, 160), (12, 3200), (13, 3440), (18, 1440), (23, -240), (24, -480), (25, -1200), (26, 320), (27, 180), (30, -1920), (32, -2400), (34, 240), (37, 720), (38, 1440), (41, 4320), (46, 720), (50, -2400), (51, 240), (53, -720), (54, -720), (55, -1200), (63, -480), (89, 720), (101, 1440), (122, 1440), (123, 1440), (148, -240)]

-- Selected source equation 169 in the original pair table.
def row127 : Integer.Sparse (Fin 271) := [(0, 102), (1, -1245), (2, 365), (3, 3440), (4, 2120), (12, 1280), (13, 240), (25, -480), (26, 320), (30, -1440), (32, -720), (33, 80), (43, 720), (44, 2160), (45, 720), (104, 360), (105, 720), (108, 720)]

-- Selected source equation 171 in the original pair table.
def row128 : Integer.Sparse (Fin 271) := [(0, 9), (1, -341), (2, 78), (3, 1568), (4, 592), (5, -28), (6, 2), (7, 48), (8, 32), (12, 608), (13, 608), (22, 288), (23, -48), (24, -96), (25, -192), (26, 224), (27, 36), (30, -288), (32, -384), (34, 160), (35, 144), (38, 576), (41, 576), (50, -384), (51, 64), (53, -432), (54, -144), (55, -336), (89, 144), (135, 288), (141, 288), (148, -48)]

-- Selected source equation 173 in the original pair table.
def row129 : Integer.Sparse (Fin 271) := [(0, 9), (1, -307), (2, 90), (3, 1280), (4, 528), (5, -44), (6, 4), (7, 64), (8, 64), (12, 400), (13, 288), (17, 288), (22, 288), (23, -48), (24, -288), (25, -144), (26, 224), (27, 48), (30, -288), (32, -240), (34, 96), (38, 576), (41, 576), (50, -288), (51, 64), (53, -96), (54, -192), (55, -240), (66, 12), (89, 144), (91, 288), (110, -96), (111, -48), (113, -96), (117, 144), (126, 288), (131, -144), (135, 288), (140, 288), (141, 288), (147, -96), (148, -48)]

-- Selected source equation 175 in the original pair table.
def row130 : Integer.Sparse (Fin 271) := [(0, 53), (1, -1175), (2, 470), (3, 4400), (4, 2400), (5, -160), (7, 480), (8, 320), (12, 1520), (15, 720), (23, -1680), (24, -1680), (25, -3360), (26, 320), (27, 420), (30, -2880), (32, -1200), (43, 1440), (47, 2880), (50, -1920), (53, -960), (54, -960), (63, -480), (66, 60), (92, 1440), (112, -720), (113, -720), (117, 1440), (125, 720), (137, 1440), (148, -480)]

-- Selected source equation 176 in the original pair table.
def row131 : Integer.Sparse (Fin 271) := [(0, 54), (1, -1555), (2, 420), (3, 6320), (4, 3040), (5, -100), (6, 5), (7, 320), (8, 80), (12, 2400), (13, 560), (18, 720), (23, -960), (24, -480), (25, -3360), (26, 720), (27, 240), (30, -2640), (32, -1200), (34, 240), (42, 720), (43, 720), (46, 720), (47, 1440), (49, 1440), (50, -2160), (51, 240), (53, -960), (54, -480), (55, -480), (63, -480), (92, 720), (96, 720), (122, 720), (127, 1440), (139, 720), (148, -240)]

-- Selected source equation 183 in the original pair table.
def row132 : Integer.Sparse (Fin 271) := [(0, 2), (1, -173), (2, 136), (3, 1264), (4, 480), (5, -72), (6, 3), (7, 240), (8, 112), (12, 128), (13, 128), (15, 144), (23, -48), (24, -192), (25, -96), (26, 528), (27, 36), (30, -192), (32, -384), (33, 112), (34, 80), (36, 288), (50, -288), (51, 32), (54, -144), (63, -96), (66, 12), (99, 288), (102, 288), (112, -48), (113, -144), (117, 288), (118, 144), (125, 144), (126, 144), (131, -48), (146, -48), (148, -96)]

-- Selected source equation 184 in the original pair table.
def row133 : Integer.Sparse (Fin 271) := [(0, 103), (1, -1580), (2, 560), (3, 7920), (4, 3840), (5, -40), (6, 5), (12, 720), (13, 480), (18, 720), (26, 3920), (30, -480), (32, -960), (33, 720), (34, 160), (51, 160), (52, 1440), (54, -480), (56, 1440), (107, 1440), (119, 720), (127, 1440)]

-- Selected source equation 187 in the original pair table.
def row134 : Integer.Sparse (Fin 271) := [(0, 71), (1, -1455), (2, 410), (3, 8000), (4, 3920), (5, -80), (6, 10), (7, 160), (8, 80), (12, 560), (13, 560), (21, 720), (26, 4080), (30, -960), (32, -1440), (33, 720), (34, 320), (36, 1440), (39, 720), (50, -240), (51, 80), (52, 1440), (54, -720), (55, -480), (56, 720), (107, 1440), (128, 720), (135, 720)]

-- Selected source equation 240 in the original pair table.
def row135 : Integer.Sparse (Fin 271) := [(0, 1), (1, -49), (2, -91), (3, -48), (5, 276), (6, -54), (7, -48), (8, -96), (9, 284), (34, -96), (51, -192), (57, -11), (67, -96), (68, -32), (69, -192), (164, -48), (183, -144), (222, -192), (247, 144), (268, 288)]

-- Selected source equation 241 in the original pair table.
def row136 : Integer.Sparse (Fin 271) := [(0, 9), (1, -255), (2, -530), (3, -480), (5, 1520), (6, -180), (7, -1920), (8, -1920), (9, 740), (34, -640), (57, -20), (67, -2400), (68, -1280), (69, -3840), (163, 720), (164, -240)]

-- Selected source equation 242 in the original pair table.
def row137 : Integer.Sparse (Fin 271) := [(1, 3), (2, -28), (3, -192), (4, -48), (5, 76), (6, -12), (7, -144), (9, 28), (11, -48), (26, -96), (34, -224), (51, -144), (57, -1), (67, -96), (68, -64), (143, 144), (164, -48), (183, -48), (222, -96), (247, 144)]

-- Selected source equation 243 in the original pair table.
def row138 : Integer.Sparse (Fin 271) := [(0, -1), (1, 70), (2, -25), (3, -1440), (4, -480), (5, 420), (6, -75), (9, 100), (11, -480), (26, -960), (34, -1440), (51, -1280), (54, 720), (57, -5), (143, 1440), (164, -80), (248, 720), (249, 480)]

-- Selected source equation 244 in the original pair table.
def row139 : Integer.Sparse (Fin 271) := [(0, 6), (1, -105), (2, -260), (3, -1440), (5, 480), (6, -90), (7, -480), (9, 120), (12, -480), (13, -2160), (34, -1680), (51, -1440), (53, 720), (57, -5), (67, -240), (68, -160), (80, -1280), (115, -1200), (132, 1440), (133, 1440), (164, -320), (183, -240), (219, 720), (222, -480), (246, 480), (247, 720)]

-- Selected source equation 245 in the original pair table.
def row140 : Integer.Sparse (Fin 271) := [(0, 1), (1, -80), (2, -270), (3, -480), (4, -80), (5, 560), (6, -60), (7, -720), (8, -800), (9, 180), (34, -160), (50, 720), (51, -240), (57, -5), (67, -480), (68, -160), (69, -960), (181, 720), (182, 480), (183, -80)]

-- Selected source equation 246 in the original pair table.
def row141 : Integer.Sparse (Fin 271) := [(0, 6), (1, -185), (2, -235), (3, -400), (4, -80), (5, 440), (6, -90), (8, -320), (9, 300), (11, -80), (13, -320), (26, -160), (34, -480), (51, -880), (55, 480), (57, -10), (67, -80), (69, -320), (80, -320), (115, -400), (133, 960), (143, 240), (164, -80), (183, -160), (219, 240), (222, -160), (263, 960), (268, 480)]

-- Selected source equation 247 in the original pair table.
def row142 : Integer.Sparse (Fin 271) := [(0, -1), (1, -15), (2, -190), (3, -640), (4, -160), (5, 320), (6, -35), (7, -480), (8, -320), (9, 100), (26, -160), (27, -60), (34, -320), (50, 480), (51, -480), (57, -5), (66, -60), (67, -320), (69, -160), (111, 240), (113, 480), (181, 480), (183, -160), (220, 480), (222, -160)]

-- Selected source equation 248 in the original pair table.
def row143 : Integer.Sparse (Fin 271) := [(0, 1), (1, 60), (2, -15), (3, -1120), (4, -320), (5, 420), (6, -25), (9, 60), (11, -320), (26, -800), (27, -120), (34, -1120), (51, -320), (54, 240), (57, -5), (66, -120), (148, 960), (164, -80), (220, 480), (222, -160), (248, 240)]

-- Selected source equation 249 in the original pair table.
def row144 : Integer.Sparse (Fin 271) := [(0, 7), (1, -55), (2, -175), (3, -1040), (5, 460), (6, -60), (7, -400), (8, -160), (9, 80), (12, -320), (13, -1360), (34, -720), (50, 480), (51, -960), (53, 240), (57, -5), (66, -60), (67, -160), (68, -160), (69, -80), (80, -320), (112, 480), (113, 240), (115, -400), (164, -80), (182, 480), (183, -160), (219, 240), (221, 480), (222, -160)]

-- Selected source equation 250 in the original pair table.
def row145 : Integer.Sparse (Fin 271) := [(0, 1), (1, 64), (2, -38), (3, -640), (4, -192), (5, 24), (6, -3), (12, -192), (13, -256), (26, -192), (27, -36), (34, -192), (50, 576), (51, -192), (54, 576), (114, 144), (115, -48), (220, 576), (221, 384), (222, -64)]

-- Selected source equation 251 in the original pair table.
def row146 : Integer.Sparse (Fin 271) := [(0, 3), (1, -45), (2, -200), (3, -400), (5, 700), (6, -60), (7, -80), (8, -480), (9, 160), (27, -180), (51, -480), (57, -10), (66, -180), (67, -80), (69, -400), (113, 240), (146, 480), (147, 480), (181, 240), (183, -80)]

-- Selected source equation 252 in the original pair table.
def row147 : Integer.Sparse (Fin 271) := [(0, 8), (1, -40), (2, -40), (3, -560), (5, 420), (6, -25), (9, 60), (11, -160), (12, -80), (13, -720), (26, -320), (34, -880), (51, -560), (54, 240), (57, -5), (66, -120), (80, -160), (115, -160), (147, 480), (164, -80), (221, 480), (222, -160), (249, 240)]

-- Selected source equation 253 in the original pair table.
def row148 : Integer.Sparse (Fin 271) := [(0, 6), (1, -5), (2, -15), (3, -480), (4, -80), (5, 480), (6, -30), (7, -160), (8, -160), (9, 140), (11, -160), (13, -320), (26, -480), (34, -960), (51, -160), (55, 240), (57, -10), (66, -180), (68, -160), (69, -240), (80, -160), (131, 480), (146, 240), (148, 240), (164, -80), (182, 240), (183, -80), (263, 240)]

-- Selected source equation 261 in the original pair table.
def row149 : Integer.Sparse (Fin 271) := [(0, 1), (1, -33), (2, -51), (3, -48), (5, 148), (6, -15), (7, -144), (8, -192), (9, 36), (34, -80), (51, -96), (67, -288), (68, -112), (69, -432), (151, 144), (152, -32), (222, -48)]

-- Selected source equation 262 in the original pair table.
def row150 : Integer.Sparse (Fin 271) := [(0, 2), (1, -15), (2, -10), (3, -280), (5, 170), (6, -25), (7, -360), (9, 50), (13, -120), (26, -120), (34, -560), (51, -240), (53, 360), (59, -80), (67, -360), (68, -320), (69, -240), (152, -80), (153, 360), (154, 240), (222, -40)]

-- Selected source equation 263 in the original pair table.
def row151 : Integer.Sparse (Fin 271) := [(0, 9), (1, -225), (2, -300), (3, -480), (4, -80), (5, 840), (6, -100), (7, -320), (8, -960), (9, 80), (13, -320), (26, -80), (34, -400), (50, 240), (51, -880), (55, 480), (58, 480), (67, -560), (68, -80), (69, -1200), (115, -160), (151, 240), (153, 240), (155, 960), (222, -160)]

-- Selected source equation 264 in the original pair table.
def row152 : Integer.Sparse (Fin 271) := [(0, 3), (1, -30), (2, -80), (3, -560), (4, -80), (5, 260), (6, -25), (7, -640), (8, -320), (9, 40), (26, -240), (34, -720), (51, -240), (65, -160), (67, -400), (68, -240), (69, -320), (79, 240), (151, 240), (152, -80), (222, -80)]

-- Selected source equation 266 in the original pair table.
def row153 : Integer.Sparse (Fin 271) := [(0, 7), (1, 60), (2, 40), (3, -1280), (5, 140), (6, -35), (7, -480), (9, 20), (12, -240), (13, -640), (26, -800), (33, -480), (34, -1360), (54, 720), (59, -160), (65, -480), (68, -240), (69, -80), (131, 720), (152, -160), (158, 480)]

-- Selected source equation 267 in the original pair table.
def row154 : Integer.Sparse (Fin 271) := [(0, -2), (1, 315), (2, -60), (3, -4080), (4, -960), (5, 220), (6, -45), (7, -960), (9, 20), (13, -1200), (26, -2880), (33, -1280), (34, -2000), (51, -480), (54, 720), (63, 1440), (65, -960), (67, -80), (68, -240), (112, 720), (152, -160), (156, 480)]

-- Selected source equation 268 in the original pair table.
def row155 : Integer.Sparse (Fin 271) := [(0, 3), (1, 20), (2, 35), (3, -480), (5, 200), (6, -40), (7, -480), (9, 80), (13, -160), (26, -480), (33, -160), (34, -960), (53, 480), (65, -320), (67, -160), (68, -320), (69, -160), (111, 240), (130, 240), (131, 480), (152, -160), (153, 480), (156, 480), (222, -160)]

-- Selected source equation 269 in the original pair table.
def row156 : Integer.Sparse (Fin 271) := [(0, 6), (1, -65), (2, -125), (3, -1360), (4, -160), (5, 420), (6, -70), (7, -320), (8, -160), (9, 60), (13, -960), (26, -640), (33, -400), (34, -1200), (51, -1040), (55, 480), (59, -400), (63, 240), (65, -160), (67, -240), (68, -160), (69, -160), (112, 480), (113, 240), (115, -320), (131, 240), (152, -160), (154, 240), (155, 480), (158, 480), (222, -240)]

-- Selected source equation 270 in the original pair table.
def row157 : Integer.Sparse (Fin 271) := [(0, 9), (1, -45), (2, -85), (3, -800), (4, -80), (5, 460), (6, -85), (7, -640), (8, -480), (9, 100), (26, -400), (34, -560), (50, 240), (51, -400), (67, -320), (68, -80), (69, -480), (110, 480), (111, 480), (113, 240), (131, 240), (146, 480), (153, 240), (222, -80)]

-- Selected source equation 275 in the original pair table.
def row158 : Integer.Sparse (Fin 271) := [(0, 8), (1, 35), (2, -340), (3, -3120), (4, -800), (5, 680), (6, -55), (7, -1920), (8, -800), (10, 240), (11, -160), (12, -80), (13, -160), (26, -1760), (32, 480), (33, -320), (34, -2640), (51, -800), (54, 240), (65, -800), (79, 1920), (80, -80), (143, 480), (160, 480), (162, -160), (179, 480), (180, 480)]

-- Selected source equation 276 in the original pair table.
def row159 : Integer.Sparse (Fin 271) := [(0, 1), (1, -12), (2, -27), (3, -224), (4, -16), (5, 52), (6, -8), (7, -16), (8, -16), (11, -16), (12, -88), (13, -304), (26, -32), (32, 96), (33, -32), (34, -144), (51, -176), (53, 48), (58, 240), (59, -64), (80, -32), (115, -96), (132, 24), (133, 48), (143, 48), (159, 48), (162, -16), (218, 96), (245, 96)]

-- Selected source equation 277 in the original pair table.
def row160 : Integer.Sparse (Fin 271) := [(0, 6), (1, 65), (2, -180), (3, -2880), (4, -720), (5, 440), (6, -35), (7, -1680), (8, -480), (11, -240), (13, -240), (26, -1920), (33, -480), (34, -2800), (51, -720), (59, -160), (65, -960), (79, 1440), (143, 720), (160, 720), (162, -240)]

-- Selected source equation 278 in the original pair table.
def row161 : Integer.Sparse (Fin 271) := [(0, 1), (1, 6), (2, -39), (3, -576), (4, -160), (5, 108), (6, -14), (7, -192), (8, -64), (11, -128), (12, -32), (13, -112), (26, -352), (32, 96), (33, -64), (34, -544), (51, -256), (53, 48), (55, 96), (58, 96), (59, -64), (65, -64), (79, 192), (115, -16), (143, 480), (159, 48), (161, 96), (162, -48), (218, 192), (245, 96)]

-- Selected source equation 285 in the original pair table.
def row162 : Integer.Sparse (Fin 271) := [(0, 7), (1, 105), (2, -120), (3, -1920), (4, -240), (12, -960), (13, -2000), (26, -240), (31, -80), (32, 1440), (33, -480), (50, 720), (51, -240), (59, -240), (60, 720), (114, 720), (115, -240), (217, 1440)]

-- Selected source equation 286 in the original pair table.
def row163 : Integer.Sparse (Fin 271) := [(0, 14), (1, -65), (2, -80), (3, -1200), (5, 340), (6, -65), (12, -160), (13, -1280), (26, -240), (32, 240), (33, -160), (34, -560), (51, -1120), (59, -160), (80, -80), (110, 480), (115, -320), (147, 480), (179, 240), (217, 480)]

-- Selected source equation 287 in the original pair table.
def row164 : Integer.Sparse (Fin 271) := [(0, 7), (1, -10), (2, -25), (3, -480), (5, 200), (6, -30), (11, -40), (12, -40), (13, -480), (26, -200), (32, 120), (34, -440), (51, -440), (54, 120), (62, 240), (80, -40), (110, 240), (115, -40), (147, 240), (179, 120), (245, 120)]

-- Selected source equation 297 in the original pair table.
def row165 : Integer.Sparse (Fin 271) := [(0, -5), (1, 131), (2, 228), (3, 224), (5, -556), (6, 42), (7, 656), (8, 928), (9, -120), (34, 224), (51, 192), (67, 848), (68, 272), (69, 1664), (151, -576), (163, -144), (165, 144), (166, 576), (167, 576), (247, -144), (268, -288)]

-- Selected source equation 298 in the original pair table.
def row166 : Integer.Sparse (Fin 271) := [(0, -23), (1, -195), (2, 220), (3, 3200), (5, -420), (6, 30), (7, 1520), (8, 640), (9, -40), (10, -240), (12, 560), (13, 160), (23, -1920), (24, -960), (26, 320), (27, 420), (34, 800), (50, -1440), (53, -1680), (54, -1440), (67, 400), (68, 240), (69, 160), (75, 2880), (77, 720), (143, -960), (163, -240), (174, 1440), (175, 2160)]

-- Selected source equation 300 in the original pair table.
def row167 : Integer.Sparse (Fin 271) := [(0, -19), (1, -115), (2, 430), (3, 3200), (5, -740), (6, 20), (7, 2800), (8, 1280), (9, -40), (10, -720), (12, 720), (13, 960), (23, -240), (24, -480), (27, 180), (34, 2240), (50, -1920), (51, 640), (53, -960), (58, -1920), (67, 720), (68, 400), (69, 320), (70, 720), (71, 1440), (72, 1440), (132, -720), (151, -960), (163, -240), (165, 720), (166, 1440), (247, -720)]

-- Selected source equation 301 in the original pair table.
def row168 : Integer.Sparse (Fin 271) := [(0, -3), (1, 41), (2, 126), (3, 176), (4, 48), (5, -208), (6, 16), (7, 304), (8, 352), (9, -32), (10, -96), (12, 32), (13, 16), (24, -96), (26, 32), (27, 24), (29, -48), (34, 80), (50, -144), (51, 48), (53, -48), (54, -48), (55, -192), (58, -96), (67, 144), (68, 16), (69, 480), (72, 288), (73, 144), (76, 288), (133, -96), (143, -96), (151, -96), (163, -48), (166, 144), (168, 144), (172, 288), (173, 288), (247, -48), (268, -48)]

-- Selected source equation 302 in the original pair table.
def row169 : Integer.Sparse (Fin 271) := [(0, -5), (1, 101), (2, 210), (3, 336), (4, 16), (5, -360), (6, 26), (7, 352), (8, 576), (9, -24), (34, 144), (50, -144), (51, 288), (67, 208), (68, 80), (69, 320), (79, -192), (84, 288), (151, -96), (167, 288), (194, 144), (197, 288), (199, 288), (268, -144)]

-- Selected source equation 303 in the original pair table.
def row170 : Integer.Sparse (Fin 271) := [(0, -13), (1, -30), (2, 155), (3, 2000), (5, -580), (6, 70), (7, 1840), (8, 960), (9, -160), (10, -480), (12, 160), (13, 80), (23, -720), (24, -240), (26, 160), (27, 120), (34, 1520), (50, -480), (51, 160), (53, -1200), (54, -240), (58, -480), (67, 1600), (68, 960), (69, 640), (70, 1440), (71, 720), (75, 1440), (132, -480), (143, -480), (151, -480), (163, -240), (165, 720), (168, 720), (170, 1440), (171, 1440), (247, -480)]

-- Selected source equation 304 in the original pair table.
def row171 : Integer.Sparse (Fin 271) := [(0, -11), (1, 10), (2, 605), (3, 3120), (4, 400), (5, -900), (6, 70), (7, 2400), (8, 720), (9, -80), (12, 160), (13, 320), (24, -240), (26, 480), (34, 2320), (50, -480), (51, 1920), (67, 640), (68, 320), (69, 640), (71, 1440), (79, -960), (82, 720), (83, 1440), (133, -480), (143, -720), (151, -1440), (163, -720), (165, 720), (166, 1440), (194, 2160), (199, 1440), (247, -240), (268, -720)]

-- Selected source equation 305 in the original pair table.
def row172 : Integer.Sparse (Fin 271) := [(0, -28), (1, 415), (2, 840), (3, 1760), (4, 400), (5, -1660), (6, 105), (7, 1920), (8, 2880), (9, -120), (13, 320), (26, 160), (34, 800), (50, -1680), (51, 640), (55, -1440), (58, -1200), (67, 1040), (68, 400), (69, 1600), (74, 2880), (75, 720), (133, -960), (143, -240), (151, -480), (167, 1440), (170, 1440), (171, 720), (172, 1440), (247, -240), (268, -480)]

-- Selected source equation 306 in the original pair table.
def row173 : Integer.Sparse (Fin 271) := [(0, -27), (1, 555), (2, 1085), (3, 1600), (4, 80), (5, -2280), (6, 225), (7, 2320), (8, 3040), (9, -160), (26, 160), (34, 880), (50, -720), (51, 1280), (67, 720), (68, 80), (69, 2400), (83, 1440), (143, -480), (151, -480), (163, -240), (166, 720), (194, 720), (197, 1440), (199, 1440), (268, -480)]

-- Selected source equation 307 in the original pair table.
def row174 : Integer.Sparse (Fin 271) := [(0, -9), (1, 20), (2, 95), (3, 800), (5, -180), (6, 20), (7, 480), (9, -40), (12, 160), (13, 160), (23, -240), (30, -480), (32, -480), (34, 320), (51, 320), (67, 160), (68, 160), (79, -960), (88, 1440), (111, -240), (130, -240), (151, -480), (194, 1440), (205, 1440), (268, -480)]

-- Selected source equation 308 in the original pair table.
def row175 : Integer.Sparse (Fin 271) := [(0, -4), (1, 15), (2, 20), (3, 2400), (4, 640), (5, -380), (6, 45), (7, 2560), (8, 480), (9, -40), (12, 320), (13, 160), (23, -480), (24, -480), (25, -1200), (26, 1120), (34, 1440), (51, 320), (53, -1200), (67, 240), (68, 80), (69, 160), (89, 2880), (103, 720), (111, -480), (131, -480), (143, -960), (151, -480), (163, -240), (175, 720), (204, 1440)]

-- Selected source equation 311 in the original pair table.
def row176 : Integer.Sparse (Fin 271) := [(0, -3), (1, -76), (2, 172), (3, 1232), (4, 224), (5, -136), (6, 11), (7, 352), (8, 224), (9, -8), (12, 256), (13, 160), (23, -144), (24, -96), (26, 256), (32, -768), (34, 208), (51, 224), (53, -240), (54, -48), (67, 48), (68, 16), (69, 32), (79, -576), (92, 576), (96, 288), (112, -96), (113, -96), (143, -192), (151, -96), (163, -48), (175, 144), (205, 288)]

-- Selected source equation 312 in the original pair table.
def row177 : Integer.Sparse (Fin 271) := [(0, -19), (1, -5), (2, 440), (3, 3680), (4, 160), (5, -1260), (6, 220), (7, 1760), (8, 320), (9, -160), (12, 400), (13, 2080), (23, -240), (26, 480), (34, 2720), (50, -480), (51, 3520), (53, -1200), (67, 560), (68, 400), (69, 160), (95, 2880), (112, -960), (113, -480), (143, -960), (151, -480), (163, -240), (175, 720), (194, 1440), (204, 1440), (268, -480)]

-- Selected source equation 313 in the original pair table.
def row178 : Integer.Sparse (Fin 271) := [(0, -33), (1, 100), (2, 985), (3, 5680), (5, -1360), (6, 170), (7, 1680), (8, 960), (9, -120), (12, 1840), (13, 4720), (23, -720), (34, 2800), (50, -480), (51, 3520), (53, -240), (58, -1200), (67, 560), (68, 400), (69, 160), (90, 1440), (94, 2880), (112, -1440), (113, -480), (133, -960), (151, -480), (171, 720), (199, 1440), (203, 1440), (247, -240), (268, -480)]

-- Selected source equation 314 in the original pair table.
def row179 : Integer.Sparse (Fin 271) := [(0, -19), (1, 50), (2, 170), (3, 2400), (5, -360), (6, 35), (7, 1760), (8, 800), (9, -40), (10, -480), (12, 960), (13, 880), (23, -240), (26, 320), (27, 360), (34, 720), (50, -1200), (51, 160), (54, -1200), (58, -480), (67, 240), (69, 240), (97, 1440), (111, -480), (143, -480), (146, -480), (151, -480), (163, -240), (174, 720), (203, 1440)]

-- Selected source equation 315 in the original pair table.
def row180 : Integer.Sparse (Fin 271) := [(0, -3), (1, 14), (2, 7), (3, 368), (5, -36), (6, 16), (7, 448), (8, 96), (9, -40), (10, -48), (12, 80), (13, 64), (23, -144), (26, 96), (27, 36), (34, 208), (50, -48), (53, -48), (54, -240), (67, 160), (68, 64), (69, 96), (85, 288), (111, -240), (130, -96), (131, -48), (143, -288), (146, -96), (163, -48), (168, 144), (174, 144), (247, -48)]

-- Selected source equation 332 in the original pair table.
def row181 : Integer.Sparse (Fin 271) := [(0, 1), (1, -320), (2, 200), (3, 2000), (4, 560), (5, -220), (6, 15), (7, 960), (9, -20), (12, 720), (13, 160), (23, -2160), (24, -2400), (25, -720), (27, 600), (34, 320), (47, 2160), (50, -720), (54, -1440), (62, -480), (66, 240), (67, 240), (68, 160), (111, -1440), (113, -1440), (130, -480), (131, -1440), (181, -240), (242, 1440), (256, 2160)]

-- Selected source equation 337 in the original pair table.
def row182 : Integer.Sparse (Fin 271) := [(0, 54), (1, -660), (2, 935), (3, 4320), (4, 2000), (5, -940), (6, 45), (7, 1920), (8, 1920), (12, 240), (13, 160), (26, 1200), (30, -3600), (34, 800), (42, 2160), (50, -3600), (55, -1440), (75, 2160), (89, 4320), (99, 4320), (143, -240), (148, -2400), (252, 1440)]

-- Selected source equation 338 in the original pair table.
def row183 : Integer.Sparse (Fin 271) := [(0, -3), (1, -190), (2, 385), (3, 2880), (4, 720), (5, -560), (6, 30), (7, 1440), (8, 960), (10, -1080), (11, 240), (12, 520), (13, 720), (26, 960), (34, 1120), (37, 1080), (39, 2160), (51, 240), (54, -1080), (58, -720), (70, 1080), (73, 2160), (132, -120), (143, -720), (193, 2160), (229, 720), (232, 4320), (248, -480)]

-- Selected source equation 339 in the original pair table.
def row184 : Integer.Sparse (Fin 271) := [(0, 9), (1, -315), (2, 170), (3, 2880), (4, 960), (5, -680), (6, 120), (7, 960), (9, -20), (11, 480), (12, 240), (26, 960), (32, -2880), (34, 2080), (35, 2160), (39, 4320), (51, 1440), (53, -720), (54, -2160), (67, 240), (68, 160), (143, -1440), (179, -2160), (185, 4320), (223, 2160), (245, -1440), (246, -240), (249, -960), (258, 4320), (260, 1440), (262, 8640)]

-- Selected source equation 340 in the original pair table.
def row185 : Integer.Sparse (Fin 271) := [(0, -29), (1, -490), (2, 485), (3, 3920), (5, -340), (7, 1840), (8, 160), (10, -240), (12, 1200), (13, 320), (23, -3360), (24, -2400), (25, -480), (26, 160), (27, 1020), (32, -480), (34, 160), (50, -2880), (53, -1200), (54, -2400), (64, -480), (77, 720), (87, 720), (109, 2880), (114, -240), (177, 1440), (178, 1440)]

-- Selected source equation 343 in the original pair table.
def row186 : Integer.Sparse (Fin 271) := [(0, -12), (1, -405), (2, 300), (3, 3440), (4, 640), (5, -260), (6, 5), (7, 1200), (8, 80), (9, -20), (10, -480), (12, 1040), (13, 320), (23, -3600), (24, -3120), (26, 160), (27, 780), (34, 320), (46, 1440), (50, -480), (51, 160), (54, -3360), (66, 180), (67, 240), (68, 160), (77, 1440), (103, 720), (111, -240), (112, -2160), (113, -1440), (131, -480), (175, 720), (181, -240), (234, 1440), (241, 1440), (248, -240), (256, 720)]

-- Selected source equation 345 in the original pair table.
def row187 : Integer.Sparse (Fin 271) := [(0, 29), (1, -515), (2, 480), (3, 1280), (4, 800), (5, -420), (6, 30), (7, 240), (8, 800), (9, -20), (12, 320), (23, -480), (24, -2880), (27, 1140), (29, -1680), (30, -960), (32, -960), (48, 1440), (50, -720), (51, 80), (54, -1920), (66, 180), (67, 80), (69, 320), (97, 720), (98, 1440), (111, -240), (113, -1680), (131, -960), (146, -1440), (147, -720), (174, 720), (177, 1440), (179, -480), (181, -240), (249, -240), (256, 720), (266, 1440), (267, 1440)]

-- Selected source equation 346 in the original pair table.
def row188 : Integer.Sparse (Fin 271) := [(0, -1), (1, -80), (2, 555), (3, 2800), (4, 960), (5, -660), (6, 40), (7, 1040), (8, 1440), (9, -20), (26, 640), (30, -960), (34, 480), (45, 1440), (50, -3360), (51, 480), (55, -1680), (67, 240), (68, 160), (69, 320), (75, 1440), (89, 720), (99, 1440), (143, -480), (148, -720), (155, -960), (170, 720), (182, -720), (199, 1440), (250, 1440), (251, 1440), (263, -240)]

-- Selected source equation 347 in the original pair table.
def row189 : Integer.Sparse (Fin 271) := [(0, 9), (1, -110), (2, 515), (3, 1040), (4, 320), (5, -740), (6, 80), (7, 400), (8, 1600), (9, -20), (12, 400), (23, -240), (27, 300), (29, -480), (32, -960), (44, 2880), (50, -2880), (51, 160), (53, -1440), (67, 80), (69, 640), (153, -960), (168, 720), (176, 1440), (181, -720), (197, 1440), (245, -480), (246, -240), (253, 2880), (254, 2880)]

-- Selected source equation 349 in the original pair table.
def row190 : Integer.Sparse (Fin 271) := [(0, -13), (1, -630), (2, 660), (3, 4800), (4, 960), (5, -660), (6, 35), (7, 1840), (8, 720), (9, -20), (12, 1440), (13, 720), (23, -2160), (24, -1200), (25, -2400), (26, 320), (27, 480), (30, -1920), (32, -960), (34, 1040), (47, 1440), (50, -4080), (51, 640), (53, -3120), (54, -960), (55, -1200), (63, -2400), (66, 180), (67, 240), (68, 160), (89, 720), (92, 4320), (96, 1440), (111, -240), (112, -2160), (113, -1440), (131, -480), (148, -1680), (175, 720), (178, 1440), (180, -480), (182, -240), (234, 720), (238, 1440), (242, 1440), (248, -240)]

-- Selected source equation 350 in the original pair table.
def row191 : Integer.Sparse (Fin 271) := [(0, 18), (1, -520), (2, 425), (3, 2760), (4, 720), (5, -510), (6, 35), (7, 1040), (8, 960), (9, -10), (10, -240), (12, 520), (13, 480), (24, -960), (26, 560), (27, 270), (29, -480), (30, -480), (34, 680), (48, 720), (50, -1080), (51, 80), (54, -840), (66, 90), (67, 40), (69, 160), (80, 80), (88, 720), (99, 1440), (111, -120), (113, -840), (131, -480), (146, -720), (148, -480), (174, 360), (182, -120), (234, 360), (249, -120), (265, 720), (266, 720)]

-- Selected source equation 351 in the original pair table.
def row192 : Integer.Sparse (Fin 271) := [(0, -2), (1, -195), (2, 360), (3, 2960), (4, 520), (5, -550), (6, 65), (7, 440), (8, 480), (9, -10), (11, 80), (12, 720), (13, 1680), (26, 480), (34, 1200), (44, 720), (50, -960), (51, 1360), (53, -480), (55, -480), (67, 120), (68, 80), (69, 160), (94, 1440), (95, 720), (143, -240), (155, -480), (170, 360), (182, -360), (199, 720), (254, 720), (263, -120), (270, 720)]

-- Selected source equation 353 in the original pair table.
def row193 : Integer.Sparse (Fin 271) := [(0, -8), (1, -345), (2, 605), (3, 5600), (4, 1280), (5, -1000), (6, 130), (7, 480), (8, 640), (11, 240), (12, 1280), (13, 2880), (26, 1440), (34, 2160), (42, 1440), (44, 1440), (50, -1200), (51, 2480), (53, -960), (54, -240), (55, -960), (75, 720), (94, 2880), (95, 2880), (143, -960), (240, 1440), (252, 1440), (254, 1440), (270, 1440)]

-- Selected source equation 354 in the original pair table.
def row194 : Integer.Sparse (Fin 271) := [(0, -29), (1, 370), (2, 835), (3, 4080), (5, -1460), (6, 210), (7, 1200), (8, 640), (9, -20), (10, -720), (12, 1280), (13, 3840), (32, -960), (34, 2560), (37, 1440), (51, 3040), (53, -960), (58, -960), (67, 240), (68, 160), (70, 720), (73, 1440), (80, 800), (115, 800), (132, -720), (133, -1920), (179, -720), (186, 2880), (223, 720), (229, 1440), (236, 1440), (245, -960), (246, -240), (258, 1440)]

-- Selected source equation 355 in the original pair table.
def row195 : Integer.Sparse (Fin 271) := [(0, -1), (1, -370), (2, 105), (3, 2400), (4, 720), (5, -40), (7, 480), (12, 1200), (13, 640), (23, -2160), (24, -2160), (25, -1440), (27, 300), (32, -1440), (34, 320), (54, -2880), (62, -960), (66, 60), (111, -720), (113, -720), (130, -480), (131, -1440), (174, 2160), (177, 2160), (179, -720), (249, -720)]

-- Selected source equation 356 in the original pair table.
def row196 : Integer.Sparse (Fin 271) := [(0, -2), (1, -69), (2, 24), (3, 432), (4, 48), (5, -36), (6, 3), (7, 192), (9, -4), (12, 240), (13, 64), (23, -432), (25, -144), (27, 84), (32, -288), (34, 96), (50, -432), (53, -576), (62, -96), (66, 24), (67, 48), (68, 32), (111, -288), (130, -192), (153, -288), (168, 432), (176, 432), (181, -144), (245, -144), (246, -144)]

-- Selected source equation 362 in the original pair table.
def row197 : Integer.Sparse (Fin 271) := [(1, -93), (2, 175), (3, 784), (4, 192), (5, -216), (6, 16), (7, 416), (8, 336), (9, -8), (12, 32), (13, 32), (24, -336), (26, 112), (27, 96), (29, -96), (30, -192), (34, 176), (45, 144), (50, -528), (51, 144), (54, -96), (55, -96), (66, 24), (67, 96), (68, 48), (69, 80), (88, 288), (98, 144), (99, 288), (113, -288), (131, -96), (146, -96), (147, -48), (148, -96), (155, -96), (181, -48), (182, -48), (194, 144), (199, 144), (250, 288), (251, 144), (253, 144)]

-- Selected source equation 363 in the original pair table.
def row198 : Integer.Sparse (Fin 271) := [(0, -7), (1, -580), (2, 570), (3, 6160), (4, 1440), (5, -460), (6, 25), (7, 1440), (8, 480), (10, -720), (12, 2000), (13, 2880), (25, -1440), (26, 1440), (30, -720), (32, -1440), (34, 2080), (37, 2160), (38, 4320), (50, -720), (51, 1520), (53, -2160), (54, -720), (58, -1440), (59, 320), (79, -1440), (80, 240), (82, 2160), (83, 4320), (115, 480), (143, -2160), (184, 2160), (193, 4320), (195, 1440), (201, 4320), (202, 4320), (218, -720), (219, -960)]

-- Selected source equation 364 in the original pair table.
def row199 : Integer.Sparse (Fin 271) := [(0, 21), (1, -705), (2, 350), (3, 6240), (4, 2720), (5, -580), (6, 30), (7, 1920), (8, 960), (10, -720), (11, 240), (12, 480), (13, 640), (26, 3120), (34, 2000), (36, 2160), (39, 4320), (51, 240), (54, -720), (55, -2160), (79, -1440), (80, 240), (81, 2160), (83, 4320), (143, -3120), (226, 4320), (232, 4320), (261, 1440), (262, 4320), (263, -960)]

-- Selected source equation 365 in the original pair table.
def row200 : Integer.Sparse (Fin 271) := [(1, -78), (2, 19), (3, 432), (4, 96), (5, -64), (6, 9), (7, 144), (9, -4), (11, 48), (12, 144), (23, -144), (25, -288), (26, 96), (27, 36), (30, -288), (32, -576), (34, 224), (35, 432), (38, 864), (50, -288), (51, 144), (53, -720), (54, -144), (66, 12), (67, 48), (68, 32), (85, 432), (110, -288), (111, -144), (130, -96), (142, -144), (143, -144), (147, -144), (153, -288), (168, 432), (179, -288), (181, -144), (185, 432), (188, 864), (223, 864), (231, 864), (245, -432), (246, -336), (249, -48), (259, 864), (260, 288)]

-- Selected source equation 368 in the original pair table.
def row201 : Integer.Sparse (Fin 271) := [(0, 1), (1, -98), (2, 113), (3, 1488), (4, 512), (5, -160), (6, 14), (7, 560), (8, 128), (11, 128), (26, 896), (34, 896), (51, 368), (52, 288), (65, 128), (79, -672), (81, 144), (82, 432), (83, 576), (143, -816), (215, 288), (243, 288), (244, 576)]

-- Selected source equation 369 in the original pair table.
def row202 : Integer.Sparse (Fin 271) := [(0, -9), (1, -25), (2, 600), (3, 4480), (4, 1120), (5, -1400), (6, 190), (7, 2400), (8, 480), (9, -40), (11, 640), (24, -480), (26, 1920), (27, 120), (30, -480), (32, -960), (34, 3520), (36, 1440), (50, -480), (51, 2560), (54, -480), (66, 60), (67, 640), (68, 480), (79, -960), (81, 720), (83, 1440), (91, 1440), (110, -480), (111, -240), (113, -480), (131, -480), (143, -3360), (147, -480), (153, -480), (179, -960), (181, -480), (185, 720), (188, 1440), (194, 1440), (233, 2880), (237, 1440), (245, -720), (249, -240), (261, 1440)]

-- Selected source equation 372 in the original pair table.
def row203 : Integer.Sparse (Fin 271) := [(0, -2), (1, -63), (2, 107), (3, 1024), (4, 288), (5, -152), (6, 8), (7, 480), (8, 224), (10, -288), (11, 48), (12, 208), (13, 176), (25, -48), (26, 384), (32, -192), (34, 544), (36, 288), (38, 288), (39, 288), (51, 160), (53, -48), (54, -288), (55, -96), (58, -288), (65, 64), (71, 288), (72, 288), (73, 288), (79, -288), (82, 144), (83, 288), (133, -48), (143, -288), (180, -144), (193, 288), (202, 576), (211, 144), (213, 288), (226, 576), (228, 288), (231, 288), (232, 864), (248, -192)]

-- Selected source equation 373 in the original pair table.
def row204 : Integer.Sparse (Fin 271) := [(0, -11), (1, -15), (2, 415), (3, 4080), (4, 880), (5, -980), (6, 145), (7, 640), (8, 480), (11, 320), (12, 880), (13, 2320), (26, 1280), (32, -960), (34, 2320), (36, 1440), (38, 1440), (39, 1440), (51, 2080), (53, -720), (54, -1440), (55, -480), (79, -960), (80, 320), (81, 720), (83, 1440), (115, 320), (132, -240), (133, -480), (143, -1920), (179, -1440), (185, 1440), (201, 2880), (225, 1440), (233, 1440), (237, 2880), (245, -480), (249, -960), (258, 1440), (259, 1440), (261, 1440), (262, 4320)]

-- Selected source equation 374 in the original pair table.
def row205 : Integer.Sparse (Fin 271) := [(0, 7), (1, -142), (2, 152), (3, 544), (4, 256), (5, -128), (6, 7), (7, 192), (8, 224), (9, -4), (12, 48), (23, -336), (24, -960), (26, 32), (27, 324), (29, -384), (30, -288), (34, 48), (46, 144), (50, -144), (51, 64), (54, -528), (66, 48), (67, 32), (68, 16), (69, 32), (98, 576), (112, -192), (113, -480), (131, -96), (146, -192), (147, -192), (181, -48), (234, 288), (241, 144), (267, 288)]

-- Selected source equation 377 in the original pair table.
def row206 : Integer.Sparse (Fin 271) := [(0, -18), (1, 295), (2, 700), (3, 3040), (4, 160), (5, -1260), (6, 135), (7, 2240), (8, 720), (9, -60), (12, 320), (13, 1440), (23, -240), (26, 160), (27, 60), (34, 3200), (37, 720), (51, 2960), (53, -240), (54, -240), (58, -720), (59, 560), (66, 60), (67, 800), (68, 400), (79, -960), (80, 80), (82, 1440), (90, 720), (112, -720), (113, -480), (115, 400), (133, -240), (143, -480), (147, -240), (154, -480), (171, 720), (179, -480), (181, -240), (195, 1440), (207, 720), (219, -240), (224, 1440), (236, 720), (237, 1440), (249, -240)]

-- Selected source equation 378 in the original pair table.
def row207 : Integer.Sparse (Fin 271) := [(0, -24), (1, 360), (2, 715), (3, 4240), (4, 80), (5, -1360), (6, 175), (7, 1760), (8, 800), (10, -720), (11, 80), (12, 1280), (13, 4400), (26, 160), (32, -480), (34, 3920), (40, 720), (51, 3440), (53, -720), (58, -1920), (59, 640), (71, 720), (72, 720), (73, 720), (79, -480), (80, 960), (82, 720), (115, 1360), (132, -960), (133, -1680), (143, -480), (179, -720), (186, 1440), (196, 1440), (207, 720), (209, 720), (225, 720), (227, 1440), (233, 720), (239, 720), (245, -480), (258, 720)]

-- Selected source equation 379 in the original pair table.
def row208 : Integer.Sparse (Fin 271) := [(0, -31), (1, -330), (2, 410), (3, 6720), (4, 160), (5, -400), (6, 15), (7, 2320), (8, 320), (10, -2640), (12, 3120), (13, 5760), (23, -240), (26, 320), (27, 60), (32, -960), (33, 320), (34, 3680), (37, 1440), (50, -960), (51, 1760), (53, -960), (54, -480), (58, -3360), (59, 640), (70, 720), (71, 720), (72, 1440), (73, 1440), (80, 640), (82, 1440), (115, 640), (132, -720), (133, -720), (143, -480), (160, -480), (184, 2880), (186, 2880), (191, 1440)]

-- Selected source equation 381 in the original pair table.
def row209 : Integer.Sparse (Fin 271) := [(0, -6), (1, -205), (2, 175), (3, 2560), (4, 720), (5, -220), (6, 20), (7, 400), (8, 240), (10, -120), (12, 760), (13, 720), (23, -120), (25, -240), (26, 800), (27, 30), (30, -240), (32, -1440), (33, 160), (34, 560), (35, 720), (38, 1440), (50, -480), (51, 240), (53, -1200), (54, -960), (58, -480), (70, 360), (72, 720), (79, -960), (81, 720), (83, 1440), (132, -360), (143, -960), (160, -240), (184, 720), (185, 1440), (187, 1440), (189, 720), (193, 720), (201, 1440), (202, 2880), (218, -720), (219, -480)]

-- Selected source equation 382 in the original pair table.
def row210 : Integer.Sparse (Fin 271) := [(0, 9), (1, -570), (2, 380), (3, 6240), (4, 2400), (5, -400), (6, 45), (7, 1360), (8, 160), (11, 480), (12, 480), (13, 640), (26, 3040), (34, 3040), (36, 1440), (39, 2880), (51, 1280), (54, -1440), (55, -1440), (65, 160), (71, 720), (73, 1440), (79, -1440), (82, 1440), (83, 2880), (133, -720), (143, -2880), (226, 1440), (228, 1440), (232, 5760), (237, 2880), (262, 2880), (263, -960)]

-- Selected source equation 383 in the original pair table.
def row211 : Integer.Sparse (Fin 271) := [(0, -12), (1, -195), (2, 375), (3, 3920), (4, 800), (5, -900), (6, 130), (7, 880), (8, 480), (10, -240), (11, 480), (12, 1120), (13, 1680), (23, -240), (25, -1920), (26, 1280), (27, 60), (30, -960), (32, -960), (34, 2480), (37, 1440), (38, 2880), (50, -1440), (51, 1920), (53, -3120), (55, -480), (58, -960), (70, 720), (72, 1440), (80, 320), (85, 1440), (86, 2880), (110, -1920), (115, 320), (132, -960), (133, -480), (142, -1440), (143, -1440), (147, -480), (179, -480), (186, 1440), (188, 2880), (223, 1440), (229, 1440), (231, 5760), (236, 2880), (245, -1440), (246, -960), (259, 2880)]

-- Selected source equation 384 in the original pair table.
def row212 : Integer.Sparse (Fin 271) := [(0, -13), (1, -150), (2, 375), (3, 3840), (4, 800), (5, -700), (6, 30), (7, 2960), (8, 960), (10, -240), (12, 160), (13, 80), (23, -240), (24, -480), (25, -480), (26, 1760), (27, 60), (34, 3680), (37, 720), (50, -480), (51, 1120), (53, -720), (54, -480), (58, -480), (63, -960), (65, 800), (70, 720), (71, 1440), (79, -1920), (82, 1440), (96, 1440), (132, -240), (143, -480), (159, -480), (191, 1440), (211, 1440), (224, 1440)]

-- Selected source equation 385 in the original pair table.
def row213 : Integer.Sparse (Fin 271) := [(0, -9), (1, -280), (2, 565), (3, 7040), (4, 2160), (5, -860), (6, 70), (7, 3120), (8, 800), (11, 640), (12, 80), (13, 160), (26, 3920), (32, -480), (33, 320), (34, 4800), (36, 720), (51, 1920), (55, -240), (65, 640), (71, 720), (79, -2880), (81, 720), (82, 1440), (83, 2880), (133, -240), (143, -4320), (161, -480), (190, 1440), (213, 1440), (215, 1440), (233, 1440), (244, 1440)]

-- Selected source equation 386 in the original pair table.
def row214 : Integer.Sparse (Fin 271) := [(0, -12), (1, -20), (2, 615), (3, 4880), (4, 1120), (5, -1320), (6, 175), (7, 1760), (8, 720), (10, -240), (11, 640), (12, 320), (13, 1040), (24, -240), (26, 1840), (27, 60), (30, -480), (32, -480), (34, 3840), (40, 720), (50, -960), (51, 3200), (55, -480), (58, -960), (59, 160), (71, 720), (79, -480), (80, 80), (82, 720), (83, 1440), (91, 1440), (95, 1440), (110, -960), (115, 240), (133, -240), (143, -3120), (147, -480), (179, -480), (186, 720), (188, 1440), (196, 1440), (227, 720), (233, 1440), (239, 1440), (245, -720)]

-- Selected source equation 387 in the original pair table.
def row215 : Integer.Sparse (Fin 271) := [(0, -2), (1, -39), (2, 93), (3, 976), (4, 352), (5, -116), (6, 6), (7, 272), (8, 192), (10, -144), (12, 112), (13, 192), (26, 416), (32, -288), (33, 64), (34, 256), (35, 144), (39, 288), (51, 64), (53, -144), (54, -144), (55, -192), (58, -192), (70, 144), (73, 288), (79, -384), (81, 288), (83, 576), (132, -48), (143, -384), (159, -96), (180, -288), (189, 288), (202, 576), (212, 288), (213, 576), (223, 288), (226, 576), (232, 1152), (248, -192)]

-- Selected source equation 388 in the original pair table.
def row216 : Integer.Sparse (Fin 271) := [(0, -13), (1, 80), (2, 605), (3, 4480), (4, 800), (5, -1220), (6, 170), (7, 1200), (8, 640), (12, 720), (13, 2880), (26, 960), (34, 3040), (37, 720), (39, 1440), (51, 2720), (53, -480), (54, -720), (55, -960), (58, -480), (59, 160), (79, -960), (80, 560), (82, 1440), (83, 2880), (115, 560), (132, -480), (133, -960), (143, -1440), (179, -720), (195, 1440), (201, 2880), (224, 720), (236, 1440), (237, 2880), (249, -960), (258, 1440), (262, 5760)]

-- Selected source equation 389 in the original pair table.
def row217 : Integer.Sparse (Fin 271) := [(0, -5), (1, 76), (2, 127), (3, 656), (5, -216), (6, 24), (7, 384), (8, 128), (10, -48), (12, 112), (13, 512), (23, -48), (27, 12), (34, 720), (50, -96), (51, 544), (53, -192), (58, -240), (59, 160), (61, -192), (70, 144), (71, 288), (79, -192), (80, 32), (90, 288), (115, 112), (132, -96), (133, -96), (147, -96), (157, -96), (169, 288), (179, -96), (207, 288), (224, 288), (227, 288)]

-- Selected source equation 390 in the original pair table.
def row218 : Integer.Sparse (Fin 271) := [(0, -29), (1, 550), (2, 855), (3, 4480), (5, -1500), (6, 190), (7, 1680), (8, 960), (10, -720), (12, 1120), (13, 5120), (31, 320), (34, 3680), (51, 4160), (58, -1920), (59, 640), (70, 720), (71, 1440), (73, 1440), (79, -960), (80, 880), (115, 1680), (132, -720), (133, -2400), (157, -480), (169, 1440), (179, -720), (209, 2880), (224, 720), (227, 2880), (258, 1440)]

-- Selected source equation 393 in the original pair table.
def row219 : Integer.Sparse (Fin 271) := [(0, -38), (1, -325), (2, 555), (3, 5040), (5, -820), (6, 30), (7, 2880), (8, 1440), (9, -20), (10, -2160), (12, 2720), (13, 4000), (23, -1440), (27, 360), (34, 1760), (37, 2160), (50, -4320), (53, -4320), (54, -720), (58, -3600), (66, 60), (67, 240), (68, 160), (70, 4320), (72, 4320), (80, 240), (111, -720), (130, -480), (132, -2400), (153, -1440), (168, 2160), (181, -720), (193, 2160), (229, 1440), (246, -720), (248, -240)]

-- Selected source equation 394 in the original pair table.
def row220 : Integer.Sparse (Fin 271) := [(0, -14), (1, -100), (2, 255), (3, 3440), (4, 400), (5, -660), (6, 45), (7, 3040), (8, 640), (10, -240), (12, 640), (13, 960), (24, -240), (26, 960), (27, 60), (33, 160), (34, 3840), (36, 1440), (50, -480), (51, 1520), (54, -480), (58, -480), (59, 320), (65, 160), (71, 720), (79, -480), (81, 1440), (82, 3600), (143, -1200), (160, -480), (184, 1440), (190, 1440)]

-- Selected source equation 395 in the original pair table.
def row221 : Integer.Sparse (Fin 271) := [(0, -3), (1, -31), (2, 91), (3, 656), (4, 48), (5, -164), (6, 9), (7, 592), (8, 256), (9, -8), (10, -192), (12, 80), (13, 64), (24, -192), (26, 96), (27, 48), (34, 512), (36, 288), (50, -288), (51, 144), (54, -96), (58, -240), (65, 32), (66, 12), (67, 128), (68, 96), (71, 576), (79, -96), (82, 144), (111, -48), (113, -96), (131, -96), (143, -48), (153, -96), (181, -96), (193, 144), (194, 288), (226, 288), (228, 288), (248, -48)]

-- Selected source equation 396 in the original pair table.
def row222 : Integer.Sparse (Fin 271) := [(0, -12), (1, -195), (2, 775), (3, 6320), (4, 1840), (5, -1040), (6, 70), (7, 2800), (8, 1280), (10, -240), (11, 240), (12, 80), (13, 80), (24, -240), (26, 2880), (27, 60), (30, -240), (32, -960), (33, 160), (34, 3280), (36, 1440), (50, -480), (51, 1760), (54, -480), (58, -480), (65, 160), (71, 720), (79, -3840), (81, 2880), (82, 2880), (83, 4320), (143, -4080), (160, -480), (184, 720), (187, 1440), (190, 1440), (218, -720)]

-- Selected source equation 397 in the original pair table.
def row223 : Integer.Sparse (Fin 271) := [(0, -1), (1, -310), (2, 730), (3, 6400), (4, 2080), (5, -1120), (6, 105), (7, 3040), (8, 960), (11, 560), (26, 3520), (34, 4160), (51, 2240), (52, 1440), (65, 160), (79, -2880), (81, 1440), (82, 3600), (83, 4320), (143, -4800), (243, 1440), (244, 1440)]

-- Selected source equation 398 in the original pair table.
def row224 : Integer.Sparse (Fin 271) := [(0, -14), (1, -15), (2, 45), (3, 2320), (5, -440), (6, 70), (7, 1680), (8, 640), (9, -60), (10, -480), (23, -480), (25, -240), (26, 640), (27, 120), (34, 2480), (35, 720), (51, 480), (53, -1200), (54, -240), (63, -480), (65, 400), (66, 60), (67, 800), (68, 400), (70, 1440), (81, 1440), (112, -720), (113, -480), (132, -480), (143, -960), (154, -480), (159, -480), (171, 720), (181, -240), (189, 1440), (211, 720), (219, -240), (223, 720), (226, 1440), (248, -240)]

-- Selected source equation 399 in the original pair table.
def row225 : Integer.Sparse (Fin 271) := [(0, -3), (1, 15), (2, 108), (3, 768), (4, 144), (5, -196), (6, 20), (7, 480), (8, 176), (11, 16), (12, 32), (13, 112), (26, 272), (33, 32), (34, 768), (36, 144), (51, 480), (55, -48), (58, -48), (59, 32), (65, 64), (71, 288), (79, -384), (81, 144), (82, 432), (115, 16), (133, -96), (143, -288), (161, -96), (190, 288), (213, 144), (215, 144), (233, 144), (244, 144)]

-- Selected source equation 400 in the original pair table.
def row226 : Integer.Sparse (Fin 271) := [(0, -33), (1, 235), (2, 950), (3, 4480), (4, 160), (5, -1600), (6, 100), (7, 3680), (8, 2240), (10, -2400), (12, 1360), (13, 2560), (26, 160), (32, -480), (33, 160), (34, 3440), (37, 720), (51, 2240), (53, -240), (58, -3840), (59, 160), (70, 1440), (71, 2880), (72, 1440), (73, 2880), (79, -1440), (80, 320), (82, 1440), (115, 400), (132, -720), (133, -960), (143, -480), (159, -480), (180, -720), (191, 1440), (212, 720), (213, 1440), (224, 720)]

-- Selected source equation 401 in the original pair table.
def row227 : Integer.Sparse (Fin 271) := [(0, -29), (1, -45), (2, 1290), (3, 6720), (4, 960), (5, -1080), (6, 60), (7, 1680), (8, 1440), (10, -720), (12, 2160), (13, 4400), (30, -720), (32, -1440), (34, 1680), (41, 4320), (50, -2880), (51, 3120), (58, -2880), (59, 480), (79, -1440), (80, 240), (84, 4320), (115, 960), (184, 2160), (198, 4320), (200, 4320), (218, -720)]

-- Selected source equation 402 in the original pair table.
def row228 : Integer.Sparse (Fin 271) := [(0, 3), (1, -230), (2, 1095), (3, 6480), (4, 1520), (5, -1720), (6, 150), (7, 3040), (8, 1760), (11, 240), (26, 2560), (34, 4000), (51, 2640), (56, 1440), (65, 800), (79, -3360), (84, 2880), (143, -720), (215, 1440), (269, 4320)]

-- Selected source equation 403 in the original pair table.
def row229 : Integer.Sparse (Fin 271) := [(0, -16), (1, 140), (2, 1155), (3, 4000), (4, 880), (5, -1820), (6, 95), (7, 3760), (8, 3040), (12, 80), (13, 160), (26, 1120), (30, -960), (32, -960), (34, 2480), (41, 1440), (50, -960), (51, 1120), (55, -240), (58, -960), (65, 480), (74, 1440), (79, -2400), (84, 1440), (89, 720), (99, 1440), (133, -240), (148, -720), (180, -720), (198, 2880), (211, 720), (213, 1440), (230, 1440)]

-- Selected source equation 404 in the original pair table.
def row230 : Integer.Sparse (Fin 271) := [(0, -1), (1, 64), (2, 143), (3, 304), (4, 32), (5, -412), (6, 60), (7, 48), (8, 256), (9, -4), (11, 32), (12, 16), (25, -96), (26, 64), (30, -192), (32, -192), (34, 288), (38, 288), (51, 608), (53, -96), (67, 16), (69, 64), (85, 144), (110, -192), (142, -48), (143, -96), (147, -144), (149, 288), (179, -144), (188, 576), (223, 144), (231, 288), (245, -192), (246, -48), (258, 288), (259, 288)]

-- Selected source equation 405 in the original pair table.
def row231 : Integer.Sparse (Fin 271) := [(0, -27), (1, 505), (2, 1080), (3, 3840), (5, -2140), (6, 250), (7, 2160), (8, 1920), (9, -20), (12, 560), (13, 2640), (34, 3680), (50, -480), (51, 4080), (53, -240), (58, -1200), (59, 720), (67, 160), (69, 560), (80, 400), (84, 1440), (115, 800), (132, -240), (133, -960), (154, -480), (155, -480), (173, 720), (182, -720), (199, 1440), (200, 1440), (207, 720), (219, -240)]

-- Selected source equation 406 in the original pair table.
def row232 : Integer.Sparse (Fin 271) := [(0, -29), (1, 535), (2, 1010), (3, 3600), (4, 160), (5, -2000), (6, 240), (7, 1600), (8, 1600), (12, 560), (13, 2720), (26, 80), (34, 3120), (41, 720), (50, -480), (51, 4240), (55, -480), (58, -1920), (59, 800), (74, 720), (80, 240), (84, 720), (94, 720), (95, 720), (115, 880), (133, -960), (200, 1440), (207, 720), (209, 720), (230, 1440), (264, 720)]

-- Selected source equation 407 in the original pair table.
def row233 : Integer.Sparse (Fin 271) := [(0, -21), (1, 275), (2, 450), (3, 1440), (4, 160), (5, -1240), (6, 200), (7, 640), (8, 1040), (9, -20), (11, 160), (12, 160), (13, 720), (25, -240), (26, 320), (34, 1360), (38, 720), (50, -480), (51, 2000), (53, -480), (55, -480), (58, -480), (67, 80), (69, 320), (72, 720), (80, 160), (86, 720), (110, -480), (115, 400), (132, -240), (133, -480), (142, -240), (143, -480), (188, 1440), (231, 2160), (236, 720), (245, -480), (246, -240), (259, 720)]

-- Selected source equation 408 in the original pair table.
def row234 : Integer.Sparse (Fin 271) := [(0, -23), (1, -105), (2, 1130), (3, 5680), (4, 1200), (5, -1300), (6, 90), (7, 1760), (8, 2000), (10, -240), (12, 1600), (13, 2800), (24, -240), (26, 480), (27, 60), (30, -720), (32, -1920), (33, 320), (34, 1040), (38, 1440), (41, 1440), (50, -3120), (51, 1920), (54, -480), (55, -960), (58, -2400), (59, 320), (72, 720), (74, 1440), (79, -960), (83, 1440), (84, 1440), (115, 480), (133, -720), (143, -480), (160, -480), (184, 2160), (187, 1440), (188, 2880), (192, 1440), (198, 2880), (200, 1440), (218, -720)]

-- Selected source equation 409 in the original pair table.
def row235 : Integer.Sparse (Fin 271) := [(0, -14), (1, 15), (2, 500), (3, 3840), (4, 960), (5, -1260), (6, 175), (7, 480), (8, 960), (9, -20), (12, 960), (13, 2880), (24, -480), (26, 800), (27, 120), (30, -480), (32, -960), (34, 2080), (38, 1440), (41, 1440), (50, -960), (51, 2080), (53, -960), (54, -480), (55, -2400), (66, 60), (67, 80), (69, 320), (80, 640), (91, 1440), (110, -480), (111, -240), (113, -480), (115, 640), (131, -480), (132, -480), (133, -960), (147, -480), (153, -480), (155, -960), (170, 720), (172, 1440), (179, -960), (181, -480), (182, -240), (185, 720), (188, 1440), (200, 1440), (201, 1440), (225, 2880), (230, 1440), (245, -720), (249, -240), (259, 1440), (263, -720), (264, 2880)]

-- Selected source equation 410 in the original pair table.
def row236 : Integer.Sparse (Fin 271) := [(0, -2), (1, 11), (2, 115), (3, 424), (4, 64), (5, -170), (6, 8), (7, 384), (8, 296), (12, 32), (13, 40), (25, -24), (26, 104), (30, -48), (32, -72), (33, 16), (34, 232), (38, 72), (50, -48), (51, 80), (53, -48), (58, -48), (63, -48), (65, 40), (72, 72), (79, -240), (83, 144), (84, 144), (92, 72), (99, 144), (132, -24), (143, -48), (148, -72), (159, -48), (180, -72), (192, 144), (198, 144), (211, 72), (212, 72), (213, 144), (225, 144)]

-- Selected source equation 412 in the original pair table.
def row237 : Integer.Sparse (Fin 271) := [(0, -6), (1, 72), (2, 193), (3, 624), (4, 80), (5, -340), (6, 31), (7, 448), (8, 384), (11, 32), (12, 16), (13, 64), (26, 176), (32, -96), (34, 384), (51, 368), (58, -48), (65, 32), (73, 144), (79, -288), (83, 432), (84, 288), (115, 16), (133, -48), (143, -288), (213, 288), (233, 144), (258, 144), (269, 144)]

-- Selected source equation 419 in the original pair table.
def row238 : Integer.Sparse (Fin 271) := [(0, 27), (1, -905), (2, 610), (3, 2960), (4, 2000), (5, -400), (6, 20), (7, 240), (8, 560), (9, -20), (12, 560), (23, -240), (24, -1680), (26, 160), (27, 900), (30, -2400), (46, 720), (50, -5040), (51, 400), (55, -960), (66, 180), (67, 80), (69, 80), (111, -240), (113, -1440), (136, 720), (137, 1440), (139, 1440), (148, -960), (155, -480), (181, -240), (182, -240), (234, 720), (256, 720), (257, 1440)]

-- Selected source equation 422 in the original pair table.
def row239 : Integer.Sparse (Fin 271) := [(0, 33), (1, -685), (2, 305), (3, 6480), (4, 2720), (5, -380), (6, 45), (7, 1120), (8, 80), (12, 400), (13, 400), (24, -240), (26, 3360), (30, -720), (32, -480), (33, 640), (34, 2000), (43, 1440), (51, 1040), (65, 640), (79, -960), (88, 720), (91, 1440), (107, 1440), (214, 1440), (215, 1440)]

-- Selected source equation 423 in the original pair table.
def row240 : Integer.Sparse (Fin 271) := [(0, -3), (1, -39), (2, 91), (3, 768), (4, 192), (5, -68), (6, 5), (7, 144), (8, 64), (12, 176), (13, 176), (25, -192), (26, 256), (30, -144), (32, -672), (33, 64), (34, 224), (42, 288), (50, -48), (51, 160), (58, -192), (63, -144), (65, 64), (79, -192), (88, 144), (95, 288), (96, 288), (101, 144), (102, 288), (133, -48), (180, -144), (211, 144), (213, 288), (216, 288)]

-- Selected source equation 425 in the original pair table.
def row241 : Integer.Sparse (Fin 271) := [(0, -11), (1, -790), (2, 850), (3, 5920), (4, 1280), (5, -520), (6, 35), (7, 640), (8, 320), (9, -20), (12, 2000), (13, 1440), (23, -1200), (25, -2880), (26, 480), (27, 720), (30, -3840), (32, -3840), (34, 400), (50, -5760), (51, 800), (53, -960), (54, -2160), (63, -2880), (66, 180), (67, 80), (68, 80), (111, -240), (112, -960), (113, -480), (120, 720), (122, 2880), (125, 1440), (148, -1920), (154, -480), (182, -480), (206, 1440), (234, 1440)]

-- Selected source equation 430 in the original pair table.
def row242 : Integer.Sparse (Fin 271) := [(0, -21), (1, 80), (2, 365), (3, 4080), (5, -900), (6, 170), (7, 560), (9, -60), (12, 1200), (13, 4160), (23, -960), (25, -960), (27, 240), (30, -960), (32, -1920), (34, 1760), (51, 2240), (53, -1440), (62, -2640), (66, 180), (67, 240), (68, 160), (110, -960), (111, -240), (112, -480), (113, -480), (116, 720), (124, 1440), (130, -720), (145, 1440), (147, -1920), (179, -720), (223, 720), (245, -960), (246, -240), (258, 1440)]

-- Selected source equation 433 in the original pair table.
def row243 : Integer.Sparse (Fin 271) := [(0, -26), (1, -335), (2, 380), (3, 3600), (4, 160), (5, -320), (6, 5), (7, 1040), (8, 480), (9, -20), (10, -960), (12, 1920), (13, 1920), (23, -1200), (24, -480), (27, 660), (34, 160), (37, 720), (46, 1440), (50, -3120), (51, 80), (53, -480), (54, -1680), (58, -1200), (66, 120), (67, 160), (111, -720), (112, -480), (113, -240), (120, 1440), (136, 720), (153, -480), (181, -480), (193, 720), (234, 1440), (235, 1440), (248, -240)]

-- Selected source equation 434 in the original pair table.
def row244 : Integer.Sparse (Fin 271) := [(0, -9), (1, -10), (2, -35), (3, 3040), (4, 800), (5, -320), (6, 40), (7, 2240), (8, 320), (9, -20), (12, 320), (13, 80), (23, -480), (25, -2160), (26, 1440), (32, -480), (34, 960), (37, 720), (50, -480), (51, 160), (53, -2640), (63, -960), (67, 240), (89, 2880), (111, -480), (143, -960), (154, -480), (193, 720), (206, 1440), (219, -240)]

-- Selected source equation 436 in the original pair table.
def row245 : Integer.Sparse (Fin 271) := [(0, 6), (1, -240), (2, 565), (3, 4160), (4, 1680), (5, -480), (6, 35), (7, 800), (8, 880), (9, -20), (24, -240), (26, 1520), (27, 60), (30, -480), (34, 320), (36, 720), (45, 1440), (50, -1440), (51, 800), (55, -1680), (67, 160), (69, 80), (79, -1200), (99, 1440), (111, -240), (113, -240), (143, -960), (155, -480), (226, 720), (250, 1440), (255, 1440), (257, 1440), (263, -240)]

-- Selected source equation 444 in the original pair table.
def row246 : Integer.Sparse (Fin 271) := [(0, 1), (1, -490), (2, 640), (3, 3520), (4, 720), (5, -740), (6, 65), (7, 880), (8, 1120), (9, -40), (10, -480), (11, 80), (12, 800), (13, 720), (23, -480), (24, -240), (26, 480), (27, 420), (29, -240), (30, -720), (34, 560), (39, 720), (42, 720), (50, -2160), (51, 800), (54, -1200), (66, 120), (67, 160), (69, 240), (88, 1440), (112, -480), (113, -960), (126, 1440), (138, 720), (146, -480), (147, -240), (148, -240), (181, -240), (232, 720), (234, 720), (240, 720), (248, -240), (253, 720)]

-- Selected source equation 445 in the original pair table.
def row247 : Integer.Sparse (Fin 271) := [(0, -14), (1, -145), (2, 360), (3, 4400), (4, 640), (5, -760), (6, 115), (7, 1120), (8, 240), (9, -20), (12, 560), (13, 2640), (25, -240), (26, 1360), (33, 560), (34, 2320), (38, 720), (51, 2480), (53, -1440), (59, 560), (63, -480), (67, 160), (69, 80), (80, 80), (91, 1440), (95, 1440), (106, 720), (113, -480), (115, 400), (143, -480), (154, -480), (201, 720), (207, 720), (210, 1440), (219, -240)]

-- Selected source equation 446 in the original pair table.
def row248 : Integer.Sparse (Fin 271) := [(0, 3), (1, -80), (2, 51), (3, 608), (4, 232), (5, -60), (6, 6), (7, 80), (8, 72), (11, 24), (12, 64), (13, 64), (26, 240), (27, 6), (30, -72), (34, 144), (42, 72), (44, 72), (50, -120), (51, 64), (55, -96), (56, 72), (79, -48), (99, 216), (135, 144), (143, -48), (147, -24), (148, -72), (240, 72), (255, 144), (269, 72), (270, 72)]

-- Selected source equation 447 in the original pair table.
def row249 : Integer.Sparse (Fin 271) := [(0, -29), (1, -5), (2, 660), (3, 5920), (4, 560), (5, -800), (6, 110), (7, 480), (8, 240), (12, 1840), (13, 5520), (26, 880), (32, -480), (33, 640), (34, 2320), (41, 720), (50, -240), (51, 3120), (58, -960), (59, 640), (80, 240), (90, 1440), (91, 720), (94, 1440), (95, 720), (106, 720), (108, 720), (115, 800), (133, -480), (147, -240), (200, 720), (207, 720), (208, 1440), (209, 720)]

-- Selected source equation 448 in the original pair table.
def row250 : Integer.Sparse (Fin 271) := [(0, -36), (1, 35), (2, 615), (3, 3440), (5, -860), (6, 100), (7, 560), (8, 800), (9, -20), (12, 1200), (13, 3360), (32, -960), (34, 640), (37, 720), (50, -1440), (51, 1840), (53, -1200), (58, -1440), (67, 80), (69, 160), (80, 160), (94, 1440), (113, -480), (115, 400), (132, -480), (147, -480), (153, -480), (235, 1440), (236, 720), (245, -480), (246, -240), (254, 1440)]

-- Selected source equation 454 in the original pair table.
def row251 : Integer.Sparse (Fin 271) := [(0, -18), (1, -455), (2, 160), (3, 7200), (4, 1520), (5, -260), (6, 45), (11, 80), (12, 1280), (13, 3680), (26, 3120), (33, 2400), (34, 1920), (40, 720), (51, 880), (54, -480), (55, -720), (59, 720), (80, 80), (115, 160), (119, 1440), (128, 1440), (135, 1440), (148, -480), (196, 720), (208, 1440)]

-- Selected source equation 455 in the original pair table.
def row252 : Integer.Sparse (Fin 271) := [(0, -38), (1, -205), (2, 240), (3, 5840), (4, 160), (5, -560), (6, 75), (7, 640), (8, 160), (9, -20), (12, 1360), (13, 4160), (23, -240), (26, 2240), (27, 180), (33, 1920), (34, 2320), (37, 720), (50, -1440), (51, 1280), (53, -480), (54, -1200), (59, 560), (63, -1440), (66, 120), (68, 80), (69, 80), (80, 320), (112, -480), (115, 400), (118, 1440), (119, 1440), (126, 720), (131, -720), (146, -240), (148, -960), (154, -480), (182, -480), (195, 720), (210, 1440), (249, -240), (265, 1440)]

-- Selected source equation 460 in the original pair table.
def row253 : Integer.Sparse (Fin 271) := [(0, -3), (1, -280), (2, 45), (3, 3440), (4, 1000), (5, -210), (6, 30), (7, 280), (8, 120), (11, 160), (12, 80), (13, 800), (26, 2200), (33, 960), (34, 1240), (50, -120), (51, 200), (52, 360), (54, -360), (55, -480), (63, -720), (65, 360), (99, 360), (119, 720), (128, 720), (143, -120), (148, -480), (214, 720), (240, 360), (243, 360), (270, 360)]

-- Selected source equation 461 in the original pair table.
def row254 : Integer.Sparse (Fin 271) := [(0, -22), (1, -190), (2, 355), (3, 5680), (4, 800), (5, -620), (6, 95), (7, 1280), (8, 240), (9, -40), (11, 80), (12, 480), (13, 2400), (24, -240), (26, 3040), (27, 120), (30, -240), (32, -480), (33, 1520), (34, 2400), (36, 720), (50, -1440), (51, 1120), (54, -960), (63, -2400), (65, 560), (66, 120), (67, 160), (68, 240), (112, -1200), (113, -240), (118, 1440), (119, 1440), (126, 720), (131, -480), (135, 720), (147, -240), (148, -1200), (180, -480), (182, -240), (216, 1440), (228, 720), (238, 720), (240, 720), (248, -240), (251, 720)]

def rows (k : Fin 255) : Integer.Sparse (Fin 271) := (#[row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83, row84, row85, row86, row87, row88, row89, row90, row91, row92, row93, row94, row95, row96, row97, row98, row99, row100, row101, row102, row103, row104, row105, row106, row107, row108, row109, row110, row111, row112, row113, row114, row115, row116, row117, row118, row119, row120, row121, row122, row123, row124, row125, row126, row127, row128, row129, row130, row131, row132, row133, row134, row135, row136, row137, row138, row139, row140, row141, row142, row143, row144, row145, row146, row147, row148, row149, row150, row151, row152, row153, row154, row155, row156, row157, row158, row159, row160, row161, row162, row163, row164, row165, row166, row167, row168, row169, row170, row171, row172, row173, row174, row175, row176, row177, row178, row179, row180, row181, row182, row183, row184, row185, row186, row187, row188, row189, row190, row191, row192, row193, row194, row195, row196, row197, row198, row199, row200, row201, row202, row203, row204, row205, row206, row207, row208, row209, row210, row211, row212, row213, row214, row215, row216, row217, row218, row219, row220, row221, row222, row223, row224, row225, row226, row227, row228, row229, row230, row231, row232, row233, row234, row235, row236, row237, row238, row239, row240, row241, row242, row243, row244, row245, row246, row247, row248, row249, row250, row251, row252, row253, row254])[k.val]!

def target0 : Integer.Sparse (Fin 271) := [(0, -9035712), (57, 45360), (5, 2721600), (6, -181440), (66, -2177280), (2, -8573040), (67, -2903040), (7, -5806080), (8, -39191040), (113, 52254720), (3, 8709120), (17, -19595520), (20, -78382080), (23, -8709120), (24, 39191040), (12, -1451520), (134, -78382080), (137, -78382080), (138, -470292480), (4, 26127360), (27, -16873920), (1, -36106560), (144, 6531840), (146, 78382080), (28, -78382080), (29, 137168640), (30, -26127360), (150, -352719360)]

def target1 : Integer.Sparse (Fin 271) := [(0, -8727264), (5, 4536000), (6, 272160), (62, -8709120), (66, -3265920), (2, -9253440), (7, -8709120), (34, -5806080), (8, -39191040), (113, 52254720), (3, 17418240), (13, -5806080), (17, -19595520), (20, -78382080), (23, -13063680), (24, 39191040), (12, -4354560), (134, -78382080), (137, -78382080), (138, -470292480), (4, 26127360), (27, -13608000), (1, -35199360), (146, 78382080), (28, -78382080), (29, 137168640), (30, -26127360), (150, -352719360)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged3 : Integer.Sparse (Fin 271) := [(0, -1107976740), (1, 32648566440), (2, -6775888140), (3, -68779985280), (4, -48839748480), (12, -19940236800), (25, 5449439520), (26, -12674317440), (30, 16225194240)]

def pairMerged4 : Integer.Sparse (Fin 271) := [(0, -1106262412), (1, 32246500790), (2, -8984897230), (3, -45516416000), (4, -40511738560), (5, 1238915520), (7, -1651887360), (8, -8259436800), (12, -5004677440), (13, 7467779680), (24, 4955662080), (25, 5449439520), (26, -12674317440), (29, 9911324160), (30, 16225194240)]

def pairMerged5 : Integer.Sparse (Fin 271) := [(0, -1635103252), (1, 28145386470), (2, -10021718190), (3, -62706631680), (4, -40211198400), (5, 6319438920), (6, -499592880), (7, -7432049280), (8, -11149517760), (12, -10709704320), (13, 7467779680), (23, 4335121440), (24, 13625904960), (25, 5449439520), (26, -12674317440), (27, -5995114560), (29, 9911324160), (30, 16225194240)]

def pairMerged6 : Integer.Sparse (Fin 271) := [(0, -489718332), (1, 5557056000), (2, -1061293740), (3, -6003104640), (4, -8311991040), (12, -2308886400), (14, -1074388320), (15, -2077997760), (17, -4297553280), (20, -4155995520), (23, 3557701440), (24, 2077997760), (25, 7115402880), (27, -1056693600), (29, 2817849600), (30, 8500734720)]

def pairMerged7 : Integer.Sparse (Fin 271) := [(0, -89710500), (1, 3349521720), (2, 102819000), (3, -2519143680), (4, -3545995200), (12, -1032618240), (16, 676535760), (17, 1353071520), (18, -1582908480), (22, -3165816960), (23, -902047680), (27, 169133940), (29, -451023840)]

def pairMerged8 : Integer.Sparse (Fin 271) := [(0, -579428832), (1, 8906577720), (2, -958474740), (3, -8522248320), (4, -11857986240), (12, -3341504640), (14, -1074388320), (15, -2077997760), (16, 676535760), (17, -2944481760), (18, -1582908480), (20, -4155995520), (22, -3165816960), (23, 2655653760), (24, 2077997760), (25, 7115402880), (27, -887559660), (29, 2366825760), (30, 8500734720)]

def pairMerged9 : Integer.Sparse (Fin 271) := [(0, 102527280), (1, -2538944880), (2, 401060880), (3, 2734060800), (4, 2953355520), (12, 427671360), (15, -328942080), (17, 1394798400), (19, 1559269440), (20, 1559269440), (22, 1559269440), (23, 164471040), (24, -2489135040), (25, 328942080), (27, 348699600), (29, -464932800), (30, -1750083840)]

def pairMerged23 : Integer.Sparse (Fin 271) := [(0, 1632106230), (1, -22825318140), (2, 6356768370), (3, 57432775680), (4, 37630293120), (5, -104274240), (7, 104274240), (8, 417096960), (12, 21094070880), (13, 4883429280), (23, -312822720), (25, -14268903840), (26, 4487559360), (27, 234617040), (29, -625645440), (30, -31567536000), (32, -14078422080), (33, 674373120), (44, 1876936320), (49, 4544592480), (50, -625645440), (53, -312822720)]

def pairMerged24 : Integer.Sparse (Fin 271) := [(0, -127417782), (1, 1285084380), (2, -492829650), (3, -2986179840), (4, -982462080), (12, -1897068480), (13, -396219840), (25, -548763840), (26, 350653920), (30, 1119817440), (32, 2377319040), (42, -479921760), (43, 1303067520), (44, -2262911040), (45, 1303067520)]

def pairMerged25 : Integer.Sparse (Fin 271) := [(0, 43175808), (1, -967939200), (2, 190252800), (3, 1811773440), (4, 1253836800), (5, 414720), (7, -552960), (8, -1105920), (12, 555171840), (13, 562913280), (23, 3317760), (24, 9953280), (25, 2119219200), (27, -4147200), (29, 6635520), (30, 860958720), (32, 1695375360), (46, 1266554880), (47, -1271531520), (48, -9953280), (50, 4976640), (54, 3317760)]

def pairMerged26 : Integer.Sparse (Fin 271) := [(0, -84241974), (1, 317145180), (2, -302576850), (3, -1174406400), (4, 271374720), (5, 414720), (7, -552960), (8, -1105920), (12, -1341896640), (13, 166693440), (23, 3317760), (24, 9953280), (25, 1570455360), (26, 350653920), (27, -4147200), (29, 6635520), (30, 1980776160), (32, 4072694400), (42, -479921760), (43, 1303067520), (44, -2262911040), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (50, 4976640), (54, 3317760)]

def pairMerged27 : Integer.Sparse (Fin 271) := [(0, 1547864256), (1, -22508172960), (2, 6054191520), (3, 56258369280), (4, 37901667840), (5, -103859520), (7, 103721280), (8, 415991040), (12, 19752174240), (13, 5050122720), (23, -309504960), (24, 9953280), (25, -12698448480), (26, 4838213280), (27, 230469840), (29, -619009920), (30, -29586759840), (32, -10005727680), (33, 674373120), (42, -479921760), (43, 1303067520), (44, -385974720), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (49, 4544592480), (50, -620668800), (53, -312822720), (54, 3317760)]

def pairMerged28 : Integer.Sparse (Fin 271) := [(0, 1854573710), (1, -28931176670), (2, 8143395470), (3, 74209995840), (4, 45957359520), (5, -6571027600), (6, 825233190), (7, 4435050720), (8, 7351878720), (12, 13488208800), (13, 1456044800), (17, 48988800), (23, 2497034880), (24, 9953280), (25, -9875579040), (26, 14827732320), (27, 242717040), (28, 97977600), (29, -700657920), (30, -29586759840), (31, -458094080), (32, -10005727680), (33, 674373120), (34, 3725212640), (42, -479921760), (43, 1303067520), (44, -385974720), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (49, 4544592480), (50, 5311450080), (51, 1760154720), (53, 12647520), (54, 1457375040), (55, -3112885440)]

def pairMerged29 : Integer.Sparse (Fin 271) := [(0, 168034126), (1, -2537413400), (2, -1079407000), (3, 25255861440), (4, 10384953600), (5, -251588680), (6, 325640310), (7, -2996998560), (8, -3797639040), (12, 8168124480), (13, 8923824480), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1500694560), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 9652281120), (24, 13224720960), (25, -270371520), (26, 2153414880), (27, -6291257580), (28, 97977600), (29, 11112559200), (30, -10963887840), (31, -458094080), (32, -10005727680), (33, 674373120), (34, 3725212640), (42, -479921760), (43, 1303067520), (44, -385974720), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (49, 4544592480), (50, 5311450080), (51, 1760154720), (53, 12647520), (54, 1457375040), (55, -3112885440)]

def pairMerged30 : Integer.Sparse (Fin 271) := [(0, -701544198), (1, 8476671000), (2, -3863485110), (3, -22859176320), (4, -14654783040), (5, 1055258640), (7, -2229355200), (8, -3225194880), (12, -5595956160), (23, -713027520), (24, 5262010560), (26, -1872841440), (27, -1884125520), (29, 2274491520), (30, 9319070880), (42, 1069541280), (44, -5550819840), (45, -5550819840), (50, 7401093120), (54, -713027520), (55, 3700546560)]

def pairMerged31 : Integer.Sparse (Fin 271) := [(0, -8391918), (1, 263935950), (2, -416033880), (3, -1494318240), (4, -469992960), (5, 174024480), (7, -183816000), (8, -656931840), (12, -2884320), (13, 497383200), (23, 216974880), (25, 36043200), (26, -313328640), (27, -162731160), (29, 433949760), (30, 469992960), (32, 1337892480), (35, -650924640), (37, 298429920), (38, -704989440), (39, -1301849280), (50, 867899520), (53, 786444480), (54, 650924640)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged32 : Integer.Sparse (Fin 271) := [(0, -709936116), (1, 8740606950), (2, -4279518990), (3, -24353494560), (4, -15124776000), (5, 1229283120), (7, -2413171200), (8, -3882126720), (12, -5598840480), (13, 497383200), (23, -496052640), (24, 5262010560), (25, 36043200), (26, -2186170080), (27, -2046856680), (29, 2708441280), (30, 9789063840), (32, 1337892480), (35, -650924640), (37, 298429920), (38, -704989440), (39, -1301849280), (42, 1069541280), (44, -5550819840), (45, -5550819840), (50, 8268992640), (53, 786444480), (54, -62102880), (55, 3700546560)]

def pairMerged33 : Integer.Sparse (Fin 271) := [(0, 51323124), (1, -806956560), (2, 363588060), (3, 2677578240), (4, 357930240), (5, -118157760), (7, 117168960), (8, 476586240), (12, 1078251840), (13, 1324455360), (23, -181686240), (26, 151278720), (27, 136264680), (29, -363372480), (36, -35596800), (37, 545058720), (39, 1018923840), (50, -726744960), (53, -363372480), (54, -545058720), (55, 35596800), (56, -71193600)]

def pairMerged34 : Integer.Sparse (Fin 271) := [(0, -80740800), (1, 1248220260), (2, -492432300), (3, -4464714240), (4, -1374914880), (12, -2351393280), (13, -2743292160), (26, -150557760), (30, 1175696640), (32, 1175696640), (40, -881772480), (41, -1763544960), (52, 145981440), (56, 145981440)]

def pairMerged35 : Integer.Sparse (Fin 271) := [(0, -29417676), (1, 441263700), (2, -128844240), (3, -1787136000), (4, -1016984640), (5, -118157760), (7, 117168960), (8, 476586240), (12, -1273141440), (13, -1418836800), (23, -181686240), (26, 720960), (27, 136264680), (29, -363372480), (30, 1175696640), (32, 1175696640), (36, -35596800), (37, 545058720), (39, 1018923840), (40, -881772480), (41, -1763544960), (50, -726744960), (52, 145981440), (53, -363372480), (54, -545058720), (55, 35596800), (56, 74787840)]

def pairMerged36 : Integer.Sparse (Fin 271) := [(0, -739353792), (1, 9181870650), (2, -4408363230), (3, -26140630560), (4, -16141760640), (5, 1111125360), (7, -2296002240), (8, -3405540480), (12, -6871981920), (13, -921453600), (23, -677738880), (24, 5262010560), (25, 36043200), (26, -2185449120), (27, -1910592000), (29, 2345068800), (30, 10964760480), (32, 2513589120), (35, -650924640), (36, -35596800), (37, 843488640), (38, -704989440), (39, -282925440), (40, -881772480), (41, -1763544960), (42, 1069541280), (44, -5550819840), (45, -5550819840), (50, 7542247680), (52, 145981440), (53, 423072000), (54, -607161600), (55, 3736143360), (56, 74787840)]

def pairMerged37 : Integer.Sparse (Fin 271) := [(0, 311282724), (1, -6563693940), (2, 3017480760), (3, 28238385600), (4, 11057085120), (5, -1125976920), (7, 2430655680), (8, 3288579840), (12, 7625388480), (13, 4384773120), (14, 1072211040), (15, 4288844160), (23, -2501825760), (24, -4718194560), (25, -2501825760), (26, 6029063040), (27, 1590621120), (29, -1644289920), (30, -3288579840), (32, -8006774400), (35, 2144422080), (36, 4932869760), (38, 4932869760), (39, 4932869760), (41, 4932869760), (47, 2144422080), (50, -7291967040), (53, -714807360), (54, -5647677120), (55, -3288579840)]

def pairMerged38 : Integer.Sparse (Fin 271) := [(0, -168894831), (1, 2243807580), (2, -404709675), (3, -9100344960), (4, -3608470080), (5, 21656520), (7, -86626080), (8, -86626080), (12, -2513691840), (13, -638511120), (15, -2056656960), (16, -638511120), (18, -3333679200), (19, -1559269440), (21, -1559269440), (23, 685552320), (24, 1984943520), (25, 898389360), (26, -519756480), (27, -248117940), (30, 1039512960), (36, -1559269440), (37, -1277022240), (46, -779634720), (47, -779634720), (49, -638511120), (50, 519756480), (54, 425674080), (55, 519756480)]

def pairMerged39 : Integer.Sparse (Fin 271) := [(0, 142387893), (1, -4319886360), (2, 2612771085), (3, 19138040640), (4, 7448615040), (5, -1104320400), (7, 2344029600), (8, 3201953760), (12, 5111696640), (13, 3746262000), (14, 1072211040), (15, 2232187200), (16, -638511120), (18, -3333679200), (19, -1559269440), (21, -1559269440), (23, -1816273440), (24, -2733251040), (25, -1603436400), (26, 5509306560), (27, 1342503180), (29, -1644289920), (30, -2249066880), (32, -8006774400), (35, 2144422080), (36, 3373600320), (37, -1277022240), (38, 4932869760), (39, 4932869760), (41, 4932869760), (46, -779634720), (47, 1364787360), (49, -638511120), (50, -6772210560), (53, -714807360), (54, -5222003040), (55, -2768823360)]

def pairMerged40 : Integer.Sparse (Fin 271) := [(0, 300331956), (1, -3076485120), (2, 746667540), (3, 3956297280), (4, 5021454240), (5, -76082640), (7, 304330560), (8, 456495840), (9, 19447200), (12, 608661120), (17, 1369487520), (20, 2738975040), (23, -456495840), (24, -2282479200), (25, -1369487520), (26, 304330560), (27, 342371880), (29, -1369487520), (30, -2738975040), (43, 2738975040), (44, 2738975040), (47, 1369487520), (50, -456495840), (57, -972360)]

def pairMerged41 : Integer.Sparse (Fin 271) := [(0, -435642), (1, 10750000), (2, 39111000), (3, 70702080), (5, -77343440), (6, 6722010), (7, 141404160), (8, 141404160), (9, -9526880), (27, -25389000), (34, 47134720), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

def pairMerged42 : Integer.Sparse (Fin 271) := [(0, 299896314), (1, -3065735120), (2, 785778540), (3, 4026999360), (4, 5021454240), (5, -153426080), (6, 6722010), (7, 445734720), (8, 597900000), (9, 9920320), (12, 608661120), (17, 1369487520), (20, 2738975040), (23, -456495840), (24, -2282479200), (25, -1369487520), (26, 304330560), (27, 316982880), (29, -1369487520), (30, -2738975040), (34, 47134720), (43, 2738975040), (44, 2738975040), (47, 1369487520), (50, -456495840), (57, -972360), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

def pairMerged43 : Integer.Sparse (Fin 271) := [(0, 442284207), (1, -7385621480), (2, 3398549625), (3, 23165040000), (4, 12470069280), (5, -1257746480), (6, 6722010), (7, 2789764320), (8, 3799853760), (9, 9920320), (12, 5720357760), (13, 3746262000), (14, 1072211040), (15, 2232187200), (16, -638511120), (17, 1369487520), (18, -3333679200), (19, -1559269440), (20, 2738975040), (21, -1559269440), (23, -2272769280), (24, -5015730240), (25, -2972923920), (26, 5813637120), (27, 1659486060), (29, -3013777440), (30, -4988041920), (32, -8006774400), (34, 47134720), (35, 2144422080), (36, 3373600320), (37, -1277022240), (38, 4932869760), (39, 4932869760), (41, 4932869760), (43, 2738975040), (44, 2738975040), (46, -779634720), (47, 2734274880), (49, -638511120), (50, -7228706400), (53, -714807360), (54, -5222003040), (55, -2768823360), (57, -972360), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

def pairMerged44 : Integer.Sparse (Fin 271) := [(0, -297069585), (1, 1796249170), (2, -1009813605), (3, -2975590560), (4, -3671691360), (5, -146621120), (6, 6722010), (7, 493762080), (8, 394313280), (9, 9920320), (12, -1151624160), (13, 2824808400), (14, 1072211040), (15, 2232187200), (16, -638511120), (17, 1369487520), (18, -3333679200), (19, -1559269440), (20, 2738975040), (21, -1559269440), (23, -2950508160), (24, 246280320), (25, -2936880720), (26, 3628188000), (27, -251105940), (29, -668708640), (30, 5976718560), (32, -5493185280), (34, 47134720), (35, 1493497440), (36, 3338003520), (37, -433533600), (38, 4227880320), (39, 4649944320), (40, -881772480), (41, 3169324800), (42, 1069541280), (43, 2738975040), (44, -2811844800), (45, -5550819840), (46, -779634720), (47, 2734274880), (49, -638511120), (50, 313541280), (52, 145981440), (53, -291735360), (54, -5829164640), (55, 967320000), (56, 74787840), (57, -972360), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

def pairMerged45 : Integer.Sparse (Fin 271) := [(0, 2253012), (1, -35796300), (2, 39664440), (3, 337326720), (4, 117492480), (5, -62641200), (6, 7343280), (7, 200252160), (8, 58746240), (9, -5896080), (12, 16008960), (13, 8004480), (23, -36020160), (24, -176238720), (26, 117492480), (34, 172665600), (51, 117492480), (67, 74755200), (68, 47168640), (69, 19582080), (111, -36020160), (112, -24013440), (113, -176238720), (131, -117492480)]

def pairMerged46 : Integer.Sparse (Fin 271) := [(0, -596160), (1, 29059980), (2, -76569000), (3, -404705280), (4, -43178880), (5, 109394880), (6, -8881140), (7, -206866560), (8, -129536640), (9, 7008400), (12, -96662400), (13, -199768960), (23, 57997440), (24, 129536640), (27, -16192080), (34, -115994880), (50, 129536640), (51, -120508800), (53, 115994880), (67, -62511360), (68, -19332480), (69, -86357760), (111, 64768320), (112, 57997440), (113, 259073280), (130, 38664960)]

def pairMerged47 : Integer.Sparse (Fin 271) := [(0, 1656852), (1, -6736320), (2, -36904560), (3, -67378560), (4, 74313600), (5, 46753680), (6, -1537860), (7, -6614400), (8, -70790400), (9, 1112320), (12, -80653440), (13, -191764480), (23, 21977280), (24, -46702080), (26, 117492480), (27, -16192080), (34, 56670720), (50, 129536640), (51, -3016320), (53, 115994880), (67, 12243840), (68, 27836160), (69, -66775680), (111, 28748160), (112, 33984000), (113, 82834560), (130, 38664960), (131, -117492480)]

def pairMerged48 : Integer.Sparse (Fin 271) := [(0, 790464), (1, 5379360), (2, 11551440), (3, -70012800), (4, -33784320), (5, 17085600), (6, -3642960), (7, -5445120), (8, 6558720), (9, 680640), (13, -42230400), (24, 50676480), (26, -33784320), (27, 4292640), (29, -34341120), (34, -42230400), (51, -22337280), (54, 25338240), (55, 101352960), (67, -2722560), (68, -8446080), (69, -5166720), (112, 25338240), (113, -17170560), (131, 101352960), (146, -68682240)]

def pairMerged49 : Integer.Sparse (Fin 271) := [(0, 11280586), (1, -375059460), (2, 1630660770), (3, 5983799520), (4, 189706080), (5, -3317388720), (6, 228491940), (7, 6673498560), (8, 5414681280), (10, -1888225920), (11, 189706080), (12, 1258817280), (13, 1678423040), (26, 379412160), (34, 4242141120), (51, 948530400), (80, 629408640), (143, -569118240)]

def pairMerged50 : Integer.Sparse (Fin 271) := [(0, 12071050), (1, -369680100), (2, 1642212210), (3, 5913786720), (4, 155921760), (5, -3300303120), (6, 224848980), (7, 6668053440), (8, 5421240000), (9, 680640), (10, -1888225920), (11, 189706080), (12, 1258817280), (13, 1636192640), (24, 50676480), (26, 345627840), (27, 4292640), (29, -34341120), (34, 4199910720), (51, 926193120), (54, 25338240), (55, 101352960), (67, -2722560), (68, -8446080), (69, -5166720), (80, 629408640), (112, 25338240), (113, -17170560), (131, 101352960), (143, -569118240), (146, -68682240)]

def pairMerged51 : Integer.Sparse (Fin 271) := [(0, 13727902), (1, -376416420), (2, 1605307650), (3, 5846408160), (4, 230235360), (5, -3253549440), (6, 223311120), (7, 6661439040), (8, 5350449600), (9, 1792960), (10, -1888225920), (11, 189706080), (12, 1178163840), (13, 1444428160), (23, 21977280), (24, 3974400), (26, 463120320), (27, -11899440), (29, -34341120), (34, 4256581440), (50, 129536640), (51, 923176800), (53, 115994880), (54, 25338240), (55, 101352960), (67, 9521280), (68, 19390080), (69, -71942400), (80, 629408640), (111, 28748160), (112, 59322240), (113, 65664000), (130, 38664960), (131, -16139520), (143, -569118240), (146, -68682240)]

def pairMerged52 : Integer.Sparse (Fin 271) := [(0, 589008), (1, -17946720), (2, -29830560), (3, -98664960), (5, 53701920), (6, -8938800), (7, -25495680), (8, -47673600), (10, 2488320), (12, -13577280), (13, -99770880), (34, -97559040), (51, -190694400), (80, -72339840), (114, 2488320), (115, -96176640), (132, 35755200), (133, 143020800)]

def pairMerged53 : Integer.Sparse (Fin 271) := [(0, -20052162), (1, 425908260), (2, -61213590), (3, -2399309280), (4, -922805280), (5, 262631520), (6, -46138320), (7, -85190400), (11, -156169440), (12, -340761600), (13, -596332800), (25, 255571200), (26, -1078974720), (27, -106468560), (30, 425874240), (34, -965413440), (51, -440085600), (53, 766713600), (54, 425874240), (55, 511142400), (142, 170380800), (143, 468508320), (147, 425874240), (148, 425874240)]

def pairMerged54 : Integer.Sparse (Fin 271) := [(0, -19463154), (1, 407961540), (2, -91044150), (3, -2497974240), (4, -922805280), (5, 316333440), (6, -55077120), (7, -110686080), (8, -47673600), (10, 2488320), (11, -156169440), (12, -354338880), (13, -696103680), (25, 255571200), (26, -1078974720), (27, -106468560), (30, 425874240), (34, -1062972480), (51, -630780000), (53, 766713600), (54, 425874240), (55, 511142400), (80, -72339840), (114, 2488320), (115, -96176640), (132, 35755200), (133, 143020800), (142, 170380800), (143, 468508320), (147, 425874240), (148, 425874240)]

def pairMerged55 : Integer.Sparse (Fin 271) := [(0, 20700400), (1, -67199300), (2, -1503912660), (3, -8931624000), (4, -634164480), (5, 4102916080), (6, -552422560), (7, -3314535360), (8, -2838912000), (12, -2136598080), (13, -6958509760), (26, -634164480), (34, -6555978560), (51, -6946152960), (53, 1426870080), (55, 951246720), (58, 2129184000), (59, -946304000), (80, -634164480), (115, -1343892480), (132, 475623360), (133, 951246720)]

def pairMerged56 : Integer.Sparse (Fin 271) := [(0, 106242624), (1, 401250720), (2, -669469680), (3, -17088683520), (4, -361543680), (5, 1254169920), (6, -132770640), (7, -2169262080), (8, -1446174720), (12, -6103399680), (13, -16953888000), (26, -5470176000), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -3842184960), (51, -723087360), (54, 6103399680), (59, -1356311040), (60, 4068933120), (65, -361543680), (79, 1084631040)]

def pairMerged57 : Integer.Sparse (Fin 271) := [(0, 126943024), (1, 334051420), (2, -2173382340), (3, -26020307520), (4, -995708160), (5, 5357086000), (6, -685193200), (7, -5483797440), (8, -4285086720), (12, -8239997760), (13, -23912397760), (26, -6104340480), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -10398163520), (51, -7669240320), (53, 1426870080), (54, 6103399680), (55, 951246720), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (79, 1084631040), (80, -634164480), (115, -1343892480), (132, 475623360), (133, 951246720)]

def pairMerged58 : Integer.Sparse (Fin 271) := [(0, 107479870), (1, 742012960), (2, -2264426490), (3, -28518281760), (4, -1918513440), (5, 5673419440), (6, -740270320), (7, -5594483520), (8, -4332760320), (10, 2488320), (11, -156169440), (12, -8594336640), (13, -24608501440), (25, 255571200), (26, -7183315200), (27, -106468560), (30, 425874240), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -11461136000), (51, -8300020320), (53, 2193583680), (54, 6529273920), (55, 1462389120), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (79, 1084631040), (80, -706504320), (114, 2488320), (115, -1440069120), (132, 511378560), (133, 1094267520), (142, 170380800), (143, 468508320), (147, 425874240), (148, 425874240)]

def pairMerged59 : Integer.Sparse (Fin 271) := [(0, 121207772), (1, 365596540), (2, -659118840), (3, -22671873600), (4, -1688278080), (5, 2419870000), (6, -516959200), (7, 1066955520), (8, 1017689280), (9, 1792960), (10, -1885737600), (11, 33536640), (12, -7416172800), (13, -23164073280), (23, 21977280), (24, 3974400), (25, 255571200), (26, -6720194880), (27, -118368000), (29, -34341120), (30, 425874240), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -7204554560), (50, 129536640), (51, -7376843520), (53, 2309578560), (54, 6554612160), (55, 1563742080), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (67, 9521280), (68, 19390080), (69, -71942400), (79, 1084631040), (80, -77095680), (111, 28748160), (112, 59322240), (113, 65664000), (114, 2488320), (115, -1440069120), (130, 38664960), (131, -16139520), (132, 511378560), (133, 1094267520), (142, 170380800), (143, -100609920), (146, -68682240), (147, 425874240), (148, 425874240)]

def pairMerged60 : Integer.Sparse (Fin 271) := [(0, -175861813), (1, 2161845710), (2, -1668932445), (3, -25647464160), (4, -5359969440), (5, 2273248880), (6, -510237190), (7, 1560717600), (8, 1412002560), (9, 11713280), (10, -1885737600), (11, 33536640), (12, -8567796960), (13, -20339264880), (14, 1072211040), (15, 2232187200), (16, -638511120), (17, 1369487520), (18, -3333679200), (19, -1559269440), (20, 2738975040), (21, -1559269440), (23, -2928530880), (24, 250254720), (25, -2681309520), (26, -3092006880), (27, -369473940), (29, -703049760), (30, 6402592800), (31, -1356311040), (32, 610214400), (33, -4068933120), (34, -7157419840), (35, 1493497440), (36, 3338003520), (37, -433533600), (38, 4227880320), (39, 4649944320), (40, -881772480), (41, 3169324800), (42, 1069541280), (43, 2738975040), (44, -2811844800), (45, -5550819840), (46, -779634720), (47, 2734274880), (49, -638511120), (50, 443077920), (51, -7376843520), (52, 145981440), (53, 2017843200), (54, 725447520), (55, 2531062080), (56, 74787840), (57, -972360), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (66, -33852000), (67, 80223360), (68, 42957440), (69, 69461760), (79, 1084631040), (80, -77095680), (111, 28748160), (112, 59322240), (113, 65664000), (114, 2488320), (115, -1440069120), (130, 38664960), (131, -16139520), (132, 511378560), (133, 1094267520), (142, 170380800), (143, -100609920), (146, -68682240), (147, 425874240), (148, 425874240)]

def pairMerged61 : Integer.Sparse (Fin 271) := [(0, -7827687), (1, -375567690), (2, -2748339445), (3, -391602720), (4, 5024984160), (5, 2021660200), (6, -184596880), (7, -1436280960), (8, -2385636480), (9, 11713280), (10, -1885737600), (11, 33536640), (12, -399672480), (13, -11415440400), (14, -2177280), (15, -174752640), (16, 38024640), (17, -131207040), (18, 16277760), (20, 142248960), (21, 37324800), (22, -9953280), (23, 6723750240), (24, 13474975680), (25, -2951681040), (26, -938592000), (27, -6660731520), (28, 97977600), (29, 10409509440), (30, -4561295040), (31, -1814405120), (32, -9395513280), (33, -3394560000), (34, -3432207200), (35, 1493497440), (36, 3338003520), (37, -433533600), (38, 4227880320), (39, 4649944320), (40, -881772480), (41, 3169324800), (42, 589619520), (43, 4042042560), (44, -3197819520), (45, -4247752320), (46, 486920160), (47, 1462743360), (48, -9953280), (49, 3906081360), (50, 5754528000), (51, -5616688800), (52, 145981440), (53, 2030490720), (54, 2182822560), (55, -581823360), (56, 74787840), (57, -972360), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (66, -33852000), (67, 80223360), (68, 42957440), (69, 69461760), (79, 1084631040), (80, -77095680), (111, 28748160), (112, 59322240), (113, 65664000), (114, 2488320), (115, -1440069120), (130, 38664960), (131, -16139520), (132, 511378560), (133, 1094267520), (142, 170380800), (143, -100609920), (146, -68682240), (147, 425874240), (148, 425874240)]

def pairMerged62 : Integer.Sparse (Fin 271) := [(0, 13193040), (1, 39671280), (2, -32953800), (3, -1689262080), (5, 52933440), (6, -6659880), (7, -921600), (12, -632897280), (13, -1477067520), (23, 1382400), (25, 315527040), (26, -423467520), (32, 1264872960), (33, -212194560), (34, -213116160), (51, -210351360), (53, 2764800), (54, 633818880), (62, 316909440), (63, 631054080), (64, 2764800), (65, -921600)]

def pairMerged63 : Integer.Sparse (Fin 271) := [(0, -51051744), (1, 28266080), (2, 368668640), (3, 8165514240), (5, -341612160), (6, 28611680), (7, 4147200), (12, 4078609920), (13, 14952138240), (26, 1360919040), (31, 1811793920), (32, -12441600), (33, 2713543680), (34, 1369213440), (51, 2721838080), (53, -12441600), (58, -4070315520), (59, 2264051200), (60, -4070315520), (61, -8294400), (115, 1356771840)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged64 : Integer.Sparse (Fin 271) := [(0, -37858704), (1, 67937360), (2, 335714840), (3, 6476252160), (5, -288678720), (6, 21951800), (7, 3225600), (12, 3445712640), (13, 13475070720), (23, 1382400), (25, 315527040), (26, 937451520), (31, 1811793920), (32, 1252431360), (33, 2501349120), (34, 1156097280), (51, 2511486720), (53, -9676800), (54, 633818880), (58, -4070315520), (59, 2264051200), (60, -4070315520), (61, -8294400), (62, 316909440), (63, 631054080), (64, 2764800), (65, -921600), (115, 1356771840)]

def pairMerged65 : Integer.Sparse (Fin 271) := [(0, -11915904), (1, -202286280), (2, 290834040), (3, 3448609920), (4, -94625280), (5, -500950560), (6, 63358080), (7, 1145155200), (8, 310164480), (12, 1478976000), (13, 3410931840), (25, 178738560), (26, 955027200), (30, 357477120), (32, 714954240), (33, 775411200), (34, 1729560960), (50, -930493440), (51, 1323893760), (53, -643985280), (63, -465246720), (65, 310164480), (79, 357477120), (110, 357477120)]

def pairMerged66 : Integer.Sparse (Fin 271) := [(0, 276959280), (1, -4048702800), (2, 2446435200), (3, 8902233600), (4, 3558105600), (5, -839890800), (6, 237600), (7, 1124500800), (8, 2241398400), (10, -1992168000), (12, 3105264000), (13, 1770816000), (23, -6648163200), (24, -18616377600), (26, 7603200), (27, 6816078000), (29, -10640102400), (34, 2534400), (50, -57024000), (53, -15206400), (54, -10632499200), (55, -30412800), (75, 11404800), (76, 22809600), (77, 1992168000), (78, 3984336000), (143, -11404800)]

def pairMerged67 : Integer.Sparse (Fin 271) := [(0, 265043376), (1, -4250989080), (2, 2737269240), (3, 12350843520), (4, 3463480320), (5, -1340841360), (6, 63595680), (7, 2269656000), (8, 2551562880), (10, -1992168000), (12, 4584240000), (13, 5181747840), (23, -6648163200), (24, -18616377600), (25, 178738560), (26, 962630400), (27, 6816078000), (29, -10640102400), (30, 357477120), (32, 714954240), (33, 775411200), (34, 1732095360), (50, -987517440), (51, 1323893760), (53, -659191680), (54, -10632499200), (55, -30412800), (63, -465246720), (65, 310164480), (75, 11404800), (76, 22809600), (77, 1992168000), (78, 3984336000), (79, 357477120), (110, 357477120), (143, -11404800)]

def pairMerged68 : Integer.Sparse (Fin 271) := [(0, 227184672), (1, -4183051720), (2, 3072984080), (3, 18827095680), (4, 3463480320), (5, -1629520080), (6, 85547480), (7, 2272881600), (8, 2551562880), (10, -1992168000), (12, 8029952640), (13, 18656818560), (23, -6646780800), (24, -18616377600), (25, 494265600), (26, 1900081920), (27, 6816078000), (29, -10640102400), (30, 357477120), (31, 1811793920), (32, 1967385600), (33, 3276760320), (34, 2888192640), (50, -987517440), (51, 3835380480), (53, -668868480), (54, -9998680320), (55, -30412800), (58, -4070315520), (59, 2264051200), (60, -4070315520), (61, -8294400), (62, 316909440), (63, 165807360), (64, 2764800), (65, 309242880), (75, 11404800), (76, 22809600), (77, 1992168000), (78, 3984336000), (79, 357477120), (110, 357477120), (115, 1356771840), (143, -11404800)]

def pairMerged69 : Integer.Sparse (Fin 271) := [(0, 13341360), (1, -227990400), (2, -1179937680), (3, -2913093120), (4, -333715200), (5, 2095998240), (6, -182104560), (7, -2868501120), (8, -2557226880), (10, 99679680), (12, -99679680), (13, -132906240), (23, 33226560), (26, -400458240), (27, -24919920), (29, 66453120), (34, -2001711360), (50, 265812480), (51, -2024152320), (53, 132906240), (58, 265812480), (70, -99679680), (72, -199359360), (73, -199359360), (79, 800916480), (82, -600687360), (83, -1201374720), (84, -1201374720), (132, 99679680), (143, 600687360)]

def pairMerged70 : Integer.Sparse (Fin 271) := [(0, -6192624), (1, 112863360), (2, 549002880), (3, 1450967040), (4, -17387520), (5, -818342400), (6, 72280560), (7, 886007040), (8, 861212160), (10, 39121920), (12, 179197440), (13, 233134080), (24, 26081280), (27, -9780480), (29, 13040640), (34, 926415360), (50, 104325120), (51, 1304770560), (55, 52162560), (58, 104325120), (71, 262275840), (72, -39121920), (73, 563673600), (74, -78243840), (79, -401863680), (84, 1205591040), (133, -262275840)]

def pairMerged71 : Integer.Sparse (Fin 271) := [(0, 7148736), (1, -115127040), (2, -630934800), (3, -1462126080), (4, -351102720), (5, 1277655840), (6, -109824000), (7, -1982494080), (8, -1696014720), (10, 138801600), (12, 79517760), (13, 100227840), (23, 33226560), (24, 26081280), (26, -400458240), (27, -34700400), (29, 79493760), (34, -1075296000), (50, 370137600), (51, -719381760), (53, 132906240), (55, 52162560), (58, 370137600), (70, -99679680), (71, 262275840), (72, -238481280), (73, 364314240), (74, -78243840), (79, 399052800), (82, -600687360), (83, -1201374720), (84, 4216320), (132, 99679680), (133, -262275840), (143, 600687360)]

def pairMerged72 : Integer.Sparse (Fin 271) := [(0, -8241738), (1, 234045120), (2, 915602970), (3, 1778734080), (4, 469138560), (5, -1299800520), (6, 102530460), (7, 1424933280), (8, 1665241920), (10, 92380320), (12, -739042560), (13, -585075360), (23, 739042560), (24, 554281920), (25, 92380320), (26, 1036097280), (27, -161665560), (34, 1036097280), (46, -1108563840), (47, -554281920), (49, -277140960), (50, 554281920), (51, 1381463040), (54, 369521280), (58, 184760640), (77, -277140960), (79, -2072194560), (81, 777072960), (83, 3108291840), (84, 1554145920), (87, -554281920), (143, -1554145920)]

def pairMerged73 : Integer.Sparse (Fin 271) := [(0, -88434696), (1, 1076906760), (2, -637198395), (3, -6092711040), (4, -2790823200), (5, 303532500), (6, -7928475), (7, -674135040), (8, -833563200), (12, -1859542320), (13, -217496400), (23, 511064640), (24, 500137920), (25, 1043982720), (26, -1264913760), (27, -62517240), (30, 1750482720), (32, 260995680), (34, -173997120), (42, -2316180960), (45, -1500413760), (49, -391493520), (50, 1500413760), (51, -170354880), (54, 260995680), (55, 1000275840), (75, -750206880), (79, 500137920), (96, -782987040), (98, -1500413760), (99, -1500413760), (103, -391493520), (109, -1500413760), (143, 250068960)]

def pairMerged74 : Integer.Sparse (Fin 271) := [(0, -96676434), (1, 1310951880), (2, 278404575), (3, -4313976960), (4, -2321684640), (5, -996268020), (6, 94601985), (7, 750798240), (8, 831678720), (10, 92380320), (12, -2598584880), (13, -802571760), (23, 1250107200), (24, 1054419840), (25, 1136363040), (26, -228816480), (27, -224182800), (30, 1750482720), (32, 260995680), (34, 862100160), (42, -2316180960), (45, -1500413760), (46, -1108563840), (47, -554281920), (49, -668634480), (50, 2054695680), (51, 1211108160), (54, 630516960), (55, 1000275840), (58, 184760640), (75, -750206880), (77, -277140960), (79, -1572056640), (81, 777072960), (83, 3108291840), (84, 1554145920), (87, -554281920), (96, -782987040), (98, -1500413760), (99, -1500413760), (103, -391493520), (109, -1500413760), (143, -1304076960)]

def pairMerged75 : Integer.Sparse (Fin 271) := [(0, -89527698), (1, 1195824840), (2, -352530225), (3, -5776103040), (4, -2672787360), (5, 281387820), (6, -15222015), (7, -1231695840), (8, -864336000), (10, 231181920), (12, -2519067120), (13, -702343920), (23, 1283333760), (24, 1080501120), (25, 1136363040), (26, -629274720), (27, -258883200), (29, 79493760), (30, 1750482720), (32, 260995680), (34, -213195840), (42, -2316180960), (45, -1500413760), (46, -1108563840), (47, -554281920), (49, -668634480), (50, 2424833280), (51, 491726400), (53, 132906240), (54, 630516960), (55, 1052438400), (58, 554898240), (70, -99679680), (71, 262275840), (72, -238481280), (73, 364314240), (74, -78243840), (75, -750206880), (77, -277140960), (79, -1173003840), (81, 777072960), (82, -600687360), (83, 1906917120), (84, 1558362240), (87, -554281920), (96, -782987040), (98, -1500413760), (99, -1500413760), (103, -391493520), (109, -1500413760), (132, 99679680), (133, -262275840), (143, -703389600)]

def pairMerged76 : Integer.Sparse (Fin 271) := [(0, 137656974), (1, -2987226880), (2, 2720453855), (3, 13050992640), (4, 790692960), (5, -1348132260), (6, 70325465), (7, 1041185760), (8, 1687226880), (10, -1760986080), (12, 5510885520), (13, 17954474640), (23, -5363447040), (24, -17535876480), (25, 1630628640), (26, 1270807200), (27, 6557194800), (29, -10560608640), (30, 2107959840), (31, 1811793920), (32, 2228381280), (33, 3276760320), (34, 2674996800), (42, -2316180960), (45, -1500413760), (46, -1108563840), (47, -554281920), (49, -668634480), (50, 1437315840), (51, 4327106880), (53, -535962240), (54, -9368163360), (55, 1022025600), (58, -3515417280), (59, 2264051200), (60, -4070315520), (61, -8294400), (62, 316909440), (63, 165807360), (64, 2764800), (65, 309242880), (70, -99679680), (71, 262275840), (72, -238481280), (73, 364314240), (74, -78243840), (75, -738802080), (76, 22809600), (77, 1715027040), (78, 3984336000), (79, -815526720), (81, 777072960), (82, -600687360), (83, 1906917120), (84, 1558362240), (87, -554281920), (96, -782987040), (98, -1500413760), (99, -1500413760), (103, -391493520), (109, -1500413760), (110, 357477120), (115, 1356771840), (132, 99679680), (133, -262275840), (143, -714794400)]

def pairMerged77 : Integer.Sparse (Fin 271) := [(0, 25825320), (1, -1258671330), (2, 712541310), (3, 6647298240), (4, 2303014560), (5, -347768760), (6, 15392040), (7, 984059040), (8, 489450720), (10, -366314400), (12, 2584831200), (13, 1471446720), (23, -247304160), (24, -491513760), (25, -1731129120), (26, 822284160), (30, -1731129120), (32, -1731129120), (34, 574980000), (37, 366314400), (39, 732628800), (42, 1483824960), (45, 1483824960), (49, 741912480), (50, -738817920), (51, 573948480), (54, -860922720), (58, -732628800), (70, 366314400), (73, 732628800), (79, -494608320), (87, 732628800), (88, 2207170080), (94, 1465257600), (96, 741912480), (103, 1483824960), (109, 1483824960), (132, -122104800)]

def pairMerged78 : Integer.Sparse (Fin 271) := [(0, -318970545), (1, 3467994960), (2, -782067150), (3, -6492083040), (4, -6951318720), (5, 148576500), (6, -9109905), (7, 11077440), (8, -291516960), (10, -100864800), (12, -572151120), (13, 67243200), (23, -907783200), (24, 471091680), (25, 2488971600), (26, -1524828000), (27, 176513400), (30, 8005055040), (34, -257895360), (42, -2018463840), (43, -6457682880), (51, -291516960), (54, 571956480), (77, 302594400), (88, -2623652640), (103, -1009231920)]

def pairMerged79 : Integer.Sparse (Fin 271) := [(0, -293145225), (1, 2209323630), (2, -69525840), (3, 155215200), (4, -4648304160), (5, -199192260), (6, 6282135), (7, 995136480), (8, 197933760), (10, -467179200), (12, 2012680080), (13, 1538689920), (23, -1155087360), (24, -20422080), (25, 757842480), (26, -702543840), (27, 176513400), (30, 6273925920), (32, -1731129120), (34, 317084640), (37, 366314400), (39, 732628800), (42, -534638880), (43, -6457682880), (45, 1483824960), (49, 741912480), (50, -738817920), (51, 282431520), (54, -288966240), (58, -732628800), (70, 366314400), (73, 732628800), (77, 302594400), (79, -494608320), (87, 732628800), (88, -416482560), (94, 1465257600), (96, 741912480), (103, 474593040), (109, 1483824960), (132, -122104800)]

def pairMerged80 : Integer.Sparse (Fin 271) := [(0, 120125376), (1, -884250330), (2, -174119190), (3, -771917280), (4, 2505269280), (5, 296443560), (6, -18007140), (7, -465488640), (8, -109334880), (10, 1068461280), (12, -2108773440), (13, -5698460160), (23, -408237120), (24, -280136160), (26, 1205945280), (27, 70034040), (30, -560272320), (32, 2849230080), (34, -1000421760), (35, -1068461280), (37, -2136922560), (39, -2136922560), (42, 1680816960), (44, 3361633920), (50, -1400680800), (51, -949743360), (53, 1780768800), (54, 508188960), (55, -1120544640), (58, 1424615040), (70, -1068461280), (73, -2136922560), (75, 840408480), (97, 1680816960), (99, 1680816960), (132, 356153760), (143, -280136160)]

def pairMerged81 : Integer.Sparse (Fin 271) := [(0, -33733836), (1, 2038082280), (2, 291902880), (3, -10373829120), (4, -3986889600), (5, -165694800), (6, 8284740), (7, 795335040), (10, 1992168000), (12, -3551846400), (13, -1782307200), (23, 1328112000), (24, 2656224000), (25, 1594500480), (26, 265111680), (27, -166014000), (32, 3721777920), (34, 1325558400), (40, 2386005120), (49, -3984336000), (51, 1060446720), (54, 5312448000), (58, 799165440), (71, 1193002560), (73, 2386005120), (77, -1992168000), (78, -3984336000), (87, -799165440), (93, -1598330880), (133, -1193002560)]

def pairMerged82 : Integer.Sparse (Fin 271) := [(0, 86391540), (1, 1153831950), (2, 117783690), (3, -11145746400), (4, -1481620320), (5, 130748760), (6, -9722400), (7, 329846400), (8, -109334880), (10, 3060629280), (12, -5660619840), (13, -7480767360), (23, 919874880), (24, 2376087840), (25, 1594500480), (26, 1471056960), (27, -95979960), (30, -560272320), (32, 6571008000), (34, 325136640), (35, -1068461280), (37, -2136922560), (39, -2136922560), (40, 2386005120), (42, 1680816960), (44, 3361633920), (49, -3984336000), (50, -1400680800), (51, 110703360), (53, 1780768800), (54, 5820636960), (55, -1120544640), (58, 2223780480), (70, -1068461280), (71, 1193002560), (73, 249082560), (75, 840408480), (77, -1992168000), (78, -3984336000), (87, -799165440), (93, -1598330880), (97, 1680816960), (99, 1680816960), (132, 356153760), (133, -1193002560), (143, -280136160)]

def pairMerged83 : Integer.Sparse (Fin 271) := [(0, -206753685), (1, 3363155580), (2, 48257850), (3, -10990531200), (4, -6129924480), (5, -68443500), (6, -3440265), (7, 1324982880), (8, 88598880), (10, 2593450080), (12, -3647939760), (13, -5942077440), (23, -235212480), (24, 2355665760), (25, 2352342960), (26, 768513120), (27, 80533440), (30, 5713653600), (32, 4839878880), (34, 642221280), (35, -1068461280), (37, -1770608160), (39, -1404293760), (40, 2386005120), (42, 1146178080), (43, -6457682880), (44, 3361633920), (45, 1483824960), (49, -3242423520), (50, -2139498720), (51, 393134880), (53, 1780768800), (54, 5531670720), (55, -1120544640), (58, 1491151680), (70, -702146880), (71, 1193002560), (73, 981711360), (75, 840408480), (77, -1689573600), (78, -3984336000), (79, -494608320), (87, -66536640), (88, -416482560), (93, -1598330880), (94, 1465257600), (96, 741912480), (97, 1680816960), (99, 1680816960), (103, 474593040), (109, 1483824960), (132, 234048960), (133, -1193002560), (143, -280136160)]

def pairMerged84 : Integer.Sparse (Fin 271) := [(0, -24225408), (1, -520643520), (2, 412390080), (3, 5499141120), (4, 380989440), (5, -208177920), (6, 483840), (7, 843033600), (8, 360345600), (10, -266388480), (12, 3159475200), (13, 4384558080), (23, -814648320), (25, -297354240), (26, 23224320), (27, 199791360), (32, -1065553920), (34, 393891840), (37, 1644779520), (40, 23224320), (42, 46448640), (50, -2131107840), (51, 18063360), (53, -2154332160), (54, -532776960), (58, -1864719360), (70, 799165440), (72, 1598330880), (82, 23224320), (87, 799165440), (89, 46448640), (90, 46448640), (93, 1598330880), (132, -799165440), (143, -7741440)]

def pairMerged85 : Integer.Sparse (Fin 271) := [(0, 134737452), (1, -1845817140), (2, 2232398700), (3, 14382169920), (4, 4618878720), (5, -2339038800), (6, 196839540), (7, 2817291840), (8, 3380323200), (12, 2651221440), (13, 1579803840), (23, -692671680), (25, -887132160), (26, 3029967360), (30, -3186930240), (32, -2272475520), (34, 2281583040), (37, 665349120), (38, 1330698240), (40, 1330698240), (43, 4156030080), (45, 1330698240), (50, -4599596160), (51, 3131217600), (53, -3436035840), (79, -1828909440), (82, 665349120), (83, 1330698240), (88, 2743364160), (91, 4156030080), (92, 4156030080), (95, 1330698240), (143, -665349120)]

def pairMerged86 : Integer.Sparse (Fin 271) := [(0, 110512044), (1, -2366460660), (2, 2644788780), (3, 19881311040), (4, 4999868160), (5, -2547216720), (6, 197323380), (7, 3660325440), (8, 3740668800), (10, -266388480), (12, 5810696640), (13, 5964361920), (23, -1507320000), (25, -1184486400), (26, 3053191680), (27, 199791360), (30, -3186930240), (32, -3338029440), (34, 2675474880), (37, 2310128640), (38, 1330698240), (40, 1353922560), (42, 46448640), (43, 4156030080), (45, 1330698240), (50, -6730704000), (51, 3149280960), (53, -5590368000), (54, -532776960), (58, -1864719360), (70, 799165440), (72, 1598330880), (79, -1828909440), (82, 688573440), (83, 1330698240), (87, 799165440), (88, 2743364160), (89, 46448640), (90, 46448640), (91, 4156030080), (92, 4156030080), (93, 1598330880), (95, 1330698240), (132, -799165440), (143, -673090560)]

def pairMerged87 : Integer.Sparse (Fin 271) := [(0, -26950692), (1, 474048720), (2, -297758820), (3, -3498460800), (4, -1668121920), (5, 213230400), (6, -13666560), (7, -545931840), (8, -325805760), (12, -259219200), (13, -189710400), (23, 30415680), (24, 325805760), (25, 60831360), (26, -1440779520), (30, 386637120), (32, 182494080), (34, -349005120), (36, -1329255360), (39, -886170240), (40, -91247040), (42, -182494080), (50, 91247040), (51, -240403200), (53, 60831360), (55, 738475200), (58, 60831360), (71, -91247040), (79, 651611520), (81, -443085120), (83, -886170240), (87, -182494080), (88, -91247040), (91, -886170240), (95, -182494080), (96, -182494080), (99, -886170240), (133, 30415680), (143, 590780160)]

def pairMerged88 : Integer.Sparse (Fin 271) := [(0, -93518736), (1, 1572881520), (2, -1269205920), (3, -7046931840), (4, -3110424960), (5, 861883680), (6, -41056800), (7, -1152063360), (8, -1474335360), (12, -661854720), (13, -330927360), (24, 992782080), (25, 992782080), (26, -1632380160), (29, -7418880), (30, 2970927360), (32, 2481955200), (34, -493918080), (38, -2978346240), (39, 22256640), (41, -2978346240), (43, -1489173120), (51, -821136000), (53, 992782080), (55, 488972160), (56, 22256640), (79, 985363200), (83, -1478044800), (84, -1478044800), (89, -1489173120), (91, -2978346240), (92, -1489173120), (99, 22256640), (143, 492681600), (149, 22256640)]

def pairMerged89 : Integer.Sparse (Fin 271) := [(0, -120469428), (1, 2046930240), (2, -1566964740), (3, -10545392640), (4, -4778546880), (5, 1075114080), (6, -54723360), (7, -1697995200), (8, -1800141120), (12, -921073920), (13, -520637760), (23, 30415680), (24, 1318587840), (25, 1053613440), (26, -3073159680), (29, -7418880), (30, 3357564480), (32, 2664449280), (34, -842923200), (36, -1329255360), (38, -2978346240), (39, -863913600), (40, -91247040), (41, -2978346240), (42, -182494080), (43, -1489173120), (50, 91247040), (51, -1061539200), (53, 1053613440), (55, 1227447360), (56, 22256640), (58, 60831360), (71, -91247040), (79, 1636974720), (81, -443085120), (83, -2364215040), (84, -1478044800), (87, -182494080), (88, -91247040), (89, -1489173120), (91, -3864516480), (92, -1489173120), (95, -182494080), (96, -182494080), (99, -863913600), (133, 30415680), (143, 1083461760), (149, 22256640)]

def pairMerged90 : Integer.Sparse (Fin 271) := [(0, -9957384), (1, -319530420), (2, 1077824040), (3, 9335918400), (4, 221321280), (5, -1472102640), (6, 142600020), (7, 1962330240), (8, 1940527680), (10, -266388480), (12, 4889622720), (13, 5443724160), (23, -1476904320), (24, 1318587840), (25, -130872960), (26, -19968000), (27, 199791360), (29, -7418880), (30, 170634240), (32, -673580160), (34, 1832551680), (36, -1329255360), (37, 2310128640), (38, -1647648000), (39, -863913600), (40, 1262675520), (41, -2978346240), (42, -136045440), (43, 2666856960), (45, 1330698240), (50, -6639456960), (51, 2087741760), (53, -4536754560), (54, -532776960), (55, 1227447360), (56, 22256640), (58, -1803888000), (70, 799165440), (71, -91247040), (72, 1598330880), (79, -191934720), (81, -443085120), (82, 688573440), (83, -1033516800), (84, -1478044800), (87, 616671360), (88, 2652117120), (89, -1442724480), (90, 46448640), (91, 291513600), (92, 2666856960), (93, 1598330880), (95, 1148204160), (96, -182494080), (99, -863913600), (132, -799165440), (133, 30415680), (143, 410371200), (149, 22256640)]

def pairMerged91 : Integer.Sparse (Fin 271) := [(0, -216711069), (1, 3043625160), (2, 1126081890), (3, -1654612800), (4, -5908603200), (5, -1540546140), (6, 139159755), (7, 3287313120), (8, 2029126560), (10, 2327061600), (12, 1241682960), (13, -498353280), (23, -1712116800), (24, 3674253600), (25, 2221470000), (26, 748545120), (27, 280324800), (29, -7418880), (30, 5884287840), (32, 4166298720), (34, 2474772960), (35, -1068461280), (36, -1329255360), (37, 539520480), (38, -1647648000), (39, -2268207360), (40, 3648680640), (41, -2978346240), (42, 1010132640), (43, -3790825920), (44, 3361633920), (45, 2814523200), (49, -3242423520), (50, -8778955680), (51, 2480876640), (53, -2755985760), (54, 4998893760), (55, 106902720), (56, 22256640), (58, -312736320), (70, 97018560), (71, 1101755520), (72, 1598330880), (73, 981711360), (75, 840408480), (77, -1689573600), (78, -3984336000), (79, -686543040), (81, -443085120), (82, 688573440), (83, -1033516800), (84, -1478044800), (87, 550134720), (88, 2235634560), (89, -1442724480), (90, 46448640), (91, 291513600), (92, 2666856960), (94, 1465257600), (95, 1148204160), (96, 559418400), (97, 1680816960), (99, 816903360), (103, 474593040), (109, 1483824960), (132, -565116480), (133, -1162586880), (143, 130235040), (149, 22256640)]

def pairMerged92 : Integer.Sparse (Fin 271) := [(0, -79054095), (1, 56398280), (2, 3846535745), (3, 11396379840), (4, -5117910240), (5, -2888678400), (6, 209485220), (7, 4328498880), (8, 3716353440), (10, 566075520), (12, 6752568480), (13, 17456121360), (23, -7075563840), (24, -13861622880), (25, 3852098640), (26, 2019352320), (27, 6837519600), (29, -10568027520), (30, 7992247680), (31, 1811793920), (32, 6394680000), (33, 3276760320), (34, 5149769760), (35, -1068461280), (36, -1329255360), (37, 539520480), (38, -1647648000), (39, -2268207360), (40, 3648680640), (41, -2978346240), (42, -1306048320), (43, -3790825920), (44, 3361633920), (45, 1314109440), (46, -1108563840), (47, -554281920), (49, -3911058000), (50, -7341639840), (51, 6807983520), (53, -3291948000), (54, -4369269600), (55, 1128928320), (56, 22256640), (58, -3828153600), (59, 2264051200), (60, -4070315520), (61, -8294400), (62, 316909440), (63, 165807360), (64, 2764800), (65, 309242880), (70, -2661120), (71, 1364031360), (72, 1359849600), (73, 1346025600), (74, -78243840), (75, 101606400), (76, 22809600), (77, 25453440), (79, -1502069760), (81, 333987840), (82, 87886080), (83, 873400320), (84, 80317440), (87, -4147200), (88, 2235634560), (89, -1442724480), (90, 46448640), (91, 291513600), (92, 2666856960), (94, 1465257600), (95, 1148204160), (96, -223568640), (97, 1680816960), (98, -1500413760), (99, -683510400), (103, 83099520), (109, -16588800), (110, 357477120), (115, 1356771840), (132, -465436800), (133, -1424862720), (143, -584559360), (149, 22256640)]

def pairMerged93 : Integer.Sparse (Fin 271) := [(0, -13415520), (1, 449411040), (2, -212304480), (3, -2726760960), (4, -886018560), (5, 114967680), (6, -5772000), (7, -306370560), (8, -184704000), (12, -670740480), (13, -269498880), (23, 187223040), (25, 275166720), (26, -797445120), (30, 187223040), (32, 926668800), (34, -149721600), (35, -561669120), (36, -550333440), (37, 11335680), (38, -1100666880), (39, -1100666880), (50, -3778560), (51, -57369600), (53, 277056000), (54, 917222400), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -561669120), (86, 11335680), (92, -561669120), (96, 5667840), (143, 368778240)]

def pairMerged94 : Integer.Sparse (Fin 271) := [(0, 70933458), (1, -1089863490), (2, 104713560), (3, -75570720), (4, 2243430720), (5, 113526360), (7, -605473920), (8, -151368480), (12, -1927470720), (13, -264399360), (23, 454105440), (24, 756842400), (25, -281586240), (26, 653948160), (27, -227052720), (30, -2640029760), (32, 793198080), (34, -100912320), (45, 2942766720), (46, 735691680), (47, -1189797120), (50, 756842400), (53, 302736960), (89, 1471383360), (92, -2379594240), (97, -2379594240), (98, 1471383360)]

def pairMerged95 : Integer.Sparse (Fin 271) := [(0, 57517938), (1, -640452450), (2, -107590920), (3, -2802331680), (4, 1357412160), (5, 228494040), (6, -5772000), (7, -911844480), (8, -336072480), (12, -2598211200), (13, -533898240), (23, 641328480), (24, 756842400), (25, -6419520), (26, -143496960), (27, -227052720), (30, -2452806720), (32, 1719866880), (34, -250633920), (35, -561669120), (36, -550333440), (37, 11335680), (38, -1100666880), (39, -1100666880), (45, 2942766720), (46, 735691680), (47, -1189797120), (50, 753063840), (51, -57369600), (53, 579792960), (54, 917222400), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -561669120), (86, 11335680), (89, 1471383360), (92, -2941263360), (96, 5667840), (97, -2379594240), (98, 1471383360), (143, 368778240)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged96 : Integer.Sparse (Fin 271) := [(0, 40425504), (1, 992250960), (2, -1041076380), (3, -9857577600), (4, -1364895360), (5, 815193360), (6, -42664860), (7, -2274825600), (8, -1061585280), (10, 1364895360), (12, -4246341120), (13, -6066201600), (23, -226912320), (25, -226912320), (26, -1213240320), (27, 132365520), (29, -226912320), (30, -453824640), (32, 1819860480), (34, -1971515520), (36, -1364895360), (38, -1364895360), (39, -1364895360), (40, -2729790720), (50, 1819860480), (51, -1516550400), (53, 909930240), (54, 1364895360), (58, 1819860480), (62, -151274880), (66, 37818720), (71, -1364895360), (72, -1364895360), (73, -1364895360), (88, -2729790720), (94, -1364895360), (95, -1364895360), (97, 680736960), (111, -226912320), (130, -75637440), (133, 454965120), (146, -453824640), (147, -226912320)]

def pairMerged97 : Integer.Sparse (Fin 271) := [(0, -840036), (1, -273783220), (2, 95774080), (3, 1551519360), (4, 634048320), (5, -53940320), (6, 558600), (7, 386376000), (8, 26812800), (12, 158125440), (13, 127302400), (23, 210375360), (24, -671345280), (26, 298375680), (27, -45890640), (29, 420750720), (30, -447563520), (34, 276490240), (50, -1145721600), (51, 149187840), (53, -13406400), (54, -223781760), (55, -559454400), (66, -72359520), (88, 671345280), (89, 335672640), (99, 671345280), (111, 434157120), (130, 144719040), (146, 868314240), (148, -335672640)]

def pairMerged98 : Integer.Sparse (Fin 271) := [(0, 39585468), (1, 718467740), (2, -945302300), (3, -8306058240), (4, -730847040), (5, 761253040), (6, -42106260), (7, -1888449600), (8, -1034772480), (10, 1364895360), (12, -4088215680), (13, -5938899200), (23, -16536960), (24, -671345280), (25, -226912320), (26, -914864640), (27, 86474880), (29, 193838400), (30, -901388160), (32, 1819860480), (34, -1695025280), (36, -1364895360), (38, -1364895360), (39, -1364895360), (40, -2729790720), (50, 674138880), (51, -1367362560), (53, 896523840), (54, 1141113600), (55, -559454400), (58, 1819860480), (62, -151274880), (66, -34540800), (71, -1364895360), (72, -1364895360), (73, -1364895360), (88, -2058445440), (89, 335672640), (94, -1364895360), (95, -1364895360), (97, 680736960), (99, 671345280), (111, 207244800), (130, 69081600), (133, 454965120), (146, 414489600), (147, -226912320), (148, -335672640)]

def pairMerged99 : Integer.Sparse (Fin 271) := [(0, 97103406), (1, 78015290), (2, -1052893220), (3, -11108389920), (4, 626565120), (5, 989747080), (6, -47878260), (7, -2800294080), (8, -1370844960), (10, 1364895360), (12, -6686426880), (13, -6472797440), (23, 624791520), (24, 85497120), (25, -233331840), (26, -1058361600), (27, -140577840), (29, 193838400), (30, -3354194880), (32, 3539727360), (34, -1945659200), (35, -561669120), (36, -1915228800), (37, 11335680), (38, -2465562240), (39, -2465562240), (40, -2729790720), (45, 2942766720), (46, 735691680), (47, -1189797120), (50, 1427202720), (51, -1424732160), (53, 1476316800), (54, 2058336000), (55, -559454400), (58, 1819860480), (62, -151274880), (66, -34540800), (71, -1364895360), (72, -1364895360), (73, -1364895360), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -561669120), (86, 11335680), (88, -2058445440), (89, 1807056000), (92, -2941263360), (94, -1364895360), (95, -1364895360), (96, 5667840), (97, -1698857280), (98, 1471383360), (99, 671345280), (111, 207244800), (130, 69081600), (133, 454965120), (143, 368778240), (146, 414489600), (147, -226912320), (148, -335672640)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged211 : Integer.Sparse (Fin 271) := [(0, -532224), (1, -1477920), (2, 24761760), (3, 209978880), (4, 53959680), (5, -43305600), (6, 5092800), (7, 57223680), (8, 34867200), (10, -13340160), (12, 29591040), (13, 94648320), (26, 64158720), (32, -26680320), (33, 5928960), (34, 104847360), (35, 13340160), (37, 19215360), (39, 65111040), (51, 78520320), (53, -26150400), (54, -32555520), (55, -43407360), (58, -30597120), (59, 4270080), (70, 13340160), (73, 26680320), (79, -61194240), (80, 14945280), (81, 26680320), (82, 38430720), (83, 130222080), (115, 14945280), (132, -17256960), (133, -25620480), (143, -74004480), (159, -8893440), (179, -19215360), (180, -26680320), (189, 26680320), (195, 38430720), (201, 76861440), (202, 53360640), (212, 26680320), (213, 53360640), (223, 26680320), (224, 19215360), (226, 53360640), (232, 106721280), (236, 38430720), (237, 76861440), (248, -17786880), (249, -25620480), (258, 38430720), (262, 153722880)]

def pairMerged212 : Integer.Sparse (Fin 271) := [(0, -34560), (1, 1468800), (2, 1900800), (3, 10368000), (5, -3628800), (6, 604800), (7, -2073600), (8, 2764800), (10, -4147200), (12, 4838400), (13, 22118400), (23, 2073600), (27, -518400), (31, 2764800), (34, 691200), (50, 4147200), (51, 12441600), (53, 8294400), (58, -6220800), (59, -1382400), (61, 8294400), (73, 12441600), (80, 6220800), (90, -12441600), (115, 9676800), (132, -2073600), (133, -16588800), (147, 4147200), (179, -2073600), (207, -12441600), (209, 24883200), (224, -6220800), (227, 12441600), (258, 12441600)]

def pairMerged213 : Integer.Sparse (Fin 271) := [(0, -566784), (1, -9120), (2, 26662560), (3, 220346880), (4, 53959680), (5, -46934400), (6, 5697600), (7, 55150080), (8, 37632000), (10, -17487360), (12, 34429440), (13, 116766720), (23, 2073600), (26, 64158720), (27, -518400), (31, 2764800), (32, -26680320), (33, 5928960), (34, 105538560), (35, 13340160), (37, 19215360), (39, 65111040), (50, 4147200), (51, 90961920), (53, -17856000), (54, -32555520), (55, -43407360), (58, -36817920), (59, 2887680), (61, 8294400), (70, 13340160), (73, 39121920), (79, -61194240), (80, 21166080), (81, 26680320), (82, 38430720), (83, 130222080), (90, -12441600), (115, 24622080), (132, -19330560), (133, -42209280), (143, -74004480), (147, 4147200), (159, -8893440), (179, -21288960), (180, -26680320), (189, 26680320), (195, 38430720), (201, 76861440), (202, 53360640), (207, -12441600), (209, 24883200), (212, 26680320), (213, 53360640), (223, 26680320), (224, 12994560), (226, 53360640), (227, 12441600), (232, 106721280), (236, 38430720), (237, 76861440), (248, -17786880), (249, -25620480), (258, 50872320), (262, 153722880)]

def pairMerged214 : Integer.Sparse (Fin 271) := [(0, 88864), (1, 623600), (2, -1647120), (3, -22728960), (4, -2764800), (5, 4391360), (6, -304800), (7, -20413440), (8, -4124160), (9, -4160), (10, 1209600), (12, -3857920), (13, -5803520), (23, -299520), (24, 1658880), (26, -6635520), (27, -339840), (33, -1105920), (34, -26176000), (36, -9953280), (37, 449280), (50, 2419200), (51, -10506240), (53, -898560), (54, 3168000), (58, 2568960), (59, -2211840), (65, -1105920), (66, 12480), (67, 49920), (68, 33280), (70, 898560), (71, -4976640), (72, 898560), (79, 3317760), (80, 49920), (81, -9953280), (82, -24883200), (111, -149760), (130, -99840), (132, -499200), (143, 8294400), (153, -299520), (160, 3317760), (168, 449280), (181, -149760), (184, -9953280), (190, -9953280), (193, 449280), (229, 299520), (246, -149760), (248, -49920)]

def pairMerged215 : Integer.Sparse (Fin 271) := [(0, -17136), (1, -504240), (2, 2413680), (3, 20778240), (4, 7868160), (5, -2706240), (6, 208080), (7, 5372160), (8, 2641920), (9, 101760), (10, 1336320), (11, 1105920), (12, -648960), (13, -445440), (24, 1336320), (26, 12049920), (27, -334080), (30, -1105920), (32, -4423680), (33, 737280), (34, 8601600), (36, 2972160), (50, 1451520), (51, 6278400), (54, -990720), (58, 840960), (65, 330240), (66, -152640), (67, -1628160), (68, -1221120), (71, -4008960), (79, -16473600), (81, 13271040), (82, 11439360), (83, 19906560), (111, 610560), (113, 1221120), (131, 1221120), (143, -18190080), (153, 1221120), (160, -2211840), (181, 1221120), (184, 3317760), (187, 6635520), (190, 6635520), (193, -1831680), (194, -3663360), (218, -3317760), (226, -3663360), (228, -3663360), (248, 610560)]

def pairMerged216 : Integer.Sparse (Fin 271) := [(0, 71728), (1, 119360), (2, 766560), (3, -1950720), (4, 5103360), (5, 1685120), (6, -96720), (7, -15041280), (8, -1482240), (9, 97600), (10, 2545920), (11, 1105920), (12, -4506880), (13, -6248960), (23, -299520), (24, 2995200), (26, 5414400), (27, -673920), (30, -1105920), (32, -4423680), (33, -368640), (34, -17574400), (36, -6981120), (37, 449280), (50, 3870720), (51, -4227840), (53, -898560), (54, 2177280), (58, 3409920), (59, -2211840), (65, -775680), (66, -140160), (67, -1578240), (68, -1187840), (70, 898560), (71, -8985600), (72, 898560), (79, -13155840), (80, 49920), (81, 3317760), (82, -13443840), (83, 19906560), (111, 460800), (113, 1221120), (130, -99840), (131, 1221120), (132, -499200), (143, -9895680), (153, 921600), (160, 1105920), (168, 449280), (181, 1071360), (184, -6635520), (187, 6635520), (190, -3317760), (193, -1382400), (194, -3663360), (218, -3317760), (226, -3663360), (228, -3663360), (229, 299520), (246, -149760), (248, 560640)]

def pairMerged217 : Integer.Sparse (Fin 271) := [(0, -495056), (1, 110240), (2, 27429120), (3, 218396160), (4, 59063040), (5, -45249280), (6, 5600880), (7, 40108800), (8, 36149760), (9, 97600), (10, -14941440), (11, 1105920), (12, 29922560), (13, 110517760), (23, 1774080), (24, 2995200), (26, 69573120), (27, -1192320), (30, -1105920), (31, 2764800), (32, -31104000), (33, 5560320), (34, 87964160), (35, 13340160), (36, -6981120), (37, 19664640), (39, 65111040), (50, 8017920), (51, 86734080), (53, -18754560), (54, -30378240), (55, -43407360), (58, -33408000), (59, 675840), (61, 8294400), (65, -775680), (66, -140160), (67, -1578240), (68, -1187840), (70, 14238720), (71, -8985600), (72, 898560), (73, 39121920), (79, -74350080), (80, 21216000), (81, 29998080), (82, 24986880), (83, 150128640), (90, -12441600), (111, 460800), (113, 1221120), (115, 24622080), (130, -99840), (131, 1221120), (132, -19829760), (133, -42209280), (143, -83900160), (147, 4147200), (153, 921600), (159, -8893440), (160, 1105920), (168, 449280), (179, -21288960), (180, -26680320), (181, 1071360), (184, -6635520), (187, 6635520), (189, 26680320), (190, -3317760), (193, -1382400), (194, -3663360), (195, 38430720), (201, 76861440), (202, 53360640), (207, -12441600), (209, 24883200), (212, 26680320), (213, 53360640), (218, -3317760), (223, 26680320), (224, 12994560), (226, 49697280), (227, 12441600), (228, -3663360), (229, 299520), (232, 106721280), (236, 38430720), (237, 76861440), (246, -149760), (248, -17226240), (249, -25620480), (258, 50872320), (262, 153722880)]

def pairMerged218 : Integer.Sparse (Fin 271) := [(0, -1101152), (1, 31412480), (2, -4811520), (3, -200816640), (4, -123313920), (5, -1888000), (6, 1113120), (7, -77084160), (8, 3056640), (9, 97600), (10, -61735680), (11, -29683200), (12, 38800640), (13, 140915200), (23, 1520640), (24, 6773760), (25, 3548160), (26, -176409600), (27, -783360), (30, -1059840), (31, 2764800), (32, -4285440), (33, 3563520), (34, -134686720), (35, -8363520), (36, -98150400), (37, 50630400), (38, -30136320), (39, -97873920), (40, -4147200), (50, -5898240), (51, -3936000), (53, -2304000), (54, 74522880), (55, 36334080), (58, -76446720), (59, 8478720), (61, 8294400), (63, 10321920), (65, -27033600), (66, -140160), (67, -1578240), (68, -1187840), (70, 14999040), (71, -63002880), (72, 9607680), (73, -18593280), (79, 98196480), (80, 26346240), (81, -1382400), (82, -63417600), (83, -86676480), (85, 6635520), (86, 13271040), (90, -12441600), (91, 8294400), (95, 8294400), (96, -15482880), (110, -14376960), (111, 460800), (113, 1221120), (115, 26065920), (130, -99840), (131, 1221120), (132, -15797760), (133, 1486080), (142, -6635520), (143, 141477120), (147, -829440), (153, 921600), (159, -3732480), (160, -2350080), (161, 6451200), (168, 449280), (179, -17971200), (180, -26680320), (181, 1071360), (184, 35804160), (185, -43407360), (186, 58337280), (187, -36771840), (188, 21565440), (189, 4976640), (190, -22671360), (191, 16588800), (193, -23086080), (194, -3663360), (195, 38430720), (196, -8294400), (201, 33454080), (202, -33454080), (207, -20736000), (209, 16588800), (211, -15482880), (212, 26680320), (213, 34007040), (215, -19353600), (218, 18385920), (219, 14469120), (223, 33315840), (224, -2488320), (225, -8294400), (226, -31795200), (228, -85155840), (229, 6935040), (231, 26542080), (232, -219248640), (233, -19353600), (236, 51701760), (237, -86123520), (244, -19353600), (245, -5253120), (246, -4573440), (248, -17226240), (249, -25620480), (258, 42577920), (259, 13271040), (262, -9262080), (263, 54328320)]

def pairMerged219 : Integer.Sparse (Fin 271) := [(0, -833888), (1, 12376640), (2, 32176480), (3, -9638400), (4, -58172160), (5, -57547520), (6, 4680000), (7, 64035840), (8, 91130880), (9, -696000), (10, -90766080), (11, -7349760), (12, 29945600), (13, 68830720), (23, -21173760), (24, -114094080), (25, 29675520), (26, -85009920), (27, 33678720), (29, -43683840), (30, -23961600), (31, 2764800), (32, -17372160), (33, 3563520), (34, 2091520), (35, -12026880), (36, -40573440), (37, -33281280), (38, -44098560), (39, -99947520), (40, -4147200), (42, 9123840), (44, -11612160), (45, 10782720), (46, 9123840), (48, 18247680), (50, -30873600), (51, 22598400), (52, 18385920), (53, 70295040), (54, -77679360), (55, 56862720), (58, -99164160), (59, 3763200), (61, 8294400), (62, -2396160), (63, 10321920), (65, -1781760), (66, 7171200), (67, 5702400), (68, 522240), (69, 7464960), (70, 414720), (71, 13858560), (72, 86469120), (73, 29099520), (75, 4561920), (79, 24192000), (80, 7829760), (81, -30758400), (82, -46759680), (83, -170449920), (85, 2972160), (86, 13271040), (88, 39813120), (90, -7050240), (91, 10091520), (94, -23224320), (95, 5806080), (96, -15482880), (98, 47278080), (99, 58060800), (110, -12533760), (111, 1105920), (112, -17556480), (113, -79557120), (115, 7664640), (130, 2557440), (131, -31449600), (132, -7342080), (133, 13512960), (142, -5414400), (143, 101456640), (146, -37601280), (147, -17763840), (148, -19353600), (153, 8847360), (154, -3594240), (155, 6635520), (159, -3732480), (160, -2350080), (161, 6451200), (168, -12337920), (170, -10368000), (171, 5391360), (174, 19077120), (176, -9123840), (177, 9953280), (179, -45826560), (180, -65111040), (181, -3697920), (182, 3732480), (184, -24330240), (185, -9400320), (187, -36771840), (188, 16035840), (189, 4976640), (190, -22671360), (191, 16588800), (193, -66493440), (194, 8916480), (195, 9123840), (196, -8294400), (199, -9953280), (201, -13271040), (207, -15344640), (209, 16588800), (211, 22947840), (212, 26680320), (213, 110868480), (215, -967680), (218, 38430720), (219, 39398400), (223, 11404800), (224, 8294400), (225, 28477440), (226, 6220800), (228, -8294400), (229, -22233600), (231, 96076800), (232, -104371200), (233, 21012480), (234, 27371520), (236, 27924480), (240, 9123840), (241, 9123840), (243, 18385920), (244, 17418240), (245, 7741440), (246, 6178560), (248, -68467200), (249, -58183680), (250, 21565440), (251, 10782720), (252, 9123840), (253, 10782720), (254, -11612160), (258, 50181120), (259, 42716160), (260, -2442240), (262, -14653440), (263, 83496960), (265, 18247680), (266, 18247680), (267, 18247680), (270, -11612160)]

def pairMerged220 : Integer.Sparse (Fin 271) := [(0, 68352), (1, 6241920), (2, -14732160), (3, -135813120), (4, -41533440), (5, 23884800), (6, -2338560), (7, -66508800), (8, -21381120), (9, 207360), (10, 1658880), (11, -11182080), (23, 1658880), (25, 829440), (26, -72499200), (27, -414720), (34, -91637760), (35, -2488320), (51, -46387200), (52, -28753920), (53, 4147200), (54, 829440), (63, 1658880), (65, -4577280), (66, -207360), (67, -2764800), (68, -1382400), (70, -4976640), (79, 57507840), (81, -33730560), (82, -71884800), (83, -86261760), (112, 2488320), (113, 1658880), (132, 1658880), (143, 99164160), (154, 1658880), (159, 1658880), (171, -2488320), (181, 829440), (189, -4976640), (211, -2488320), (219, 829440), (223, -2488320), (226, -4976640), (243, -28753920), (244, -28753920), (248, 829440)]

def pairMerged221 : Integer.Sparse (Fin 271) := [(0, 144000), (1, -1526400), (2, -2442240), (3, 8847360), (4, 9492480), (5, 3002880), (6, 422400), (7, -4608000), (8, -11950080), (10, 27648000), (11, 1259520), (12, -13148160), (13, -20674560), (26, 19568640), (32, 5529600), (33, 675840), (34, 20828160), (36, 11335680), (37, -8294400), (51, 11980800), (53, 2764800), (55, -3778560), (58, 40458240), (59, 675840), (65, 5038080), (70, -16588800), (71, -10506240), (72, -16588800), (73, -33177600), (79, -13639680), (80, -3686400), (81, 11335680), (82, 17418240), (115, -3348480), (132, 8294400), (133, 3502080), (143, -17141760), (159, 5529600), (161, -7557120), (180, 8294400), (190, 22671360), (191, -16588800), (212, -8294400), (213, -5253120), (215, 11335680), (224, -8294400), (233, 11335680), (244, 11335680)]

def pairMerged222 : Integer.Sparse (Fin 271) := [(0, 212352), (1, 4715520), (2, -17174400), (3, -126965760), (4, -32040960), (5, 26887680), (6, -1916160), (7, -71116800), (8, -33331200), (9, 207360), (10, 29306880), (11, -9922560), (12, -13148160), (13, -20674560), (23, 1658880), (25, 829440), (26, -52930560), (27, -414720), (32, 5529600), (33, 675840), (34, -70809600), (35, -2488320), (36, 11335680), (37, -8294400), (51, -34406400), (52, -28753920), (53, 6912000), (54, 829440), (55, -3778560), (58, 40458240), (59, 675840), (63, 1658880), (65, 460800), (66, -207360), (67, -2764800), (68, -1382400), (70, -21565440), (71, -10506240), (72, -16588800), (73, -33177600), (79, 43868160), (80, -3686400), (81, -22394880), (82, -54466560), (83, -86261760), (112, 2488320), (113, 1658880), (115, -3348480), (132, 9953280), (133, 3502080), (143, 82022400), (154, 1658880), (159, 7188480), (161, -7557120), (171, -2488320), (180, 8294400), (181, 829440), (189, -4976640), (190, 22671360), (191, -16588800), (211, -2488320), (212, -8294400), (213, -5253120), (215, 11335680), (219, 829440), (223, -2488320), (224, -8294400), (226, -4976640), (233, 11335680), (243, -28753920), (244, -17418240), (248, 829440)]

def pairMerged223 : Integer.Sparse (Fin 271) := [(0, 435488), (1, -1013760), (2, -10526880), (3, -49251840), (4, -2757120), (5, 3029760), (6, 223680), (7, -2088960), (8, -7879680), (10, 10275840), (11, 1728000), (12, -30827520), (13, -62796800), (26, 18432000), (30, 10275840), (32, 20551680), (34, 4823040), (41, -61655040), (50, 41103360), (51, -25520640), (56, 10368000), (58, 41103360), (59, -6850560), (65, 5760000), (79, -3640320), (80, -3425280), (84, -40919040), (115, -13701120), (143, -5184000), (184, -30827520), (198, -61655040), (200, -61655040), (215, 10368000), (218, 10275840), (269, 31104000)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged224 : Integer.Sparse (Fin 271) := [(0, -60960), (1, -3736320), (2, -1071840), (3, 11066880), (4, 5130240), (5, 16114560), (6, -3816000), (7, 28776960), (8, 6481920), (9, 309120), (11, -2472960), (12, -545280), (13, 1382400), (25, 7418880), (26, 4730880), (30, 6543360), (32, 6543360), (34, -829440), (38, -22256640), (41, 12441600), (50, -8294400), (51, -37309440), (53, 7418880), (55, -2073600), (58, -8294400), (65, 4147200), (67, -1236480), (69, -4945920), (74, 12441600), (79, -20736000), (84, 12441600), (85, -11128320), (89, 6220800), (99, 12441600), (110, 14837760), (133, -2073600), (142, 3709440), (143, 7418880), (147, 11128320), (148, -6220800), (149, -22256640), (179, 11128320), (180, -6220800), (188, -44513280), (198, 24883200), (211, 6220800), (213, 12441600), (223, -11128320), (230, 12441600), (231, -22256640), (245, 14837760), (246, 3709440), (258, -22256640), (259, -22256640)]

def pairMerged225 : Integer.Sparse (Fin 271) := [(0, 374528), (1, -4750080), (2, -11598720), (3, -38184960), (4, 2373120), (5, 19144320), (6, -3592320), (7, 26688000), (8, -1397760), (9, 309120), (10, 10275840), (11, -744960), (12, -31372800), (13, -61414400), (25, 7418880), (26, 23162880), (30, 16819200), (32, 27095040), (34, 3993600), (38, -22256640), (41, -49213440), (50, 32808960), (51, -62830080), (53, 7418880), (55, -2073600), (56, 10368000), (58, 32808960), (59, -6850560), (65, 9907200), (67, -1236480), (69, -4945920), (74, 12441600), (79, -24376320), (80, -3425280), (84, -28477440), (85, -11128320), (89, 6220800), (99, 12441600), (110, 14837760), (115, -13701120), (133, -2073600), (142, 3709440), (143, 2234880), (147, 11128320), (148, -6220800), (149, -22256640), (179, 11128320), (180, -6220800), (184, -30827520), (188, -44513280), (198, -36771840), (200, -61655040), (211, 6220800), (213, 12441600), (215, 10368000), (218, 10275840), (223, -11128320), (230, 12441600), (231, -22256640), (245, 14837760), (246, 3709440), (258, -22256640), (259, -22256640), (269, 31104000)]

def pairMerged226 : Integer.Sparse (Fin 271) := [(0, 586880), (1, -34560), (2, -28773120), (3, -165150720), (4, -29667840), (5, 46032000), (6, -5508480), (7, -44428800), (8, -34728960), (9, 516480), (10, 39582720), (11, -10667520), (12, -44520960), (13, -82088960), (23, 1658880), (25, 8248320), (26, -29767680), (27, -414720), (30, 16819200), (32, 32624640), (33, 675840), (34, -66816000), (35, -2488320), (36, 11335680), (37, -8294400), (38, -22256640), (41, -49213440), (50, 32808960), (51, -97236480), (52, -28753920), (53, 14330880), (54, 829440), (55, -5852160), (56, 10368000), (58, 73267200), (59, -6174720), (63, 1658880), (65, 10368000), (66, -207360), (67, -4001280), (68, -1382400), (69, -4945920), (70, -21565440), (71, -10506240), (72, -16588800), (73, -33177600), (74, 12441600), (79, 19491840), (80, -7111680), (81, -22394880), (82, -54466560), (83, -86261760), (84, -28477440), (85, -11128320), (89, 6220800), (99, 12441600), (110, 14837760), (112, 2488320), (113, 1658880), (115, -17049600), (132, 9953280), (133, 1428480), (142, 3709440), (143, 84257280), (147, 11128320), (148, -6220800), (149, -22256640), (154, 1658880), (159, 7188480), (161, -7557120), (171, -2488320), (179, 11128320), (180, 2073600), (181, 829440), (184, -30827520), (188, -44513280), (189, -4976640), (190, 22671360), (191, -16588800), (198, -36771840), (200, -61655040), (211, 3732480), (212, -8294400), (213, 7188480), (215, 21703680), (218, 10275840), (219, 829440), (223, -13616640), (224, -8294400), (226, -4976640), (230, 12441600), (231, -22256640), (233, 11335680), (243, -28753920), (244, -17418240), (245, 14837760), (246, 3709440), (248, 829440), (258, -22256640), (259, -22256640), (269, 31104000)]

def pairMerged227 : Integer.Sparse (Fin 271) := [(0, -521280), (1, 9835200), (2, 22579200), (3, 80179200), (4, -1843200), (5, -44755200), (6, 5155200), (7, 49996800), (8, 42393600), (9, -633600), (12, 11289600), (13, 52300800), (26, -921600), (34, 80640000), (41, -8294400), (50, -9676800), (51, 80409600), (53, -7603200), (55, 5529600), (58, -15897600), (59, 13593600), (67, 5068800), (69, 17740800), (74, -8294400), (80, 9907200), (84, 37324800), (94, -8294400), (95, -8294400), (115, 15206400), (132, -7603200), (133, -19353600), (154, -15206400), (155, -15206400), (173, 22809600), (182, -22809600), (199, 45619200), (200, 29030400), (207, 14515200), (209, -8294400), (219, -7603200), (230, -16588800), (264, -8294400)]

def pairMerged228 : Integer.Sparse (Fin 271) := [(0, 130368), (1, -12079680), (2, 13476480), (3, 95831040), (4, 25175040), (5, 9181440), (6, -4536960), (7, 23070720), (8, 15528960), (9, 683520), (10, -6128640), (11, -5468160), (12, 35389440), (13, 46894080), (24, -6128640), (25, 8202240), (26, 1320960), (27, 1532160), (30, -18385920), (32, -49029120), (33, 8171520), (34, -19921920), (38, 12165120), (41, 36771840), (50, -63267840), (51, -19322880), (53, 16404480), (54, -12257280), (55, -8110080), (58, -44881920), (59, 8171520), (67, -2734080), (69, -10936320), (72, -6220800), (74, 36771840), (79, -24514560), (80, -5468160), (83, 36771840), (84, 36771840), (86, -24606720), (110, 16404480), (115, -1413120), (132, 8202240), (133, -1981440), (142, 8202240), (143, 4147200), (160, -12257280), (184, 55157760), (187, 36771840), (188, 24330240), (192, 36771840), (198, 73543680), (200, 36771840), (218, -18385920), (231, -73820160), (236, -24606720), (245, 16404480), (246, 8202240), (259, -24606720)]

def pairMerged229 : Integer.Sparse (Fin 271) := [(0, -390912), (1, -2244480), (2, 36055680), (3, 176010240), (4, 23331840), (5, -35573760), (6, 618240), (7, 73067520), (8, 57922560), (9, 49920), (10, -6128640), (11, -5468160), (12, 46679040), (13, 99194880), (24, -6128640), (25, 8202240), (26, 399360), (27, 1532160), (30, -18385920), (32, -49029120), (33, 8171520), (34, 60718080), (38, 12165120), (41, 28477440), (50, -72944640), (51, 61086720), (53, 8801280), (54, -12257280), (55, -2580480), (58, -60779520), (59, 21765120), (67, 2334720), (69, 6804480), (72, -6220800), (74, 28477440), (79, -24514560), (80, 4439040), (83, 36771840), (84, 74096640), (86, -24606720), (94, -8294400), (95, -8294400), (110, 16404480), (115, 13793280), (132, 599040), (133, -21335040), (142, 8202240), (143, 4147200), (154, -15206400), (155, -15206400), (160, -12257280), (173, 22809600), (182, -22809600), (184, 55157760), (187, 36771840), (188, 24330240), (192, 36771840), (198, 73543680), (199, 45619200), (200, 65802240), (207, 14515200), (209, -8294400), (218, -18385920), (219, -7603200), (230, -16588800), (231, -73820160), (236, -24606720), (245, 16404480), (246, 8202240), (259, -24606720), (264, -8294400)]

def pairMerged230 : Integer.Sparse (Fin 271) := [(0, 470400), (1, -2765760), (2, -27926400), (3, -97213440), (4, -13578240), (5, 39782400), (6, -1538880), (7, -96675840), (8, -72821760), (9, -57600), (12, -5406720), (13, -1920000), (24, -1382400), (25, 6128640), (26, -24253440), (27, 345600), (30, 10874880), (32, 15621120), (33, -4085760), (34, -53253120), (38, -14238720), (41, 4147200), (50, 9492480), (51, -14438400), (53, 9492480), (54, -1382400), (55, -6912000), (58, 12257280), (63, 12257280), (65, -10214400), (66, 172800), (67, 230400), (69, 921600), (72, -18385920), (79, 61286400), (80, 1843200), (83, -36771840), (84, -36771840), (91, 4147200), (92, -18385920), (99, -36771840), (110, -1382400), (111, -691200), (113, -1382400), (115, 1843200), (131, -1382400), (132, 4746240), (133, -2764800), (143, 12257280), (147, -1382400), (148, 18385920), (153, -1382400), (155, -2764800), (159, 12257280), (170, 2073600), (172, 4147200), (179, -2764800), (180, 18385920), (181, -1382400), (182, -691200), (185, 2073600), (188, 4147200), (192, -36771840), (198, -36771840), (200, 4147200), (201, 4147200), (211, -18385920), (212, -18385920), (213, -36771840), (225, -28477440), (230, 4147200), (245, -2073600), (249, -691200), (259, 4147200), (263, -2073600), (264, 8294400)]

def pairMerged231 : Integer.Sparse (Fin 271) := [(0, 1394496), (1, -17737920), (2, -42301440), (3, -135060480), (4, -14515200), (5, 75686400), (6, -6929280), (7, -100224000), (8, -85294080), (9, -34560), (11, -7188480), (12, -2626560), (13, -14376960), (23, -414720), (24, -2903040), (26, -39260160), (27, 1555200), (30, -4147200), (32, 21565440), (34, -86261760), (46, 1244160), (50, -8709120), (51, -81976320), (55, -1658880), (58, 10782720), (65, -7188480), (66, 311040), (67, 138240), (69, 138240), (73, -32348160), (79, 64696320), (83, -97044480), (84, -64696320), (111, -414720), (113, -2488320), (115, -3594240), (133, 10782720), (136, 1244160), (137, 2488320), (139, 2488320), (143, 64696320), (148, -1658880), (155, -829440), (181, -414720), (182, -414720), (213, -64696320), (233, -32348160), (234, 1244160), (256, 1244160), (257, 2488320), (258, -32348160), (269, -32348160)]

def pairMerged232 : Integer.Sparse (Fin 271) := [(0, 1864896), (1, -20503680), (2, -70227840), (3, -232273920), (4, -28093440), (5, 115468800), (6, -8468160), (7, -196899840), (8, -158115840), (9, -92160), (11, -7188480), (12, -8033280), (13, -16296960), (23, -414720), (24, -4285440), (25, 6128640), (26, -63513600), (27, 1900800), (30, 6727680), (32, 37186560), (33, -4085760), (34, -139514880), (38, -14238720), (41, 4147200), (46, 1244160), (50, 783360), (51, -96414720), (53, 9492480), (54, -1382400), (55, -8570880), (58, 23040000), (63, 12257280), (65, -17402880), (66, 483840), (67, 368640), (69, 1059840), (72, -18385920), (73, -32348160), (79, 125982720), (80, 1843200), (83, -133816320), (84, -101468160), (91, 4147200), (92, -18385920), (99, -36771840), (110, -1382400), (111, -1105920), (113, -3870720), (115, -1751040), (131, -1382400), (132, 4746240), (133, 8017920), (136, 1244160), (137, 2488320), (139, 2488320), (143, 76953600), (147, -1382400), (148, 16727040), (153, -1382400), (155, -3594240), (159, 12257280), (170, 2073600), (172, 4147200), (179, -2764800), (180, 18385920), (181, -1797120), (182, -1105920), (185, 2073600), (188, 4147200), (192, -36771840), (198, -36771840), (200, 4147200), (201, 4147200), (211, -18385920), (212, -18385920), (213, -101468160), (225, -28477440), (230, 4147200), (233, -32348160), (234, 1244160), (245, -2073600), (249, -691200), (256, 1244160), (257, 2488320), (258, -32348160), (259, 4147200), (263, -2073600), (264, 8294400), (269, -32348160)]

def pairMerged233 : Integer.Sparse (Fin 271) := [(0, 1473984), (1, -22748160), (2, -34172160), (3, -56263680), (4, -4761600), (5, 79895040), (6, -7849920), (7, -123832320), (8, -100193280), (9, -42240), (10, -6128640), (11, -12656640), (12, 38645760), (13, 82897920), (23, -414720), (24, -10414080), (25, 14330880), (26, -63114240), (27, 3432960), (30, -11658240), (32, -11842560), (33, 4085760), (34, -78796800), (38, -2073600), (41, 32624640), (46, 1244160), (50, -72161280), (51, -35328000), (53, 18293760), (54, -13639680), (55, -11151360), (58, -37739520), (59, 21765120), (63, 12257280), (65, -17402880), (66, 483840), (67, 2703360), (69, 7864320), (72, -24606720), (73, -32348160), (74, 28477440), (79, 101468160), (80, 6282240), (83, -97044480), (84, -27371520), (86, -24606720), (91, 4147200), (92, -18385920), (94, -8294400), (95, -8294400), (99, -36771840), (110, 15022080), (111, -1105920), (113, -3870720), (115, 12042240), (131, -1382400), (132, 5345280), (133, -13317120), (136, 1244160), (137, 2488320), (139, 2488320), (142, 8202240), (143, 81100800), (147, -1382400), (148, 16727040), (153, -1382400), (154, -15206400), (155, -18800640), (159, 12257280), (160, -12257280), (170, 2073600), (172, 4147200), (173, 22809600), (179, -2764800), (180, 18385920), (181, -1797120), (182, -23915520), (184, 55157760), (185, 2073600), (187, 36771840), (188, 28477440), (198, 36771840), (199, 45619200), (200, 69949440), (201, 4147200), (207, 14515200), (209, -8294400), (211, -18385920), (212, -18385920), (213, -101468160), (218, -18385920), (219, -7603200), (225, -28477440), (230, -12441600), (231, -73820160), (233, -32348160), (234, 1244160), (236, -24606720), (245, 14330880), (246, 8202240), (249, -691200), (256, 1244160), (257, 2488320), (258, -32348160), (259, -20459520), (263, -2073600), (269, -32348160)]

def pairMerged234 : Integer.Sparse (Fin 271) := [(0, 2060864), (1, -22782720), (2, -62945280), (3, -221414400), (4, -34429440), (5, 125927040), (6, -13358400), (7, -168261120), (8, -134922240), (9, 474240), (10, 33454080), (11, -23324160), (12, -5875200), (13, 808960), (23, 1244160), (24, -10414080), (25, 22579200), (26, -92881920), (27, 3018240), (30, 5160960), (32, 20782080), (33, 4761600), (34, -145612800), (35, -2488320), (36, 11335680), (37, -8294400), (38, -24330240), (41, -16588800), (46, 1244160), (50, -39352320), (51, -132564480), (52, -28753920), (53, 32624640), (54, -12810240), (55, -17003520), (56, 10368000), (58, 35527680), (59, 15590400), (63, 13916160), (65, -7034880), (66, 276480), (67, -1297920), (68, -1382400), (69, 2918400), (70, -21565440), (71, -10506240), (72, -41195520), (73, -65525760), (74, 40919040), (79, 120960000), (80, -829440), (81, -22394880), (82, -54466560), (83, -183306240), (84, -55848960), (85, -11128320), (86, -24606720), (89, 6220800), (91, 4147200), (92, -18385920), (94, -8294400), (95, -8294400), (99, -24330240), (110, 29859840), (111, -1105920), (112, 2488320), (113, -2211840), (115, -5007360), (131, -1382400), (132, 15298560), (133, -11888640), (136, 1244160), (137, 2488320), (139, 2488320), (142, 11911680), (143, 165358080), (147, 9745920), (148, 10506240), (149, -22256640), (153, -1382400), (154, -13547520), (155, -18800640), (159, 19445760), (160, -12257280), (161, -7557120), (170, 2073600), (171, -2488320), (172, 4147200), (173, 22809600), (179, 8363520), (180, 20459520), (181, -967680), (182, -23915520), (184, 24330240), (185, 2073600), (187, 36771840), (188, -16035840), (189, -4976640), (190, 22671360), (191, -16588800), (199, 45619200), (200, 8294400), (201, 4147200), (207, 14515200), (209, -8294400), (211, -14653440), (212, -26680320), (213, -94279680), (215, 21703680), (218, -8110080), (219, -6773760), (223, -13616640), (224, -8294400), (225, -28477440), (226, -4976640), (231, -96076800), (233, -21012480), (234, 1244160), (236, -24606720), (243, -28753920), (244, -17418240), (245, 29168640), (246, 11911680), (248, 829440), (249, -691200), (256, 1244160), (257, 2488320), (258, -54604800), (259, -42716160), (263, -2073600), (269, -1244160)]

def pairMerged235 : Integer.Sparse (Fin 271) := [(0, -302400), (1, 12110400), (2, -9633600), (3, -137548800), (4, -50227200), (5, 9388800), (6, -936000), (7, -24422400), (8, -4838400), (12, -15897600), (13, -15897600), (24, 3456000), (25, 11059200), (26, -63129600), (30, 18662400), (32, 45619200), (33, -12902400), (34, -41702400), (42, -16588800), (43, -20736000), (50, 2764800), (51, -24192000), (58, 11059200), (63, 8294400), (65, -12902400), (79, 24883200), (88, -18662400), (91, -20736000), (95, -16588800), (96, -16588800), (101, -8294400), (102, -16588800), (107, -20736000), (133, 2764800), (180, 8294400), (211, -8294400), (213, -16588800), (214, -20736000), (215, -20736000), (216, -16588800)]

def pairMerged236 : Integer.Sparse (Fin 271) := [(0, -11520), (1, -4029120), (2, 3425760), (3, 20759040), (4, 6266880), (5, -731520), (6, -171360), (7, 2004480), (8, 1566720), (9, 23040), (12, 7372800), (13, -1336320), (23, -3939840), (25, -12165120), (26, 2350080), (27, 3041280), (30, -16865280), (32, -14929920), (34, -1589760), (50, -28200960), (51, -599040), (53, -1797120), (54, -10575360), (62, 5322240), (63, -14100480), (66, 518400), (67, -92160), (68, 69120), (110, 1935360), (111, -691200), (112, -3732480), (113, -1382400), (116, -1451520), (120, 3525120), (122, 14100480), (124, -2903040), (125, 7050240), (130, 1451520), (145, -2903040), (147, 3870720), (148, -9400320), (154, -2350080), (179, 1451520), (182, -2350080), (206, 7050240), (223, -1451520), (234, 7050240), (245, 1935360), (246, 483840), (258, -2903040)]

def pairMerged237 : Integer.Sparse (Fin 271) := [(0, -313920), (1, 8081280), (2, -6207840), (3, -116789760), (4, -43960320), (5, 8657280), (6, -1107360), (7, -22417920), (8, -3271680), (9, 23040), (12, -8524800), (13, -17233920), (23, -3939840), (24, 3456000), (25, -1105920), (26, -60779520), (27, 3041280), (30, 1797120), (32, 30689280), (33, -12902400), (34, -43292160), (42, -16588800), (43, -20736000), (50, -25436160), (51, -24791040), (53, -1797120), (54, -10575360), (58, 11059200), (62, 5322240), (63, -5806080), (65, -12902400), (66, 518400), (67, -92160), (68, 69120), (79, 24883200), (88, -18662400), (91, -20736000), (95, -16588800), (96, -16588800), (101, -8294400), (102, -16588800), (107, -20736000), (110, 1935360), (111, -691200), (112, -3732480), (113, -1382400), (116, -1451520), (120, 3525120), (122, 14100480), (124, -2903040), (125, 7050240), (130, 1451520), (133, 2764800), (145, -2903040), (147, 3870720), (148, -9400320), (154, -2350080), (179, 1451520), (180, 8294400), (182, -2350080), (206, 7050240), (211, -8294400), (213, -16588800), (214, -20736000), (215, -20736000), (216, -16588800), (223, -1451520), (234, 7050240), (245, 1935360), (246, 483840), (258, -2903040)]

def pairMerged238 : Integer.Sparse (Fin 271) := [(0, -75744), (1, -1494720), (2, 1922400), (3, 1704960), (4, -3179520), (5, 92160), (6, -172800), (7, -6174720), (8, 645120), (9, 5760), (10, -4423680), (12, 7280640), (13, 8455680), (23, -3179520), (24, -2211840), (25, 10575360), (26, -7050240), (27, 3041280), (32, 2350080), (34, -3962880), (37, -207360), (46, 6635520), (50, -12026880), (51, -414720), (53, 10713600), (54, -7741440), (58, -5529600), (63, 4700160), (66, 552960), (67, -437760), (89, -14100480), (111, -967680), (112, -2211840), (113, -1105920), (120, 6635520), (136, 3317760), (143, 4700160), (153, -2211840), (154, 2350080), (181, -2211840), (193, -207360), (206, -7050240), (219, 1175040), (234, 6635520), (235, 6635520), (248, -1105920)]

def pairMerged239 : Integer.Sparse (Fin 271) := [(0, -50688), (1, 20171520), (2, -26781120), (3, -149114880), (4, -31933440), (5, 30666240), (6, -2681280), (7, -36864000), (8, -46679040), (9, 1647360), (10, 19353600), (11, -3225600), (12, -32256000), (13, -29030400), (23, 19353600), (24, 10091520), (26, -21980160), (27, -17038080), (29, 9676800), (30, 29859840), (34, -23132160), (36, -1244160), (39, -29030400), (42, -29030400), (45, -2488320), (50, 89579520), (51, -33638400), (54, 48384000), (55, 2903040), (66, -4838400), (67, -6727680), (69, -9815040), (79, 2073600), (88, -58060800), (99, -2488320), (111, 414720), (112, 19353600), (113, 39121920), (126, -58060800), (138, -29030400), (143, 1658880), (146, 19353600), (147, 9676800), (148, 9676800), (155, 829440), (181, 9676800), (226, -1244160), (232, -29030400), (234, -29030400), (240, -29030400), (248, 9676800), (250, -2488320), (253, -29030400), (255, -2488320), (257, -2488320), (263, 414720)]

def pairMerged240 : Integer.Sparse (Fin 271) := [(0, -126432), (1, 18676800), (2, -24858720), (3, -147409920), (4, -35112960), (5, 30758400), (6, -2854080), (7, -43038720), (8, -46033920), (9, 1653120), (10, 14929920), (11, -3225600), (12, -24975360), (13, -20574720), (23, 16174080), (24, 7879680), (25, 10575360), (26, -29030400), (27, -13996800), (29, 9676800), (30, 29859840), (32, 2350080), (34, -27095040), (36, -1244160), (37, -207360), (39, -29030400), (42, -29030400), (45, -2488320), (46, 6635520), (50, 77552640), (51, -34053120), (53, 10713600), (54, 40642560), (55, 2903040), (58, -5529600), (63, 4700160), (66, -4285440), (67, -7165440), (69, -9815040), (79, 2073600), (88, -58060800), (89, -14100480), (99, -2488320), (111, -552960), (112, 17141760), (113, 38016000), (120, 6635520), (126, -58060800), (136, 3317760), (138, -29030400), (143, 6359040), (146, 19353600), (147, 9676800), (148, 9676800), (153, -2211840), (154, 2350080), (155, 829440), (181, 7464960), (193, -207360), (206, -7050240), (219, 1175040), (226, -1244160), (232, -29030400), (234, -22394880), (235, 6635520), (240, -29030400), (248, 8570880), (250, -2488320), (253, -29030400), (255, -2488320), (257, -2488320), (263, 414720)]

def pairMerged241 : Integer.Sparse (Fin 271) := [(0, -440352), (1, 26758080), (2, -31066560), (3, -264199680), (4, -79073280), (5, 39415680), (6, -3961440), (7, -65456640), (8, -49305600), (9, 1676160), (10, 14929920), (11, -3225600), (12, -33500160), (13, -37808640), (23, 12234240), (24, 11335680), (25, 9469440), (26, -89809920), (27, -10955520), (29, 9676800), (30, 31656960), (32, 33039360), (33, -12902400), (34, -70387200), (36, -1244160), (37, -207360), (39, -29030400), (42, -45619200), (43, -20736000), (45, -2488320), (46, 6635520), (50, 52116480), (51, -58844160), (53, 8916480), (54, 30067200), (55, 2903040), (58, 5529600), (62, 5322240), (63, -1105920), (65, -12902400), (66, -3767040), (67, -7257600), (68, 69120), (69, -9815040), (79, 26956800), (88, -76723200), (89, -14100480), (91, -20736000), (95, -16588800), (96, -16588800), (99, -2488320), (101, -8294400), (102, -16588800), (107, -20736000), (110, 1935360), (111, -1244160), (112, 13409280), (113, 36633600), (116, -1451520), (120, 10160640), (122, 14100480), (124, -2903040), (125, 7050240), (126, -58060800), (130, 1451520), (133, 2764800), (136, 3317760), (138, -29030400), (143, 6359040), (145, -2903040), (146, 19353600), (147, 13547520), (148, 276480), (153, -2211840), (155, 829440), (179, 1451520), (180, 8294400), (181, 7464960), (182, -2350080), (193, -207360), (211, -8294400), (213, -16588800), (214, -20736000), (215, -20736000), (216, -16588800), (219, 1175040), (223, -1451520), (226, -1244160), (232, -29030400), (234, -15344640), (235, 6635520), (240, -29030400), (245, 1935360), (246, 483840), (248, 8570880), (250, -2488320), (253, -29030400), (255, -2488320), (257, -2488320), (258, -2903040), (263, 414720)]

def pairMerged242 : Integer.Sparse (Fin 271) := [(0, -125568), (1, -3219840), (2, 5443200), (3, 66263040), (4, 12119040), (5, -10667520), (6, 1560960), (7, 15575040), (8, 4285440), (9, -253440), (11, 414720), (12, 8202240), (13, 34560000), (25, -3041280), (26, 21381120), (27, 103680), (30, -1244160), (33, 7096320), (34, 31887360), (38, 9123840), (42, 1244160), (44, 1244160), (50, -2073600), (51, 32532480), (53, -18247680), (55, -1658880), (56, 1244160), (59, 7096320), (63, -6082560), (67, 2027520), (69, 1013760), (79, -829440), (80, 1013760), (91, 18247680), (95, 18247680), (99, 3732480), (106, 9123840), (113, -6082560), (115, 5068800), (135, 2488320), (143, -6912000), (147, -414720), (148, -1244160), (154, -6082560), (201, 9123840), (207, 9123840), (210, 18247680), (219, -3041280), (240, 1244160), (255, 2488320), (269, 1244160), (270, 1244160)]

def pairMerged243 : Integer.Sparse (Fin 271) := [(0, 499968), (1, -103680), (2, -10437120), (3, -84049920), (4, -6451200), (5, 13178880), (6, -1728000), (7, -8110080), (8, -6451200), (9, 92160), (12, -26726400), (13, -79073280), (26, -10137600), (32, 9953280), (33, -7372800), (34, -29675520), (37, -3317760), (41, -8294400), (50, 9400320), (51, -44421120), (53, 5529600), (58, 17694720), (59, -7372800), (67, -368640), (69, -737280), (80, -3502080), (90, -16588800), (91, -8294400), (94, -23224320), (95, -8294400), (106, -8294400), (108, -8294400), (113, 2211840), (115, -11059200), (132, 2211840), (133, 5529600), (147, 4976640), (153, 2211840), (200, -8294400), (207, -8294400), (208, -16588800), (209, -8294400), (235, -6635520), (236, -3317760), (245, 2211840), (246, 1105920), (254, -6635520)]

def pairMerged244 : Integer.Sparse (Fin 271) := [(0, 374400), (1, -3323520), (2, -4993920), (3, -17786880), (4, 5667840), (5, 2511360), (6, -167040), (7, 7464960), (8, -2165760), (9, -161280), (11, 414720), (12, -18524160), (13, -44513280), (25, -3041280), (26, 11243520), (27, 103680), (30, -1244160), (32, 9953280), (33, -276480), (34, 2211840), (37, -3317760), (38, 9123840), (41, -8294400), (42, 1244160), (44, 1244160), (50, 7326720), (51, -11888640), (53, -12718080), (55, -1658880), (56, 1244160), (58, 17694720), (59, -276480), (63, -6082560), (67, 1658880), (69, 276480), (79, -829440), (80, -2488320), (90, -16588800), (91, 9953280), (94, -23224320), (95, 9953280), (99, 3732480), (106, 829440), (108, -8294400), (113, -3870720), (115, -5990400), (132, 2211840), (133, 5529600), (135, 2488320), (143, -6912000), (147, 4561920), (148, -1244160), (153, 2211840), (154, -6082560), (200, -8294400), (201, 9123840), (207, 829440), (208, -16588800), (209, -8294400), (210, 18247680), (219, -3041280), (235, -6635520), (236, -3317760), (240, 1244160), (245, 2211840), (246, 1105920), (254, -6635520), (255, 2488320), (269, 1244160), (270, 1244160)]

def pairMerged245 : Integer.Sparse (Fin 271) := [(0, 274176), (1, -2643840), (2, -1198080), (3, 8939520), (4, 15482880), (5, 4101120), (6, -432000), (7, -8110080), (8, -2027520), (9, 253440), (11, 921600), (12, -2488320), (13, -10321920), (23, 3041280), (26, 7557120), (27, -2280960), (33, 3317760), (34, -7280640), (37, -9123840), (40, 8294400), (50, 18247680), (51, -6082560), (53, 6082560), (54, 9676800), (55, -8294400), (59, 1198080), (63, 18247680), (66, -1520640), (68, -1013760), (69, -1013760), (80, -3133440), (112, 6082560), (115, -3225600), (118, -18247680), (119, -1658880), (126, -9123840), (128, 16588800), (131, 9123840), (135, 16588800), (146, 3041280), (148, 6635520), (154, 6082560), (182, 6082560), (195, -9123840), (196, 8294400), (208, 16588800), (210, -18247680), (249, 3041280), (265, -18247680)]

def pairMerged246 : Integer.Sparse (Fin 271) := [(0, -339840), (1, -10252800), (2, 5385600), (3, 164505600), (4, 38016000), (5, -13190400), (6, 1958400), (7, 22809600), (8, 6220800), (9, -460800), (11, 5529600), (12, 7833600), (13, 50688000), (24, -2764800), (26, 98380800), (27, 1382400), (30, -2764800), (32, -5529600), (33, 45158400), (34, 63360000), (36, 8294400), (50, -20044800), (51, 18662400), (52, 10368000), (54, -21427200), (55, -13824000), (63, -48384000), (65, 16819200), (66, 1382400), (67, 1843200), (68, 2764800), (99, 10368000), (112, -13824000), (113, -2764800), (118, 16588800), (119, 37324800), (126, 8294400), (128, 20736000), (131, -5529600), (135, 8294400), (143, -3456000), (147, -2764800), (148, -27648000), (180, -5529600), (182, -2764800), (214, 20736000), (216, 16588800), (228, 8294400), (238, 8294400), (240, 18662400), (243, 10368000), (248, -2764800), (251, 8294400), (270, 10368000)]

def pairMerged247 : Integer.Sparse (Fin 271) := [(0, -65664), (1, -12896640), (2, 4187520), (3, 173445120), (4, 53498880), (5, -9089280), (6, 1526400), (7, 14699520), (8, 4193280), (9, -207360), (11, 6451200), (12, 5345280), (13, 40366080), (23, 3041280), (24, -2764800), (26, 105937920), (27, -898560), (30, -2764800), (32, -5529600), (33, 48476160), (34, 56079360), (36, 8294400), (37, -9123840), (40, 8294400), (50, -1797120), (51, 12579840), (52, 10368000), (53, 6082560), (54, -11750400), (55, -22118400), (59, 1198080), (63, -30136320), (65, 16819200), (66, -138240), (67, 1843200), (68, 1751040), (69, -1013760), (80, -3133440), (99, 10368000), (112, -7741440), (113, -2764800), (115, -3225600), (118, -1658880), (119, 35665920), (126, -829440), (128, 37324800), (131, 3594240), (135, 24883200), (143, -3456000), (146, 3041280), (147, -2764800), (148, -21012480), (154, 6082560), (180, -5529600), (182, 3317760), (195, -9123840), (196, 8294400), (208, 16588800), (210, -18247680), (214, 20736000), (216, 16588800), (228, 8294400), (238, 8294400), (240, 18662400), (243, 10368000), (248, -2764800), (249, 3041280), (251, 8294400), (265, -18247680), (270, 10368000)]

def pairMerged248 : Integer.Sparse (Fin 271) := [(0, 308736), (1, -16220160), (2, -806400), (3, 155658240), (4, 59166720), (5, -6577920), (6, 1359360), (7, 22164480), (8, 2027520), (9, -368640), (11, 6865920), (12, -13178880), (13, -4147200), (23, 3041280), (24, -2764800), (25, -3041280), (26, 117181440), (27, -794880), (30, -4008960), (32, 4423680), (33, 48199680), (34, 58291200), (36, 8294400), (37, -12441600), (38, 9123840), (40, 8294400), (41, -8294400), (42, 1244160), (44, 1244160), (50, 5529600), (51, 691200), (52, 10368000), (53, -6635520), (54, -11750400), (55, -23777280), (56, 1244160), (58, 17694720), (59, 921600), (63, -36218880), (65, 16819200), (66, -138240), (67, 3502080), (68, 1751040), (69, -737280), (79, -829440), (80, -5621760), (90, -16588800), (91, 9953280), (94, -23224320), (95, 9953280), (99, 14100480), (106, 829440), (108, -8294400), (112, -7741440), (113, -6635520), (115, -9216000), (118, -1658880), (119, 35665920), (126, -829440), (128, 37324800), (131, 3594240), (132, 2211840), (133, 5529600), (135, 27371520), (143, -10368000), (146, 3041280), (147, 1797120), (148, -22256640), (153, 2211840), (180, -5529600), (182, 3317760), (195, -9123840), (196, 8294400), (200, -8294400), (201, 9123840), (207, 829440), (209, -8294400), (214, 20736000), (216, 16588800), (219, -3041280), (228, 8294400), (235, -6635520), (236, -3317760), (238, 8294400), (240, 19906560), (243, 10368000), (245, 2211840), (246, 1105920), (248, -2764800), (249, 3041280), (251, 8294400), (254, -6635520), (255, 2488320), (265, -18247680), (269, 1244160), (270, 11612160)]

def pairMerged249 : Integer.Sparse (Fin 271) := [(0, -131616), (1, 10537920), (2, -31872960), (3, -108541440), (4, -19906560), (5, 32837760), (6, -2602080), (7, -43292160), (8, -47278080), (9, 1307520), (10, 14929920), (11, 3640320), (12, -46679040), (13, -41955840), (23, 15275520), (24, 8570880), (25, 6428160), (26, 27371520), (27, -11750400), (29, 9676800), (30, 27648000), (32, 37463040), (33, 35297280), (34, -12096000), (36, 7050240), (37, -12648960), (38, 9123840), (39, -29030400), (40, 8294400), (41, -8294400), (42, -44375040), (43, -20736000), (44, 1244160), (45, -2488320), (46, 6635520), (50, 57646080), (51, -58152960), (52, 10368000), (53, 2280960), (54, 18316800), (55, -20874240), (56, 1244160), (58, 23224320), (59, 921600), (62, 5322240), (63, -37324800), (65, 3916800), (66, -3905280), (67, -3755520), (68, 1820160), (69, -10552320), (79, 26127360), (80, -5621760), (88, -76723200), (89, -14100480), (90, -16588800), (91, -10782720), (94, -23224320), (95, -6635520), (96, -16588800), (99, 11612160), (101, -8294400), (102, -16588800), (106, 829440), (107, -20736000), (108, -8294400), (110, 1935360), (111, -1244160), (112, 5667840), (113, 29998080), (115, -9216000), (116, -1451520), (118, -1658880), (119, 35665920), (120, 10160640), (122, 14100480), (124, -2903040), (125, 7050240), (126, -58890240), (128, 37324800), (130, 1451520), (131, 3594240), (132, 2211840), (133, 8294400), (135, 27371520), (136, 3317760), (138, -29030400), (143, -4008960), (145, -2903040), (146, 22394880), (147, 15344640), (148, -21980160), (155, 829440), (179, 1451520), (180, 2764800), (181, 7464960), (182, 967680), (193, -207360), (195, -9123840), (196, 8294400), (200, -8294400), (201, 9123840), (207, 829440), (209, -8294400), (211, -8294400), (213, -16588800), (215, -20736000), (219, -1866240), (223, -1451520), (226, -1244160), (228, 8294400), (232, -29030400), (234, -15344640), (236, -3317760), (238, 8294400), (240, -9123840), (243, 10368000), (245, 4147200), (246, 1589760), (248, 5806080), (249, 3041280), (250, -2488320), (251, 8294400), (253, -29030400), (254, -6635520), (257, -2488320), (258, -2903040), (263, 414720), (265, -18247680), (269, 1244160), (270, 11612160)]

def pairMerged250 : Integer.Sparse (Fin 271) := [(0, 1929248), (1, -12244800), (2, -94818240), (3, -329955840), (4, -54336000), (5, 158764800), (6, -15960480), (7, -211553280), (8, -182200320), (9, 1781760), (10, 48384000), (11, -19683840), (12, -52554240), (13, -41146880), (23, 16519680), (24, -1843200), (25, 29007360), (26, -65510400), (27, -8732160), (29, 9676800), (30, 32808960), (32, 58245120), (33, 40058880), (34, -157708800), (35, -2488320), (36, 18385920), (37, -20943360), (38, -15206400), (39, -29030400), (40, 8294400), (41, -24883200), (42, -44375040), (43, -20736000), (44, 1244160), (45, -2488320), (46, 7879680), (50, 18293760), (51, -190717440), (52, -18385920), (53, 34905600), (54, 5506560), (55, -37877760), (56, 11612160), (58, 58752000), (59, 16512000), (62, 5322240), (63, -23408640), (65, -3118080), (66, -3628800), (67, -5053440), (68, 437760), (69, -7633920), (70, -21565440), (71, -10506240), (72, -41195520), (73, -65525760), (74, 40919040), (79, 147087360), (80, -6451200), (81, -22394880), (82, -54466560), (83, -183306240), (84, -55848960), (85, -11128320), (86, -24606720), (88, -76723200), (89, -7879680), (90, -16588800), (91, -6635520), (92, -18385920), (94, -31518720), (95, -14929920), (96, -16588800), (99, -12718080), (101, -8294400), (102, -16588800), (106, 829440), (107, -20736000), (108, -8294400), (110, 31795200), (111, -2350080), (112, 8156160), (113, 27786240), (115, -14223360), (116, -1451520), (118, -1658880), (119, 35665920), (120, 10160640), (122, 14100480), (124, -2903040), (125, 7050240), (126, -58890240), (128, 37324800), (130, 1451520), (131, 2211840), (132, 17510400), (133, -3594240), (135, 27371520), (136, 4561920), (137, 2488320), (138, -29030400), (139, 2488320), (142, 11911680), (143, 161349120), (145, -2903040), (146, 22394880), (147, 25090560), (148, -11473920), (149, -22256640), (153, -1382400), (154, -13547520), (155, -17971200), (159, 19445760), (160, -12257280), (161, -7557120), (170, 2073600), (171, -2488320), (172, 4147200), (173, 22809600), (179, 9815040), (180, 23224320), (181, 6497280), (182, -22947840), (184, 24330240), (185, 2073600), (187, 36771840), (188, -16035840), (189, -4976640), (190, 22671360), (191, -16588800), (193, -207360), (195, -9123840), (196, 8294400), (199, 45619200), (201, 13271040), (207, 15344640), (209, -16588800), (211, -22947840), (212, -26680320), (213, -110868480), (215, 967680), (218, -8110080), (219, -8640000), (223, -15068160), (224, -8294400), (225, -28477440), (226, -6220800), (228, 8294400), (231, -96076800), (232, -29030400), (233, -21012480), (234, -14100480), (236, -27924480), (238, 8294400), (240, -9123840), (243, -18385920), (244, -17418240), (245, 33315840), (246, 13501440), (248, 6635520), (249, 2350080), (250, -2488320), (251, 8294400), (253, -29030400), (254, -6635520), (256, 1244160), (258, -57507840), (259, -42716160), (263, -1658880), (265, -18247680), (270, 11612160)]

def pairMerged251 : Integer.Sparse (Fin 271) := [(0, 1095360), (1, 131840), (2, -62641760), (3, -339594240), (4, -112508160), (5, 101217280), (6, -11280480), (7, -147517440), (8, -91069440), (9, 1085760), (10, -42382080), (11, -27033600), (12, -22608640), (13, 27683840), (23, -4654080), (24, -115937280), (25, 58682880), (26, -150520320), (27, 24946560), (29, -34007040), (30, 8847360), (31, 2764800), (32, 40872960), (33, 43622400), (34, -155617280), (35, -14515200), (36, -22187520), (37, -54224640), (38, -59304960), (39, -128977920), (40, 4147200), (41, -24883200), (42, -35251200), (43, -20736000), (44, -10368000), (45, 8294400), (46, 17003520), (48, 18247680), (50, -12579840), (51, -168119040), (53, 105200640), (54, -72172800), (55, 18984960), (56, 11612160), (58, -40412160), (59, 20275200), (61, 8294400), (62, 2926080), (63, -13086720), (65, -4899840), (66, 3542400), (67, 648960), (68, 960000), (69, -168960), (70, -21150720), (71, 3352320), (72, 45273600), (73, -36426240), (74, 40919040), (75, 4561920), (79, 171279360), (80, 1378560), (81, -53153280), (82, -101226240), (83, -353756160), (84, -55848960), (85, -8156160), (86, -11335680), (88, -36910080), (89, -7879680), (90, -23639040), (91, 3456000), (92, -18385920), (94, -54743040), (95, -9123840), (96, -32071680), (98, 47278080), (99, 45342720), (101, -8294400), (102, -16588800), (106, 829440), (107, -20736000), (108, -8294400), (110, 19261440), (111, -1244160), (112, -9400320), (113, -51770880), (115, -6558720), (116, -1451520), (118, -1658880), (119, 35665920), (120, 10160640), (122, 14100480), (124, -2903040), (125, 7050240), (126, -58890240), (128, 37324800), (130, 4008960), (131, -29237760), (132, 10168320), (133, 9918720), (135, 27371520), (136, 4561920), (137, 2488320), (138, -29030400), (139, 2488320), (142, 6497280), (143, 262805760), (145, -2903040), (146, -15206400), (147, 7326720), (148, -30827520), (149, -22256640), (153, 7464960), (154, -17141760), (155, -11335680), (159, 15713280), (160, -14607360), (161, -1105920), (168, -12337920), (170, -8294400), (171, 2903040), (172, 4147200), (173, 22809600), (174, 19077120), (176, -9123840), (177, 9953280), (179, -36011520), (180, -41886720), (181, 2799360), (182, -19215360), (185, -7326720), (193, -66700800), (194, 8916480), (199, 35665920), (218, 30320640), (219, 30758400), (223, -3663360), (229, -22233600), (232, -133401600), (234, 13271040), (238, 8294400), (241, 9123840), (245, 41057280), (246, 19680000), (248, -61831680), (249, -55833600), (250, 19077120), (251, 19077120), (252, 9123840), (253, -18247680), (254, -18247680), (256, 1244160), (258, -7326720), (260, -2442240), (262, -14653440), (263, 81838080), (266, 18247680), (267, 18247680)]

def pairMerged252 : Integer.Sparse (Fin 271) := [(0, -29815080), (1, 174493520), (2, -59262560), (3, 185687040), (4, -448552320), (5, -145415360), (6, 21225200), (7, -24508800), (8, 13793280), (9, -11713280), (10, -45233280), (11, -33536640), (12, 284127360), (13, 781952000), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -42168960), (24, 158883840), (25, -146880000), (26, -174209280), (27, 56607840), (29, -11957760), (30, 231655680), (31, 2611200), (32, -278087040), (33, 42320640), (34, 323747200), (35, 136632960), (36, -93519360), (37, -20874240), (38, -59304960), (39, -92275200), (40, 4147200), (41, -24883200), (42, 69050880), (43, -142041600), (44, -467389440), (45, -169205760), (46, 125867520), (47, 78382080), (49, 235975680), (50, -274682880), (51, 280479360), (52, -145981440), (53, -370103040), (54, -25568640), (55, -143585280), (56, -97044480), (57, 1017720), (58, -120890880), (59, 38563840), (60, 1382400), (61, 8294400), (62, -8133120), (63, -158618880), (64, -2764800), (65, 52300800), (66, 41463360), (67, -83126400), (68, -42957440), (69, -69461760), (70, 2661120), (71, 864000), (72, 5045760), (73, 18869760), (74, 78243840), (75, -101606400), (76, -22809600), (77, -25453440), (79, 46771200), (80, 77095680), (81, -53153280), (82, -93553920), (83, -323066880), (84, -80317440), (85, 31034880), (86, -11335680), (87, 4147200), (88, -177189120), (89, -274752000), (90, -46448640), (91, -291513600), (92, 274406400), (94, -100362240), (95, 216691200), (96, 217900800), (97, 13685760), (98, 29030400), (99, 2211840), (101, -8294400), (102, -13271040), (103, -61015680), (104, -79211520), (105, -158423040), (106, 829440), (107, -166717440), (108, -166717440), (109, 16588800), (110, -3720960), (111, 2488320), (112, -62709120), (113, 5253120), (114, -2488320), (115, 83297280), (116, -1451520), (117, -225037440), (120, 10160640), (122, 132088320), (124, -2903040), (125, -31726080), (126, -352200960), (127, 164643840), (130, 30032640), (131, 101727360), (132, -45941760), (133, -124369920), (135, -9953280), (136, 4561920), (137, -78382080), (138, -29030400), (139, 120476160), (140, -294969600), (142, 6497280), (143, 316391040), (145, -2903040), (146, -247656960), (147, -20632320), (148, -116743680), (149, -22256640)]

def pairMerged253 : Integer.Sparse (Fin 271) := [(0, -9035712), (1, -36106560), (2, -8573040), (3, 8709120), (4, 26127360), (5, 2721600), (6, -181440), (7, -5806080), (8, -39191040), (12, -1451520), (17, -19595520), (20, -78382080), (23, -8709120), (24, 39191040), (27, -16873920), (28, -78382080), (29, 137168640), (30, -26127360), (57, 45360), (66, -2177280), (67, -2903040), (113, 52254720), (134, -78382080), (137, -78382080), (138, -470292480), (144, 6531840), (146, 78382080), (150, -352719360)]

def pairMerged254 : Integer.Sparse (Fin 271) := [(0, 94904460), (1, 4942607040), (2, -1659268800), (3, -13274150400), (4, -6637075200), (5, 3040730280), (6, -302313060), (7, -3318537600), (8, -1659268800), (12, -4977806400), (23, 2488903200), (24, 4977806400), (27, -3627756720)]

def pairMerged255 : Integer.Sparse (Fin 271) := [(0, -406890540), (1, -4535742960), (2, -265393800), (3, -8813750400), (4, 2283724800), (5, 3040730280), (6, -302313060), (7, -3318537600), (8, -1659268800), (12, -2747606400), (23, 2488903200), (24, 4977806400), (27, -3627756720)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged256 : Integer.Sparse (Fin 271) := [(0, -92782368), (1, 1923477570), (2, 11440170), (3, -5430741120), (4, -4707218880), (12, -723522240), (13, 3621935520), (25, 2987772480), (26, -3983696640)]

def pairMerged257 : Integer.Sparse (Fin 271) := [(0, -343196784), (1, 7627361490), (2, -3049180470), (3, -9882552960), (4, -9159030720), (5, 834714720), (7, -1112952960), (8, -5564764800), (12, -723522240), (13, 3621935520), (24, 3338858880), (25, 2987772480), (26, -3983696640), (29, 6677717760)]

def pairMerged258 : Integer.Sparse (Fin 271) := [(0, -750087324), (1, 3091618530), (2, -3314574270), (3, -18696303360), (4, -6875305920), (5, 3875445000), (6, -302313060), (7, -4431490560), (8, -7224033600), (12, -3471128640), (13, 3621935520), (23, 2488903200), (24, 8316665280), (25, 2987772480), (26, -3983696640), (27, -3627756720), (29, 6677717760)]

def pairMerged259 : Integer.Sparse (Fin 271) := [(0, -392917392), (1, 4477939200), (2, -840929040), (3, -4887267840), (4, -6766986240), (12, -1879718400), (14, -770757120), (15, -1691746560), (17, -3083028480), (20, -3383493120), (23, 2619267840), (24, 1691746560), (25, 5238535680), (27, -808315200), (29, 2155507200), (30, 6366366720)]

def pairMerged260 : Integer.Sparse (Fin 271) := [(0, -946123416), (1, 23840150040), (2, -5143642560), (3, -34391589120), (4, -31353920640), (12, -6797105280), (14, -770757120), (15, -1691746560), (17, -3083028480), (20, -3383493120), (23, 2619267840), (24, 1691746560), (25, 5238535680), (26, -4917386880), (27, -808315200), (29, 2155507200), (30, 21118527360)]

def pairMerged261 : Integer.Sparse (Fin 271) := [(0, -34203708), (1, -1622187000), (2, 387669240), (3, 3945957120), (4, 2550864960), (12, 1501960320), (16, 759734640), (17, 1519469280), (18, 400075200), (22, 800150400), (23, -1012979520), (27, 189933660), (29, -506489760)]

def pairMerged262 : Integer.Sparse (Fin 271) := [(0, -60555600), (1, 996786000), (2, -197089200), (3, -1614816000), (4, -1397088000), (12, -657720000), (15, -326592000), (17, -563371200), (19, -400075200), (20, -400075200), (22, -400075200), (23, 163296000), (24, 775656000), (25, 326592000), (27, -140842800), (29, 187790400), (30, 860025600)]

def pairMerged263 : Integer.Sparse (Fin 271) := [(0, -94759308), (1, -625401000), (2, 190580040), (3, 2331141120), (4, 1153776960), (12, 844240320), (15, -326592000), (16, 759734640), (17, 956098080), (18, 400075200), (19, -400075200), (20, -400075200), (22, 400075200), (23, -849683520), (24, 775656000), (25, 326592000), (27, 49090860), (29, -318699360), (30, 860025600)]

def pairMerged264 : Integer.Sparse (Fin 271) := [(0, -1040882724), (1, 23214749040), (2, -4953062520), (3, -32060448000), (4, -30200143680), (12, -5952864960), (14, -770757120), (15, -2018338560), (16, 759734640), (17, -2126930400), (18, 400075200), (19, -400075200), (20, -3783568320), (22, 400075200), (23, 1769584320), (24, 2467402560), (25, 5565127680), (26, -4917386880), (27, -759224340), (29, 1836807840), (30, 21978552960)]

def pairMerged265 : Integer.Sparse (Fin 271) := [(0, -1790970048), (1, 26306367570), (2, -8267636790), (3, -50756751360), (4, -37075449600), (5, 3875445000), (6, -302313060), (7, -4431490560), (8, -7224033600), (12, -9423993600), (13, 3621935520), (14, -770757120), (15, -2018338560), (16, 759734640), (17, -2126930400), (18, 400075200), (19, -400075200), (20, -3783568320), (22, 400075200), (23, 4258487520), (24, 10784067840), (25, 8552900160), (26, -8901083520), (27, -4386981060), (29, 8514525600), (30, 21978552960)]

def pairMerged266 : Integer.Sparse (Fin 271) := [(0, 83516832), (1, -2141865180), (2, 445514580), (3, 6181297920), (4, 3879640800), (12, 2345202720), (17, 48988800), (18, 2301657120), (23, -16329600), (25, -1534438080), (27, 12247200), (28, 97977600), (29, -81648000), (30, -1534438080)]

def pairMerged267 : Integer.Sparse (Fin 271) := [(0, 31840452), (1, -1188908280), (2, 328825980), (3, 4580997120), (4, 2546056800), (12, 1500599520), (17, 48988800), (18, 2301657120), (21, -400075200), (22, -400075200), (23, -16329600), (25, -1534438080), (27, 12247200), (28, 97977600), (29, -81648000), (30, -1267721280)]

def pairMerged268 : Integer.Sparse (Fin 271) := [(0, -30607038), (1, 643949460), (2, -1544617620), (3, -5032329120), (4, -334666080), (5, 1609455960), (6, -78172290), (7, -3112240320), (8, -3112240320), (12, -2806876800), (13, -1871251200), (26, 1221454080), (34, -732049920), (50, 4668360480), (51, -1556120160), (54, -916090560)]

def pairMerged269 : Integer.Sparse (Fin 271) := [(0, 56443716), (1, -1476269550), (2, 345875670), (3, 7922486880), (4, 1734203520), (5, -1442788200), (6, 216775440), (7, 478548000), (8, 957096000), (12, 1554215040), (13, 5051198880), (26, 1734203520), (34, 2032763040), (51, 1734203520), (53, -1165661280), (55, -2331322560)]

def pairMerged270 : Integer.Sparse (Fin 271) := [(0, 25836678), (1, -832320090), (2, -1198741950), (3, 2890157760), (4, 1399537440), (5, 166667760), (6, 138603150), (7, -2633692320), (8, -2155144320), (12, -1252661760), (13, 3179947680), (26, 2955657600), (34, 1300713120), (50, 4668360480), (51, 178083360), (53, -1165661280), (54, -916090560), (55, -2331322560)]

def pairMerged271 : Integer.Sparse (Fin 271) := [(0, 57677130), (1, -2021228370), (2, -869915970), (3, 7471154880), (4, 3945594240), (5, 166667760), (6, 138603150), (7, -2633692320), (8, -2155144320), (12, 247937760), (13, 3179947680), (17, 48988800), (18, 2301657120), (21, -400075200), (22, -400075200), (23, -16329600), (25, -1534438080), (26, 2955657600), (27, 12247200), (28, 97977600), (29, -81648000), (30, -1267721280), (34, 1300713120), (50, 4668360480), (51, 178083360), (53, -1165661280), (54, -916090560), (55, -2331322560)]

def pairMerged272 : Integer.Sparse (Fin 271) := [(0, -18753336), (1, 664319880), (2, -52889760), (3, -4910129280), (5, 59285520), (7, -948568320), (12, -2692206720), (13, -4807797120), (23, 2134278720), (25, 2134278720), (31, -282078720), (34, -474284160), (53, 1422852480)]

def pairMerged273 : Integer.Sparse (Fin 271) := [(0, 184863924), (1, -3315472020), (2, 1705622940), (3, 8417545920), (4, 4442558400), (5, -2902420080), (6, 277659900), (7, 3493990080), (8, 4442558400), (12, -2692206720), (13, -4807797120), (23, 2134278720), (25, 2134278720), (26, 4442558400), (31, -282078720), (34, 1006568640), (53, 1422852480)]

def pairMerged274 : Integer.Sparse (Fin 271) := [(0, 472385844), (1, -7550670960), (2, 1870997940), (3, 17096728320), (4, 12102410880), (12, 5096014560), (13, 426746880), (25, -5731145280), (26, 2657188800), (30, -11462290560), (32, -6051205440), (33, 213373440)]

def pairMerged275 : Integer.Sparse (Fin 271) := [(0, 767228112), (1, -10078164180), (2, 2801762460), (3, 26339826240), (4, 17681328000), (5, 45541440), (7, -45541440), (8, -182165760), (12, 11152391040), (13, 2856409920), (23, 136624320), (25, -5984254080), (27, -102468240), (29, 273248640), (30, -14416859520), (32, -4623454080), (44, -819745920), (49, 3672527040), (50, 273248640), (53, 136624320)]

def pairMerged276 : Integer.Sparse (Fin 271) := [(0, 1239613956), (1, -17628835140), (2, 4672760400), (3, 43436554560), (4, 29783738880), (5, 45541440), (7, -45541440), (8, -182165760), (12, 16248405600), (13, 3283156800), (23, 136624320), (25, -11715399360), (26, 2657188800), (27, -102468240), (29, 273248640), (30, -25879150080), (32, -10674659520), (33, 213373440), (44, -819745920), (49, 3672527040), (50, 273248640), (53, 136624320)]

def pairMerged277 : Integer.Sparse (Fin 271) := [(0, 1424477880), (1, -20944307160), (2, 6378383340), (3, 51854100480), (4, 34226297280), (5, -2856878640), (6, 277659900), (7, 3448448640), (8, 4260392640), (12, 13556198880), (13, -1524640320), (23, 2270903040), (25, -9581120640), (26, 7099747200), (27, -102468240), (29, 273248640), (30, -25879150080), (31, -282078720), (32, -10674659520), (33, 213373440), (34, 1006568640), (44, -819745920), (49, 3672527040), (50, 273248640), (53, 1559476800)]

def pairMerged278 : Integer.Sparse (Fin 271) := [(0, 1482155010), (1, -22965535530), (2, 5508467370), (3, 59325255360), (4, 38171891520), (5, -2690210880), (6, 416263050), (7, 814756320), (8, 2105248320), (12, 13804136640), (13, 1655307360), (17, 48988800), (18, 2301657120), (21, -400075200), (22, -400075200), (23, 2254573440), (25, -11115558720), (26, 10055404800), (27, -90221040), (28, 97977600), (29, 191600640), (30, -27146871360), (31, -282078720), (32, -10674659520), (33, 213373440), (34, 2307281760), (44, -819745920), (49, 3672527040), (50, 4941609120), (51, 178083360), (53, 393815520), (54, -916090560), (55, -2331322560)]

def pairMerged279 : Integer.Sparse (Fin 271) := [(0, -308815038), (1, 3340832040), (2, -2759169420), (3, 8568504000), (4, 1096441920), (5, 1185234120), (6, 113949990), (7, -3616734240), (8, -5118785280), (12, 4380143040), (13, 5277242880), (14, -770757120), (15, -2018338560), (16, 759734640), (17, -2077941600), (18, 2701732320), (19, -400075200), (20, -3783568320), (21, -400075200), (23, 6513060960), (24, 10784067840), (25, -2562658560), (26, 1154321280), (27, -4477202100), (28, 97977600), (29, 8706126240), (30, -5168318400), (31, -282078720), (32, -10674659520), (33, 213373440), (34, 2307281760), (44, -819745920), (49, 3672527040), (50, 4941609120), (51, 178083360), (53, 393815520), (54, -916090560), (55, -2331322560)]

def pairMerged280 : Integer.Sparse (Fin 271) := [(0, -145224576), (1, 1199363760), (2, -737871120), (3, -1027676160), (4, -1080656640), (5, 162207360), (7, -216276480), (8, -432552960), (12, -1238872320), (23, 1297658880), (24, 3892976640), (25, 1981324800), (26, 1262822400), (27, -1622073600), (29, 2595317760), (30, 4278355200), (32, 2595317760), (42, 947116800), (43, 947116800), (44, 947116800), (45, 947116800), (47, -1946488320), (48, -3892976640), (50, 1946488320), (54, 1297658880)]

def pairMerged281 : Integer.Sparse (Fin 271) := [(0, -393020586), (1, 4053290220), (2, -1583795430), (3, -8683718400), (4, -5455537920), (5, 162207360), (7, -216276480), (8, -432552960), (12, -4246603200), (13, -273430080), (23, 1297658880), (24, 3892976640), (25, 2801615040), (26, 305817120), (27, -1622073600), (29, 2595317760), (30, 7149371040), (32, 4235898240), (42, -283318560), (43, 947116800), (44, -1513753920), (45, 947116800), (47, -1946488320), (48, -3892976640), (50, 1946488320), (54, 1297658880)]

def pairMerged282 : Integer.Sparse (Fin 271) := [(0, -324300186), (1, 3931464600), (2, -1812852090), (3, -11079089280), (4, -7168512960), (5, 521322480), (7, -1172646720), (8, -1628968320), (12, -2639770560), (23, -780010560), (24, 1957919040), (26, -782641440), (27, -636718320), (29, 588954240), (30, 4496899680), (42, 1170015840), (44, -3223463040), (45, -3223463040), (50, 4297950720), (54, -780010560), (55, 2148975360)]

def pairMerged283 : Integer.Sparse (Fin 271) := [(0, 56887110), (1, -840135240), (2, -244847610), (3, -1346647680), (4, -247665600), (5, 359115120), (7, -956370240), (8, -1196415360), (12, 1253206080), (13, 865105920), (23, -2077669440), (24, -1935057600), (26, -782641440), (27, 985355280), (29, -2006363520), (30, -693735840), (42, 1170015840), (44, -3223463040), (45, -3223463040), (46, 1946488320), (48, 3892976640), (50, 2351462400), (54, -2077669440), (55, 2148975360)]

def pairMerged284 : Integer.Sparse (Fin 271) := [(0, -336133476), (1, 3213154980), (2, -1828643040), (3, -10030366080), (4, -5703203520), (5, 521322480), (7, -1172646720), (8, -1628968320), (12, -2993397120), (13, 591675840), (23, -780010560), (24, 1957919040), (25, 2801615040), (26, -476824320), (27, -636718320), (29, 588954240), (30, 6455635200), (32, 4235898240), (42, 886697280), (43, 947116800), (44, -4737216960), (45, -2276346240), (46, 1946488320), (47, -1946488320), (50, 4297950720), (54, -780010560), (55, 2148975360)]

def pairMerged285 : Integer.Sparse (Fin 271) := [(0, 101640420), (1, -1560049470), (2, 630555030), (3, 5003117280), (4, 719591040), (5, -185091480), (7, 179897760), (8, 761140800), (12, 2055352320), (13, 2664446400), (23, -301008960), (25, 124649280), (26, 318245760), (27, 225756720), (29, -602017920), (30, 249298560), (32, 498597120), (35, -186973920), (37, 1090000800), (38, -373947840), (39, 1806053760), (50, -1204035840), (53, -415044000), (54, -903026880)]

def pairMerged286 : Integer.Sparse (Fin 271) := [(0, 197448678), (1, -3004323210), (2, 895100220), (3, 9579034080), (4, 2092366080), (5, -270889920), (7, 294295680), (8, 989936640), (12, 3542525280), (13, 4380415200), (23, -301008960), (25, -1248125760), (26, 1233429120), (27, 225756720), (29, -602017920), (30, -1123476480), (32, -874177920), (35, -186973920), (37, 2119582080), (38, 1685214720), (39, 1806053760), (50, -1204035840), (53, -1444625280), (54, -903026880)]

def pairMerged287 : Integer.Sparse (Fin 271) := [(0, 134016120), (1, -2681921340), (2, 1234801260), (3, 10821444480), (4, 4342766400), (5, -491339520), (7, 982679040), (8, 1474018560), (12, 2356542720), (13, 1848510720), (24, -1474018560), (26, 2673155520), (27, 552756960), (29, -737009280), (30, -1423941120), (32, -2897959680), (36, 2211027840), (38, 2211027840), (39, 2211027840), (40, -37558080), (41, 2135911680), (50, -2948037120), (54, -2211027840), (55, -1474018560)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged288 : Integer.Sparse (Fin 271) := [(0, -81486405), (1, 707190750), (2, 3773385), (3, -2750721120), (4, -1078116480), (5, -21409920), (7, 171279360), (12, -231789600), (13, -725442480), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -1314804960), (24, -544047840), (25, -1072990800), (27, 196465500), (32, -1027676160), (35, 1541514240), (37, -1450884960), (47, 1541514240), (49, -725442480), (50, -513838080), (53, -513838080), (54, -30209760)]

def pairMerged289 : Integer.Sparse (Fin 271) := [(0, 52529715), (1, -1974730590), (2, 1238574645), (3, 8070723360), (4, 3264649920), (5, -512749440), (7, 1153958400), (8, 1474018560), (12, 2124753120), (13, 1123068240), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -1314804960), (24, -2018066400), (25, -1072990800), (26, 2673155520), (27, 749222460), (29, -737009280), (30, -1423941120), (32, -3925635840), (35, 1541514240), (36, 2211027840), (37, -1450884960), (38, 2211027840), (39, 2211027840), (40, -37558080), (41, 2135911680), (47, 1541514240), (49, -725442480), (50, -3461875200), (53, -513838080), (54, -2241237600), (55, -1474018560)]

def pairMerged290 : Integer.Sparse (Fin 271) := [(0, 249978393), (1, -4979053800), (2, 2133674865), (3, 17649757440), (4, 5357016000), (5, -783639360), (7, 1448254080), (8, 2463955200), (12, 5667278400), (13, 5503483440), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -1615813920), (24, -2018066400), (25, -2321116560), (26, 3906584640), (27, 974979180), (29, -1339027200), (30, -2547417600), (32, -4799813760), (35, 1354540320), (36, 2211027840), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (47, 1541514240), (49, -725442480), (50, -4665911040), (53, -1958463360), (54, -3144264480), (55, -1474018560)]

def pairMerged291 : Integer.Sparse (Fin 271) := [(0, -86155083), (1, -1765898820), (2, 305031825), (3, 7619391360), (4, -346187520), (5, -262316880), (7, 275607360), (8, 834986880), (12, 2673881280), (13, 6095159280), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -2395824480), (24, -60147360), (25, 480498480), (26, 3429760320), (27, 338260860), (29, -750072960), (30, 3908217600), (32, -563915520), (35, 1354540320), (36, 2211027840), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (42, 886697280), (43, 947116800), (44, -4737216960), (45, -2276346240), (46, 1946488320), (47, -404974080), (49, -725442480), (50, -367960320), (53, -1958463360), (54, -3924275040), (55, 674956800)]

def pairMerged292 : Integer.Sparse (Fin 271) := [(0, 432508356), (1, -4436865720), (2, 1073160900), (3, 5691591360), (4, 7223942880), (5, -129412080), (6, 2494800), (7, 437814720), (8, 656722080), (9, -2661120), (12, 875629440), (17, 1970166240), (20, 3940332480), (23, -656722080), (24, -3283610400), (25, -1970166240), (26, 437814720), (27, 522479160), (29, -1970166240), (30, -3940332480), (43, 3940332480), (44, 3940332480), (47, 1970166240), (50, -656722080), (66, 39916800)]

def pairMerged293 : Integer.Sparse (Fin 271) := [(0, 456957396), (1, -4782764070), (2, 1144007550), (3, 6825137760), (4, 7712923680), (5, -134968680), (6, 2494800), (7, 460041120), (8, 678948480), (9, -2661120), (12, 1120119840), (15, 200037600), (17, 1970166240), (18, 200037600), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -723401280), (24, -3683685600), (25, -2036845440), (26, 571173120), (27, 572488560), (29, -1970166240), (30, -4207049280), (36, 400075200), (43, 3940332480), (44, 3940332480), (46, 200037600), (47, 2170203840), (50, -790080480), (55, -133358400), (66, 39916800)]

def pairMerged294 : Integer.Sparse (Fin 271) := [(0, 611226), (1, -21642390), (2, -57754620), (3, 5987520), (5, 131974920), (6, -11975040), (7, -89812800), (8, -191600640), (9, 11725560), (12, 67858560), (13, 33929280), (23, -152681760), (34, 3991680), (67, -27941760), (68, 1995840), (69, -191600640), (111, -152681760), (112, -101787840)]

def pairMerged295 : Integer.Sparse (Fin 271) := [(0, 1614816), (1, 3447360), (2, 2268000), (3, -114670080), (4, 56609280), (5, 8074080), (6, -1995840), (7, -3628800), (8, 28304640), (9, -514080), (12, -110678400), (13, -228735360), (23, 66407040), (24, -84913920), (26, 56609280), (34, -57335040), (51, -31933440), (53, 132814080), (67, 6168960), (68, -3265920), (69, 9434880), (112, 66407040), (113, -84913920), (130, 44271360), (131, -56609280)]

def pairMerged296 : Integer.Sparse (Fin 271) := [(0, 2226042), (1, -18195030), (2, -55486620), (3, -108682560), (4, 56609280), (5, 140049000), (6, -13970880), (7, -93441600), (8, -163296000), (9, 11211480), (12, -42819840), (13, -194806080), (23, -86274720), (24, -84913920), (26, 56609280), (34, -53343360), (51, -31933440), (53, 132814080), (67, -21772800), (68, -1270080), (69, -182165760), (111, -152681760), (112, -35380800), (113, -84913920), (130, 44271360), (131, -56609280)]

def pairMerged297 : Integer.Sparse (Fin 271) := [(0, 459183438), (1, -4800959100), (2, 1088520930), (3, 6716455200), (4, 7769532960), (5, 5080320), (6, -11476080), (7, 366599520), (8, 515652480), (9, 8550360), (12, 1077300000), (13, -194806080), (15, 200037600), (17, 1970166240), (18, 200037600), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -809676000), (24, -3768599520), (25, -2036845440), (26, 627782400), (27, 572488560), (29, -1970166240), (30, -4207049280), (34, -53343360), (36, 400075200), (43, 3940332480), (44, 3940332480), (46, 200037600), (47, 2170203840), (50, -790080480), (51, -31933440), (53, 132814080), (55, -133358400), (66, 39916800), (67, -21772800), (68, -1270080), (69, -182165760), (111, -152681760), (112, -35380800), (113, -84913920), (130, 44271360), (131, -56609280)]

def pairMerged298 : Integer.Sparse (Fin 271) := [(0, 7969752), (1, -38363220), (2, 142702560), (3, 195410880), (4, 5080320), (5, -256782960), (6, 26546940), (7, 93260160), (8, 461220480), (9, -11657520), (13, 6350400), (24, -7620480), (26, 5080320), (27, 34020000), (29, -272160000), (34, 6350400), (51, 95800320), (54, -3810240), (55, -15240960), (67, 46630080), (68, 1270080), (69, 231880320), (112, -3810240), (113, -136080000), (131, -15240960), (146, -544320000)]

def pairMerged299 : Integer.Sparse (Fin 271) := [(0, 7348320), (1, -31372110), (2, 106970220), (3, 95981760), (4, -19776960), (5, -213282720), (6, 24216570), (7, 18688320), (8, 386648640), (9, -8550360), (13, 6350400), (24, 66951360), (26, 5080320), (27, 24698520), (29, -272160000), (34, 6350400), (50, 74571840), (51, 70943040), (54, -3810240), (55, -15240960), (67, 21772800), (68, 1270080), (69, 182165760), (111, 37285920), (112, -3810240), (113, 13063680), (131, -15240960), (146, -544320000)]

def pairMerged300 : Integer.Sparse (Fin 271) := [(0, 8714034), (1, -290504340), (2, 1257630570), (3, 4599957600), (4, 139073760), (5, -2549700720), (6, 174171060), (7, 5158883520), (8, 4182736320), (10, -1464220800), (11, 139073760), (12, 976147200), (13, 1301529600), (26, 278147520), (34, 3252070080), (51, 695368800), (80, 488073600), (143, -417221280)]

def pairMerged301 : Integer.Sparse (Fin 271) := [(0, -5298048), (1, 263042640), (2, 117936000), (3, -1111864320), (4, -489888000), (5, -88996320), (6, 12111120), (7, -33022080), (8, 129911040), (11, -97977600), (12, -359432640), (13, -426021120), (25, 293932800), (26, -587865600), (34, -360702720), (51, 421666560), (53, 881798400), (55, 587865600), (80, 194866560), (115, 259822080), (132, -97433280), (133, -389733120), (142, 195955200), (143, 293932800)]

def pairMerged302 : Integer.Sparse (Fin 271) := [(0, 3415986), (1, -27461700), (2, 1375566570), (3, 3488093280), (4, -350814240), (5, -2638697040), (6, 186282180), (7, 5125861440), (8, 4312647360), (10, -1464220800), (11, 41096160), (12, 616714560), (13, 875508480), (25, 293932800), (26, -309718080), (34, 2891367360), (51, 1117035360), (53, 881798400), (55, 587865600), (80, 682940160), (115, 259822080), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480)]

def pairMerged303 : Integer.Sparse (Fin 271) := [(0, 10764306), (1, -58833810), (2, 1482536790), (3, 3584075040), (4, -370591200), (5, -2851979760), (6, 210498750), (7, 5144549760), (8, 4699296000), (9, -8550360), (10, -1464220800), (11, 41096160), (12, 616714560), (13, 881858880), (24, 66951360), (25, 293932800), (26, -304637760), (27, 24698520), (29, -272160000), (34, 2897717760), (50, 74571840), (51, 1187978400), (53, 881798400), (54, -3810240), (55, 572624640), (67, 21772800), (68, 1270080), (69, 182165760), (80, 682940160), (111, 37285920), (112, -3810240), (113, 13063680), (115, 259822080), (131, -15240960), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

def pairMerged304 : Integer.Sparse (Fin 271) := [(0, 469947744), (1, -4859792910), (2, 2571057720), (3, 10300530240), (4, 7398941760), (5, -2846899440), (6, 199022670), (7, 5511149280), (8, 5214948480), (10, -1464220800), (11, 41096160), (12, 1694014560), (13, 687052800), (15, 200037600), (17, 1970166240), (18, 200037600), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -809676000), (24, -3701648160), (25, -1742912640), (26, 323144640), (27, 597187080), (29, -2242326240), (30, -4207049280), (34, 2844374400), (36, 400075200), (43, 3940332480), (44, 3940332480), (46, 200037600), (47, 2170203840), (50, -715508640), (51, 1156044960), (53, 1014612480), (54, -3810240), (55, 439266240), (66, 39916800), (80, 682940160), (111, -115395840), (112, -39191040), (113, -71850240), (115, 259822080), (130, 44271360), (131, -71850240), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

def pairMerged305 : Integer.Sparse (Fin 271) := [(0, 383792661), (1, -6625691730), (2, 2876089545), (3, 17919921600), (4, 7052754240), (5, -3109216320), (6, 199022670), (7, 5786756640), (8, 6049935360), (10, -1464220800), (11, 41096160), (12, 4367895840), (13, 6782212080), (14, 770757120), (15, 1832181120), (16, -725442480), (17, 1970166240), (18, -2701732320), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -3205500480), (24, -3761795520), (25, -1262414160), (26, 3752904960), (27, 935447940), (29, -2992399200), (30, -298831680), (32, -563915520), (34, 2844374400), (35, 1354540320), (36, 2611103040), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (42, 886697280), (43, 4887449280), (44, -796884480), (45, -2276346240), (46, 2146525920), (47, 1765229760), (49, -725442480), (50, -1083468960), (51, 1156044960), (53, -943850880), (54, -3928085280), (55, 1114223040), (66, 39916800), (80, 682940160), (111, -115395840), (112, -39191040), (113, -71850240), (115, 259822080), (130, 44271360), (131, -71850240), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

def pairMerged306 : Integer.Sparse (Fin 271) := [(0, 74977623), (1, -3284859690), (2, 116920125), (3, 26488425600), (4, 8149196160), (5, -1923982200), (6, 312972660), (7, 2170022400), (8, 931150080), (10, -1464220800), (11, 41096160), (12, 8748038880), (13, 12059454960), (15, -186157440), (16, 34292160), (17, -107775360), (20, 156764160), (23, 3307560480), (24, 7022272320), (25, -3825072720), (26, 4907226240), (27, -3541754160), (28, 97977600), (29, 5713727040), (30, -5467150080), (31, -282078720), (32, -11238575040), (33, 213373440), (34, 5151656160), (35, 1354540320), (36, 2611103040), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (42, 886697280), (43, 4887449280), (44, -1616630400), (45, -2276346240), (46, 2146525920), (47, 1765229760), (49, 2947084560), (50, 3858140160), (51, 1334128320), (53, -550035360), (54, -4844175840), (55, -1217099520), (66, 39916800), (80, 682940160), (111, -115395840), (112, -39191040), (113, -71850240), (115, 259822080), (130, 44271360), (131, -71850240), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

def pairMerged307 : Integer.Sparse (Fin 271) := [(0, 12340944), (1, 126664020), (2, -958513500), (3, -7230202560), (4, -682940160), (5, 2655631440), (6, -367446240), (7, -2204677440), (8, -1692472320), (12, -1959733440), (13, -5901456960), (26, -682940160), (34, -4899303360), (51, -4750824960), (53, 1536615360), (55, 1024410240), (58, 1269354240), (59, -564157440), (80, -682940160), (115, -1106058240), (132, 512205120), (133, 1024410240)]

def pairMerged308 : Integer.Sparse (Fin 271) := [(0, 2580606), (1, 265363560), (2, -1012452210), (3, -7928837280), (4, -970613280), (5, 2778919920), (6, -387994320), (7, -2204677440), (8, -1692472320), (11, -41096160), (12, -1959733440), (13, -5901456960), (26, -1011709440), (27, -61644240), (30, 246576960), (34, -5145880320), (51, -4956305760), (53, 1536615360), (54, 246576960), (55, 1024410240), (58, 1269354240), (59, -564157440), (80, -682940160), (115, -1106058240), (132, 512205120), (133, 1024410240), (143, 123288480), (147, 246576960), (148, 246576960)]

def pairMerged309 : Integer.Sparse (Fin 271) := [(0, 72675792), (1, 292073040), (2, -102354840), (3, -10487232000), (5, 142611840), (6, -31048920), (12, -4250050560), (13, -11609256960), (25, 220993920), (26, -3256485120), (31, -846236160), (32, 4692038400), (33, -2686037760), (34, -1416683520), (51, -147329280), (54, 4250050560), (59, -846236160), (60, 2538708480), (62, 220993920), (63, 441987840)]

def pairMerged310 : Integer.Sparse (Fin 271) := [(0, 76576752), (1, 272568240), (2, -570470040), (3, -12359692800), (4, -312076800), (5, 1078842240), (6, -109068120), (7, -1872460800), (8, -1248307200), (12, -4250050560), (13, -11609256960), (25, 220993920), (26, -3880638720), (31, -846236160), (32, 4692038400), (33, -2686037760), (34, -2977067520), (51, -771482880), (54, 4250050560), (59, -846236160), (60, 2538708480), (62, 220993920), (63, 441987840), (65, -312076800), (79, 936230400)]

def pairMerged311 : Integer.Sparse (Fin 271) := [(0, 79157358), (1, 537931800), (2, -1582922250), (3, -20288530080), (4, -1282690080), (5, 3857762160), (6, -497062440), (7, -4077138240), (8, -2940779520), (11, -41096160), (12, -6209784000), (13, -17510713920), (25, 220993920), (26, -4892348160), (27, -61644240), (30, 246576960), (31, -846236160), (32, 4692038400), (33, -2686037760), (34, -8122947840), (51, -5727788640), (53, 1536615360), (54, 4496627520), (55, 1024410240), (58, 1269354240), (59, -1410393600), (60, 2538708480), (62, 220993920), (63, 441987840), (65, -312076800), (79, 936230400), (80, -682940160), (115, -1106058240), (132, 512205120), (133, 1024410240), (143, 123288480), (147, 246576960), (148, 246576960)]

def pairMerged312 : Integer.Sparse (Fin 271) := [(0, -9362304), (1, -248686200), (2, 303299640), (3, 3666902400), (4, 62415360), (5, -487620000), (6, 60464880), (7, 1139080320), (8, 312076800), (12, 1435553280), (13, 3261202560), (25, 140434560), (26, 1092268800), (30, 280869120), (32, 561738240), (33, 780192000), (34, 1700818560), (50, -936230400), (51, 1279514880), (53, -608549760), (63, -468115200), (65, 312076800), (79, 280869120), (110, 280869120)]

def pairMerged313 : Integer.Sparse (Fin 271) := [(0, -41096160), (1, -231056280), (2, 532488600), (3, 8744319360), (4, 62415360), (5, -699179040), (6, 78094800), (7, 1139080320), (8, 312076800), (12, 3974261760), (13, 12569800320), (25, 140434560), (26, 1938504960), (30, 280869120), (31, 1128314880), (32, 561738240), (33, 2472664320), (34, 2547054720), (50, -936230400), (51, 2971987200), (53, -608549760), (58, -2538708480), (59, 1410393600), (60, -2538708480), (63, -468115200), (65, 312076800), (79, 280869120), (110, 280869120), (115, 846236160)]

def pairMerged314 : Integer.Sparse (Fin 271) := [(0, 150259536), (1, -2232437760), (2, 1754887680), (3, 5873575680), (4, 1985679360), (5, -1033754400), (6, 32477760), (7, 1594857600), (8, 2085471360), (10, -1409244480), (12, 2029769280), (13, 1382572800), (23, -3820582080), (24, -10424816640), (27, 3889302480), (29, -6151904640), (34, 389733120), (50, -779466240), (51, 259822080), (53, -389733120), (54, -5957038080), (58, -779466240), (70, 292299840), (72, 584599680), (73, 584599680), (77, 1116944640), (78, 2233889280), (132, -292299840)]

def pairMerged315 : Integer.Sparse (Fin 271) := [(0, 2519748), (1, -54976320), (2, -245102760), (3, -549763200), (4, -183254400), (5, 549763200), (6, -51540300), (7, -824644800), (8, -696366720), (12, 109952640), (13, 146603520), (26, -219905280), (34, -476461440), (51, -329857920), (71, 164928960), (73, 329857920), (79, 219905280), (82, -329857920), (83, -659715840), (133, -164928960), (143, 329857920)]

def pairMerged316 : Integer.Sparse (Fin 271) := [(0, 152779284), (1, -2287414080), (2, 1509784920), (3, 5323812480), (4, 1802424960), (5, -483991200), (6, -19062540), (7, 770212800), (8, 1389104640), (10, -1409244480), (12, 2139721920), (13, 1529176320), (23, -3820582080), (24, -10424816640), (26, -219905280), (27, 3889302480), (29, -6151904640), (34, -86728320), (50, -779466240), (51, -70035840), (53, -389733120), (54, -5957038080), (58, -779466240), (70, 292299840), (71, 164928960), (72, 584599680), (73, 914457600), (77, 1116944640), (78, 2233889280), (79, 219905280), (82, -329857920), (83, -659715840), (132, -292299840), (133, -164928960), (143, 329857920)]

def pairMerged317 : Integer.Sparse (Fin 271) := [(0, 111683124), (1, -2518470360), (2, 2042273520), (3, 14068131840), (4, 1864840320), (5, -1183170240), (6, 59032260), (7, 1909293120), (8, 1701181440), (10, -1409244480), (12, 6113983680), (13, 14098976640), (23, -3820582080), (24, -10424816640), (25, 140434560), (26, 1718599680), (27, 3889302480), (29, -6151904640), (30, 280869120), (31, 1128314880), (32, 561738240), (33, 2472664320), (34, 2460326400), (50, -1715696640), (51, 2901951360), (53, -998282880), (54, -5957038080), (58, -3318174720), (59, 1410393600), (60, -2538708480), (63, -468115200), (65, 312076800), (70, 292299840), (71, 164928960), (72, 584599680), (73, 914457600), (77, 1116944640), (78, 2233889280), (79, 500774400), (82, -329857920), (83, -659715840), (110, 280869120), (115, 846236160), (132, -292299840), (133, -164928960), (143, 329857920)]

def pairMerged318 : Integer.Sparse (Fin 271) := [(0, 190840482), (1, -1980538560), (2, 459351270), (3, -6220398240), (4, 582150240), (5, 2674591920), (6, -438030180), (7, -2167845120), (8, -1239598080), (10, -1409244480), (11, -41096160), (12, -95800320), (13, -3411737280), (23, -3820582080), (24, -10424816640), (25, 361428480), (26, -3173748480), (27, 3827658240), (29, -6151904640), (30, 527446080), (31, 282078720), (32, 5253776640), (33, -213373440), (34, -5662621440), (50, -1715696640), (51, -2825837280), (53, 538332480), (54, -1460410560), (55, 1024410240), (58, -2048820480), (62, 220993920), (63, -26127360), (70, 292299840), (71, 164928960), (72, 584599680), (73, 914457600), (77, 1116944640), (78, 2233889280), (79, 1437004800), (80, -682940160), (82, -329857920), (83, -659715840), (110, 280869120), (115, -259822080), (132, 219905280), (133, 859481280), (143, 453146400), (147, 246576960), (148, 246576960)]

def pairMerged319 : Integer.Sparse (Fin 271) := [(0, -38359818), (1, 911770020), (2, -365865255), (3, -6769072800), (4, -1878901920), (5, 125000820), (6, -3433185), (7, -689018400), (8, -134084160), (10, 201126240), (12, -3641455440), (13, -1548454320), (23, 1938595680), (24, 1206757440), (25, 1519469280), (26, -439447680), (27, -351970920), (32, 329585760), (34, -219723840), (42, -1977514560), (46, -2413514880), (47, -1206757440), (49, -1097757360), (50, 1206757440), (51, -109861920), (54, 1134090720), (58, 402252480), (77, -603378720), (87, -1206757440), (96, -988757280), (103, -494378640)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged320 : Integer.Sparse (Fin 271) := [(0, -40666374), (1, 919458540), (2, 364544145), (3, -4185730080), (4, -1325328480), (5, -828375660), (6, 69607755), (7, 479636640), (8, 1096079040), (10, 201126240), (12, -3641455440), (13, -1548454320), (23, 1938595680), (24, 1206757440), (25, 1519469280), (26, 298650240), (27, -351970920), (32, 329585760), (34, 518374080), (42, -1977514560), (46, -2413514880), (47, -1206757440), (49, -1097757360), (50, 1206757440), (51, 874268640), (54, 1134090720), (58, 402252480), (77, -603378720), (79, -1476195840), (81, 553573440), (83, 2214293760), (84, 1107146880), (87, -1206757440), (96, -988757280), (103, -494378640), (143, -1107146880)]

def pairMerged321 : Integer.Sparse (Fin 271) := [(0, -19085220), (1, -131912550), (2, -56133000), (3, 224532000), (4, 44906400), (5, 67359600), (6, 2806650), (7, 44906400), (8, -404157600), (12, 763408800), (13, 269438400), (24, 134719200), (25, -943034400), (26, -134719200), (27, -33679800), (32, -943034400), (34, 224532000), (42, 404157600), (49, 404157600), (50, 538876800), (51, 134719200), (54, -269438400), (55, 538876800), (75, -404157600), (88, 404157600), (96, 404157600), (98, -808315200), (99, -808315200), (103, 808315200), (143, 134719200)]

def pairMerged322 : Integer.Sparse (Fin 271) := [(0, -331692165), (1, 3580905510), (2, -708483510), (3, -6105637440), (4, -7088860800), (5, 38385900), (6, -6239835), (7, 7711200), (8, 7711200), (10, -311078880), (12, -725714640), (13, 829543680), (24, 806410080), (25, 2534490000), (26, -1551402720), (30, 8110368000), (34, -199674720), (37, 311078880), (39, 622157760), (42, -3041388000), (43, -6082776000), (50, -207385920), (51, -130546080), (54, 702717120), (58, -622157760), (70, 311078880), (73, 622157760), (87, 622157760), (88, -1797072480), (94, 1244315520), (103, -1520694000), (132, -103692960)]

def pairMerged323 : Integer.Sparse (Fin 271) := [(0, -350777385), (1, 3448992960), (2, -764616510), (3, -5881105440), (4, -7043954400), (5, 105745500), (6, -3433185), (7, 52617600), (8, -396446400), (10, -311078880), (12, 37694160), (13, 1098982080), (24, 941129280), (25, 1591455600), (26, -1686121920), (27, -33679800), (30, 8110368000), (32, -943034400), (34, 24857280), (37, 311078880), (39, 622157760), (42, -2637230400), (43, -6082776000), (49, 404157600), (50, 331490880), (51, 4173120), (54, 433278720), (55, 538876800), (58, -622157760), (70, 311078880), (73, 622157760), (75, -404157600), (87, 622157760), (88, -1392914880), (94, 1244315520), (96, 404157600), (98, -808315200), (99, -808315200), (103, -712378800), (132, -103692960), (143, 134719200)]

def pairMerged324 : Integer.Sparse (Fin 271) := [(0, -391443759), (1, 4368451500), (2, -400072365), (3, -10066835520), (4, -8369282880), (5, -722630160), (6, 66174570), (7, 532254240), (8, 699632640), (10, -109952640), (12, -3603761280), (13, -449472240), (23, 1938595680), (24, 2147886720), (25, 3110924880), (26, -1387471680), (27, -385650720), (30, 8110368000), (32, -613448640), (34, 543231360), (37, 311078880), (39, 622157760), (42, -4614744960), (43, -6082776000), (46, -2413514880), (47, -1206757440), (49, -693599760), (50, 1538248320), (51, 878441760), (54, 1567369440), (55, 538876800), (58, -219905280), (70, 311078880), (73, 622157760), (75, -404157600), (77, -603378720), (79, -1476195840), (81, 553573440), (83, 2214293760), (84, 1107146880), (87, -584599680), (88, -1392914880), (94, 1244315520), (96, -584599680), (98, -808315200), (99, -808315200), (103, -1206757440), (132, -103692960), (143, -972427680)]

def pairMerged325 : Integer.Sparse (Fin 271) := [(0, 55438992), (1, 84454650), (2, -436153410), (3, -3679875360), (4, 831993120), (5, 387215640), (6, -20309940), (7, -736464960), (8, -425386080), (10, 933236640), (12, -2831552640), (13, -4977262080), (23, 83280960), (24, -134719200), (26, 393543360), (27, 33679800), (30, -269438400), (32, 2488631040), (34, -947116800), (35, -933236640), (37, -1866473280), (39, -1866473280), (42, 808315200), (44, 1616630400), (50, -673596000), (51, -829543680), (53, 1555394400), (54, 663798240), (55, -538876800), (58, 1244315520), (70, -933236640), (73, -1866473280), (75, 404157600), (97, 808315200), (99, 808315200), (132, 311078880), (143, -134719200)]

def pairMerged326 : Integer.Sparse (Fin 271) := [(0, 112424760), (1, -1092971880), (2, 16380630), (3, 543775680), (4, 2709171360), (5, 236370960), (6, -16119810), (7, 997920), (8, -291301920), (10, 732110400), (12, -753248160), (13, -4843177920), (23, -1726855200), (24, -1341476640), (25, -402252480), (26, 929880000), (27, 385650720), (30, -1476195840), (32, 2488631040), (34, -745990560), (35, -933236640), (37, -1866473280), (39, -1866473280), (42, 3221830080), (44, 1616630400), (50, -673596000), (51, -695459520), (53, 1555394400), (54, -341832960), (55, -538876800), (58, 1244315520), (70, -933236640), (73, -1866473280), (75, 404157600), (77, 603378720), (88, 1206757440), (97, 808315200), (99, 808315200), (103, 1206757440), (132, 311078880), (143, -134719200)]

def pairMerged327 : Integer.Sparse (Fin 271) := [(0, -20062728), (1, 1058135400), (2, 235078200), (3, -5067619200), (4, -2103978240), (5, -109317600), (6, 5465880), (7, 524724480), (10, 1116944640), (12, -1466035200), (13, -408240000), (23, 744629760), (24, 1489259520), (25, 854582400), (26, 174908160), (27, -93078720), (32, 1929070080), (34, 874540800), (40, 1574173440), (49, -2233889280), (51, 699632640), (54, 2978519040), (58, 329857920), (71, 787086720), (73, 1574173440), (77, -1116944640), (78, -2233889280), (87, -329857920), (93, -659715840), (133, -787086720)]

def pairMerged328 : Integer.Sparse (Fin 271) := [(0, 72977436), (1, -1032949260), (2, 1476955620), (3, 9902450880), (4, 2191069440), (5, -1658406960), (6, 138427380), (7, 1863207360), (8, 2531813760), (10, -109952640), (12, 2475385920), (13, 2307009600), (23, -840974400), (25, -109952640), (26, 1362977280), (27, 82464480), (30, -1533349440), (32, -1462043520), (34, 1339208640), (37, 659715840), (43, 3066698880), (50, -3946320000), (51, 1874093760), (53, -2924087040), (54, -219905280), (58, -769668480), (70, 329857920), (72, 659715840), (79, -1022232960), (87, 329857920), (88, 1533349440), (91, 3066698880), (92, 3066698880), (93, 659715840), (132, -329857920)]

def pairMerged329 : Integer.Sparse (Fin 271) := [(0, 52914708), (1, 25186140), (2, 1712033820), (3, 4834831680), (4, 87091200), (5, -1767724560), (6, 143893260), (7, 2387931840), (8, 2531813760), (10, 1006992000), (12, 1009350720), (13, 1898769600), (23, -96344640), (24, 1489259520), (25, 744629760), (26, 1537885440), (27, -10614240), (30, -1533349440), (32, 467026560), (34, 2213749440), (37, 659715840), (40, 1574173440), (43, 3066698880), (49, -2233889280), (50, -3946320000), (51, 2573726400), (53, -2924087040), (54, 2758613760), (58, -439810560), (70, 329857920), (71, 787086720), (72, 659715840), (73, 1574173440), (77, -1116944640), (78, -2233889280), (79, -1022232960), (88, 1533349440), (91, 3066698880), (92, 3066698880), (132, -329857920), (133, -787086720)]

def pairMerged330 : Integer.Sparse (Fin 271) := [(0, 165339468), (1, -1067785740), (2, 1728414450), (3, 5378607360), (4, 2796262560), (5, -1531353600), (6, 127773450), (7, 2388929760), (8, 2240511840), (10, 1739102400), (12, 256102560), (13, -2944408320), (23, -1823199840), (24, 147782880), (25, 342377280), (26, 2467765440), (27, 375036480), (30, -3009545280), (32, 2955657600), (34, 1467758880), (35, -933236640), (37, -1206757440), (39, -1866473280), (40, 1574173440), (42, 3221830080), (43, 3066698880), (44, 1616630400), (49, -2233889280), (50, -4619916000), (51, 1878266880), (53, -1368692640), (54, 2416780800), (55, -538876800), (58, 804504960), (70, -603378720), (71, 787086720), (72, 659715840), (73, -292299840), (75, 404157600), (77, -513565920), (78, -2233889280), (79, -1022232960), (88, 2740106880), (91, 3066698880), (92, 3066698880), (97, 808315200), (99, 808315200), (103, 1206757440), (132, -18779040), (133, -787086720), (143, -134719200)]

def pairMerged331 : Integer.Sparse (Fin 271) := [(0, -226104291), (1, 3300665760), (2, 1328342085), (3, -4688228160), (4, -5573020320), (5, -2253983760), (6, 193948020), (7, 2921184000), (8, 2940144480), (10, 1629149760), (12, -3347658720), (13, -3393880560), (23, 115395840), (24, 2295669600), (25, 3453302160), (26, 1080293760), (27, -10614240), (30, 5100822720), (32, 2342208960), (34, 2010990240), (35, -933236640), (37, -895678560), (39, -1244315520), (40, 1574173440), (42, -1392914880), (43, -3016077120), (44, 1616630400), (46, -2413514880), (47, -1206757440), (49, -2927489040), (50, -3081667680), (51, 2756708640), (53, -1368692640), (54, 3984150240), (58, 584599680), (70, -292299840), (71, 787086720), (72, 659715840), (73, 329857920), (77, -1116944640), (78, -2233889280), (79, -2498428800), (81, 553573440), (83, 2214293760), (84, 1107146880), (87, -584599680), (88, 1347192000), (91, 3066698880), (92, 3066698880), (94, 1244315520), (96, -584599680), (97, 808315200), (98, -808315200), (132, -122472000), (133, -787086720), (143, -1107146880)]

def pairMerged332 : Integer.Sparse (Fin 271) := [(0, -35263809), (1, 1320127200), (2, 1787693355), (3, -10908626400), (4, -4990870080), (5, 420608160), (6, -244082160), (7, 753338880), (8, 1700546400), (10, 219905280), (11, -41096160), (12, -3443459040), (13, -6805617840), (23, -3705186240), (24, -8129147040), (25, 3814730640), (26, -2093454720), (27, 3817044000), (29, -6151904640), (30, 5628268800), (31, 282078720), (32, 7595985600), (33, -213373440), (34, -3651631200), (35, -933236640), (37, -895678560), (39, -1244315520), (40, 1574173440), (42, -1392914880), (43, -3016077120), (44, 1616630400), (46, -2413514880), (47, -1206757440), (49, -2927489040), (50, -4797364320), (51, -69128640), (53, -830360160), (54, 2523739680), (55, 1024410240), (58, -1464220800), (62, 220993920), (63, -26127360), (71, 952015680), (72, 1244315520), (73, 1244315520), (79, -1061424000), (80, -682940160), (81, 553573440), (82, -329857920), (83, 1554577920), (84, 1107146880), (87, -584599680), (88, 1347192000), (91, 3066698880), (92, 3066698880), (94, 1244315520), (96, -584599680), (97, 808315200), (98, -808315200), (110, 280869120), (115, -259822080), (132, 97433280), (133, 72394560), (143, -654000480), (147, 246576960), (148, 246576960)]

def pairMerged333 : Integer.Sparse (Fin 271) := [(0, -16272900), (1, 90493200), (2, 56030940), (3, -359614080), (4, -439629120), (5, -76749120), (6, 8799840), (7, 256374720), (8, -75660480), (12, 270708480), (13, 234601920), (23, -97433280), (24, 75660480), (25, -194866560), (26, -421666560), (30, -119206080), (32, -584599680), (34, 371770560), (36, -778921920), (39, -519281280), (40, 292299840), (42, 584599680), (50, -292299840), (51, 396990720), (53, -194866560), (55, 432734400), (58, -194866560), (71, 292299840), (79, 151320960), (81, -259640640), (83, -519281280), (87, 584599680), (88, 292299840), (91, -519281280), (95, 584599680), (96, 584599680), (99, -519281280), (133, -97433280), (143, 346187520)]

def pairMerged334 : Integer.Sparse (Fin 271) := [(0, -5277636), (1, -273724920), (2, 282808260), (3, 1619533440), (4, 476642880), (5, -177539040), (6, 13381200), (7, 622883520), (8, -2358720), (12, 783820800), (13, 674412480), (23, -97433280), (24, 75660480), (25, -634677120), (26, 164747520), (30, -668969280), (32, -1024410240), (34, 701628480), (36, -778921920), (37, 329857920), (38, 659715840), (39, -519281280), (40, 952015680), (42, 584599680), (45, 659715840), (50, -512205120), (51, 690197760), (53, -524724480), (55, 432734400), (58, -194866560), (71, 292299840), (79, -68584320), (81, -259640640), (82, 329857920), (83, 140434560), (87, 584599680), (88, 622157760), (91, -519281280), (95, 1244315520), (96, 584599680), (99, -519281280), (133, -97433280), (143, 16329600)]

def pairMerged335 : Integer.Sparse (Fin 271) := [(0, -34047216), (1, 811989360), (2, -513974160), (3, -5924378880), (4, -1593768960), (5, 284135040), (6, -6123600), (7, -1188794880), (8, -411505920), (12, -2299207680), (13, -437633280), (23, 842607360), (24, 1077753600), (25, 940584960), (26, -849139200), (27, -323326080), (30, 627056640), (32, 1410877440), (34, -306996480), (35, -587865600), (36, -587865600), (38, -1175731200), (39, -1175731200), (47, -646652160), (50, 1077753600), (51, -65318400), (53, 725034240), (54, 979776000), (79, 391910400), (81, -293932800), (83, -587865600), (85, -587865600), (92, -1881169920), (97, -1293304320), (143, 391910400)]

def pairMerged336 : Integer.Sparse (Fin 271) := [(0, -104781600), (1, 1996021440), (2, -1467350640), (3, -11214080640), (4, -3931079040), (5, 929970720), (6, -36877680), (7, -2049909120), (8, -1518652800), (12, -2791272960), (13, -683665920), (23, 842607360), (24, 1815851520), (25, 1678682880), (26, -2079302400), (27, -323326080), (30, 2841350400), (32, 3256122240), (34, -676045440), (35, -587865600), (36, -587865600), (38, -3390024960), (39, -1175731200), (41, -2214293760), (43, -1107146880), (47, -646652160), (50, 1077753600), (51, -680400000), (53, 1463132160), (54, 979776000), (55, 369048960), (79, 1130008320), (81, -293932800), (83, -1695012480), (84, -1107146880), (85, -587865600), (89, -1107146880), (91, -2214293760), (92, -2988316800), (97, -1293304320), (143, 760959360)]

def pairMerged337 : Integer.Sparse (Fin 271) := [(0, -110059236), (1, 1722296520), (2, -1184542380), (3, -9594547200), (4, -3454436160), (5, 752431680), (6, -23496480), (7, -1427025600), (8, -1521011520), (12, -2007452160), (13, -9253440), (23, 745174080), (24, 1891512000), (25, 1044005760), (26, -1914554880), (27, -323326080), (30, 2172381120), (32, 2231712000), (34, 25583040), (35, -587865600), (36, -1366787520), (37, 329857920), (38, -2730309120), (39, -1695012480), (40, 952015680), (41, -2214293760), (42, 584599680), (43, -1107146880), (45, 659715840), (47, -646652160), (50, 565548480), (51, 9797760), (53, 938407680), (54, 979776000), (55, 801783360), (58, -194866560), (71, 292299840), (79, 1061424000), (81, -553573440), (82, 329857920), (83, -1554577920), (84, -1107146880), (85, -587865600), (87, 584599680), (88, 622157760), (89, -1107146880), (91, -2733575040), (92, -2988316800), (95, 1244315520), (96, 584599680), (97, -1293304320), (99, -519281280), (133, -97433280), (143, 777288960)]

def pairMerged338 : Integer.Sparse (Fin 271) := [(0, 35598528), (1, 918403920), (2, -951301260), (3, -8986723200), (4, -1244315520), (5, 746943120), (6, -39837420), (7, -2073859200), (8, -967800960), (10, 1244315520), (12, -3871203840), (13, -5530291200), (23, -161663040), (25, -161663040), (26, -1106058240), (27, 94303440), (29, -161663040), (30, -323326080), (32, 1659087360), (34, -1797344640), (36, -1244315520), (38, -1244315520), (39, -1244315520), (40, -2488631040), (50, 1659087360), (51, -1382572800), (53, 829543680), (54, 1244315520), (58, 1659087360), (62, -107775360), (66, 26943840), (71, -1244315520), (72, -1244315520), (73, -1244315520), (88, -2488631040), (94, -1244315520), (95, -1244315520), (97, 484989120), (111, -161663040), (130, -53887680), (133, 414771840), (146, -323326080), (147, -161663040)]

def pairMerged339 : Integer.Sparse (Fin 271) := [(0, 94538178), (1, -16210530), (2, -603276660), (3, -5977994400), (4, 641753280), (5, 645903720), (6, -39837420), (7, -1534982400), (8, -833081760), (10, 1244315520), (12, -3332327040), (13, -5530291200), (23, -565820640), (24, -673596000), (25, -969978240), (26, -746807040), (27, 296382240), (29, -161663040), (30, -2209394880), (32, 1659087360), (34, -1707531840), (36, -1244315520), (38, -1244315520), (39, -1244315520), (40, -2488631040), (45, 1616630400), (46, 404157600), (50, 985491360), (51, -1382572800), (53, 560105280), (54, 1244315520), (58, 1659087360), (62, -107775360), (66, 26943840), (71, -1244315520), (72, -1244315520), (73, -1244315520), (88, -2488631040), (89, 808315200), (94, -1244315520), (95, -1244315520), (97, 484989120), (98, 808315200), (111, -161663040), (130, -53887680), (133, 414771840), (146, -323326080), (147, -161663040)]

def pairMerged340 : Integer.Sparse (Fin 271) := [(0, -6910596), (1, -156465540), (2, -50092560), (3, 949656960), (4, 490432320), (5, 75146400), (6, -5828760), (7, 148599360), (8, -279780480), (12, 22135680), (13, 65076480), (23, 312984000), (24, -519281280), (26, 230791680), (27, -148191120), (29, 625968000), (30, -346187520), (34, 180472320), (50, -585688320), (51, 115395840), (53, 139890240), (54, -173093760), (55, -432734400), (66, -81012960), (88, 519281280), (89, 259640640), (99, 519281280), (111, 486077760), (130, 162025920), (146, 972155520), (148, -259640640)]

def pairMerged341 : Integer.Sparse (Fin 271) := [(0, -111132), (1, -6146280), (2, 5590620), (3, 82736640), (4, 19595520), (5, -2177280), (7, 13063680), (12, 50077440), (13, 13063680), (14, 122472000), (15, 58786560), (23, -194866560), (24, -19595520), (25, -120839040), (27, 11430720), (32, -39191040), (34, 4354560), (50, -39191040), (53, -39191040), (62, -94711680), (66, 5034960), (111, -74027520), (113, -6531840), (116, 81648000), (124, 39191040), (130, -40279680), (136, 58786560), (144, 122472000)]

def pairMerged342 : Integer.Sparse (Fin 271) := [(0, -7021728), (1, -162611820), (2, -44501940), (3, 1032393600), (4, 510027840), (5, 72969120), (6, -5828760), (7, 161663040), (8, -279780480), (12, 72213120), (13, 78140160), (14, 122472000), (15, 58786560), (23, 118117440), (24, -538876800), (25, -120839040), (26, 230791680), (27, -136760400), (29, 625968000), (30, -346187520), (32, -39191040), (34, 184826880), (50, -624879360), (51, 115395840), (53, 100699200), (54, -173093760), (55, -432734400), (62, -94711680), (66, -75978000), (88, 519281280), (89, 259640640), (99, 519281280), (111, 412050240), (113, -6531840), (116, 81648000), (124, 39191040), (130, 121746240), (136, 58786560), (144, 122472000), (146, 972155520), (148, -259640640)]

def pairMerged343 : Integer.Sparse (Fin 271) := [(0, 87516450), (1, -178822350), (2, -647778600), (3, -4945600800), (4, 1151781120), (5, 718872840), (6, -45666180), (7, -1373319360), (8, -1112862240), (10, 1244315520), (12, -3260113920), (13, -5452151040), (14, 122472000), (15, 58786560), (23, -447703200), (24, -1212472800), (25, -1090817280), (26, -516015360), (27, 159621840), (29, 464304960), (30, -2555582400), (32, 1619896320), (34, -1522704960), (36, -1244315520), (38, -1244315520), (39, -1244315520), (40, -2488631040), (45, 1616630400), (46, 404157600), (50, 360612000), (51, -1267176960), (53, 660804480), (54, 1071221760), (55, -432734400), (58, 1659087360), (62, -202487040), (66, -49034160), (71, -1244315520), (72, -1244315520), (73, -1244315520), (88, -1969349760), (89, 1067955840), (94, -1244315520), (95, -1244315520), (97, 484989120), (98, 808315200), (99, 519281280), (111, 250387200), (113, -6531840), (116, 81648000), (124, 39191040), (130, 67858560), (133, 414771840), (136, 58786560), (144, 122472000), (146, 648829440), (147, -161663040), (148, -259640640)]

def pairMerged344 : Integer.Sparse (Fin 271) := [(0, -22542786), (1, 1543474170), (2, -1832320980), (3, -14540148000), (4, -2302655040), (5, 1471304520), (6, -69162660), (7, -2800344960), (8, -2633873760), (10, 1244315520), (12, -5267566080), (13, -5461404480), (14, 122472000), (15, 58786560), (23, 297470880), (24, 679039200), (25, -46811520), (26, -2430570240), (27, -163704240), (29, 464304960), (30, -383201280), (32, 3851608320), (34, -1497121920), (35, -587865600), (36, -2611103040), (37, 329857920), (38, -3974624640), (39, -2939328000), (40, -1536615360), (41, -2214293760), (42, 584599680), (43, -1107146880), (45, 2276346240), (46, 404157600), (47, -646652160), (50, 926160480), (51, -1257379200), (53, 1599212160), (54, 2050997760), (55, 369048960), (58, 1464220800), (62, -202487040), (66, -49034160), (71, -952015680), (72, -1244315520), (73, -1244315520), (79, 1061424000), (81, -553573440), (82, 329857920), (83, -1554577920), (84, -1107146880), (85, -587865600), (87, 584599680), (88, -1347192000), (89, -39191040), (91, -2733575040), (92, -2988316800), (94, -1244315520), (96, 584599680), (97, -808315200), (98, 808315200), (111, 250387200), (113, -6531840), (116, 81648000), (124, 39191040), (130, 67858560), (133, 317338560), (136, 58786560), (143, 777288960), (144, 122472000), (146, 648829440), (147, -161663040), (148, -259640640)]

def pairMerged345 : Integer.Sparse (Fin 271) := [(0, -23308236), (1, 394552620), (2, -62506080), (3, -1373319360), (4, -838252800), (5, 12519360), (7, -113218560), (12, -323144640), (13, -226618560), (16, -83280960), (23, 339655680), (24, 228614400), (25, 571536000), (26, -381024000), (27, -58922640), (30, 571536000), (34, -101243520), (37, -166561920), (43, -685843200), (50, 111041280), (53, 111041280), (54, 398442240), (62, 76204800), (66, -2313360), (100, -342921600), (110, 114307200), (111, 27760320), (112, 9253440), (120, -83280960), (121, -55520640), (130, 18506880)]

def pairMerged346 : Integer.Sparse (Fin 271) := [(0, -12421836), (1, 353728620), (2, -28486080), (3, -1373319360), (4, -838252800), (5, -3810240), (6, 4082400), (7, -113218560), (12, -323144640), (13, -226618560), (16, -83280960), (17, 587865600), (23, -52254720), (24, 228614400), (25, -277603200), (26, -381024000), (27, 6395760), (29, -195955200), (30, -212284800), (34, -101243520), (37, -166561920), (43, -685843200), (50, 111041280), (53, 111041280), (54, 398442240), (62, -54432000), (66, 14016240), (85, 587865600), (100, 244944000), (110, -473558400), (111, -168194880), (112, 9253440), (120, -83280960), (121, -55520640), (130, -112129920), (134, 587865600), (140, 391910400), (142, -195955200), (146, -65318400), (147, -195955200)]

def pairMerged347 : Integer.Sparse (Fin 271) := [(0, -12065760), (1, 99179640), (2, -49147560), (3, -191600640), (4, -104509440), (5, 13335840), (12, -87091200), (13, -17418240), (14, -122472000), (15, -117573120), (17, -244944000), (20, -235146240), (23, 256919040), (24, 117573120), (25, 326592000), (27, -103420800), (29, 160030080), (30, 244944000), (50, 78382080), (51, -26127360), (62, 27216000), (100, -244944000), (110, 81648000), (111, 54432000), (113, 52254720), (116, -81648000), (124, -78382080), (134, -489888000), (136, -235146240), (138, -470292480), (144, -244944000)]

def pairMerged348 : Integer.Sparse (Fin 271) := [(0, 2181816), (1, -63753480), (2, 7620480), (3, 296110080), (4, 92534400), (5, 9797760), (6, -1224720), (12, 141886080), (13, 74027520), (16, 83280960), (17, 78382080), (23, -53887680), (25, 39191040), (26, 37013760), (27, -36741600), (28, -176359680), (29, 146966400), (30, 58786560), (34, 18506880), (37, 83280960), (39, 166561920), (50, -55520640), (51, 18506880), (54, -138801600), (112, -37013760), (120, 166561920), (121, 55520640), (126, 333123840), (134, -176359680), (140, -58786560), (146, 39191040), (150, -352719360)]

def pairMerged349 : Integer.Sparse (Fin 271) := [(0, -9883944), (1, 35426160), (2, -41527080), (3, 104509440), (4, -11975040), (5, 23133600), (6, -1224720), (12, 54794880), (13, 56609280), (14, -122472000), (15, -117573120), (16, 83280960), (17, -166561920), (20, -235146240), (23, 203031360), (24, 117573120), (25, 365783040), (26, 37013760), (27, -140162400), (28, -176359680), (29, 306996480), (30, 303730560), (34, 18506880), (37, 83280960), (39, 166561920), (50, 22861440), (51, -7620480), (54, -138801600), (62, 27216000), (100, -244944000), (110, 81648000), (111, 54432000), (112, -37013760), (113, 52254720), (116, -81648000), (120, 166561920), (121, 55520640), (124, -78382080), (126, 333123840), (134, -666247680), (136, -235146240), (138, -470292480), (140, -58786560), (144, -244944000), (146, 39191040), (150, -352719360)]

def pairMerged350 : Integer.Sparse (Fin 271) := [(0, -22305780), (1, 389154780), (2, -70013160), (3, -1268809920), (4, -850227840), (5, 19323360), (6, 2857680), (7, -113218560), (12, -268349760), (13, -170009280), (14, -122472000), (15, -117573120), (17, 421303680), (20, -235146240), (23, 150776640), (24, 346187520), (25, 88179840), (26, -344010240), (27, -133766640), (28, -176359680), (29, 111041280), (30, 91445760), (34, -82736640), (37, -83280960), (39, 166561920), (43, -685843200), (50, 133902720), (51, -7620480), (53, 111041280), (54, 259640640), (62, -27216000), (66, 14016240), (85, 587865600), (110, -391910400), (111, -113762880), (112, -27760320), (113, 52254720), (116, -81648000), (120, 83280960), (124, -78382080), (126, 333123840), (130, -112129920), (134, -78382080), (136, -235146240), (138, -470292480), (140, 333123840), (142, -195955200), (144, -244944000), (146, -26127360), (147, -195955200), (150, -352719360)]

def pairMerged351 : Integer.Sparse (Fin 271) := [(0, -1789452), (1, 51948540), (2, -16737840), (3, -351086400), (4, -101243520), (5, 6259680), (7, -37013760), (12, -180169920), (13, -35380800), (16, -34292160), (23, 150232320), (24, 91445760), (25, 71850240), (26, -21772800), (27, -25719120), (32, 39191040), (37, -19595520), (42, -78382080), (46, -137168640), (49, -19595520), (50, 45722880), (53, 6531840), (54, 91445760), (63, 13063680), (66, -2857680), (101, -39191040), (111, 11430720), (112, 34292160), (113, 22861440), (120, -102876480), (136, -68584320)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged352 : Integer.Sparse (Fin 271) := [(0, -1279152), (1, 2619540), (2, 11328660), (3, 2721600), (4, 7620480), (5, -3946320), (7, 17418240), (12, 10342080), (13, -35380800), (15, 244944000), (16, -34292160), (23, -135535680), (24, -153498240), (25, -132269760), (26, -21772800), (27, 35516880), (32, -42456960), (37, -19595520), (42, -78382080), (46, -137168640), (47, 244944000), (49, -19595520), (50, -35925120), (53, 6531840), (54, -71850240), (63, 13063680), (66, 7348320), (101, -39191040), (111, -70217280), (112, 34292160), (113, -58786560), (117, 244944000), (120, -102876480), (131, -81648000), (136, 176359680), (144, 122472000)]

def pairMerged353 : Integer.Sparse (Fin 271) := [(0, 10981656), (1, -424773720), (2, 106822800), (3, 1963906560), (4, 754427520), (5, -38374560), (6, 2313360), (7, 64229760), (8, 54432000), (12, 762048000), (13, 740275200), (15, 39191040), (22, 333123840), (23, -75116160), (24, -150232320), (25, -248209920), (26, 259096320), (27, 51438240), (30, -385378560), (32, -509483520), (34, 185068800), (35, 166561920), (38, 744629760), (41, 744629760), (50, -522547200), (51, 74027520), (53, -499685760), (54, -192689280), (55, -453962880), (63, -13063680), (66, 1632960), (89, 205752960), (101, 39191040), (111, -6531840), (112, -6531840), (113, -13063680), (120, 19595520), (124, 39191040), (125, 39191040), (131, -13063680), (135, 333123840), (141, 333123840), (148, -68584320)]

def pairMerged354 : Integer.Sparse (Fin 271) := [(0, -13295016), (1, 419058360), (2, -129684240), (3, -1720051200), (4, -741363840), (5, 59603040), (6, -4626720), (7, -100154880), (8, -91445760), (12, -545408640), (13, -333123840), (15, -39191040), (17, -333123840), (22, -333123840), (23, 146966400), (24, 424569600), (25, 349453440), (26, -276514560), (27, -78382080), (30, 489888000), (32, 342921600), (34, -111041280), (38, -666247680), (41, -666247680), (43, -78382080), (47, -156764160), (50, 437633280), (51, -74027520), (53, 163296000), (54, 274337280), (55, 277603200), (63, 26127360), (66, -17146080), (89, -166561920), (91, -333123840), (92, -78382080), (110, 111041280), (111, 55520640), (112, 39191040), (113, 150232320), (117, -244944000), (125, -39191040), (126, -333123840), (131, 166561920), (135, -333123840), (137, -78382080), (140, -333123840), (141, -333123840), (147, 111041280), (148, 81648000)]

def pairMerged355 : Integer.Sparse (Fin 271) := [(0, -2313360), (1, -5715360), (2, -22861440), (3, 243855360), (4, 13063680), (5, 21228480), (6, -2313360), (7, -35925120), (8, -37013760), (12, 216639360), (13, 407151360), (17, -333123840), (23, 71850240), (24, 274337280), (25, 101243520), (26, -17418240), (27, -26943840), (30, 104509440), (32, -166561920), (34, 74027520), (35, 166561920), (38, 78382080), (41, 78382080), (43, -78382080), (47, -156764160), (50, -84913920), (53, -336389760), (54, 81648000), (55, -176359680), (63, 13063680), (66, -15513120), (89, 39191040), (91, -333123840), (92, -78382080), (101, 39191040), (110, 111041280), (111, 48988800), (112, 32659200), (113, 137168640), (117, -244944000), (120, 19595520), (124, 39191040), (126, -333123840), (131, 153498240), (137, -78382080), (140, -333123840), (147, 111041280), (148, 13063680)]

def pairMerged356 : Integer.Sparse (Fin 271) := [(0, -3592512), (1, -3095820), (2, -11532780), (3, 246576960), (4, 20684160), (5, 17282160), (6, -2313360), (7, -18506880), (8, -37013760), (12, 226981440), (13, 371770560), (15, 244944000), (16, -34292160), (17, -333123840), (23, -63685440), (24, 120839040), (25, -31026240), (26, -39191040), (27, 8573040), (30, 104509440), (32, -209018880), (34, 74027520), (35, 166561920), (37, -19595520), (38, 78382080), (41, 78382080), (42, -78382080), (43, -78382080), (46, -137168640), (47, 88179840), (49, -19595520), (50, -120839040), (53, -329857920), (54, 9797760), (55, -176359680), (63, 26127360), (66, -8164800), (89, 39191040), (91, -333123840), (92, -78382080), (110, 111041280), (111, -21228480), (112, 66951360), (113, 78382080), (120, -83280960), (124, 39191040), (126, -333123840), (131, 71850240), (136, 176359680), (137, -78382080), (140, -333123840), (144, 122472000), (147, 111041280), (148, 13063680)]

def pairMerged357 : Integer.Sparse (Fin 271) := [(0, -25898292), (1, 386058960), (2, -81545940), (3, -1022232960), (4, -829543680), (5, 36605520), (6, 544320), (7, -131725440), (8, -37013760), (12, -41368320), (13, 201761280), (14, -122472000), (15, 127370880), (16, -34292160), (17, 88179840), (20, -235146240), (23, 87091200), (24, 467026560), (25, 57153600), (26, -383201280), (27, -125193600), (28, -176359680), (29, 111041280), (30, 195955200), (32, -209018880), (34, -8709120), (35, 166561920), (37, -102876480), (38, 78382080), (39, 166561920), (41, 78382080), (42, -78382080), (43, -764225280), (46, -137168640), (47, 88179840), (49, -19595520), (50, 13063680), (51, -7620480), (53, -218816640), (54, 269438400), (55, -176359680), (62, -27216000), (63, 26127360), (66, 5851440), (85, 587865600), (89, 39191040), (91, -333123840), (92, -78382080), (110, -280869120), (111, -134991360), (112, 39191040), (113, 130636800), (116, -81648000), (124, -39191040), (130, -112129920), (131, 71850240), (134, -78382080), (136, -58786560), (137, -78382080), (138, -470292480), (142, -195955200), (144, -122472000), (146, -26127360), (147, -84913920), (148, 13063680), (150, -352719360)]

def pairMerged358 : Integer.Sparse (Fin 271) := [(0, -48441078), (1, 1929533130), (2, -1913866920), (3, -15562380960), (4, -3132198720), (5, 1507910040), (6, -68618340), (7, -2932070400), (8, -2670887520), (10, 1244315520), (12, -5308934400), (13, -5259643200), (15, 186157440), (16, -34292160), (17, 88179840), (20, -235146240), (23, 384562080), (24, 1146065760), (25, 10342080), (26, -2813771520), (27, -288897840), (28, -176359680), (29, 575346240), (30, -187246080), (32, 3642589440), (34, -1505831040), (35, -421303680), (36, -2611103040), (37, 226981440), (38, -3896242560), (39, -2772766080), (40, -1536615360), (41, -2135911680), (42, 506217600), (43, -1871372160), (45, 2276346240), (46, 266988960), (47, -558472320), (49, -19595520), (50, 939224160), (51, -1264999680), (53, 1380395520), (54, 2320436160), (55, 192689280), (58, 1464220800), (62, -229703040), (63, 26127360), (66, -43182720), (71, -952015680), (72, -1244315520), (73, -1244315520), (79, 1061424000), (81, -553573440), (82, 329857920), (83, -1554577920), (84, -1107146880), (87, 584599680), (88, -1347192000), (91, -3066698880), (92, -3066698880), (94, -1244315520), (96, 584599680), (97, -808315200), (98, 808315200), (110, -280869120), (111, 115395840), (112, 39191040), (113, 124104960), (130, -44271360), (131, 71850240), (133, 317338560), (134, -78382080), (137, -78382080), (138, -470292480), (142, -195955200), (143, 777288960), (146, 622702080), (147, -246576960), (148, -246576960), (150, -352719360)]

def pairMerged359 : Integer.Sparse (Fin 271) := [(0, -83704887), (1, 3249660330), (2, -126173565), (3, -26471007360), (4, -8123068800), (5, 1928518200), (6, -312700500), (7, -2178731520), (8, -970341120), (10, 1464220800), (11, -41096160), (12, -8752393440), (13, -12065261040), (15, 186157440), (16, -34292160), (17, 88179840), (20, -235146240), (23, -3320624160), (24, -6983081280), (25, 3825072720), (26, -4907226240), (27, 3528146160), (28, -176359680), (29, -5576558400), (30, 5441022720), (31, 282078720), (32, 11238575040), (33, -213373440), (34, -5157462240), (35, -1354540320), (36, -2611103040), (37, -668697120), (38, -3896242560), (39, -4017081600), (40, 37558080), (41, -2135911680), (42, -886697280), (43, -4887449280), (44, 1616630400), (45, 2276346240), (46, -2146525920), (47, -1765229760), (49, -2947084560), (50, -3858140160), (51, -1334128320), (53, 550035360), (54, 4844175840), (55, 1217099520), (62, -8709120), (66, -43182720), (80, -682940160), (111, 115395840), (112, 39191040), (113, 124104960), (115, -259822080), (130, -44271360), (131, 71850240), (132, 97433280), (133, 389733120), (134, -78382080), (137, -78382080), (138, -470292480), (142, -195955200), (143, 123288480), (146, 622702080), (150, -352719360)]

def pairMerged360 : Integer.Sparse (Fin 271) := [(0, -8727264), (1, -35199360), (2, -9253440), (3, 17418240), (4, 26127360), (5, 4536000), (6, 272160), (7, -8709120), (8, -39191040), (12, -4354560), (13, -5806080), (17, -19595520), (20, -78382080), (23, -13063680), (24, 39191040), (27, -13608000), (28, -78382080), (29, 137168640), (30, -26127360), (34, -5806080), (62, -8709120), (66, -3265920), (113, 52254720), (134, -78382080), (137, -78382080), (138, -470292480), (146, 78382080), (150, -352719360)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

structure Term where
  arity : ℕ
  charges : Matrix Coord (Fin arity) ℤ
  coefficient : ℤ
  deriving Inhabited

noncomputable def weightedAverage (H : CMatrix) (t : Term) : ℝ :=
  (t.coefficient : ℝ) * pairAverage H (fun K => (∏ j, g K (fun i => t.charges i j)).re)

def term0 : Term := ⟨2, ![![-3, 3], ![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![2, -2]], 3⟩

def term1 : Term := ⟨3, ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]], -6⟩

def term2 : Term := ⟨3, ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]], -3⟩

def term3 : Term := ⟨3, ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]], -3⟩

def term4 : Term := ⟨3, ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]], -3⟩

def term5 : Term := ⟨3, ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]], -6⟩

def term6 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 12⟩

def term7 : Term := ⟨4, ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 6⟩

def term8 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]], 6⟩

def term9 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]], 6⟩

def term10 : Term := ⟨3, ![![-2, -1, 3], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]], -3⟩

def term11 : Term := ⟨4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 6⟩

def term12 : Term := ⟨4, ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]], 3⟩

def term13 : Term := ⟨4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]], 3⟩

def term14 : Term := ⟨4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]], 3⟩

def term15 : Term := ⟨3, ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]], -3⟩

def term16 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]], 6⟩

def term17 : Term := ⟨4, ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]], 3⟩

def term18 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]], 3⟩

def term19 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]], 3⟩

def term20 : Term := ⟨3, ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]], -3⟩

def term21 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]], 6⟩

def term22 : Term := ⟨4, ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]], 3⟩

def term23 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]], 3⟩

def term24 : Term := ⟨4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]], 3⟩

def term25 : Term := ⟨4, ![![1, 2, -1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, -2, 1, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]], 1⟩

def term26 : Term := ⟨4, ![![1, 2, -1, -2], ![1, -2, -1, 2], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0]], 1⟩

def terms0 (i : Fin 26) : Term :=
  (#[term0, term1, term2, term3, term4, term5, term6, term7, term8, term9, term10, term11, term12, term13, term14, term15, term16, term17, term18, term19, term20, term21, term22, term23, term24, term25])[i.val]!

noncomputable def expanded0 (H : CMatrix) : ℝ := ∑ i : Fin 26, weightedAverage H (terms0 i)

def terms1 (i : Fin 26) : Term :=
  (#[term0, term1, term2, term3, term4, term5, term6, term7, term8, term9, term10, term11, term12, term13, term14, term15, term16, term17, term18, term19, term20, term21, term22, term23, term24, term26])[i.val]!

noncomputable def expanded1 (H : CMatrix) : ℝ := ∑ i : Fin 26, weightedAverage H (terms1 i)

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Terms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

def termPolynomial (H : CMatrix) (t : Term) : ℂ :=
  (t.coefficient : ℂ) * ∏ j, g H (fun i => t.charges i j)

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

def termGrid : Fin 5 → Fin 5 → Term :=
  ![![term0, term1, term2, term3, term4], ![term5, term6, term7, term8, term9], ![term10, term11, term12, term13, term14], ![term15, term16, term17, term18, term19], ![term20, term21, term22, term23, term24]]

def pairSummand (H : CMatrix) : Fin 5 → ℂ :=
  ![-g H pairW, 2 * g H (pairA 0) * g H (pairW - pairA 0),
    g H (pairA 1) * g H (pairW - pairA 1),
    g H (pairA 2) * g H (pairW - pairA 2),
    g H (pairA 3) * g H (pairW - pairA 3)]

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow0 : Integer.Sparse (Fin 909) := [(0, 9), (1, 170), (2, -25), (3, -80), (4, -160), (12, -40)]

def boundaryRow1 : Integer.Sparse (Fin 909) := [(0, -1), (1, -4), (5, -8), (6, 1), (27, 12)]

def boundaryRow2 : Integer.Sparse (Fin 909) := [(0, -1), (1, 18), (2, -8), (3, -64), (4, -32), (5, 3), (7, -16), (8, -8), (12, -24), (23, 12), (24, 24)]

def boundaryRow3 : Integer.Sparse (Fin 909) := [(0, -9), (1, 205), (2, -110), (3, -160), (4, -160), (5, 30), (7, -40), (8, -200), (24, 120), (30, 240)]

def boundaryRow4 : Integer.Sparse (Fin 909) := [(0, -4), (1, 95), (2, -25), (3, -320), (4, -160), (12, -160), (13, -80)]

def boundaryRow5 : Integer.Sparse (Fin 909) := [(0, -11), (1, 250), (2, -45), (3, -800), (4, -480), (12, -320), (25, 120), (26, -160)]

def boundaryRow6 : Integer.Sparse (Fin 909) := [(0, -9), (1, 315), (2, -70), (3, -480), (4, -400), (12, -80), (26, -80), (31, 240)]

def boundaryRow7 : Integer.Sparse (Fin 909) := [(0, 1), (1, -8), (2, 4), (14, 18), (17, 72), (23, -48), (25, -96), (27, 9), (30, -24), (31, -96)]

def boundaryRow8 : Integer.Sparse (Fin 909) := [(0, 149), (1, -1760), (2, 285), (3, 2080), (4, 2880), (12, 800), (15, 720), (20, 1440), (23, -240), (24, -720), (25, -480), (27, 180), (30, -480), (31, -960)]

def boundaryRow9 : Integer.Sparse (Fin 909) := [(0, -11), (1, -150), (2, 80), (3, 640), (4, 320), (12, 240), (16, 180), (17, 360), (23, -240), (27, 45), (30, -120)]

def boundaryRow10 : Integer.Sparse (Fin 909) := [(0, 11), (1, -890), (2, 45), (3, 1120), (4, 1080), (12, 440), (18, 360), (22, 720)]

def boundaryRow11 : Integer.Sparse (Fin 909) := [(0, 12), (1, -121), (2, 33), (3, 320), (4, 224), (12, 192), (15, 144), (17, 72), (23, -72), (24, -48), (25, -144), (27, 18), (30, -24), (31, -144)]

def boundaryRow12 : Integer.Sparse (Fin 909) := [(0, 3), (1, -65), (2, 11), (3, 80), (4, 80), (12, 20), (17, 36), (19, 36), (20, 36), (22, 36), (24, -60), (27, 9), (30, -12), (31, -48)]

def boundaryRow13 : Integer.Sparse (Fin 909) := [(0, 93), (1, -1715), (2, 210), (3, 2880), (4, 2400), (12, 1520), (21, 720), (22, 720), (31, -480)]

def boundaryRow14 : Integer.Sparse (Fin 909) := [(0, 16), (1, -315), (2, 65), (3, 960), (4, 600), (12, 360), (18, 360), (25, -240), (31, -240)]

def boundaryRow16 : Integer.Sparse (Fin 909) := [(0, -69), (1, -470), (2, 110), (3, 160), (4, 160), (12, 160), (17, 180), (23, -60), (27, 45), (28, 360), (30, -300)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow17 : Integer.Sparse (Fin 909) := [(0, -11), (1, 220), (2, -250), (3, -1200), (4, -240), (5, 260), (6, -15), (7, -480), (8, -480), (12, -480), (13, -320), (35, -160), (51, 720), (52, -240)]

def boundaryRow18 : Integer.Sparse (Fin 909) := [(0, -32), (1, 615), (2, -60), (3, -2160), (4, -960), (5, 60), (6, -15), (12, -240), (13, -160), (26, -960), (35, -240), (55, 720)]

def boundaryRow19 : Integer.Sparse (Fin 909) := [(0, -7), (1, 125), (2, -70), (3, -480), (4, -160), (5, 160), (6, -20), (7, -80), (8, -160), (26, -160), (35, -80), (52, -160)]

def boundaryRow20 : Integer.Sparse (Fin 909) := [(0, -2), (1, 55), (2, -11), (3, -304), (4, -64), (5, 52), (6, -8), (7, -16), (8, -32), (12, -64), (13, -208), (26, -64), (35, -80), (52, -64), (54, 48), (56, 96)]

def boundaryRow21 : Integer.Sparse (Fin 909) := [(0, -11), (1, 215), (2, -95), (3, -720), (4, -240), (5, 160), (6, -15), (7, -240), (8, -240), (26, -240), (35, -80)]

def boundaryRow22 : Integer.Sparse (Fin 909) := [(0, 1), (1, 5), (3, -400), (5, 10), (7, -160), (12, -240), (13, -240), (23, 360), (25, 360), (35, -80), (54, 240)]

def boundaryRow23 : Integer.Sparse (Fin 909) := [(0, -7), (1, 180), (2, -15), (3, -720), (12, -360), (13, -960), (32, -80)]

def boundaryRow24 : Integer.Sparse (Fin 909) := [(0, -7), (1, 145), (2, -30), (3, -680), (4, -240), (12, -120), (13, -160), (26, -280), (33, 120), (34, -80)]

def boundaryRow25 : Integer.Sparse (Fin 909) := [(0, -19), (1, 300), (2, -75), (3, -640), (4, -480), (12, -200), (25, 240), (26, -80), (31, 480), (33, 240)]

def boundaryRow26 : Integer.Sparse (Fin 909) := [(0, 157), (1, -2040), (2, 585), (3, 5280), (4, 3520), (12, 2240), (13, 560), (25, -1200), (31, -2880), (33, -960), (50, 720)]

def boundaryRow27 : Integer.Sparse (Fin 909) := [(0, 59), (1, -575), (2, 320), (3, 1040), (4, 480), (5, -80), (7, 80), (8, 320), (12, 480), (23, -240), (25, -240), (27, 180), (30, -480), (31, -480), (33, -480), (45, 1440), (51, -480), (54, -240)]

def boundaryRow28 : Integer.Sparse (Fin 909) := [(0, 29), (1, -334), (2, 99), (3, 896), (4, 512), (12, 352), (13, 32), (25, -96), (26, 112), (31, -336), (33, -192), (43, 144), (45, 288)]

def boundaryRow29 : Integer.Sparse (Fin 909) := [(0, 128), (1, -1575), (2, 405), (3, 4480), (4, 2960), (12, 1360), (25, -960), (26, 960), (31, -1680), (43, 720), (44, 720), (45, 720), (46, 720)]

def boundaryRow30 : Integer.Sparse (Fin 909) := [(0, 58), (1, -605), (2, 235), (3, 1280), (4, 920), (5, -30), (7, 40), (8, 80), (12, 560), (23, -240), (24, -720), (25, -600), (27, 300), (30, -480), (31, -1200), (33, -480), (48, 360), (49, 720), (51, -360), (55, -240)]

def boundaryRow31 : Integer.Sparse (Fin 909) := [(0, 141), (1, -1765), (2, 580), (3, 3600), (4, 2560), (5, -60), (7, 80), (8, 160), (12, 1440), (13, 320), (23, -480), (24, -1440), (27, 600), (30, -960), (31, -1920), (47, 720), (49, 1440), (51, -720), (55, -480)]

def boundaryRow32 : Integer.Sparse (Fin 909) := [(0, 109), (1, -1300), (2, 565), (3, 2880), (4, 1760), (5, -120), (7, 160), (8, 320), (12, 800), (23, -480), (24, -1440), (26, 400), (27, 600), (30, -960), (31, -1200), (43, 720), (55, -480)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow269 : Integer.Sparse (Fin 909) := [(0, 6), (1, -65), (2, -125), (3, -1360), (4, -160), (5, 420), (6, -70), (7, -320), (8, -160), (9, 60), (13, -960), (26, -640), (34, -400), (35, -1200), (52, -1040), (56, 480), (60, -400), (64, 240), (67, -160), (69, -240), (70, -160), (71, -160), (125, 480), (126, 240), (128, -320), (197, 240), (257, -160), (260, 240), (262, 480), (268, 480), (495, -240)]

def boundaryRow270 : Integer.Sparse (Fin 909) := [(0, 9), (1, -45), (2, -85), (3, -800), (4, -80), (5, 460), (6, -85), (7, -640), (8, -480), (9, 100), (26, -400), (35, -560), (51, 240), (52, -400), (69, -320), (70, -80), (71, -480), (123, 480), (124, 480), (126, 240), (197, 240), (236, 480), (259, 240), (495, -80)]

def boundaryRow271 : Integer.Sparse (Fin 909) := [(0, 1), (1, -3), (2, -12), (3, -112), (5, 16), (6, -2), (12, -32), (13, -144), (26, -16), (33, 48), (34, -32), (35, -32), (52, -96), (55, 96), (59, 96), (60, -16), (61, 48), (64, 96), (69, -32), (71, -16), (125, 96), (128, -32), (197, 48), (256, 48), (260, 48), (263, -96), (495, -16)]

def boundaryRow273 : Integer.Sparse (Fin 909) := [(0, 7), (1, 95), (2, -25), (3, -1920), (4, -560), (5, 180), (6, -15), (7, -720), (8, -160), (12, -160), (13, -80), (23, 240), (25, 480), (26, -1120), (33, 240), (34, -240), (35, -960), (51, 240), (52, -240), (54, 240), (55, 240), (64, 480), (67, -320), (69, -80), (70, -80), (81, 480), (123, 480), (124, 240), (125, 240), (256, 240), (257, -80), (259, 240), (266, 240), (487, -480), (495, -80)]

def boundaryRow275 : Integer.Sparse (Fin 909) := [(0, 8), (1, 35), (2, -340), (3, -3120), (4, -800), (5, 680), (6, -55), (7, -1920), (8, -800), (10, 240), (11, -160), (12, -80), (13, -160), (26, -1760), (33, 480), (34, -320), (35, -2640), (52, -800), (55, 240), (67, -800), (81, 1920), (82, -80), (228, 480), (273, 480), (276, -160), (306, 480), (307, 480)]

def boundaryRow276 : Integer.Sparse (Fin 909) := [(0, 1), (1, -12), (2, -27), (3, -224), (4, -16), (5, 52), (6, -8), (7, -16), (8, -16), (11, -16), (12, -88), (13, -304), (26, -32), (33, 96), (34, -32), (35, -144), (52, -176), (54, 48), (59, 240), (60, -64), (82, -32), (128, -96), (199, 24), (201, 48), (228, 48), (271, 48), (276, -16), (490, 96), (721, 96)]

def boundaryRow277 : Integer.Sparse (Fin 909) := [(0, 6), (1, 65), (2, -180), (3, -2880), (4, -720), (5, 440), (6, -35), (7, -1680), (8, -480), (11, -240), (13, -240), (26, -1920), (34, -480), (35, -2800), (52, -720), (60, -160), (67, -960), (81, 1440), (228, 720), (273, 720), (276, -240)]

def boundaryRow278 : Integer.Sparse (Fin 909) := [(0, 1), (1, 6), (2, -39), (3, -576), (4, -160), (5, 108), (6, -14), (7, -192), (8, -64), (11, -128), (12, -32), (13, -112), (26, -352), (33, 96), (34, -64), (35, -544), (52, -256), (54, 48), (56, 96), (59, 96), (60, -64), (67, -64), (81, 192), (128, -16), (228, 480), (271, 48), (275, 96), (276, -48), (490, 192), (721, 96)]

def boundaryRow285 : Integer.Sparse (Fin 909) := [(0, 7), (1, 105), (2, -120), (3, -1920), (4, -240), (12, -960), (13, -2000), (26, -240), (32, -80), (33, 1440), (34, -480), (51, 720), (52, -240), (60, -240), (61, 720), (127, 720), (128, -240), (489, 1440)]

def boundaryRow286 : Integer.Sparse (Fin 909) := [(0, 14), (1, -65), (2, -80), (3, -1200), (5, 340), (6, -65), (12, -160), (13, -1280), (26, -240), (33, 240), (34, -160), (35, -560), (52, -1120), (60, -160), (82, -80), (123, 480), (128, -320), (237, 480), (306, 240), (489, 480)]

def boundaryRow287 : Integer.Sparse (Fin 909) := [(0, 7), (1, -10), (2, -25), (3, -480), (5, 200), (6, -30), (11, -40), (12, -40), (13, -480), (26, -200), (33, 120), (35, -440), (52, -440), (55, 120), (63, 240), (82, -40), (123, 240), (128, -40), (237, 240), (306, 120), (721, 120)]

def boundaryRow297 : Integer.Sparse (Fin 909) := [(0, -5), (1, 131), (2, 228), (3, 224), (5, -556), (6, 42), (7, 656), (8, 928), (9, -120), (35, 224), (52, 192), (69, 848), (70, 272), (71, 1664), (256, -576), (277, -144), (279, 144), (280, 576), (281, 576), (726, -144), (818, -288)]

def boundaryRow298 : Integer.Sparse (Fin 909) := [(0, -23), (1, -195), (2, 220), (3, 3200), (5, -420), (6, 30), (7, 1520), (8, 640), (9, -40), (10, -240), (12, 560), (13, 160), (23, -1920), (24, -960), (26, 320), (27, 420), (35, 800), (51, -1440), (54, -1680), (55, -1440), (69, 400), (70, 240), (71, 160), (77, 2880), (79, 720), (228, -960), (277, -240), (290, 1440), (291, 2160)]

def boundaryRow300 : Integer.Sparse (Fin 909) := [(0, -19), (1, -115), (2, 430), (3, 3200), (5, -740), (6, 20), (7, 2800), (8, 1280), (9, -40), (10, -720), (12, 720), (13, 960), (23, -240), (24, -480), (27, 180), (35, 2240), (51, -1920), (52, 640), (54, -960), (59, -1920), (69, 720), (70, 400), (71, 320), (72, 720), (73, 1440), (74, 1440), (199, -720), (256, -960), (277, -240), (279, 720), (280, 1440), (726, -720)]

def boundaryRow301 : Integer.Sparse (Fin 909) := [(0, -3), (1, 41), (2, 126), (3, 176), (4, 48), (5, -208), (6, 16), (7, 304), (8, 352), (9, -32), (10, -96), (12, 32), (13, 16), (24, -96), (26, 32), (27, 24), (30, -48), (35, 80), (51, -144), (52, 48), (54, -48), (55, -48), (56, -192), (59, -96), (69, 144), (70, 16), (71, 480), (74, 288), (75, 144), (78, 288), (201, -96), (228, -96), (256, -96), (277, -48), (280, 144), (282, 144), (288, 288), (289, 288), (726, -48), (818, -48)]

def boundaryRow302 : Integer.Sparse (Fin 909) := [(0, -5), (1, 101), (2, 210), (3, 336), (4, 16), (5, -360), (6, 26), (7, 352), (8, 576), (9, -24), (35, 144), (51, -144), (52, 288), (69, 208), (70, 80), (71, 320), (81, -192), (86, 288), (256, -96), (281, 288), (322, 144), (325, 288), (327, 288), (818, -144)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow303 : Integer.Sparse (Fin 909) := [(0, -13), (1, -30), (2, 155), (3, 2000), (5, -580), (6, 70), (7, 1840), (8, 960), (9, -160), (10, -480), (12, 160), (13, 80), (23, -720), (24, -240), (26, 160), (27, 120), (35, 1520), (51, -480), (52, 160), (54, -1200), (55, -240), (59, -480), (69, 1600), (70, 960), (71, 640), (72, 1440), (73, 720), (77, 1440), (199, -480), (228, -480), (256, -480), (277, -240), (279, 720), (282, 720), (286, 1440), (287, 1440), (726, -480)]

def boundaryRow304 : Integer.Sparse (Fin 909) := [(0, -11), (1, 10), (2, 605), (3, 3120), (4, 400), (5, -900), (6, 70), (7, 2400), (8, 720), (9, -80), (12, 160), (13, 320), (24, -240), (26, 480), (35, 2320), (51, -480), (52, 1920), (69, 640), (70, 320), (71, 640), (73, 1440), (81, -960), (84, 720), (85, 1440), (201, -480), (228, -720), (256, -1440), (277, -720), (279, 720), (280, 1440), (322, 2160), (327, 1440), (726, -240), (818, -720)]

def boundaryRow305 : Integer.Sparse (Fin 909) := [(0, -28), (1, 415), (2, 840), (3, 1760), (4, 400), (5, -1660), (6, 105), (7, 1920), (8, 2880), (9, -120), (13, 320), (26, 160), (35, 800), (51, -1680), (52, 640), (56, -1440), (59, -1200), (69, 1040), (70, 400), (71, 1600), (76, 2880), (77, 720), (201, -960), (228, -240), (256, -480), (281, 1440), (286, 1440), (287, 720), (288, 1440), (726, -240), (818, -480)]

def boundaryRow306 : Integer.Sparse (Fin 909) := [(0, -27), (1, 555), (2, 1085), (3, 1600), (4, 80), (5, -2280), (6, 225), (7, 2320), (8, 3040), (9, -160), (26, 160), (35, 880), (51, -720), (52, 1280), (69, 720), (70, 80), (71, 2400), (85, 1440), (228, -480), (256, -480), (277, -240), (280, 720), (322, 720), (325, 1440), (327, 1440), (818, -480)]

def boundaryRow307 : Integer.Sparse (Fin 909) := [(0, -9), (1, 20), (2, 95), (3, 800), (5, -180), (6, 20), (7, 480), (9, -40), (12, 160), (13, 160), (23, -240), (31, -480), (33, -480), (35, 320), (52, 320), (69, 160), (70, 160), (81, -960), (95, 1440), (124, -240), (196, -240), (256, -480), (322, 1440), (379, 1440), (818, -480)]

def boundaryRow308 : Integer.Sparse (Fin 909) := [(0, -4), (1, 15), (2, 20), (3, 2400), (4, 640), (5, -380), (6, 45), (7, 2560), (8, 480), (9, -40), (12, 320), (13, 160), (23, -480), (24, -480), (25, -1200), (26, 1120), (35, 1440), (52, 320), (54, -1200), (69, 240), (70, 80), (71, 160), (97, 2880), (113, 720), (124, -480), (197, -480), (228, -960), (256, -480), (277, -240), (291, 720), (378, 1440)]

def boundaryRow311 : Integer.Sparse (Fin 909) := [(0, -3), (1, -76), (2, 172), (3, 1232), (4, 224), (5, -136), (6, 11), (7, 352), (8, 224), (9, -8), (12, 256), (13, 160), (23, -144), (24, -96), (26, 256), (33, -768), (35, 208), (52, 224), (54, -240), (55, -48), (69, 48), (70, 16), (71, 32), (81, -576), (100, 576), (104, 288), (125, -96), (126, -96), (228, -192), (256, -96), (277, -48), (291, 144), (379, 288)]

def boundaryRow312 : Integer.Sparse (Fin 909) := [(0, -19), (1, -5), (2, 440), (3, 3680), (4, 160), (5, -1260), (6, 220), (7, 1760), (8, 320), (9, -160), (12, 400), (13, 2080), (23, -240), (26, 480), (35, 2720), (51, -480), (52, 3520), (54, -1200), (69, 560), (70, 400), (71, 160), (103, 2880), (125, -960), (126, -480), (228, -960), (256, -480), (277, -240), (291, 720), (322, 1440), (378, 1440), (818, -480)]

def boundaryRow313 : Integer.Sparse (Fin 909) := [(0, -33), (1, 100), (2, 985), (3, 5680), (5, -1360), (6, 170), (7, 1680), (8, 960), (9, -120), (12, 1840), (13, 4720), (23, -720), (35, 2800), (51, -480), (52, 3520), (54, -240), (59, -1200), (69, 560), (70, 400), (71, 160), (98, 1440), (102, 2880), (125, -1440), (126, -480), (201, -960), (256, -480), (287, 720), (327, 1440), (352, 1440), (726, -240), (818, -480)]

def boundaryRow314 : Integer.Sparse (Fin 909) := [(0, -19), (1, 50), (2, 170), (3, 2400), (5, -360), (6, 35), (7, 1760), (8, 800), (9, -40), (10, -480), (12, 960), (13, 880), (23, -240), (26, 320), (27, 360), (35, 720), (51, -1200), (52, 160), (55, -1200), (59, -480), (69, 240), (71, 240), (105, 1440), (124, -480), (228, -480), (236, -480), (256, -480), (277, -240), (290, 720), (352, 1440)]

def boundaryRow315 : Integer.Sparse (Fin 909) := [(0, -3), (1, 14), (2, 7), (3, 368), (5, -36), (6, 16), (7, 448), (8, 96), (9, -40), (10, -48), (12, 80), (13, 64), (23, -144), (26, 96), (27, 36), (35, 208), (51, -48), (54, -48), (55, -240), (69, 160), (70, 64), (71, 96), (87, 288), (124, -240), (196, -96), (197, -48), (228, -288), (236, -96), (277, -48), (282, 144), (290, 144), (726, -48)]

def boundaryRow332 : Integer.Sparse (Fin 909) := [(0, 1), (1, -320), (2, 200), (3, 2000), (4, 560), (5, -220), (6, 15), (7, 960), (9, -20), (12, 720), (13, 160), (23, -2160), (24, -2400), (25, -720), (27, 600), (35, 320), (48, 2160), (51, -720), (55, -1440), (63, -480), (68, 240), (69, 240), (70, 160), (124, -1440), (126, -1440), (196, -480), (197, -1440), (308, -240), (643, 1440), (751, 2160)]

def boundaryRow337 : Integer.Sparse (Fin 909) := [(0, 54), (1, -660), (2, 935), (3, 4320), (4, 2000), (5, -940), (6, 45), (7, 1920), (8, 1920), (12, 240), (13, 160), (26, 1200), (31, -3600), (35, 800), (43, 2160), (51, -3600), (56, -1440), (77, 2160), (97, 4320), (107, 4320), (228, -240), (238, -2400), (737, 1440)]

def boundaryRow338 : Integer.Sparse (Fin 909) := [(0, -3), (1, -190), (2, 385), (3, 2880), (4, 720), (5, -560), (6, 30), (7, 1440), (8, 960), (10, -1080), (11, 240), (12, 520), (13, 720), (26, 960), (35, 1120), (38, 1080), (40, 2160), (52, 240), (55, -1080), (59, -720), (72, 1080), (75, 2160), (199, -120), (228, -720), (321, 2160), (505, 720), (508, 4320), (727, -480)]

def boundaryRow339 : Integer.Sparse (Fin 909) := [(0, 9), (1, -315), (2, 170), (3, 2880), (4, 960), (5, -680), (6, 120), (7, 960), (9, -20), (11, 480), (12, 240), (26, 960), (33, -2880), (35, 2080), (36, 2160), (40, 4320), (52, 1440), (54, -720), (55, -2160), (69, 240), (70, 160), (228, -1440), (306, -2160), (312, 4320), (498, 2160), (721, -1440), (723, -240), (728, -960), (760, 4320), (783, 1440), (794, 8640)]

def boundaryRow340 : Integer.Sparse (Fin 909) := [(0, -29), (1, -490), (2, 485), (3, 3920), (5, -340), (7, 1840), (8, 160), (10, -240), (12, 1200), (13, 320), (23, -3360), (24, -2400), (25, -480), (26, 160), (27, 1020), (33, -480), (35, 160), (51, -2880), (54, -1200), (55, -2400), (65, -480), (79, 720), (94, 720), (122, 2880), (127, -240), (299, 1440), (300, 1440)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow343 : Integer.Sparse (Fin 909) := [(0, -12), (1, -405), (2, 300), (3, 3440), (4, 640), (5, -260), (6, 5), (7, 1200), (8, 80), (9, -20), (10, -480), (12, 1040), (13, 320), (23, -3600), (24, -3120), (26, 160), (27, 780), (35, 320), (47, 1440), (51, -480), (52, 160), (55, -3360), (68, 180), (69, 240), (70, 160), (79, 1440), (113, 720), (124, -240), (125, -2160), (126, -1440), (197, -480), (291, 720), (308, -240), (538, 1440), (640, 1440), (727, -240), (751, 720)]

def boundaryRow345 : Integer.Sparse (Fin 909) := [(0, 29), (1, -515), (2, 480), (3, 1280), (4, 800), (5, -420), (6, 30), (7, 240), (8, 800), (9, -20), (12, 320), (23, -480), (24, -2880), (27, 1140), (30, -1680), (31, -960), (33, -960), (49, 1440), (51, -720), (52, 80), (55, -1920), (68, 180), (69, 80), (71, 320), (105, 720), (106, 1440), (124, -240), (126, -1680), (197, -960), (236, -1440), (237, -720), (290, 720), (299, 1440), (306, -480), (308, -240), (728, -240), (751, 720), (811, 1440), (812, 1440)]

def boundaryRow346 : Integer.Sparse (Fin 909) := [(0, -1), (1, -80), (2, 555), (3, 2800), (4, 960), (5, -660), (6, 40), (7, 1040), (8, 1440), (9, -20), (26, 640), (31, -960), (35, 480), (46, 1440), (51, -3360), (52, 480), (56, -1680), (69, 240), (70, 160), (71, 320), (77, 1440), (97, 720), (107, 1440), (228, -480), (238, -720), (262, -960), (286, 720), (309, -720), (327, 1440), (735, 1440), (736, 1440), (796, -240)]

def boundaryRow347 : Integer.Sparse (Fin 909) := [(0, 9), (1, -110), (2, 515), (3, 1040), (4, 320), (5, -740), (6, 80), (7, 400), (8, 1600), (9, -20), (12, 400), (23, -240), (27, 300), (30, -480), (33, -960), (45, 2880), (51, -2880), (52, 160), (54, -1440), (69, 80), (71, 640), (259, -960), (282, 720), (293, 1440), (308, -720), (325, 1440), (721, -480), (723, -240), (738, 2880), (739, 2880)]

def boundaryRow349 : Integer.Sparse (Fin 909) := [(0, -13), (1, -630), (2, 660), (3, 4800), (4, 960), (5, -660), (6, 35), (7, 1840), (8, 720), (9, -20), (12, 1440), (13, 720), (23, -2160), (24, -1200), (25, -2400), (26, 320), (27, 480), (31, -1920), (33, -960), (35, 1040), (48, 1440), (51, -4080), (52, 640), (54, -3120), (55, -960), (56, -1200), (64, -2400), (68, 180), (69, 240), (70, 160), (97, 720), (100, 4320), (104, 1440), (124, -240), (125, -2160), (126, -1440), (197, -480), (238, -1680), (291, 720), (300, 1440), (307, -480), (309, -240), (538, 720), (543, 1440), (643, 1440), (727, -240)]

def boundaryRow350 : Integer.Sparse (Fin 909) := [(0, 18), (1, -520), (2, 425), (3, 2760), (4, 720), (5, -510), (6, 35), (7, 1040), (8, 960), (9, -10), (10, -240), (12, 520), (13, 480), (24, -960), (26, 560), (27, 270), (30, -480), (31, -480), (35, 680), (49, 720), (51, -1080), (52, 80), (55, -840), (68, 90), (69, 40), (71, 160), (82, 80), (95, 720), (107, 1440), (124, -120), (126, -840), (197, -480), (236, -720), (238, -480), (290, 360), (309, -120), (538, 360), (728, -120), (810, 720), (811, 720)]

def boundaryRow351 : Integer.Sparse (Fin 909) := [(0, -2), (1, -195), (2, 360), (3, 2960), (4, 520), (5, -550), (6, 65), (7, 440), (8, 480), (9, -10), (11, 80), (12, 720), (13, 1680), (26, 480), (35, 1200), (45, 720), (51, -960), (52, 1360), (54, -480), (56, -480), (69, 120), (70, 80), (71, 160), (102, 1440), (103, 720), (228, -240), (262, -480), (286, 360), (309, -360), (327, 720), (739, 720), (796, -120), (870, 720)]

def boundaryRow353 : Integer.Sparse (Fin 909) := [(0, -8), (1, -345), (2, 605), (3, 5600), (4, 1280), (5, -1000), (6, 130), (7, 480), (8, 640), (11, 240), (12, 1280), (13, 2880), (26, 1440), (35, 2160), (43, 1440), (45, 1440), (51, -1200), (52, 2480), (54, -960), (55, -240), (56, -960), (77, 720), (102, 2880), (103, 2880), (228, -960), (546, 1440), (737, 1440), (739, 1440), (870, 1440)]

def boundaryRow354 : Integer.Sparse (Fin 909) := [(0, -29), (1, 370), (2, 835), (3, 4080), (5, -1460), (6, 210), (7, 1200), (8, 640), (9, -20), (10, -720), (12, 1280), (13, 3840), (33, -960), (35, 2560), (38, 1440), (52, 3040), (54, -960), (59, -960), (69, 240), (70, 160), (72, 720), (75, 1440), (82, 800), (128, 800), (199, -720), (201, -1920), (306, -720), (313, 2880), (498, 720), (505, 1440), (540, 1440), (721, -960), (723, -240), (760, 1440)]

def boundaryRow355 : Integer.Sparse (Fin 909) := [(0, -1), (1, -370), (2, 105), (3, 2400), (4, 720), (5, -40), (7, 480), (12, 1200), (13, 640), (23, -2160), (24, -2160), (25, -1440), (27, 300), (33, -1440), (35, 320), (55, -2880), (63, -960), (68, 60), (124, -720), (126, -720), (196, -480), (197, -1440), (290, 2160), (299, 2160), (306, -720), (728, -720)]

def boundaryRow356 : Integer.Sparse (Fin 909) := [(0, -2), (1, -69), (2, 24), (3, 432), (4, 48), (5, -36), (6, 3), (7, 192), (9, -4), (12, 240), (13, 64), (23, -432), (25, -144), (27, 84), (33, -288), (35, 96), (51, -432), (54, -576), (63, -96), (68, 24), (69, 48), (70, 32), (124, -288), (196, -192), (259, -288), (282, 432), (293, 432), (308, -144), (721, -144), (723, -144)]

def boundaryRow362 : Integer.Sparse (Fin 909) := [(1, -93), (2, 175), (3, 784), (4, 192), (5, -216), (6, 16), (7, 416), (8, 336), (9, -8), (12, 32), (13, 32), (24, -336), (26, 112), (27, 96), (30, -96), (31, -192), (35, 176), (46, 144), (51, -528), (52, 144), (55, -96), (56, -96), (68, 24), (69, 96), (70, 48), (71, 80), (95, 288), (106, 144), (107, 288), (126, -288), (197, -96), (236, -96), (237, -48), (238, -96), (262, -96), (308, -48), (309, -48), (322, 144), (327, 144), (735, 288), (736, 144), (738, 144)]

def boundaryRow363 : Integer.Sparse (Fin 909) := [(0, -7), (1, -580), (2, 570), (3, 6160), (4, 1440), (5, -460), (6, 25), (7, 1440), (8, 480), (10, -720), (12, 2000), (13, 2880), (25, -1440), (26, 1440), (31, -720), (33, -1440), (35, 2080), (38, 2160), (39, 4320), (51, -720), (52, 1520), (54, -2160), (55, -720), (59, -1440), (60, 320), (81, -1440), (82, 240), (84, 2160), (85, 4320), (128, 480), (228, -2160), (311, 2160), (321, 4320), (323, 1440), (329, 4320), (330, 4320), (490, -720), (492, -960)]

def boundaryRow364 : Integer.Sparse (Fin 909) := [(0, 21), (1, -705), (2, 350), (3, 6240), (4, 2720), (5, -580), (6, 30), (7, 1920), (8, 960), (10, -720), (11, 240), (12, 480), (13, 640), (26, 3120), (35, 2000), (37, 2160), (40, 4320), (52, 240), (55, -720), (56, -2160), (81, -1440), (82, 240), (83, 2160), (85, 4320), (228, -3120), (501, 4320), (508, 4320), (784, 1440), (794, 4320), (796, -960)]

def boundaryRow365 : Integer.Sparse (Fin 909) := [(1, -78), (2, 19), (3, 432), (4, 96), (5, -64), (6, 9), (7, 144), (9, -4), (11, 48), (12, 144), (23, -144), (25, -288), (26, 96), (27, 36), (31, -288), (33, -576), (35, 224), (36, 432), (39, 864), (51, -288), (52, 144), (54, -720), (55, -144), (68, 12), (69, 48), (70, 32), (87, 432), (123, -288), (124, -144), (196, -96), (226, -144), (228, -144), (237, -144), (259, -288), (282, 432), (306, -288), (308, -144), (312, 432), (315, 864), (498, 864), (507, 864), (721, -432), (723, -336), (728, -48), (764, 864), (783, 288)]

def boundaryRow368 : Integer.Sparse (Fin 909) := [(0, 1), (1, -98), (2, 113), (3, 1488), (4, 512), (5, -160), (6, 14), (7, 560), (8, 128), (11, 128), (26, 896), (35, 896), (52, 368), (53, 288), (67, 128), (81, -672), (83, 144), (84, 432), (85, 576), (228, -816), (460, 288), (702, 288), (709, 576)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow369 : Integer.Sparse (Fin 909) := [(0, -9), (1, -25), (2, 600), (3, 4480), (4, 1120), (5, -1400), (6, 190), (7, 2400), (8, 480), (9, -40), (11, 640), (24, -480), (26, 1920), (27, 120), (31, -480), (33, -960), (35, 3520), (37, 1440), (51, -480), (52, 2560), (55, -480), (68, 60), (69, 640), (70, 480), (81, -960), (83, 720), (85, 1440), (99, 1440), (123, -480), (124, -240), (126, -480), (197, -480), (228, -3360), (237, -480), (259, -480), (306, -960), (308, -480), (312, 720), (315, 1440), (322, 1440), (517, 2880), (541, 1440), (721, -720), (728, -240), (784, 1440)]

def boundaryRow372 : Integer.Sparse (Fin 909) := [(0, -2), (1, -63), (2, 107), (3, 1024), (4, 288), (5, -152), (6, 8), (7, 480), (8, 224), (10, -288), (11, 48), (12, 208), (13, 176), (25, -48), (26, 384), (33, -192), (35, 544), (37, 288), (39, 288), (40, 288), (52, 160), (54, -48), (55, -288), (56, -96), (59, -288), (67, 64), (73, 288), (74, 288), (75, 288), (81, -288), (84, 144), (85, 288), (201, -48), (228, -288), (307, -144), (321, 288), (330, 576), (425, 144), (428, 288), (501, 576), (503, 288), (507, 288), (508, 864), (727, -192)]

def boundaryRow373 : Integer.Sparse (Fin 909) := [(0, -11), (1, -15), (2, 415), (3, 4080), (4, 880), (5, -980), (6, 145), (7, 640), (8, 480), (11, 320), (12, 880), (13, 2320), (26, 1280), (33, -960), (35, 2320), (37, 1440), (39, 1440), (40, 1440), (52, 2080), (54, -720), (55, -1440), (56, -480), (81, -960), (82, 320), (83, 720), (85, 1440), (128, 320), (199, -240), (201, -480), (228, -1920), (306, -1440), (312, 1440), (329, 2880), (500, 1440), (517, 1440), (541, 2880), (721, -480), (728, -960), (760, 1440), (764, 1440), (784, 1440), (794, 4320)]

def boundaryRow374 : Integer.Sparse (Fin 909) := [(0, 7), (1, -142), (2, 152), (3, 544), (4, 256), (5, -128), (6, 7), (7, 192), (8, 224), (9, -4), (12, 48), (23, -336), (24, -960), (26, 32), (27, 324), (30, -384), (31, -288), (35, 48), (47, 144), (51, -144), (52, 64), (55, -528), (68, 48), (69, 32), (70, 16), (71, 32), (106, 576), (125, -192), (126, -480), (197, -96), (236, -192), (237, -192), (308, -48), (538, 288), (640, 144), (812, 288)]

def boundaryRow377 : Integer.Sparse (Fin 909) := [(0, -18), (1, 295), (2, 700), (3, 3040), (4, 160), (5, -1260), (6, 135), (7, 2240), (8, 720), (9, -60), (12, 320), (13, 1440), (23, -240), (26, 160), (27, 60), (35, 3200), (38, 720), (52, 2960), (54, -240), (55, -240), (59, -720), (60, 560), (68, 60), (69, 800), (70, 400), (81, -960), (82, 80), (84, 1440), (98, 720), (125, -720), (126, -480), (128, 400), (201, -240), (228, -480), (237, -240), (260, -480), (287, 720), (306, -480), (308, -240), (323, 1440), (392, 720), (492, -240), (499, 1440), (540, 720), (541, 1440), (728, -240)]

def boundaryRow378 : Integer.Sparse (Fin 909) := [(0, -24), (1, 360), (2, 715), (3, 4240), (4, 80), (5, -1360), (6, 175), (7, 1760), (8, 800), (10, -720), (11, 80), (12, 1280), (13, 4400), (26, 160), (33, -480), (35, 3920), (41, 720), (52, 3440), (54, -720), (59, -1920), (60, 640), (73, 720), (74, 720), (75, 720), (81, -480), (82, 960), (84, 720), (128, 1360), (199, -960), (201, -1680), (228, -480), (306, -720), (313, 1440), (324, 1440), (392, 720), (399, 720), (500, 720), (502, 1440), (517, 720), (545, 720), (721, -480), (760, 720)]

def boundaryRow379 : Integer.Sparse (Fin 909) := [(0, -31), (1, -330), (2, 410), (3, 6720), (4, 160), (5, -400), (6, 15), (7, 2320), (8, 320), (10, -2640), (12, 3120), (13, 5760), (23, -240), (26, 320), (27, 60), (33, -960), (34, 320), (35, 3680), (38, 1440), (51, -960), (52, 1760), (54, -960), (55, -480), (59, -3360), (60, 640), (72, 720), (73, 720), (74, 1440), (75, 1440), (82, 640), (84, 1440), (128, 640), (199, -720), (201, -720), (228, -480), (273, -480), (311, 2880), (313, 2880), (318, 1440)]

def boundaryRow381 : Integer.Sparse (Fin 909) := [(0, -6), (1, -205), (2, 175), (3, 2560), (4, 720), (5, -220), (6, 20), (7, 400), (8, 240), (10, -120), (12, 760), (13, 720), (23, -120), (25, -240), (26, 800), (27, 30), (31, -240), (33, -1440), (34, 160), (35, 560), (36, 720), (39, 1440), (51, -480), (52, 240), (54, -1200), (55, -960), (59, -480), (72, 360), (74, 720), (81, -960), (83, 720), (85, 1440), (199, -360), (228, -960), (273, -240), (311, 720), (312, 1440), (314, 1440), (316, 720), (321, 720), (329, 1440), (330, 2880), (490, -720), (492, -480)]

def boundaryRow382 : Integer.Sparse (Fin 909) := [(0, 9), (1, -570), (2, 380), (3, 6240), (4, 2400), (5, -400), (6, 45), (7, 1360), (8, 160), (11, 480), (12, 480), (13, 640), (26, 3040), (35, 3040), (37, 1440), (40, 2880), (52, 1280), (55, -1440), (56, -1440), (67, 160), (73, 720), (75, 1440), (81, -1440), (84, 1440), (85, 2880), (201, -720), (228, -2880), (501, 1440), (503, 1440), (508, 5760), (541, 2880), (794, 2880), (796, -960)]

def boundaryRow383 : Integer.Sparse (Fin 909) := [(0, -12), (1, -195), (2, 375), (3, 3920), (4, 800), (5, -900), (6, 130), (7, 880), (8, 480), (10, -240), (11, 480), (12, 1120), (13, 1680), (23, -240), (25, -1920), (26, 1280), (27, 60), (31, -960), (33, -960), (35, 2480), (38, 1440), (39, 2880), (51, -1440), (52, 1920), (54, -3120), (56, -480), (59, -960), (72, 720), (74, 1440), (82, 320), (87, 1440), (89, 2880), (123, -1920), (128, 320), (199, -960), (201, -480), (226, -1440), (228, -1440), (237, -480), (306, -480), (313, 1440), (315, 2880), (498, 1440), (505, 1440), (507, 5760), (540, 2880), (721, -1440), (723, -960), (764, 2880)]

def boundaryRow384 : Integer.Sparse (Fin 909) := [(0, -13), (1, -150), (2, 375), (3, 3840), (4, 800), (5, -700), (6, 30), (7, 2960), (8, 960), (10, -240), (12, 160), (13, 80), (23, -240), (24, -480), (25, -480), (26, 1760), (27, 60), (35, 3680), (38, 720), (51, -480), (52, 1120), (54, -720), (55, -480), (59, -480), (64, -960), (67, 800), (72, 720), (73, 1440), (81, -1920), (84, 1440), (104, 1440), (199, -240), (228, -480), (271, -480), (318, 1440), (425, 1440), (499, 1440)]

def boundaryRow385 : Integer.Sparse (Fin 909) := [(0, -9), (1, -280), (2, 565), (3, 7040), (4, 2160), (5, -860), (6, 70), (7, 3120), (8, 800), (11, 640), (12, 80), (13, 160), (26, 3920), (33, -480), (34, 320), (35, 4800), (37, 720), (52, 1920), (56, -240), (67, 640), (73, 720), (81, -2880), (83, 720), (84, 1440), (85, 2880), (201, -240), (228, -4320), (275, -480), (317, 1440), (428, 1440), (460, 1440), (517, 1440), (709, 1440)]

def boundaryRow386 : Integer.Sparse (Fin 909) := [(0, -12), (1, -20), (2, 615), (3, 4880), (4, 1120), (5, -1320), (6, 175), (7, 1760), (8, 720), (10, -240), (11, 640), (12, 320), (13, 1040), (24, -240), (26, 1840), (27, 60), (31, -480), (33, -480), (35, 3840), (41, 720), (51, -960), (52, 3200), (56, -480), (59, -960), (60, 160), (73, 720), (81, -480), (82, 80), (84, 720), (85, 1440), (99, 1440), (103, 1440), (123, -960), (128, 240), (201, -240), (228, -3120), (237, -480), (306, -480), (313, 720), (315, 1440), (324, 1440), (502, 720), (517, 1440), (545, 1440), (721, -720)]

def boundaryRow387 : Integer.Sparse (Fin 909) := [(0, -2), (1, -39), (2, 93), (3, 976), (4, 352), (5, -116), (6, 6), (7, 272), (8, 192), (10, -144), (12, 112), (13, 192), (26, 416), (33, -288), (34, 64), (35, 256), (36, 144), (40, 288), (52, 64), (54, -144), (55, -144), (56, -192), (59, -192), (72, 144), (75, 288), (81, -384), (83, 288), (85, 576), (199, -48), (228, -384), (271, -96), (307, -288), (316, 288), (330, 576), (426, 288), (428, 576), (498, 288), (501, 576), (508, 1152), (727, -192)]

def boundaryRow388 : Integer.Sparse (Fin 909) := [(0, -13), (1, 80), (2, 605), (3, 4480), (4, 800), (5, -1220), (6, 170), (7, 1200), (8, 640), (12, 720), (13, 2880), (26, 960), (35, 3040), (38, 720), (40, 1440), (52, 2720), (54, -480), (55, -720), (56, -960), (59, -480), (60, 160), (81, -960), (82, 560), (84, 1440), (85, 2880), (128, 560), (199, -480), (201, -960), (228, -1440), (306, -720), (323, 1440), (329, 2880), (499, 720), (540, 1440), (541, 2880), (728, -960), (760, 1440), (794, 5760)]

def boundaryRow389 : Integer.Sparse (Fin 909) := [(0, -5), (1, 76), (2, 127), (3, 656), (5, -216), (6, 24), (7, 384), (8, 128), (10, -48), (12, 112), (13, 512), (23, -48), (27, 12), (35, 720), (51, -96), (52, 544), (54, -192), (59, -240), (60, 160), (62, -192), (72, 144), (73, 288), (81, -192), (82, 32), (98, 288), (128, 112), (199, -96), (201, -96), (237, -96), (267, -96), (284, 288), (306, -96), (392, 288), (499, 288), (502, 288)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow390 : Integer.Sparse (Fin 909) := [(0, -29), (1, 550), (2, 855), (3, 4480), (5, -1500), (6, 190), (7, 1680), (8, 960), (10, -720), (12, 1120), (13, 5120), (32, 320), (35, 3680), (52, 4160), (59, -1920), (60, 640), (72, 720), (73, 1440), (75, 1440), (81, -960), (82, 880), (128, 1680), (199, -720), (201, -2400), (267, -480), (284, 1440), (306, -720), (399, 2880), (499, 720), (502, 2880), (760, 1440)]

def boundaryRow393 : Integer.Sparse (Fin 909) := [(0, -38), (1, -325), (2, 555), (3, 5040), (5, -820), (6, 30), (7, 2880), (8, 1440), (9, -20), (10, -2160), (12, 2720), (13, 4000), (23, -1440), (27, 360), (35, 1760), (38, 2160), (51, -4320), (54, -4320), (55, -720), (59, -3600), (68, 60), (69, 240), (70, 160), (72, 4320), (74, 4320), (82, 240), (124, -720), (196, -480), (199, -2400), (259, -1440), (282, 2160), (308, -720), (321, 2160), (505, 1440), (723, -720), (727, -240)]

def boundaryRow394 : Integer.Sparse (Fin 909) := [(0, -14), (1, -100), (2, 255), (3, 3440), (4, 400), (5, -660), (6, 45), (7, 3040), (8, 640), (10, -240), (12, 640), (13, 960), (24, -240), (26, 960), (27, 60), (34, 160), (35, 3840), (37, 1440), (51, -480), (52, 1520), (55, -480), (59, -480), (60, 320), (67, 160), (73, 720), (81, -480), (83, 1440), (84, 3600), (228, -1200), (273, -480), (311, 1440), (317, 1440)]

def boundaryRow395 : Integer.Sparse (Fin 909) := [(0, -3), (1, -31), (2, 91), (3, 656), (4, 48), (5, -164), (6, 9), (7, 592), (8, 256), (9, -8), (10, -192), (12, 80), (13, 64), (24, -192), (26, 96), (27, 48), (35, 512), (37, 288), (51, -288), (52, 144), (55, -96), (59, -240), (67, 32), (68, 12), (69, 128), (70, 96), (73, 576), (81, -96), (84, 144), (124, -48), (126, -96), (197, -96), (228, -48), (259, -96), (308, -96), (321, 144), (322, 288), (501, 288), (503, 288), (727, -48)]

def boundaryRow396 : Integer.Sparse (Fin 909) := [(0, -12), (1, -195), (2, 775), (3, 6320), (4, 1840), (5, -1040), (6, 70), (7, 2800), (8, 1280), (10, -240), (11, 240), (12, 80), (13, 80), (24, -240), (26, 2880), (27, 60), (31, -240), (33, -960), (34, 160), (35, 3280), (37, 1440), (51, -480), (52, 1760), (55, -480), (59, -480), (67, 160), (73, 720), (81, -3840), (83, 2880), (84, 2880), (85, 4320), (228, -4080), (273, -480), (311, 720), (314, 1440), (317, 1440), (490, -720)]

def boundaryRow397 : Integer.Sparse (Fin 909) := [(0, -1), (1, -310), (2, 730), (3, 6400), (4, 2080), (5, -1120), (6, 105), (7, 3040), (8, 960), (11, 560), (26, 3520), (35, 4160), (52, 2240), (53, 1440), (67, 160), (81, -2880), (83, 1440), (84, 3600), (85, 4320), (228, -4800), (702, 1440), (709, 1440)]

def boundaryRow398 : Integer.Sparse (Fin 909) := [(0, -14), (1, -15), (2, 45), (3, 2320), (5, -440), (6, 70), (7, 1680), (8, 640), (9, -60), (10, -480), (23, -480), (25, -240), (26, 640), (27, 120), (35, 2480), (36, 720), (52, 480), (54, -1200), (55, -240), (64, -480), (67, 400), (68, 60), (69, 800), (70, 400), (72, 1440), (83, 1440), (125, -720), (126, -480), (199, -480), (228, -960), (260, -480), (271, -480), (287, 720), (308, -240), (316, 1440), (425, 720), (492, -240), (498, 720), (501, 1440), (727, -240)]

def boundaryRow399 : Integer.Sparse (Fin 909) := [(0, -3), (1, 15), (2, 108), (3, 768), (4, 144), (5, -196), (6, 20), (7, 480), (8, 176), (11, 16), (12, 32), (13, 112), (26, 272), (34, 32), (35, 768), (37, 144), (52, 480), (56, -48), (59, -48), (60, 32), (67, 64), (73, 288), (81, -384), (83, 144), (84, 432), (128, 16), (201, -96), (228, -288), (275, -96), (317, 288), (428, 144), (460, 144), (517, 144), (709, 144)]

def boundaryRow400 : Integer.Sparse (Fin 909) := [(0, -33), (1, 235), (2, 950), (3, 4480), (4, 160), (5, -1600), (6, 100), (7, 3680), (8, 2240), (10, -2400), (12, 1360), (13, 2560), (26, 160), (33, -480), (34, 160), (35, 3440), (38, 720), (52, 2240), (54, -240), (59, -3840), (60, 160), (72, 1440), (73, 2880), (74, 1440), (75, 2880), (81, -1440), (82, 320), (84, 1440), (128, 400), (199, -720), (201, -960), (228, -480), (271, -480), (307, -720), (318, 1440), (426, 720), (428, 1440), (499, 720)]

def boundaryRow401 : Integer.Sparse (Fin 909) := [(0, -29), (1, -45), (2, 1290), (3, 6720), (4, 960), (5, -1080), (6, 60), (7, 1680), (8, 1440), (10, -720), (12, 2160), (13, 4400), (31, -720), (33, -1440), (35, 1680), (42, 4320), (51, -2880), (52, 3120), (59, -2880), (60, 480), (81, -1440), (82, 240), (86, 4320), (128, 960), (311, 2160), (326, 4320), (328, 4320), (490, -720)]

def boundaryRow402 : Integer.Sparse (Fin 909) := [(0, 3), (1, -230), (2, 1095), (3, 6480), (4, 1520), (5, -1720), (6, 150), (7, 3040), (8, 1760), (11, 240), (26, 2560), (35, 4000), (52, 2640), (57, 1440), (67, 800), (81, -3360), (86, 2880), (228, -720), (460, 1440), (855, 4320)]

def boundaryRow403 : Integer.Sparse (Fin 909) := [(0, -16), (1, 140), (2, 1155), (3, 4000), (4, 880), (5, -1820), (6, 95), (7, 3760), (8, 3040), (12, 80), (13, 160), (26, 1120), (31, -960), (33, -960), (35, 2480), (42, 1440), (51, -960), (52, 1120), (56, -240), (59, -960), (67, 480), (76, 1440), (81, -2400), (86, 1440), (97, 720), (107, 1440), (201, -240), (238, -720), (307, -720), (326, 2880), (425, 720), (428, 1440), (506, 1440)]

def boundaryRow404 : Integer.Sparse (Fin 909) := [(0, -1), (1, 64), (2, 143), (3, 304), (4, 32), (5, -412), (6, 60), (7, 48), (8, 256), (9, -4), (11, 32), (12, 16), (25, -96), (26, 64), (31, -192), (33, -192), (35, 288), (39, 288), (52, 608), (54, -96), (69, 16), (71, 64), (87, 144), (123, -192), (226, -48), (228, -96), (237, -144), (239, 288), (306, -144), (315, 576), (498, 144), (507, 288), (721, -192), (723, -48), (760, 288), (764, 288)]

def boundaryRow405 : Integer.Sparse (Fin 909) := [(0, -27), (1, 505), (2, 1080), (3, 3840), (5, -2140), (6, 250), (7, 2160), (8, 1920), (9, -20), (12, 560), (13, 2640), (35, 3680), (51, -480), (52, 4080), (54, -240), (59, -1200), (60, 720), (69, 160), (71, 560), (82, 400), (86, 1440), (128, 800), (199, -240), (201, -960), (260, -480), (262, -480), (289, 720), (309, -720), (327, 1440), (328, 1440), (392, 720), (492, -240)]

def boundaryRow406 : Integer.Sparse (Fin 909) := [(0, -29), (1, 535), (2, 1010), (3, 3600), (4, 160), (5, -2000), (6, 240), (7, 1600), (8, 1600), (12, 560), (13, 2720), (26, 80), (35, 3120), (42, 720), (51, -480), (52, 4240), (56, -480), (59, -1920), (60, 800), (76, 720), (82, 240), (86, 720), (102, 720), (103, 720), (128, 880), (201, -960), (328, 1440), (392, 720), (399, 720), (506, 1440), (798, 720)]

def boundaryRow407 : Integer.Sparse (Fin 909) := [(0, -21), (1, 275), (2, 450), (3, 1440), (4, 160), (5, -1240), (6, 200), (7, 640), (8, 1040), (9, -20), (11, 160), (12, 160), (13, 720), (25, -240), (26, 320), (35, 1360), (39, 720), (51, -480), (52, 2000), (54, -480), (56, -480), (59, -480), (69, 80), (71, 320), (74, 720), (82, 160), (89, 720), (123, -480), (128, 400), (199, -240), (201, -480), (226, -240), (228, -480), (315, 1440), (507, 2160), (540, 720), (721, -480), (723, -240), (764, 720)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow408 : Integer.Sparse (Fin 909) := [(0, -23), (1, -105), (2, 1130), (3, 5680), (4, 1200), (5, -1300), (6, 90), (7, 1760), (8, 2000), (10, -240), (12, 1600), (13, 2800), (24, -240), (26, 480), (27, 60), (31, -720), (33, -1920), (34, 320), (35, 1040), (39, 1440), (42, 1440), (51, -3120), (52, 1920), (55, -480), (56, -960), (59, -2400), (60, 320), (74, 720), (76, 1440), (81, -960), (85, 1440), (86, 1440), (128, 480), (201, -720), (228, -480), (273, -480), (311, 2160), (314, 1440), (315, 2880), (319, 1440), (326, 2880), (328, 1440), (490, -720)]

def boundaryRow409 : Integer.Sparse (Fin 909) := [(0, -14), (1, 15), (2, 500), (3, 3840), (4, 960), (5, -1260), (6, 175), (7, 480), (8, 960), (9, -20), (12, 960), (13, 2880), (24, -480), (26, 800), (27, 120), (31, -480), (33, -960), (35, 2080), (39, 1440), (42, 1440), (51, -960), (52, 2080), (54, -960), (55, -480), (56, -2400), (68, 60), (69, 80), (71, 320), (82, 640), (99, 1440), (123, -480), (124, -240), (126, -480), (128, 640), (197, -480), (199, -480), (201, -960), (237, -480), (259, -480), (262, -960), (286, 720), (288, 1440), (306, -960), (308, -480), (309, -240), (312, 720), (315, 1440), (328, 1440), (329, 1440), (500, 2880), (506, 1440), (721, -720), (728, -240), (764, 1440), (796, -720), (798, 2880)]

def boundaryRow410 : Integer.Sparse (Fin 909) := [(0, -2), (1, 11), (2, 115), (3, 424), (4, 64), (5, -170), (6, 8), (7, 384), (8, 296), (12, 32), (13, 40), (25, -24), (26, 104), (31, -48), (33, -72), (34, 16), (35, 232), (39, 72), (51, -48), (52, 80), (54, -48), (59, -48), (64, -48), (67, 40), (74, 72), (81, -240), (85, 144), (86, 144), (100, 72), (107, 144), (199, -24), (228, -48), (238, -72), (271, -48), (307, -72), (319, 144), (326, 144), (425, 72), (426, 72), (428, 144), (500, 144)]

def boundaryRow412 : Integer.Sparse (Fin 909) := [(0, -6), (1, 72), (2, 193), (3, 624), (4, 80), (5, -340), (6, 31), (7, 448), (8, 384), (11, 32), (12, 16), (13, 64), (26, 176), (33, -96), (35, 384), (52, 368), (59, -48), (67, 32), (75, 144), (81, -288), (85, 432), (86, 288), (128, 16), (201, -48), (228, -288), (428, 288), (517, 144), (760, 144), (855, 144)]

def boundaryRow419 : Integer.Sparse (Fin 909) := [(0, 27), (1, -905), (2, 610), (3, 2960), (4, 2000), (5, -400), (6, 20), (7, 240), (8, 560), (9, -20), (12, 560), (23, -240), (24, -1680), (26, 160), (27, 900), (31, -2400), (47, 720), (51, -5040), (52, 400), (56, -960), (68, 180), (69, 80), (71, 80), (124, -240), (126, -1440), (205, 720), (207, 1440), (209, 1440), (238, -960), (262, -480), (308, -240), (309, -240), (538, 720), (751, 720), (753, 1440)]

def boundaryRow422 : Integer.Sparse (Fin 909) := [(0, 33), (1, -685), (2, 305), (3, 6480), (4, 2720), (5, -380), (6, 45), (7, 1120), (8, 80), (12, 400), (13, 400), (24, -240), (26, 3360), (31, -720), (33, -480), (34, 640), (35, 2000), (44, 1440), (52, 1040), (67, 640), (81, -960), (95, 720), (99, 1440), (119, 1440), (453, 1440), (460, 1440)]

def boundaryRow423 : Integer.Sparse (Fin 909) := [(0, -3), (1, -39), (2, 91), (3, 768), (4, 192), (5, -68), (6, 5), (7, 144), (8, 64), (12, 176), (13, 176), (25, -192), (26, 256), (31, -144), (33, -672), (34, 64), (35, 224), (43, 288), (51, -48), (52, 160), (59, -192), (64, -144), (67, 64), (81, -192), (95, 144), (103, 288), (104, 288), (110, 144), (112, 288), (201, -48), (307, -144), (425, 144), (428, 288), (472, 288)]

def boundaryRow425 : Integer.Sparse (Fin 909) := [(0, -11), (1, -790), (2, 850), (3, 5920), (4, 1280), (5, -520), (6, 35), (7, 640), (8, 320), (9, -20), (12, 2000), (13, 1440), (23, -1200), (25, -2880), (26, 480), (27, 720), (31, -3840), (33, -3840), (35, 400), (51, -5760), (52, 800), (54, -960), (55, -2160), (64, -2880), (68, 180), (69, 80), (70, 80), (124, -240), (125, -960), (126, -480), (140, 720), (142, 2880), (145, 1440), (238, -1920), (260, -480), (309, -480), (383, 1440), (538, 1440)]

def boundaryRow430 : Integer.Sparse (Fin 909) := [(0, -21), (1, 80), (2, 365), (3, 4080), (5, -900), (6, 170), (7, 560), (9, -60), (12, 1200), (13, 4160), (23, -960), (25, -960), (27, 240), (31, -960), (33, -1920), (35, 1760), (52, 2240), (54, -1440), (63, -2640), (68, 180), (69, 240), (70, 160), (123, -960), (124, -240), (125, -480), (126, -480), (129, 720), (144, 1440), (196, -720), (231, 1440), (237, -1920), (306, -720), (498, 720), (721, -960), (723, -240), (760, 1440)]

def boundaryRow433 : Integer.Sparse (Fin 909) := [(0, -26), (1, -335), (2, 380), (3, 3600), (4, 160), (5, -320), (6, 5), (7, 1040), (8, 480), (9, -20), (10, -960), (12, 1920), (13, 1920), (23, -1200), (24, -480), (27, 660), (35, 160), (38, 720), (47, 1440), (51, -3120), (52, 80), (54, -480), (55, -1680), (59, -1200), (68, 120), (69, 160), (124, -720), (125, -480), (126, -240), (140, 1440), (205, 720), (259, -480), (308, -480), (321, 720), (538, 1440), (539, 1440), (727, -240)]

def boundaryRow434 : Integer.Sparse (Fin 909) := [(0, -9), (1, -10), (2, -35), (3, 3040), (4, 800), (5, -320), (6, 40), (7, 2240), (8, 320), (9, -20), (12, 320), (13, 80), (23, -480), (25, -2160), (26, 1440), (33, -480), (35, 960), (38, 720), (51, -480), (52, 160), (54, -2640), (64, -960), (69, 240), (97, 2880), (124, -480), (228, -960), (260, -480), (321, 720), (383, 1440), (492, -240)]

def boundaryRow436 : Integer.Sparse (Fin 909) := [(0, 6), (1, -240), (2, 565), (3, 4160), (4, 1680), (5, -480), (6, 35), (7, 800), (8, 880), (9, -20), (24, -240), (26, 1520), (27, 60), (31, -480), (35, 320), (37, 720), (46, 1440), (51, -1440), (52, 800), (56, -1680), (69, 160), (71, 80), (81, -1200), (107, 1440), (124, -240), (126, -240), (228, -960), (262, -480), (501, 720), (735, 1440), (745, 1440), (753, 1440), (796, -240)]

def boundaryRow444 : Integer.Sparse (Fin 909) := [(0, 1), (1, -490), (2, 640), (3, 3520), (4, 720), (5, -740), (6, 65), (7, 880), (8, 1120), (9, -40), (10, -480), (11, 80), (12, 800), (13, 720), (23, -480), (24, -240), (26, 480), (27, 420), (30, -240), (31, -720), (35, 560), (40, 720), (43, 720), (51, -2160), (52, 800), (55, -1200), (68, 120), (69, 160), (71, 240), (95, 1440), (125, -480), (126, -960), (146, 1440), (208, 720), (236, -480), (237, -240), (238, -240), (308, -240), (508, 720), (538, 720), (546, 720), (727, -240), (738, 720)]

def boundaryRow445 : Integer.Sparse (Fin 909) := [(0, -14), (1, -145), (2, 360), (3, 4400), (4, 640), (5, -760), (6, 115), (7, 1120), (8, 240), (9, -20), (12, 560), (13, 2640), (25, -240), (26, 1360), (34, 560), (35, 2320), (39, 720), (52, 2480), (54, -1440), (60, 560), (64, -480), (69, 160), (71, 80), (82, 80), (99, 1440), (103, 1440), (116, 720), (126, -480), (128, 400), (228, -480), (260, -480), (329, 720), (392, 720), (400, 1440), (492, -240)]

def boundaryRow446 : Integer.Sparse (Fin 909) := [(0, 3), (1, -80), (2, 51), (3, 608), (4, 232), (5, -60), (6, 6), (7, 80), (8, 72), (11, 24), (12, 64), (13, 64), (26, 240), (27, 6), (31, -72), (35, 144), (43, 72), (45, 72), (51, -120), (52, 64), (56, -96), (57, 72), (81, -48), (107, 216), (204, 144), (228, -48), (237, -24), (238, -72), (546, 72), (745, 144), (855, 72), (870, 72)]

def boundaryRow447 : Integer.Sparse (Fin 909) := [(0, -29), (1, -5), (2, 660), (3, 5920), (4, 560), (5, -800), (6, 110), (7, 480), (8, 240), (12, 1840), (13, 5520), (26, 880), (33, -480), (34, 640), (35, 2320), (42, 720), (51, -240), (52, 3120), (59, -960), (60, 640), (82, 240), (98, 1440), (99, 720), (102, 1440), (103, 720), (116, 720), (120, 720), (128, 800), (201, -480), (237, -240), (328, 720), (392, 720), (398, 1440), (399, 720)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow448 : Integer.Sparse (Fin 909) := [(0, -36), (1, 35), (2, 615), (3, 3440), (5, -860), (6, 100), (7, 560), (8, 800), (9, -20), (12, 1200), (13, 3360), (33, -960), (35, 640), (38, 720), (51, -1440), (52, 1840), (54, -1200), (59, -1440), (69, 80), (71, 160), (82, 160), (102, 1440), (126, -480), (128, 400), (199, -480), (237, -480), (259, -480), (539, 1440), (540, 720), (721, -480), (723, -240), (739, 1440)]

def boundaryRow454 : Integer.Sparse (Fin 909) := [(0, -18), (1, -455), (2, 160), (3, 7200), (4, 1520), (5, -260), (6, 45), (11, 80), (12, 1280), (13, 3680), (26, 3120), (34, 2400), (35, 1920), (41, 720), (52, 880), (55, -480), (56, -720), (60, 720), (82, 80), (128, 160), (139, 1440), (190, 1440), (204, 1440), (238, -480), (324, 720), (398, 1440)]

def boundaryRow455 : Integer.Sparse (Fin 909) := [(0, -38), (1, -205), (2, 240), (3, 5840), (4, 160), (5, -560), (6, 75), (7, 640), (8, 160), (9, -20), (12, 1360), (13, 4160), (23, -240), (26, 2240), (27, 180), (34, 1920), (35, 2320), (38, 720), (51, -1440), (52, 1280), (54, -480), (55, -1200), (60, 560), (64, -1440), (68, 120), (70, 80), (71, 80), (82, 320), (125, -480), (128, 400), (138, 1440), (139, 1440), (146, 720), (197, -720), (236, -240), (238, -960), (260, -480), (309, -480), (323, 720), (400, 1440), (728, -240), (810, 1440)]

def boundaryRow460 : Integer.Sparse (Fin 909) := [(0, -3), (1, -280), (2, 45), (3, 3440), (4, 1000), (5, -210), (6, 30), (7, 280), (8, 120), (11, 160), (12, 80), (13, 800), (26, 2200), (34, 960), (35, 1240), (51, -120), (52, 200), (53, 360), (55, -360), (56, -480), (64, -720), (67, 360), (107, 360), (139, 720), (190, 720), (228, -120), (238, -480), (453, 720), (546, 360), (702, 360), (870, 360)]

def boundaryRow461 : Integer.Sparse (Fin 909) := [(0, -22), (1, -190), (2, 355), (3, 5680), (4, 800), (5, -620), (6, 95), (7, 1280), (8, 240), (9, -40), (11, 80), (12, 480), (13, 2400), (24, -240), (26, 3040), (27, 120), (31, -240), (33, -480), (34, 1520), (35, 2400), (37, 720), (51, -1440), (52, 1120), (55, -960), (64, -2400), (67, 560), (68, 120), (69, 160), (70, 240), (125, -1200), (126, -240), (138, 1440), (139, 1440), (146, 720), (197, -480), (204, 720), (237, -240), (238, -1200), (307, -480), (309, -240), (472, 1440), (503, 720), (543, 720), (546, 720), (727, -240), (736, 720)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow33 : Integer.Sparse (Fin 909) := [(0, 56), (1, -675), (2, 305), (3, 1760), (4, 1120), (5, -80), (7, 160), (8, 240), (12, 440), (24, -480), (26, 160), (27, 180), (30, -240), (31, -720), (45, 360), (46, 360), (51, -480), (56, -240)]

def boundaryRow34 : Integer.Sparse (Fin 909) := [(0, 67), (1, -1010), (2, 185), (3, 3200), (4, 960), (5, -60), (7, 80), (8, 160), (12, 1040), (13, 1200), (25, -960), (26, 640), (31, -960), (33, -960), (38, 720), (39, 1440), (54, -720)]

def boundaryRow35 : Integer.Sparse (Fin 909) := [(0, 8), (1, -151), (2, 109), (3, 624), (4, 192), (5, -44), (7, 48), (8, 160), (12, 96), (23, -48), (25, -96), (26, 128), (27, 36), (30, -96), (31, -192), (33, -384), (36, 144), (39, 288), (40, 288), (51, -192), (54, -240), (55, -144)]

def boundaryRow36 : Integer.Sparse (Fin 909) := [(0, 19), (1, -288), (2, 91), (3, 928), (4, 512), (5, -12), (7, 16), (8, 32), (12, 48), (13, 32), (26, 368), (37, 144), (40, 288), (56, -144), (57, 288)]

def boundaryRow37 : Integer.Sparse (Fin 909) := [(0, 37), (1, -580), (2, 255), (3, 1920), (4, 320), (5, -80), (7, 80), (8, 320), (12, 720), (13, 880), (23, -120), (26, 160), (27, 90), (30, -240), (38, 360), (40, 720), (51, -480), (54, -240), (55, -360)]

def boundaryRow38 : Integer.Sparse (Fin 909) := [(0, 16), (1, -255), (2, 93), (3, 896), (4, 304), (12, 384), (13, 448), (26, 112), (31, -192), (33, -192), (41, 144), (42, 288)]

def boundaryRow39 : Integer.Sparse (Fin 909) := [(0, 17), (1, -309), (2, 76), (3, 1008), (4, 480), (26, 528), (53, 144), (57, 144)]

def boundaryRow40 : Integer.Sparse (Fin 909) := [(0, 9), (1, -179), (2, 82), (3, 720), (4, 288), (5, -32), (7, 64), (8, 96), (12, 160), (13, 128), (24, -96), (26, 176), (27, 36), (30, -48), (31, -96), (33, -192), (37, 144), (39, 144), (40, 144), (42, 144), (51, -192), (55, -144), (56, -96)]

def boundaryRow41 : Integer.Sparse (Fin 909) := [(0, 1), (1, -145), (2, 70), (3, 1200), (4, 400), (5, -10), (7, 80), (12, 720), (14, 360), (15, 1440), (23, -840), (24, -480), (25, -840), (27, 120), (33, -480), (36, 720), (48, 720), (51, -240), (54, -240), (55, -240)]

def boundaryRow42 : Integer.Sparse (Fin 909) := [(0, 83), (1, -1010), (2, 145), (3, 5280), (4, 1920), (12, 1760), (13, 720), (15, 1440), (16, 720), (18, 2880), (23, -480), (24, -480), (25, -720), (27, 60), (38, 1440), (50, 720), (55, -480)]

def boundaryRow43 : Integer.Sparse (Fin 909) := [(0, 88), (1, -1245), (2, 255), (3, 4080), (4, 1760), (5, -20), (7, 80), (8, 80), (12, 880), (15, 720), (18, 720), (19, 1440), (21, 1440), (23, -240), (24, -1440), (25, -240), (26, 480), (27, 180), (31, -960), (37, 1440), (47, 720), (48, 720), (51, -480), (56, -480)]

def boundaryRow44 : Integer.Sparse (Fin 909) := [(0, 79), (1, -810), (2, 195), (3, 1040), (4, 1320), (5, -20), (7, 80), (8, 120), (12, 160), (17, 360), (20, 720), (23, -120), (24, -600), (25, -360), (26, 80), (27, 90), (30, -360), (31, -720), (44, 720), (45, 720), (48, 360), (51, -120)]

def boundaryRow45 : Integer.Sparse (Fin 909) := [(0, 1), (1, -25), (2, -25), (9, -100), (58, 5)]

def boundaryRow46 : Integer.Sparse (Fin 909) := [(0, 1), (1, -24), (2, 36), (5, -120), (6, 15), (9, -16), (27, 180), (68, 240)]

def boundaryRow47 : Integer.Sparse (Fin 909) := [(0, 1), (1, -25), (2, -150), (3, -240), (5, 320), (6, -30), (7, -480), (8, -480), (9, 40), (35, -160), (69, -240), (70, -80), (71, -480)]

def boundaryRow48 : Integer.Sparse (Fin 909) := [(0, -1), (1, 55), (2, -10), (3, -480), (5, -20), (7, -480), (9, 20), (12, -320), (13, -160), (23, 720), (35, -320), (69, -320), (70, -160), (124, 720), (125, 480)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow49 : Integer.Sparse (Fin 909) := [(0, -9), (1, 135), (2, -160), (3, -1280), (4, -480), (5, 260), (6, -30), (7, -720), (8, -240), (9, 20), (24, 720), (26, -480), (35, -640), (52, -480), (69, -240), (70, -160), (71, -80), (126, 720), (197, 480)]

def boundaryRow50 : Integer.Sparse (Fin 909) := [(0, 3), (1, 105), (2, -90), (3, -1440), (5, 210), (6, -30), (7, -480), (9, 10), (12, -600), (13, -1240), (23, 360), (35, -720), (52, -480), (54, 720), (69, -120), (70, -120), (125, 360), (196, 240)]

def boundaryRow51 : Integer.Sparse (Fin 909) := [(0, -4), (1, 45), (2, -230), (3, -640), (4, -160), (5, 280), (6, -15), (7, -480), (8, -480), (9, 20), (24, 480), (27, -60), (51, 480), (52, -160), (69, -160), (71, -320), (124, 240), (126, 960)]

def boundaryRow52 : Integer.Sparse (Fin 909) := [(0, -14), (1, 65), (2, -250), (3, -320), (5, 440), (6, -45), (7, -160), (8, -800), (9, 20), (27, -60), (30, 480), (52, -160), (69, -80), (71, -400), (126, 240), (236, 960)]

def boundaryRow53 : Integer.Sparse (Fin 909) := [(0, -2), (1, 95), (2, -60), (3, -880), (4, -320), (5, 460), (6, -65), (7, -160), (8, -480), (9, 20), (13, -400), (24, 480), (26, -320), (35, -400), (52, -320), (55, 240), (56, 960), (69, -80), (70, -80), (71, -320), (125, 240), (197, 960)]

def boundaryRow54 : Integer.Sparse (Fin 909) := [(0, -1), (1, 35), (2, -140), (3, -480), (5, 265), (6, -15), (7, -600), (8, -480), (10, 180), (12, -120), (13, -160), (35, -320), (82, -60)]

def boundaryRow55 : Integer.Sparse (Fin 909) := [(0, -1), (1, 10), (2, -205), (3, -1200), (4, -240), (5, 680), (6, -90), (7, -480), (8, -480), (11, -240), (26, -480), (35, -1120), (52, -1200), (228, 720)]

def boundaryRow56 : Integer.Sparse (Fin 909) := [(0, 1), (1, -30), (2, -50), (3, -160), (5, 90), (6, -15), (7, -40), (8, -80), (12, -20), (13, -160), (35, -160), (52, -320), (82, -120), (128, -160), (199, 60), (201, 240)]

def boundaryRow57 : Integer.Sparse (Fin 909) := [(0, -1), (1, -10), (2, -5), (3, -480), (5, 10), (7, -240), (10, 360), (12, -240), (13, -640), (35, -320), (82, -120), (127, 360), (128, -120)]

def boundaryRow58 : Integer.Sparse (Fin 909) := [(0, -9), (1, 525), (2, 90), (3, -3360), (4, -1200), (5, 140), (6, -30), (7, -240), (11, -240), (12, -960), (13, -1680), (25, 720), (26, -1440), (35, -1520), (52, -240), (54, 2160), (56, 1440), (226, 480), (228, 720)]

def boundaryRow59 : Integer.Sparse (Fin 909) := [(0, -19), (1, 270), (2, -105), (3, -1360), (4, -560), (5, 240), (6, -40), (11, -80), (26, -640), (27, -120), (31, 480), (35, -480), (52, -400), (55, 480), (228, 240), (237, 480), (238, 480)]

def boundaryRow60 : Integer.Sparse (Fin 909) := [(1, 35), (2, -13), (3, -400), (4, -64), (5, 44), (6, -8), (7, -48), (12, -144), (13, -368), (26, -64), (35, -208), (52, -128), (54, 144), (56, 96), (82, -64), (128, -64), (199, 48), (201, 96)]

def boundaryRow64 : Integer.Sparse (Fin 909) := [(0, 7), (1, -140), (2, -465), (3, -1680), (5, 1240), (6, -160), (7, -960), (8, -960), (12, -240), (13, -1120), (35, -1520), (52, -1920), (59, 720), (60, -320), (128, -240)]

def boundaryRow65 : Integer.Sparse (Fin 909) := [(0, 1), (1, -5), (2, -120), (3, -480), (4, -80), (5, 240), (6, -20), (7, -480), (8, -320), (26, -160), (35, -400), (52, -160), (67, -80), (81, 240)]

def boundaryRow66 : Integer.Sparse (Fin 909) := [(0, 12), (1, 50), (2, -15), (3, -1760), (5, 20), (6, -5), (12, -720), (13, -2000), (26, -560), (32, -160), (33, 720), (34, -480), (35, -240), (55, 720), (60, -160), (61, 480)]

def boundaryRow67 : Integer.Sparse (Fin 909) := [(0, 2), (1, 6), (2, -5), (3, -256), (5, 8), (6, -1), (12, -96), (13, -224), (25, 48), (26, -64), (33, 192), (34, -32), (35, -32), (52, -32), (55, 96), (63, 48), (64, 96)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow68 : Integer.Sparse (Fin 909) := [(0, 8), (1, 40), (2, -15), (3, -1120), (5, 60), (6, -15), (7, -160), (12, -320), (13, -800), (23, 240), (26, -480), (33, 480), (34, -320), (35, -480), (54, 480), (55, 480), (63, 240), (65, 480), (67, -160)]

def boundaryRow69 : Integer.Sparse (Fin 909) := [(0, -2), (1, 67), (2, -13), (3, -528), (4, -224), (5, 16), (6, -2), (7, -16), (8, -16), (12, -16), (13, -80), (24, 48), (26, -336), (33, 48), (34, -112), (35, -64), (52, -16), (55, 144), (56, 96), (64, 48), (66, 96), (67, -32)]

def boundaryRow70 : Integer.Sparse (Fin 909) := [(0, 9), (1, -5), (2, -65), (3, -1440), (5, 60), (6, -5), (12, -720), (13, -2640), (26, -240), (32, -320), (34, -480), (35, -240), (52, -480), (59, 720), (60, -400), (61, 720), (128, -240)]

def boundaryRow71 : Integer.Sparse (Fin 909) := [(0, 1), (2, -7), (3, -144), (5, 14), (6, -2), (7, -24), (12, -48), (13, -160), (26, -24), (32, -16), (33, 72), (35, -72), (52, -48), (54, 72), (60, -16), (62, 48)]

def boundaryRow72 : Integer.Sparse (Fin 909) := [(0, -16), (1, 485), (2, -240), (3, -3440), (4, -1280), (5, 120), (6, -5), (7, -480), (8, -160), (12, -320), (13, -320), (25, 240), (26, -1600), (31, 480), (33, 960), (34, -400), (35, -560), (51, 480), (52, -240), (64, 240), (67, -160), (81, 480), (123, 480)]

def boundaryRow73 : Integer.Sparse (Fin 909) := [(1, 42), (2, -35), (3, -448), (4, -64), (5, 44), (6, -5), (7, -112), (8, -32), (12, -128), (13, -272), (26, -160), (34, -80), (35, -160), (51, 96), (52, -112), (54, 48), (64, 48), (67, -32)]

def boundaryRow74 : Integer.Sparse (Fin 909) := [(0, -9), (1, 345), (2, -120), (3, -2560), (4, -880), (7, -80), (12, -800), (13, -480), (23, 240), (25, 720), (26, -880), (31, 480), (33, 1440), (34, -320), (35, -160), (54, 480), (65, 240), (67, -80), (81, 240), (195, -480)]

def boundaryRow75 : Integer.Sparse (Fin 909) := [(0, 1), (1, 65), (2, -40), (3, -620), (4, -140), (5, 5), (12, -260), (13, -340), (25, 60), (26, -100), (27, -15), (31, 120), (33, 360), (34, -80), (35, -20), (51, 180), (52, -60), (55, 60), (59, 120), (60, -20), (61, 60), (128, -20), (194, -120)]

def boundaryRow77 : Integer.Sparse (Fin 909) := [(0, 5), (1, -73), (2, 44), (3, 160), (4, 64), (5, -15), (7, 20), (8, 40), (10, -36), (12, 56), (13, 32), (23, -120), (24, -336), (27, 123), (30, -192), (55, -192), (79, 36), (80, 72)]

def boundaryRow78 : Integer.Sparse (Fin 909) := [(0, 17), (1, -570), (2, 730), (3, 3040), (4, 1040), (5, -620), (6, 15), (7, 1120), (8, 1760), (12, 400), (23, -480), (24, -1440), (26, 480), (27, 600), (30, -960), (35, 160), (51, -3600), (54, -960), (55, -480), (56, -1920), (77, 720), (78, 1440), (228, -720)]

def boundaryRow79 : Integer.Sparse (Fin 909) := [(0, -3), (1, 20), (2, 240), (3, 560), (5, -350), (6, 20), (7, 600), (8, 520), (10, -180), (12, 180), (13, 240), (23, -60), (27, 45), (30, -120), (35, 240), (51, -480), (52, 160), (54, -240), (59, -480), (72, 180), (74, 360), (75, 360), (199, -180)]

def boundaryRow80 : Integer.Sparse (Fin 909) := [(0, -14), (1, 260), (2, 1255), (3, 3120), (4, 400), (5, -2280), (6, 205), (7, 3040), (8, 2720), (26, 480), (35, 2240), (52, 2320), (81, -960), (84, 720), (85, 1440), (86, 1440), (228, -720)]

def boundaryRow81 : Integer.Sparse (Fin 909) := [(0, -17), (1, 80), (2, 990), (3, 2880), (4, 320), (5, -1580), (6, 95), (7, 2800), (8, 2640), (10, -720), (12, 400), (13, 640), (24, -480), (27, 180), (30, -240), (35, 1440), (51, -1920), (52, 640), (56, -960), (59, -1920), (73, 720), (74, 720), (75, 720), (76, 1440), (201, -720)]

def boundaryRow82 : Integer.Sparse (Fin 909) := [(0, -17), (1, 280), (2, 1440), (3, 3840), (5, -2160), (6, 185), (7, 2480), (8, 2400), (12, 480), (13, 640), (35, 2400), (52, 3200), (73, 720), (75, 1440), (81, -960), (86, 2880), (201, -720)]

def boundaryRow83 : Integer.Sparse (Fin 909) := [(0, -3), (1, 10), (2, 950), (3, 3360), (4, 720), (5, -1240), (6, 95), (7, 1520), (8, 1600), (26, 960), (35, 960), (52, 1280), (81, -1920), (83, 720), (85, 2880), (86, 1440), (228, -1440)]

def boundaryRow84 : Integer.Sparse (Fin 909) := [(0, 13), (1, -580), (2, 285), (3, 4800), (4, 800), (5, -100), (7, 560), (8, 160), (10, -240), (12, 1920), (13, 1520), (23, -1920), (24, -1440), (25, -240), (27, 420), (47, 2880), (48, 1440), (50, 720), (51, -1440), (55, -960), (59, -480), (79, 720), (94, 1440)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow85 : Integer.Sparse (Fin 909) := [(0, 8), (1, -124), (2, 37), (3, 800), (4, 352), (5, -12), (6, 1), (7, 64), (12, 592), (13, 80), (23, -96), (25, -384), (26, 128), (33, -96), (35, 64), (43, 576), (50, 144), (52, 32), (55, -96), (104, 288), (113, 144)]

def boundaryRow87 : Integer.Sparse (Fin 909) := [(0, 64), (1, -710), (2, 515), (3, 3760), (4, 1760), (5, -260), (6, 5), (7, 480), (8, 800), (12, 240), (23, -240), (24, -480), (26, 880), (27, 60), (31, -1680), (43, 720), (46, 1440), (51, -1440), (52, 80), (56, -960), (77, 720), (81, -480), (106, 1440), (107, 1440), (122, 1440), (228, -240)]

def boundaryRow88 : Integer.Sparse (Fin 909) := [(0, 6), (1, -189), (2, 83), (3, 832), (4, 368), (5, -28), (6, 2), (7, 112), (8, 16), (12, 320), (13, 96), (23, -48), (24, -48), (25, -336), (26, 128), (31, -336), (33, -336), (35, 80), (43, 288), (46, 288), (50, 144), (51, -96), (52, 64), (55, -96), (81, -96), (95, 144), (104, 144), (113, 288), (122, 288)]

def boundaryRow89 : Integer.Sparse (Fin 909) := [(0, -1), (1, -56), (2, 56), (3, 464), (4, 80), (5, -40), (6, 1), (7, 80), (8, 80), (10, -72), (12, 184), (13, 192), (24, -48), (26, 32), (35, 32), (38, 72), (40, 144), (51, -48), (52, 48), (55, -72), (59, -144), (72, 72), (75, 144), (94, 144), (95, 288), (102, 288), (199, -24)]

def boundaryRow90 : Integer.Sparse (Fin 909) := [(0, 31), (1, -362), (2, 90), (3, 768), (4, 704), (5, -20), (6, 1), (7, 32), (8, 32), (12, 144), (24, -96), (25, -240), (26, 160), (31, -768), (35, 32), (43, 288), (44, 576), (52, 32), (55, -96), (95, 288), (113, 144)]

def boundaryRow91 : Integer.Sparse (Fin 909) := [(0, 68), (1, -1405), (2, 540), (3, 5040), (4, 2240), (5, -180), (6, 5), (7, 880), (8, 160), (10, -240), (12, 2480), (13, 160), (23, -2160), (24, -1440), (25, -480), (26, 640), (27, 420), (31, -1440), (35, 240), (43, 2880), (52, 160), (55, -1200), (79, 720), (95, 1440), (113, 1440)]

def boundaryRow92 : Integer.Sparse (Fin 909) := [(0, 54), (1, -935), (2, 310), (3, 3280), (4, 1480), (5, -140), (6, 5), (7, 360), (8, 360), (12, 1080), (23, -480), (24, -120), (26, 720), (27, 30), (31, -240), (35, 80), (43, 720), (45, 1440), (51, -600), (55, -240), (56, -480), (77, 360), (105, 720), (107, 720), (228, -120)]

def boundaryRow93 : Integer.Sparse (Fin 909) := [(0, 4), (1, -875), (2, 605), (3, 5680), (4, 640), (5, -420), (6, 20), (7, 880), (8, 640), (10, -720), (12, 3120), (13, 3840), (23, -480), (26, 320), (33, -1920), (35, 800), (36, 720), (38, 1440), (40, 1440), (52, 640), (54, -1200), (55, -720), (59, -960), (72, 720), (75, 1440), (199, -240)]

def boundaryRow94 : Integer.Sparse (Fin 909) := [(0, 8), (1, -1045), (2, 155), (3, 6480), (4, 1920), (10, -720), (12, 3200), (13, 2800), (23, -480), (24, -960), (25, -720), (27, 60), (33, -1920), (50, 1440), (55, -1920), (59, -720), (79, 720), (80, 1440), (94, 720), (101, 1440)]

def boundaryRow95 : Integer.Sparse (Fin 909) := [(0, -7), (1, -515), (2, 435), (3, 4560), (4, 800), (5, -100), (6, 5), (7, 480), (12, 3200), (13, 3600), (25, -240), (26, 160), (33, -960), (35, 800), (41, 1440), (52, 640), (59, -720), (73, 720), (75, 1440), (94, 720), (101, 1440), (201, -720)]

def boundaryRow96 : Integer.Sparse (Fin 909) := [(0, -22), (1, -465), (2, 365), (3, 4880), (4, 320), (5, -180), (7, 720), (8, 320), (10, -240), (12, 2800), (13, 3920), (23, -720), (25, -240), (27, 180), (33, -960), (35, 320), (38, 1440), (51, -1920), (54, -1920), (55, -480), (59, -1680), (72, 720), (74, 1440), (94, 720), (101, 1440), (199, -720)]

def boundaryRow97 : Integer.Sparse (Fin 909) := [(0, 6), (1, -140), (2, 225), (3, 2560), (4, 800), (5, -260), (6, 15), (7, 1360), (8, 160), (12, 1600), (13, 1040), (23, -480), (25, -960), (26, 720), (35, 1200), (38, 1440), (41, 720), (43, 1440), (52, 560), (54, -720), (84, 720), (97, 1440), (98, 1440), (228, -240)]

def boundaryRow98 : Integer.Sparse (Fin 909) := [(0, 39), (1, -385), (2, 615), (3, 3600), (4, 960), (5, -740), (6, 65), (7, 720), (8, 1120), (12, 560), (13, 240), (23, -240), (26, 640), (31, -720), (33, -480), (35, 560), (44, 1440), (51, -1440), (52, 880), (54, -960), (81, -480), (95, 720), (99, 1440), (100, 1440)]

def boundaryRow99 : Integer.Sparse (Fin 909) := [(0, 24), (1, -795), (2, 495), (3, 4320), (4, 2000), (5, -220), (6, 10), (7, 800), (8, 160), (12, 1120), (13, 960), (25, -960), (26, 1280), (31, -1200), (33, -960), (35, 720), (38, 720), (39, 1440), (41, 1440), (46, 1440), (51, -480), (52, 640), (54, -720), (81, -480), (84, 720), (85, 1440), (95, 720), (103, 1440), (228, -720)]

def boundaryRow100 : Integer.Sparse (Fin 909) := [(0, 44), (1, -690), (2, 385), (3, 4960), (4, 2480), (5, -260), (6, 15), (7, 640), (8, 480), (12, 240), (13, 160), (24, -480), (26, 2160), (31, -480), (35, 320), (37, 2160), (40, 1440), (52, 160), (56, -1200), (81, -960), (83, 720), (85, 1440), (99, 1440), (107, 1440), (228, -960)]

def boundaryRow101 : Integer.Sparse (Fin 909) := [(0, -1), (1, -390), (2, 480), (3, 3520), (4, 1120), (5, -420), (6, 35), (7, 1200), (8, 240), (12, 880), (13, 720), (23, -240), (24, -240), (25, -480), (26, 880), (31, -720), (33, -1440), (35, 1200), (41, 720), (43, 1440), (51, -720), (52, 1120), (54, -480), (59, -480), (73, 720), (81, -480), (94, 1440), (95, 720), (103, 1440), (104, 1440), (201, -240)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow102 : Integer.Sparse (Fin 909) := [(0, 23), (1, -385), (2, 310), (3, 1720), (4, 760), (5, -210), (6, 10), (7, 280), (8, 360), (12, 160), (13, 80), (24, -240), (25, -240), (26, 400), (31, -720), (33, -600), (35, 120), (39, 720), (42, 720), (44, 360), (52, 200), (54, -240), (56, -120), (81, -240), (85, 360), (86, 360), (97, 360), (99, 720), (100, 360), (228, -120)]

def boundaryRow103 : Integer.Sparse (Fin 909) := [(0, 21), (1, -255), (2, 170), (3, 880), (4, 432), (5, -88), (6, 4), (7, 80), (8, 192), (26, 288), (30, -96), (31, -96), (35, 32), (40, 288), (52, 80), (56, -96), (57, 288), (81, -96), (85, 144), (86, 144), (107, 288), (228, -48), (239, 288)]

def boundaryRow104 : Integer.Sparse (Fin 909) := [(0, 3), (1, -113), (2, 53), (3, 640), (4, 240), (5, -26), (6, 1), (7, 72), (8, 32), (12, 200), (13, 144), (25, -72), (26, 176), (33, -120), (35, 80), (37, 144), (38, 144), (39, 288), (40, 288), (51, -48), (52, 64), (54, -48), (55, -240), (81, -48), (84, 72), (85, 144), (89, 144), (104, 72), (228, -72)]

def boundaryRow105 : Integer.Sparse (Fin 909) := [(0, 7), (1, -235), (2, 111), (3, 1424), (4, 464), (5, -60), (6, 3), (7, 160), (8, 96), (12, 352), (13, 144), (23, -96), (25, -144), (26, 416), (31, -96), (33, -480), (35, 80), (36, 288), (37, 288), (39, 576), (40, 576), (52, 32), (54, -144), (55, -480), (81, -192), (83, 144), (85, 288), (87, 288), (100, 288), (228, -192)]

def boundaryRow106 : Integer.Sparse (Fin 909) := [(0, 11), (1, -185), (2, 160), (3, 1680), (4, 360), (5, -90), (7, 480), (8, 120), (12, 880), (13, 80), (23, -360), (24, -600), (25, -360), (27, 180), (31, -240), (33, -240), (35, 80), (48, 360), (51, -600), (54, -240), (100, 720), (105, 720)]

def boundaryRow107 : Integer.Sparse (Fin 909) := [(0, 21), (1, -333), (2, 124), (3, 1072), (4, 672), (5, -36), (7, 192), (8, 48), (12, 192), (23, -144), (24, -240), (25, -288), (26, 128), (27, 72), (31, -672), (35, 32), (46, 576), (47, 144), (51, -240), (54, -96), (97, 288), (106, 288)]

def boundaryRow108 : Integer.Sparse (Fin 909) := [(0, -18), (1, -560), (2, 555), (3, 5200), (4, 720), (5, -440), (6, 25), (7, 1200), (8, 560), (10, -720), (12, 2240), (13, 3200), (26, 640), (33, -960), (35, 1040), (37, 720), (39, 720), (40, 720), (41, 1440), (51, -960), (52, 800), (54, -480), (55, -720), (59, -960), (73, 720), (74, 720), (75, 720), (95, 1440), (102, 720), (103, 720), (201, -240)]

def boundaryRow128 : Integer.Sparse (Fin 909) := [(0, 4), (1, -44), (2, 7), (5, -12), (6, 3), (23, -144), (25, -144), (27, 84), (30, -144), (31, -288), (63, -96), (68, 24), (105, 432), (124, -144), (196, -48), (236, -288), (237, -144)]

def boundaryRow129 : Integer.Sparse (Fin 909) := [(0, 6), (1, -53), (2, 119), (3, 240), (5, -112), (6, 6), (7, 144), (8, 288), (12, 96), (13, 32), (23, -144), (27, 108), (30, -288), (35, 32), (51, -288), (54, -144), (68, 24), (124, -144), (196, -48), (236, -288)]

def boundaryRow130 : Integer.Sparse (Fin 909) := [(0, 37), (1, -930), (2, 975), (3, 4880), (4, 1360), (5, -840), (6, 40), (7, 1760), (8, 1920), (12, 960), (13, 480), (23, -480), (24, -1440), (26, 640), (27, 600), (30, -960), (31, -960), (35, 800), (51, -4320), (52, 320), (54, -960), (55, -480), (56, -1200), (95, 1440), (97, 720), (107, 1440), (238, -720)]

def boundaryRow131 : Integer.Sparse (Fin 909) := [(0, -1), (1, 110), (2, 5), (14, 2160), (23, -2400), (25, -1440), (63, -1440), (68, 60), (124, -960), (129, 1440), (196, -480), (230, 2160)]

def boundaryRow133 : Integer.Sparse (Fin 909) := [(0, -2), (1, -455), (2, 195), (3, 3040), (4, 720), (5, -80), (7, 480), (12, 1840), (13, 480), (15, 2160), (23, -2160), (24, -720), (25, -1440), (27, 420), (33, -1440), (35, 160), (51, -1440), (54, -1440), (63, -480), (68, 60), (124, -720), (126, -240), (144, 1440), (196, -480), (205, 2160)]

def boundaryRow134 : Integer.Sparse (Fin 909) := [(0, 8), (1, -30), (2, 25), (5, -12), (6, 3), (17, 432), (23, -288), (25, -624), (27, 48), (30, -144), (31, -576), (63, -96), (68, 12), (87, 432), (108, 432), (123, -432), (124, -144), (196, -96), (203, 432), (216, 288), (226, -144), (236, -48), (237, -144)]

def boundaryRow135 : Integer.Sparse (Fin 909) := [(0, 52), (1, -425), (2, 55), (17, 2160), (23, -1440), (25, -3600), (27, 480), (30, -960), (31, -4080), (63, -960), (105, 2160), (108, 2160), (123, -720), (231, 1440), (237, -720)]

def boundaryRow138 : Integer.Sparse (Fin 909) := [(0, -9), (1, -845), (2, 530), (3, 6960), (5, -160), (7, 960), (12, 3440), (13, 4560), (16, 2160), (23, -2880), (27, 540), (35, 320), (38, 4320), (51, -2880), (54, -2880), (55, -1440), (68, 60), (124, -720), (125, -240), (140, 2160), (141, 1440), (196, -480)]

def boundaryRow139 : Integer.Sparse (Fin 909) := [(0, 101), (1, -2045), (2, 420), (3, 8560), (4, 3280), (5, -20), (7, 240), (12, 2640), (13, 480), (18, 2160), (23, -1440), (24, -1440), (25, -1440), (26, 1760), (27, 240), (31, -1440), (33, -1440), (35, 160), (43, 4320), (47, 2160), (51, -240), (55, -1440), (63, -480), (143, 1440)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow140 : Integer.Sparse (Fin 909) := [(0, 149), (1, -2280), (2, 265), (3, 6960), (4, 5280), (5, -40), (7, 480), (12, 1200), (13, 320), (23, -1440), (24, -1440), (25, -3600), (26, 2400), (27, 240), (31, -3600), (35, 560), (44, 4320), (55, -2160), (63, -480), (108, 2160), (123, -720)]

def boundaryRow144 : Integer.Sparse (Fin 909) := [(0, 32), (1, -25), (2, 95), (5, -60), (14, 1080), (17, 2160), (23, -1920), (25, -2880), (27, 480), (30, -720), (31, -2160), (63, -240), (108, 2160), (123, -720), (124, -480), (129, 720), (203, 4320), (230, 2160)]

def boundaryRow145 : Integer.Sparse (Fin 909) := [(0, 31), (1, -354), (2, 141), (3, 704), (4, 384), (5, -24), (12, 320), (13, 64), (15, 432), (20, 864), (23, -144), (24, -432), (27, 180), (30, -288), (51, -288), (52, 96), (126, -192), (144, 288), (205, 864), (208, 1728)]

def boundaryRow146 : Integer.Sparse (Fin 909) := [(0, 23), (1, -885), (2, 210), (3, 3840), (4, 1200), (12, 1840), (13, 960), (16, 1080), (17, 2160), (23, -1080), (26, 480), (35, 240), (38, 1080), (40, 2160), (51, -720), (52, 240), (55, -1800), (125, -480), (140, 2160), (141, 720), (146, 4320)]

def boundaryRow147 : Integer.Sparse (Fin 909) := [(0, -1), (1, -11), (2, 21), (5, -24), (6, 3), (17, 216), (23, -72), (25, -96), (27, 90), (28, 432), (30, -360), (31, -144), (203, 432), (216, 144), (236, -96), (253, 864)]

def boundaryRow150 : Integer.Sparse (Fin 909) := [(0, 3), (1, -290), (2, 165), (3, 2080), (4, 640), (5, -60), (7, 320), (12, 1120), (15, 1440), (23, -1680), (24, -1440), (25, -1200), (27, 360), (33, -480), (48, 1440), (51, -480), (55, -960), (68, 60), (124, -480), (126, -480), (137, 1440), (197, -480), (205, 1440), (230, 720)]

def boundaryRow151 : Integer.Sparse (Fin 909) := [(0, 17), (1, -725), (2, 260), (3, 4720), (4, 1120), (5, -120), (7, 640), (12, 2000), (13, 560), (16, 720), (23, -2880), (24, -1920), (27, 540), (47, 2880), (51, -960), (55, -1920), (68, 60), (124, -240), (125, -720), (126, -480), (140, 2160), (205, 1440)]

def boundaryRow152 : Integer.Sparse (Fin 909) := [(0, 9), (1, -160), (2, 40), (3, 1160), (4, 440), (5, -5), (7, 60), (12, 780), (13, 80), (23, -120), (25, -660), (26, 200), (33, -360), (38, 180), (43, 720), (50, 180), (54, -60), (64, -120), (110, 360)]

def boundaryRow153 : Integer.Sparse (Fin 909) := [(0, 47), (1, -1150), (2, 350), (3, 4640), (4, 2480), (5, -120), (6, 5), (7, 240), (8, 160), (12, 1120), (21, 1440), (23, -480), (24, -960), (25, -240), (26, 720), (27, 360), (31, -1680), (33, -480), (35, 160), (43, 720), (47, 1440), (48, 720), (51, -2880), (52, 240), (54, -480), (56, -1200), (97, 720), (191, 1440), (209, 1440), (238, -240)]

def boundaryRow156 : Integer.Sparse (Fin 909) := [(0, 9), (1, -206), (2, 31), (3, 1088), (4, 432), (5, -4), (7, 48), (12, 464), (13, 144), (18, 288), (23, -240), (24, -288), (25, -144), (26, 32), (27, 36), (33, -96), (35, 32), (47, 288), (48, 144), (50, 432), (51, -48), (55, -384), (113, 144), (177, 288)]

def boundaryRow157 : Integer.Sparse (Fin 909) := [(0, 32), (1, -825), (2, 235), (3, 4960), (4, 1760), (12, 3520), (13, 1440), (25, -1920), (26, 400), (33, -1440), (34, 160), (41, 720), (43, 2880), (50, 1440), (114, 720), (116, 1440)]

def boundaryRow158 : Integer.Sparse (Fin 909) := [(0, 29), (1, -340), (2, 105), (3, 1560), (4, 760), (12, 440), (13, 440), (26, 320), (31, -540), (33, -360), (34, 160), (42, 360), (44, 360), (45, 360), (115, 180), (119, 360), (120, 360)]

def boundaryRow161 : Integer.Sparse (Fin 909) := [(0, 116), (1, -1215), (2, 325), (3, 3200), (4, 2000), (5, -60), (7, 240), (8, 160), (12, 800), (13, 160), (22, 1440), (26, 480), (31, -2880), (35, 160), (43, 1440), (46, 1440), (47, 720), (49, 1440), (51, -1680), (56, -240), (97, 720), (107, 1440), (204, 1440), (238, -720)]

def boundaryRow162 : Integer.Sparse (Fin 909) := [(0, 29), (1, -1090), (2, 335), (3, 4880), (4, 2000), (12, 2080), (13, 1200), (25, -2880), (26, 800), (31, -2160), (33, -2400), (34, 320), (38, 720), (39, 1440), (43, 1440), (46, 1440), (50, 1440), (54, -720), (64, -720), (110, 720), (112, 1440), (115, 720), (116, 1440)]

def boundaryRow165 : Integer.Sparse (Fin 909) := [(0, 21), (1, -1115), (2, 610), (3, 5520), (4, 2560), (5, -220), (7, 320), (8, 640), (12, 2160), (13, 1360), (15, 1440), (23, -720), (24, -1440), (25, -960), (27, 360), (31, -1920), (33, -2400), (39, 2880), (42, 2880), (51, -2880), (55, -960), (56, -2400), (64, -480), (68, 60), (97, 1440), (110, 1440), (124, -240), (125, -240), (126, -480), (140, 720), (144, 1440), (145, 1440), (197, -480), (238, -480)]

def boundaryRow166 : Integer.Sparse (Fin 909) := [(0, 37), (1, -406), (2, 139), (3, 1216), (4, 704), (12, 384), (13, 16), (25, -144), (26, 224), (31, -576), (33, -96), (34, 32), (43, 288), (45, 576), (46, 576), (50, 144), (115, 288), (116, 288)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow167 : Integer.Sparse (Fin 909) := [(0, 126), (1, -2265), (2, 305), (3, 7920), (4, 5120), (5, -20), (7, 240), (12, 2320), (21, 1440), (23, -1200), (24, -1440), (25, -2640), (26, 2000), (27, 180), (31, -1680), (33, -480), (35, 160), (43, 2160), (44, 4320), (47, 720), (48, 1440), (51, -240), (55, -1920), (113, 720), (114, 1440), (191, 1440)]

def boundaryRow168 : Integer.Sparse (Fin 909) := [(0, 39), (1, -1590), (2, 670), (3, 8160), (4, 2720), (5, -100), (6, 5), (7, 160), (8, 160), (12, 3200), (13, 3440), (18, 1440), (23, -240), (24, -480), (25, -1200), (26, 320), (27, 180), (31, -1920), (33, -2400), (35, 240), (38, 720), (39, 1440), (42, 4320), (47, 720), (51, -2400), (52, 240), (54, -720), (55, -720), (56, -1200), (64, -480), (97, 720), (110, 1440), (142, 1440), (143, 1440), (238, -240)]

def boundaryRow169 : Integer.Sparse (Fin 909) := [(0, 102), (1, -1245), (2, 365), (3, 3440), (4, 2120), (12, 1280), (13, 240), (25, -480), (26, 320), (31, -1440), (33, -720), (34, 80), (44, 720), (45, 2160), (46, 720), (114, 360), (115, 720), (120, 720)]

def boundaryRow171 : Integer.Sparse (Fin 909) := [(0, 9), (1, -341), (2, 78), (3, 1568), (4, 592), (5, -28), (6, 2), (7, 48), (8, 32), (12, 608), (13, 608), (22, 288), (23, -48), (24, -96), (25, -192), (26, 224), (27, 36), (31, -288), (33, -384), (35, 160), (36, 144), (39, 576), (42, 576), (51, -384), (52, 64), (54, -432), (55, -144), (56, -336), (97, 144), (204, 288), (217, 288), (238, -48)]

def boundaryRow173 : Integer.Sparse (Fin 909) := [(0, 9), (1, -307), (2, 90), (3, 1280), (4, 528), (5, -44), (6, 4), (7, 64), (8, 64), (12, 400), (13, 288), (17, 288), (22, 288), (23, -48), (24, -288), (25, -144), (26, 224), (27, 48), (31, -288), (33, -240), (35, 96), (39, 576), (42, 576), (51, -288), (52, 64), (54, -96), (55, -192), (56, -240), (68, 12), (97, 144), (99, 288), (123, -96), (124, -48), (126, -96), (137, 144), (146, 288), (197, -144), (204, 288), (216, 288), (217, 288), (237, -96), (238, -48)]

def boundaryRow175 : Integer.Sparse (Fin 909) := [(0, 53), (1, -1175), (2, 470), (3, 4400), (4, 2400), (5, -160), (7, 480), (8, 320), (12, 1520), (15, 720), (23, -1680), (24, -1680), (25, -3360), (26, 320), (27, 420), (31, -2880), (33, -1200), (44, 1440), (48, 2880), (51, -1920), (54, -960), (55, -960), (64, -480), (68, 60), (100, 1440), (125, -720), (126, -720), (137, 1440), (145, 720), (207, 1440), (238, -480)]

def boundaryRow176 : Integer.Sparse (Fin 909) := [(0, 54), (1, -1555), (2, 420), (3, 6320), (4, 3040), (5, -100), (6, 5), (7, 320), (8, 80), (12, 2400), (13, 560), (18, 720), (23, -960), (24, -480), (25, -3360), (26, 720), (27, 240), (31, -2640), (33, -1200), (35, 240), (43, 720), (44, 720), (47, 720), (48, 1440), (50, 1440), (51, -2160), (52, 240), (54, -960), (55, -480), (56, -480), (64, -480), (100, 720), (104, 720), (142, 720), (177, 1440), (209, 720), (238, -240)]

def boundaryRow183 : Integer.Sparse (Fin 909) := [(0, 2), (1, -173), (2, 136), (3, 1264), (4, 480), (5, -72), (6, 3), (7, 240), (8, 112), (12, 128), (13, 128), (15, 144), (23, -48), (24, -192), (25, -96), (26, 528), (27, 36), (31, -192), (33, -384), (34, 112), (35, 80), (37, 288), (51, -288), (52, 32), (55, -144), (64, -96), (68, 12), (107, 288), (112, 288), (125, -48), (126, -144), (137, 288), (138, 144), (145, 144), (146, 144), (197, -48), (236, -48), (238, -96)]

def boundaryRow184 : Integer.Sparse (Fin 909) := [(0, 103), (1, -1580), (2, 560), (3, 7920), (4, 3840), (5, -40), (6, 5), (12, 720), (13, 480), (18, 720), (26, 3920), (31, -480), (33, -960), (34, 720), (35, 160), (52, 160), (53, 1440), (55, -480), (57, 1440), (119, 1440), (139, 720), (177, 1440)]

def boundaryRow187 : Integer.Sparse (Fin 909) := [(0, 71), (1, -1455), (2, 410), (3, 8000), (4, 3920), (5, -80), (6, 10), (7, 160), (8, 80), (12, 560), (13, 560), (21, 720), (26, 4080), (31, -960), (33, -1440), (34, 720), (35, 320), (37, 1440), (40, 720), (51, -240), (52, 80), (53, 1440), (55, -720), (56, -480), (57, 720), (119, 1440), (190, 720), (204, 720)]

def boundaryRow240 : Integer.Sparse (Fin 909) := [(0, 1), (1, -49), (2, -91), (3, -48), (5, 276), (6, -54), (7, -48), (8, -96), (9, 284), (35, -96), (52, -192), (58, -11), (69, -96), (70, -32), (71, -192), (278, -48), (310, -144), (495, -192), (726, 144), (818, 288)]

def boundaryRow241 : Integer.Sparse (Fin 909) := [(0, 9), (1, -255), (2, -530), (3, -480), (5, 1520), (6, -180), (7, -1920), (8, -1920), (9, 740), (35, -640), (58, -20), (69, -2400), (70, -1280), (71, -3840), (277, 720), (278, -240)]

def boundaryRow242 : Integer.Sparse (Fin 909) := [(1, 3), (2, -28), (3, -192), (4, -48), (5, 76), (6, -12), (7, -144), (9, 28), (11, -48), (26, -96), (35, -224), (52, -144), (58, -1), (69, -96), (70, -64), (228, 144), (278, -48), (310, -48), (495, -96), (726, 144)]

def boundaryRow243 : Integer.Sparse (Fin 909) := [(0, -1), (1, 70), (2, -25), (3, -1440), (4, -480), (5, 420), (6, -75), (9, 100), (11, -480), (26, -960), (35, -1440), (52, -1280), (55, 720), (58, -5), (228, 1440), (278, -80), (727, 720), (728, 480)]

def boundaryRow244 : Integer.Sparse (Fin 909) := [(0, 6), (1, -105), (2, -260), (3, -1440), (5, 480), (6, -90), (7, -480), (9, 120), (12, -480), (13, -2160), (35, -1680), (52, -1440), (54, 720), (58, -5), (69, -240), (70, -160), (82, -1280), (128, -1200), (199, 1440), (201, 1440), (278, -320), (310, -240), (492, 720), (495, -480), (723, 480), (726, 720)]

def boundaryRow245 : Integer.Sparse (Fin 909) := [(0, 1), (1, -80), (2, -270), (3, -480), (4, -80), (5, 560), (6, -60), (7, -720), (8, -800), (9, 180), (35, -160), (51, 720), (52, -240), (58, -5), (69, -480), (70, -160), (71, -960), (308, 720), (309, 480), (310, -80)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow246 : Integer.Sparse (Fin 909) := [(0, 6), (1, -185), (2, -235), (3, -400), (4, -80), (5, 440), (6, -90), (8, -320), (9, 300), (11, -80), (13, -320), (26, -160), (35, -480), (52, -880), (56, 480), (58, -10), (69, -80), (71, -320), (82, -320), (128, -400), (201, 960), (228, 240), (278, -80), (310, -160), (492, 240), (495, -160), (796, 960), (818, 480)]

def boundaryRow247 : Integer.Sparse (Fin 909) := [(0, -1), (1, -15), (2, -190), (3, -640), (4, -160), (5, 320), (6, -35), (7, -480), (8, -320), (9, 100), (26, -160), (27, -60), (35, -320), (51, 480), (52, -480), (58, -5), (68, -60), (69, -320), (71, -160), (124, 240), (126, 480), (308, 480), (310, -160), (493, 480), (495, -160)]

def boundaryRow248 : Integer.Sparse (Fin 909) := [(0, 1), (1, 60), (2, -15), (3, -1120), (4, -320), (5, 420), (6, -25), (9, 60), (11, -320), (26, -800), (27, -120), (35, -1120), (52, -320), (55, 240), (58, -5), (68, -120), (238, 960), (278, -80), (493, 480), (495, -160), (727, 240)]

def boundaryRow249 : Integer.Sparse (Fin 909) := [(0, 7), (1, -55), (2, -175), (3, -1040), (5, 460), (6, -60), (7, -400), (8, -160), (9, 80), (12, -320), (13, -1360), (35, -720), (51, 480), (52, -960), (54, 240), (58, -5), (68, -60), (69, -160), (70, -160), (71, -80), (82, -320), (125, 480), (126, 240), (128, -400), (278, -80), (309, 480), (310, -160), (492, 240), (494, 480), (495, -160)]

def boundaryRow250 : Integer.Sparse (Fin 909) := [(0, 1), (1, 64), (2, -38), (3, -640), (4, -192), (5, 24), (6, -3), (12, -192), (13, -256), (26, -192), (27, -36), (35, -192), (51, 576), (52, -192), (55, 576), (127, 144), (128, -48), (493, 576), (494, 384), (495, -64)]

def boundaryRow251 : Integer.Sparse (Fin 909) := [(0, 3), (1, -45), (2, -200), (3, -400), (5, 700), (6, -60), (7, -80), (8, -480), (9, 160), (27, -180), (52, -480), (58, -10), (68, -180), (69, -80), (71, -400), (126, 240), (236, 480), (237, 480), (308, 240), (310, -80)]

def boundaryRow252 : Integer.Sparse (Fin 909) := [(0, 8), (1, -40), (2, -40), (3, -560), (5, 420), (6, -25), (9, 60), (11, -160), (12, -80), (13, -720), (26, -320), (35, -880), (52, -560), (55, 240), (58, -5), (68, -120), (82, -160), (128, -160), (237, 480), (278, -80), (494, 480), (495, -160), (728, 240)]

def boundaryRow253 : Integer.Sparse (Fin 909) := [(0, 6), (1, -5), (2, -15), (3, -480), (4, -80), (5, 480), (6, -30), (7, -160), (8, -160), (9, 140), (11, -160), (13, -320), (26, -480), (35, -960), (52, -160), (56, 240), (58, -10), (68, -180), (70, -160), (71, -240), (82, -160), (197, 480), (236, 240), (238, 240), (278, -80), (309, 240), (310, -80), (796, 240)]

def boundaryRow261 : Integer.Sparse (Fin 909) := [(0, 1), (1, -33), (2, -51), (3, -48), (5, 148), (6, -15), (7, -144), (8, -192), (9, 36), (35, -80), (52, -96), (69, -288), (70, -112), (71, -432), (256, 144), (257, -32), (495, -48)]

def boundaryRow262 : Integer.Sparse (Fin 909) := [(0, 2), (1, -15), (2, -10), (3, -280), (5, 170), (6, -25), (7, -360), (9, 50), (13, -120), (26, -120), (35, -560), (52, -240), (54, 360), (60, -80), (69, -360), (70, -320), (71, -240), (257, -80), (259, 360), (260, 240), (495, -40)]

def boundaryRow263 : Integer.Sparse (Fin 909) := [(0, 9), (1, -225), (2, -300), (3, -480), (4, -80), (5, 840), (6, -100), (7, -320), (8, -960), (9, 80), (13, -320), (26, -80), (35, -400), (51, 240), (52, -880), (56, 480), (59, 480), (69, -560), (70, -80), (71, -1200), (128, -160), (256, 240), (259, 240), (262, 960), (495, -160)]

def boundaryRow264 : Integer.Sparse (Fin 909) := [(0, 3), (1, -30), (2, -80), (3, -560), (4, -80), (5, 260), (6, -25), (7, -640), (8, -320), (9, 40), (26, -240), (35, -720), (52, -240), (67, -160), (69, -400), (70, -240), (71, -320), (81, 240), (256, 240), (257, -80), (495, -80)]

def boundaryRow265 : Integer.Sparse (Fin 909) := [(1, -1), (2, 12), (6, 1), (9, 4), (13, -160), (32, -32), (35, -96), (60, -64), (63, 144), (70, -64), (196, 144), (257, -32), (264, 96)]

def boundaryRow266 : Integer.Sparse (Fin 909) := [(0, 7), (1, 60), (2, 40), (3, -1280), (5, 140), (6, -35), (7, -480), (9, 20), (12, -240), (13, -640), (26, -800), (34, -480), (35, -1360), (55, 720), (60, -160), (67, -480), (70, -240), (71, -80), (197, 720), (257, -160), (268, 480)]

def boundaryRow267 : Integer.Sparse (Fin 909) := [(0, -2), (1, 315), (2, -60), (3, -4080), (4, -960), (5, 220), (6, -45), (7, -960), (9, 20), (13, -1200), (26, -2880), (34, -1280), (35, -2000), (52, -480), (55, 720), (64, 1440), (67, -960), (69, -80), (70, -240), (125, 720), (257, -160), (266, 480)]

def boundaryRow268 : Integer.Sparse (Fin 909) := [(0, 3), (1, 20), (2, 35), (3, -480), (5, 200), (6, -40), (7, -480), (9, 80), (13, -160), (26, -480), (34, -160), (35, -960), (54, 480), (67, -320), (69, -160), (70, -320), (71, -160), (124, 240), (196, 240), (197, 480), (257, -160), (259, 480), (266, 480), (495, -160)]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_IntegerTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def integerTerm0 : Integer.Sparse (Fin 909) := [(0, 23514624), (1, -9797760), (2, -9797760), (5, 19595520), (27, -58786560), (68, -117573120)]

def integerTerm1 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -16329600), (2, 3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 39191040), (236, 156764160)]

def integerTerm2 : Integer.Sparse (Fin 909) := [(0, -3265920), (1, -1632960), (2, 1632960), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 19595520), (126, 78382080)]

def integerTerm3 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm4 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm5 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -16329600), (2, 3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 39191040), (236, 156764160)]

def integerTerm6 : Integer.Sparse (Fin 909) := [(0, 13934592), (1, 21772800), (2, -4354560), (5, 2177280), (8, 17418240), (27, -6531840), (28, -78382080), (30, -26127360), (68, -13063680), (236, -104509440), (253, -156764160)]

def integerTerm7 : Integer.Sparse (Fin 909) := [(0, -2395008), (2, 1088640), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -6531840), (126, -26127360), (208, -78382080), (236, -26127360)]

def integerTerm8 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm9 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm10 : Integer.Sparse (Fin 909) := [(0, -3265920), (1, -1632960), (2, 1632960), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 19595520), (126, 78382080)]

def integerTerm11 : Integer.Sparse (Fin 909) := [(0, -2395008), (2, 1088640), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -6531840), (126, -26127360), (208, -78382080), (236, -26127360)]

def integerTerm12 : Integer.Sparse (Fin 909) := [(0, 3646944), (1, -3538080), (2, -1632960), (3, 8709120), (4, 8709120), (5, 544320), (8, 4354560), (12, 4354560), (17, -19595520), (24, -13063680), (27, -1632960), (30, 6531840), (68, -3265920), (126, -26127360), (203, -39191040)]

def integerTerm13 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm14 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm15 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm16 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm17 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm18 : Integer.Sparse (Fin 909) := [(0, 6069168), (1, -5579280), (2, 3538080), (3, 4354560), (4, 4354560), (68, -3265920), (126, -13063680), (203, -19595520), (236, -13063680), (253, -19595520)]

def integerTerm19 : Integer.Sparse (Fin 909) := [(0, 1088640), (1, -1632960), (2, 544320), (68, -3265920), (126, -13063680), (208, -39191040), (236, -13063680)]

def integerTerm20 : Integer.Sparse (Fin 909) := [(0, -5552064), (1, 4898880), (2, -3265920), (68, 19595520), (126, 39191040), (236, 39191040)]

def integerTerm21 : Integer.Sparse (Fin 909) := [(0, -3483648), (1, -544320), (2, -544320), (68, -6531840), (126, -13063680), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerTerm22 : Integer.Sparse (Fin 909) := [(0, 408240), (1, -1224720), (2, 272160), (4, 2177280), (31, -6531840), (68, -3265920), (126, -19595520), (207, -19595520), (208, -19595520), (236, -6531840)]

def integerTerm23 : Integer.Sparse (Fin 909) := [(0, 1088640), (1, -1632960), (2, 544320), (68, -3265920), (126, -13063680), (208, -39191040), (236, -13063680)]

def integerTerm24 : Integer.Sparse (Fin 909) := [(0, 6069168), (1, -5579280), (2, 3538080), (3, 4354560), (4, 4354560), (68, -3265920), (126, -13063680), (203, -19595520), (236, -13063680), (253, -19595520)]

def integerTerm25 : Integer.Sparse (Fin 909) := [(0, -326592), (1, -6713280), (2, 1224720), (3, -8709120), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (58, 45360), (68, 1088640), (69, -2903040), (230, 6531840)]

def integerTerm26 : Integer.Sparse (Fin 909) := [(0, -18144), (1, -5806080), (2, 544320), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (35, -5806080), (63, -8709120)]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoSparse
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def encode (a : Charge) : List ℤ := List.ofFn a

def decode (l : List ℤ) : Charge := fun i => l[i.val]?.getD 0

@[simp] theorem decode_encode (a : Charge) : decode (encode a) = a := by
  funext i
  fin_cases i <;> simp [decode, encode]

abbrev Sparse := Certificate.Integer.Sparse (List ℤ)

def momentValues (f : Charge → ℂ) (key : List ℤ) : ℝ :=
  if key.headD 0 = 0 then (f (decode key.tail)).re
  else (omega * f (decode key.tail)).re

def offDiagonalPairs : List (Coord × Coord) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),
   (1,0),(1,2),(1,3),(1,4),(1,5),
   (2,0),(2,1),(2,3),(2,4),(2,5),
   (3,0),(3,1),(3,2),(3,4),(3,5),
   (4,0),(4,1),(4,2),(4,3),(4,5),
   (5,0),(5,1),(5,2),(5,3),(5,4)]

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined0_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -36), ([0, -1, -2, 0, 0, 1, 2], 27), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -36), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -1, -2, 0, 0, 1, 2], 27), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 27)]

def combined0_part1 : Sparse := [([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, 0, -2, 0, 0, 1, 1], -36), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9)]

def combined0 : Sparse := combined0_part0 ++ combined0_part1

def combined1_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -27), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -2, 0, 0, 1, 2], 27), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -27), ([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, 0, 0, 0, 1, 1], 18)]

def combined1_part1 : Sparse := [([1, -1, -2, 0, 0, 1, 2], 27), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9)]

def combined1 : Sparse := combined1_part0 ++ combined1_part1

def combined2_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -18), ([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -2, 0, 0, 1, 2], 18), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], 18), ([0, -1, -1, 0, -1, 1, 2], -18), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -27)]

def combined2_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, 0, 0, 0, 1, 1], 9), ([1, -1, -2, 0, 0, 1, 2], 18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, 0, -1, 1, 2], -18), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18)]

def combined2 : Sparse := combined2_part0 ++ combined2_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined10_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 1, 2, 0], -18), ([0, -2, -1, 0, 2, 1, 0], -27), ([0, -2, -1, 1, 1, 1, 0], -18), ([0, -1, -2, 0, 1, 1, 1], -18), ([0, -1, -2, 0, 1, 2, 0], -18), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -18), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 1, 2, -1], -18), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -18)]

def combined10_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -18), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, 0, 0, 1, 1, 0], 9), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 2, -1], -18), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], 9)]

def combined10 : Sparse := combined10_part0 ++ combined10_part1

def combined11_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -18), ([0, -2, -1, 0, 1, 2, 0], -18), ([0, -2, -1, 0, 2, 1, 0], -18), ([0, -2, -1, 1, 1, 1, 0], -18), ([0, -1, -2, 0, 1, 1, 1], -18), ([0, -1, -2, 0, 1, 2, 0], -18), ([0, -1, -2, 0, 2, 1, 0], -18), ([0, -1, -2, 1, 1, 1, 0], -18), ([0, -1, -1, -1, 1, 2, 0], -18), ([0, -1, -1, -1, 2, 1, 0], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 1, 2, -1], -18), ([0, -1, -1, 0, 2, 1, -1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 0, 0], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18)]

def combined11_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -18), ([1, -2, -1, 1, 1, 1, 0], -18), ([1, -1, -2, 0, 1, 1, 1], -18), ([1, -1, -2, 1, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 2, 1, 0], -18), ([1, -1, -1, 0, 1, 2, -1], -18), ([1, -1, -1, 0, 2, 1, -1], -18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], -18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 0, 1, 0, 0], -18)]

def combined11 : Sparse := combined11_part0 ++ combined11_part1

def combined12_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -36), ([0, -2, -1, 2, 0, 0, 1], -36), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -27), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -2, 1, 0, 0, 1], -36), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -2, 1, 0, 1, 1], 9)]

def combined12_part1 : Sparse := [([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, 0, -2, 1, 0, 0, 1], -36), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined12 : Sparse := combined12_part0 ++ combined12_part1

def combined13_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -27), ([0, -2, -1, 2, 0, 0, 1], -27), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -27), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18)]

def combined13_part1 : Sparse := [([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], -18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined13 : Sparse := combined13_part0 ++ combined13_part1

def combined14_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -18), ([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 2, 0, 0, 1], -27), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -1, -2, 1, 0, 0, 2], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -18), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 18), ([1, -2, 0, 1, 0, 0, 1], -9)]

def combined14_part1 : Sparse := [([1, -1, -2, 1, 0, 1, 1], 18), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 1, -1, 0, 2], 18), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], 18), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined14 : Sparse := combined14_part0 ++ combined14_part1

def combined15 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -18), ([0, -2, -1, 2, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -18), ([0, -1, -2, 2, 0, 0, 1], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([1, -2, -1, 1, 0, 1, 1], 18), ([1, -2, -1, 1, 1, 0, 1], 18), ([1, -1, -2, 1, 0, 1, 1], 18), ([1, -1, -2, 1, 1, 0, 1], 18), ([1, -1, -1, 1, -1, 0, 2], 18), ([1, -1, -1, 1, 0, -1, 2], 18), ([1, -1, -1, 2, -1, 0, 1], 18), ([1, -1, -1, 2, 0, -1, 1], 18), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 1, 0, 0, 0], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined16_part0 : Sparse := [([0, -2, -1, 1, 0, 2, 0], -36), ([0, -2, -1, 2, 0, 1, 0], 36), ([0, -2, 0, 1, 0, 1, 0], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, -1, 2, 0, 1, 0], 36), ([1, -2, 0, 1, 0, 1, 0], -18), ([1, -1, -2, 1, 0, 2, 0], -27), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 1, 1], 9)]

def combined16_part1 : Sparse := [([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, 0, -2, 1, 0, 1, 0], 36), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27)]

def combined16 : Sparse := combined16_part0 ++ combined16_part1

def combined17_part0 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 0, 2, 0], -27), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -2, -1, 2, 0, 1, 0], 27), ([0, -2, 0, 1, 0, 1, 0], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, -1, 2, 0, 1, 0], 27), ([1, -2, 0, 1, 0, 1, 0], -18)]

def combined17_part1 : Sparse := [([1, -1, -2, 1, 0, 2, 0], -27), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, 0, -2, 1, 0, 1, 0], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27)]

def combined17 : Sparse := combined17_part0 ++ combined17_part1

def combined18_part0 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -18), ([0, -2, -1, 1, 0, 2, 0], -18), ([0, -2, -1, 1, 1, 1, 0], 18), ([0, -2, -1, 2, 0, 1, 0], 27), ([0, -2, 0, 1, 0, 1, 0], -9), ([0, -1, -2, 1, 0, 1, 1], 18), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, -1, 2, 0], 18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, -1, 1, 1, 1, 0], 9)]

def combined18_part1 : Sparse := [([1, -2, -1, 2, 0, 1, 0], 27), ([1, -2, 0, 1, 0, 1, 0], -9), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 0, 2, 0], -18), ([1, -1, -2, 1, 1, 1, 0], 18), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 2, -1], 18), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -18)]

def combined18 : Sparse := combined18_part0 ++ combined18_part1

def combined19_part0 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -18), ([0, -2, -1, 1, 0, 2, 0], -18), ([0, -2, -1, 1, 1, 1, 0], 18), ([0, -2, -1, 2, 0, 1, 0], 18), ([0, -1, -2, 1, 0, 1, 1], 18), ([0, -1, -2, 2, 0, 1, 0], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, -1, 2, -1, 1, 0], -18), ([0, -1, -1, 2, 0, 1, -1], 18), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, 0, 0], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, 0, 0], 18), ([1, -2, -1, 1, 0, 1, 1], -18), ([1, -2, -1, 2, 0, 1, 0], 18), ([1, -1, -2, 1, 0, 2, 0], -18), ([1, -1, -2, 1, 1, 1, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18)]

def combined19_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], 18), ([1, -1, -1, 2, -1, 1, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 1, 0, 0, 0], -18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, 0, 1, -1], -18)]

def combined19 : Sparse := combined19_part0 ++ combined19_part1

def combined20_part0 : Sparse := [([0, -2, -1, 2, 1, 0, 0], -36), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], -27), ([0, -1, -2, 2, 1, 0, 0], 27), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, 0, -2, 1, 1, 0, 0], -36), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -27), ([1, -2, -1, 1, 2, 0, 0], -36), ([1, -2, 0, 1, 1, 0, 0], 18), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 2, 1, 0, 0], 27), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 1, 1, 0], -36)]

def combined20_part1 : Sparse := [([1, -1, -1, 0, 2, 0, 0], 27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, 0, -2, 1, 1, 0, 0], -36), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27)]

def combined20 : Sparse := combined20_part0 ++ combined20_part1

def combined21_part0 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 2, 1, 0, 0], -27), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], -27), ([0, -1, -2, 2, 1, 0, 0], 27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, 0, -2, 1, 1, 0, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -27), ([1, -2, -1, 1, 1, 1, 0], 9), ([1, -2, -1, 1, 2, 0, 0], -27), ([1, -2, 0, 1, 1, 0, 0], 18)]

def combined21_part1 : Sparse := [([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 2, 1, 0, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, 0, -2, 1, 1, 0, 0], -18), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27)]

def combined21 : Sparse := combined21_part0 ++ combined21_part1

def combined22_part0 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 18), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -2, -1, 2, 1, 0, 0], -27), ([0, -1, -2, 1, 1, 0, 1], -18), ([0, -1, -2, 1, 1, 1, 0], 18), ([0, -1, -2, 1, 2, 0, 0], -18), ([0, -1, -2, 2, 1, 0, 0], 27), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 2, -1, 0], 18), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, -1, 1, 1, 1, 0], 18)]

def combined22_part1 : Sparse := [([1, -2, -1, 1, 2, 0, 0], -18), ([1, -2, 0, 1, 1, 0, 0], 9), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -2, 2, 1, 0, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 1, 2, 0, -1], 18), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], 18), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, 0, -2, 1, 1, 0, 0], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 1, 1, 0, -1], 9)]

def combined22 : Sparse := combined22_part0 ++ combined22_part1

def combined23_part0 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 18), ([0, -2, -1, 2, 1, 0, 0], -18), ([0, -1, -2, 1, 1, 0, 1], -18), ([0, -1, -2, 1, 1, 1, 0], 18), ([0, -1, -2, 1, 2, 0, 0], -18), ([0, -1, -2, 2, 1, 0, 0], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 2, -1, 0], 18), ([0, -1, -1, 2, 1, -1, 0], -18), ([0, -1, -1, 2, 1, 0, -1], 18), ([0, -1, 0, 1, 0, 0, 0], 18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([1, -2, -1, 1, 1, 1, 0], 18), ([1, -2, -1, 1, 2, 0, 0], -18), ([1, -1, -2, 1, 1, 0, 1], -18), ([1, -1, -2, 2, 1, 0, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18)]

def combined23_part1 : Sparse := [([1, -1, -1, 1, 2, 0, -1], 18), ([1, -1, -1, 2, 1, -1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, -1, 1, 1, -1, 0], 18)]

def combined23 : Sparse := combined23_part0 ++ combined23_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined24_part0 : Sparse := [([0, -2, 0, -1, 0, 1, 2], -36), ([0, -2, 0, -1, 0, 2, 1], -36), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, 0, -2, 0, 1, 2], -27), ([0, -1, 0, -2, 0, 2, 1], -27), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 1, -2, 0, 1, 1], -9), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 0, 1, 0], -9), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, 0, -2, 1, 1, 1], -9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, -1, 0, 0, 2], 27)]

def combined24_part1 : Sparse := [([1, -1, 0, -1, 0, 2, 0], 27), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, 0, 0, -2, 0, 1, 1], 36), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 0, 1, 0], -9)]

def combined24 : Sparse := combined24_part0 ++ combined24_part1

def combined25_part0 : Sparse := [([0, -2, 0, -1, 0, 1, 2], -27), ([0, -2, 0, -1, 0, 2, 1], -27), ([0, -2, 0, -1, 1, 1, 1], -9), ([0, -2, 1, -1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, 0, -2, 0, 1, 2], -27), ([0, -1, 0, -2, 0, 2, 1], -27), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, -1, -1, 2, 1], -9), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 1, -2, 0, 1, 1], -9), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 0, 1, 0], -9)]

def combined25_part1 : Sparse := [([1, -2, 0, -1, 1, 1, 1], -9), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -2, 1, -1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 0, 2, 1], -9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, 0, -2, 1, 1, 1], -9), ([1, -1, 0, -1, -1, 1, 2], -9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, -1, 0, 0, 2], 18), ([1, -1, 0, -1, 0, 2, 0], 18), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, 0, 0, -2, 0, 1, 1], 18), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 0, 1, 0], -9)]

def combined25 : Sparse := combined25_part0 ++ combined25_part1

def combined26_part0 : Sparse := [([0, -2, 0, -1, 0, 1, 2], -18), ([0, -2, 0, -1, 0, 2, 1], -27), ([0, -2, 0, -1, 1, 1, 1], -18), ([0, -2, 1, -1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], -18), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, 0, -2, 0, 1, 2], -18), ([0, -1, 0, -2, 0, 2, 1], -27), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -1, -1, 1, 2], -18), ([0, -1, 0, -1, -1, 2, 1], -9), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 1, -2, 0, 1, 1], -18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, -1, 0, 1, 0], -9)]

def combined26_part1 : Sparse := [([1, -2, 0, -1, 1, 1, 1], -9), ([1, -2, 0, 0, 0, 1, 1], 9), ([1, -2, 1, -1, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 1, 2], -18), ([1, -1, -1, -1, 0, 2, 1], -9), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, 0, -2, 1, 1, 1], -18), ([1, -1, 0, -1, -1, 1, 2], -18), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, -1, 0, 0, 2], 18), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, 0, -2, 0, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 0, -1, 0, 1, 0], -9)]

def combined26 : Sparse := combined26_part0 ++ combined26_part1

def combined27_part0 : Sparse := [([0, -2, 0, -1, 0, 1, 2], -18), ([0, -2, 0, -1, 0, 2, 1], -18), ([0, -2, 0, -1, 1, 1, 1], -18), ([0, -2, 1, -1, 0, 1, 1], -18), ([0, -1, -1, -1, 0, 1, 2], -18), ([0, -1, -1, -1, 0, 2, 1], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, -2, 0, 1, 2], -18), ([0, -1, 0, -2, 0, 2, 1], -18), ([0, -1, 0, -2, 1, 1, 1], -18), ([0, -1, 0, -1, -1, 1, 2], -18), ([0, -1, 0, -1, -1, 2, 1], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 1, -2, 0, 1, 1], -18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, -1, 0, 1, 0], -18)]

def combined27_part1 : Sparse := [([1, -2, 0, -1, 1, 1, 1], -18), ([1, -2, 1, -1, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 1, 2], -18), ([1, -1, -1, -1, 0, 2, 1], -18), ([1, -1, 0, -2, 1, 1, 1], -18), ([1, -1, 0, -1, -1, 1, 2], -18), ([1, -1, 0, -1, -1, 2, 1], -18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 1, -2, 0, 1, 1], -18), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 0, -1, 0, 1, 0], -18)]

def combined27 : Sparse := combined27_part0 ++ combined27_part1

def combined28_part0 : Sparse := [([0, -2, 0, -1, 1, 0, 2], -36), ([0, -2, 0, -1, 2, 0, 1], 36), ([0, -2, 0, 0, 1, 0, 1], -18), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, 0, -2, 2, 0, 1], -27), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], 9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, -1, 2, -1, 1], -9), ([0, -1, 0, -1, 2, 0, 0], -27), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 1, -2, 1, 0, 1], 9), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], 9), ([1, -2, 0, -1, 2, 0, 1], 36), ([1, -2, 0, 0, 1, 0, 1], -18), ([1, -1, -1, -1, 1, 0, 2], 9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 2, 0, 1], 9)]

def combined28_part1 : Sparse := [([1, -1, 0, -2, 1, 0, 2], -27), ([1, -1, 0, -2, 1, 1, 1], 9), ([1, -1, 0, -1, 0, 0, 2], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, -1, 1, -1, 2], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 2, 0, 0], -27), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, 0, -2, 1, 0, 1], 36), ([1, 0, 0, -1, 0, 0, 1], 9)]

def combined28 : Sparse := combined28_part0 ++ combined28_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined100_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -18), ([0, -2, 1, 0, 2, -1, 0], 36), ([0, -2, 2, 0, 1, -1, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 2, -1, 0], -27), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 0, 2, -2, 0], -27), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([1, -2, 1, 0, 1, 0, 0], -18), ([1, -2, 1, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 0, 0, 2, -1, 0], -27), ([1, -1, 0, 1, 1, -1, 0], 9)]

def combined100_part1 : Sparse := [([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], 27), ([1, -1, 2, 0, 1, -2, 0], -27), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -2, 0], 36), ([1, 0, 1, 0, 1, -1, -1], -27)]

def combined100 : Sparse := combined100_part0 ++ combined100_part1

def combined101_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -9), ([0, -2, 1, 0, 2, -1, 0], 27), ([0, -2, 2, 0, 1, -1, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 2, -1, 0], -27), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 2, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 0, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -1, -1], 18), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, 1, -1, -1], -9), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 0, 1, 0, 0], -9)]

def combined101_part1 : Sparse := [([1, -2, 1, 0, 2, -1, 0], 27), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 2, -1, 0], -27), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 0, 1, -2, 0], -27), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -2, 0], 27), ([1, 0, 1, 0, 1, -1, -1], -27)]

def combined101 : Sparse := combined101_part0 ++ combined101_part1

def combined102_part0 : Sparse := [([0, -2, 1, 0, 1, -1, 1], -9), ([0, -2, 1, 0, 2, -1, 0], 27), ([0, -2, 1, 1, 1, -1, 0], 9), ([0, -2, 2, 0, 1, -1, 0], -27), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 2, -1, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 2, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 1, -2, 1], 18), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 0, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -1, -1], 18), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 18), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -18), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 0, 2, -1, 0], 27)]

def combined102_part1 : Sparse := [([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 2, -1, 0], -9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 1, 1, -2, 0], 18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 0, 1, -2, 0], -18), ([1, -1, 2, 0, 1, -1, -1], 18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 1, 0, 1, -2, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined102 : Sparse := combined102_part0 ++ combined102_part1

def combined103_part0 : Sparse := [([0, -2, 1, 0, 1, -1, 1], -18), ([0, -2, 1, 0, 2, -1, 0], 18), ([0, -2, 1, 1, 1, -1, 0], 18), ([0, -2, 2, 0, 1, -1, 0], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], -18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, -1, 2, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], 18), ([0, -1, 1, 0, 1, -2, 1], 18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 0, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -1, -1], 18), ([0, -1, 2, -1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -18), ([1, -2, 1, 0, 1, -1, 1], -18), ([1, -2, 1, 0, 2, -1, 0], 18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 0, 1, 0, 0], -18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, -1, 2, -1, 0], -18)]

def combined103_part1 : Sparse := [([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 1, 1, -2, 0], 18), ([1, -1, 2, 0, 1, -2, 0], -18), ([1, -1, 2, 0, 1, -1, -1], 18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined103 : Sparse := combined103_part0 ++ combined103_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined104_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -18), ([0, -2, 1, 0, 2, 0, -1], -36), ([0, -2, 2, 0, 1, 0, -1], 36), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 1, -2], 9), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, -1, 2, 0, 0, 0, -1], -27), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, -1, 2, 0, 1, 0, -2], -27), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, 0, 0, 0, -1], 9), ([1, -2, 1, 0, 1, 0, 0], -18), ([1, -2, 2, 0, 1, 0, -1], 36), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], 27), ([1, -1, 0, 1, 1, 0, -1], -27)]

def combined104_part1 : Sparse := [([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 0, 2, 0, -2], -27), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 2, 0, 0, 0, -1], -27), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 0, 1, 0, -2], 36)]

def combined104 : Sparse := combined104_part0 ++ combined104_part1

def combined105_part0 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -9), ([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 0, 2, 0, -1], -27), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 0, 1, 0, -1], 36), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, -1, 2, 0, -1], 18), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 1, -2], 18), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, -1, 2, 0, 1, 0, -2], -27), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], 9)]

def combined105_part1 : Sparse := [([1, -2, 1, 0, 1, 0, 0], -9), ([1, -2, 1, 1, 1, 0, -1], 9), ([1, -2, 2, 0, 1, 0, -1], 36), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], 27), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 0, 1, 1, -2], 9), ([1, -1, 1, 0, 2, -1, -1], 18), ([1, -1, 1, 0, 2, 0, -2], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 1, 1, 0, -2], 18), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 0, 1, 0, -2], 27)]

def combined105 : Sparse := combined105_part0 ++ combined105_part1

def combined106_part0 : Sparse := [([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 0, 2, 0, -1], -27), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 0, 1, 0, -1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, -1, 2, 0, -1], 18), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 1, -2], 18), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 2, -1, 1, 0, -1], -18), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 0, 1, -1, -1], 18), ([0, -1, 2, 0, 1, 0, -2], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([1, -2, 1, 0, 1, 1, -1], -9), ([1, -2, 2, 0, 1, 0, -1], 27)]

def combined106_part1 : Sparse := [([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -9), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 0, 2, -1, -1], 18), ([1, -1, 1, 0, 2, 0, -2], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 1, 1, 0, -2], 18), ([1, -1, 2, -1, 1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 0, 1, 0, -2], 18)]

def combined106 : Sparse := combined106_part0 ++ combined106_part1

def combined107_part0 : Sparse := [([0, -2, 1, 0, 1, 1, -1], -18), ([0, -2, 1, 0, 2, 0, -1], -18), ([0, -2, 1, 1, 1, 0, -1], 18), ([0, -2, 2, 0, 1, 0, -1], 18), ([0, -1, 0, 0, 1, 0, 0], 18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, -1, 2, 0, -1], 18), ([0, -1, 1, 0, 0, 0, 0], -18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 0, 1, 1, -2], 18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 2, -1, 1, 0, -1], -18), ([0, -1, 2, 0, 1, -1, -1], 18), ([0, -1, 2, 0, 1, 0, -2], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([1, -2, 1, 0, 1, 1, -1], -18), ([1, -2, 2, 0, 1, 0, -1], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, 0, 0, 0, 0], -18), ([1, -1, 1, 0, 0, 1, -1], 18)]

def combined107_part1 : Sparse := [([1, -1, 1, 0, 2, -1, -1], 18), ([1, -1, 1, 0, 2, 0, -2], -18), ([1, -1, 1, 1, 1, 0, -2], 18), ([1, -1, 2, -1, 1, 0, -1], -18), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined107 : Sparse := combined107_part0 ++ combined107_part1

def combined108_part0 : Sparse := [([0, -2, 1, 2, -1, 0, 0], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 2, -1, 0, 0], -27), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, -2, 0, 0], 27), ([0, -1, 2, 1, -2, 0, 0], -27), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -2, 0, 0], -36), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 27), ([1, -2, 1, 1, 0, 0, 0], 18), ([1, -2, 2, 1, -1, 0, 0], -36), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 2, -1, 0, 0], -27), ([1, -1, 1, 0, -1, 0, 1], -36)]

def combined108_part1 : Sparse := [([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 2, -2, 0, 0], 27), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, -1, 0, 0], 27), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 1, 1, -2, 0, 0], -36), ([1, 0, 1, 1, -1, 0, -1], 27)]

def combined108 : Sparse := combined108_part0 ++ combined108_part1

def combined109_part0 : Sparse := [([0, -2, 1, 1, -1, 0, 1], -9), ([0, -2, 1, 2, -1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 2, -1, 0, 0], -27), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, -2, 0, 0], 18), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -2, 0, 0], -27), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -2, 0, 0], -27), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 27), ([1, -2, 1, 1, -1, 1, 0], -9)]

def combined109_part1 : Sparse := [([1, -2, 1, 1, 0, 0, 0], 9), ([1, -2, 2, 1, -1, 0, 0], -36), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 2, -1, 0, 0], -27), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -2, 1, 0], -18), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 2, -2, 0, 0], 18), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -18), ([1, -1, 2, 0, -1, 0, 0], 9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 1, 1, -2, 0, 0], -27), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined109 : Sparse := combined109_part0 ++ combined109_part1

def combined110_part0 : Sparse := [([0, -2, 1, 1, -1, 1, 0], 9), ([0, -2, 1, 2, -1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 2, -1, 0, 0], -9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 1, -2, 0, 1], 18), ([0, -1, 1, 1, -2, 1, 0], -18), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 2, -2, 0, 0], 18), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -2, 0, 0], -18), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 0, 1, 1, -2, 0, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([1, -2, 1, 1, -1, 0, 1], 9)]

def combined110_part1 : Sparse := [([1, -2, 2, 1, -1, 0, 0], -27), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 2, -1, 0, 0], -9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 1, -2, 1, 0], -18), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 2, -2, 0, 0], 18), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -18), ([1, -1, 2, 0, -1, 0, 0], 9), ([1, -1, 2, 1, -1, -1, 0], 9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 1, 1, -2, 0, 0], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined110 : Sparse := combined110_part0 ++ combined110_part1

def combined111_part0 : Sparse := [([0, -2, 1, 1, -1, 1, 0], 18), ([0, -2, 1, 2, -1, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, 0, 0], 18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 1, -2, 0, 1], 18), ([0, -1, 1, 1, -2, 1, 0], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, -2, 0, 0], 18), ([0, -1, 1, 2, -1, -1, 0], 18), ([0, -1, 1, 2, -1, 0, -1], -18), ([0, -1, 2, 1, -2, 0, 0], -18), ([0, -1, 2, 1, -1, 0, -1], 18), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([1, -2, 1, 1, -1, 0, 1], 18), ([1, -2, 2, 1, -1, 0, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 0, 0, 0, 0], 18), ([1, -1, 1, 1, -2, 1, 0], -18)]

def combined111_part1 : Sparse := [([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 2, -2, 0, 0], 18), ([1, -1, 1, 2, -1, 0, -1], -18), ([1, -1, 2, 1, -1, -1, 0], 18), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined111 : Sparse := combined111_part0 ++ combined111_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined112_part0 : Sparse := [([0, -2, 1, 2, 0, -1, 0], -36), ([0, -2, 2, 1, 0, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 1, 2, 0, -2, 0], -27), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], -27), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, 0, -1, -1], -27), ([1, -2, 1, 1, 0, 0, 0], 18), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], 27), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -1, 0], 9)]

def combined112_part1 : Sparse := [([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 2, 0, 0, -1, 0], 27), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, 0, -2, 0], 36)]

def combined112 : Sparse := combined112_part0 ++ combined112_part1

def combined113_part0 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -9), ([0, -2, 1, 2, 0, -1, 0], -27), ([0, -2, 2, 1, 0, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, -2, 0], -18), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, -1, 1, 2, 0, -2, 0], -18), ([0, -1, 1, 2, 0, -1, -1], -18), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], -27), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -27), ([1, -2, 1, 1, 0, 0, 0], 9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], 9)]

def combined113_part1 : Sparse := [([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], 27), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, 0, -2, 1], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 2, -1, -1, 0], -18), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -2, 0], 27), ([1, 0, 1, 1, 0, -1, -1], -9)]

def combined113 : Sparse := combined113_part0 ++ combined113_part1

def combined114_part0 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -9), ([0, -2, 1, 1, 1, -1, 0], -9), ([0, -2, 1, 2, 0, -1, 0], -27), ([0, -2, 2, 1, 0, -1, 0], -27), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, 0, -2, 1], -18), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, -2, 0], -18), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, -1, 1, 2, 0, -2, 0], -18), ([0, -1, 1, 2, 0, -1, -1], -18), ([0, -1, 2, 1, -1, -1, 0], -18), ([0, -1, 2, 1, 0, -2, 0], -18), ([0, -1, 2, 1, 0, -1, -1], -9), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -18)]

def combined114_part1 : Sparse := [([1, -2, 1, 1, 0, -1, 1], -9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], 9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, 0, -2, 1], -18), ([1, -1, 1, 1, 1, -2, 0], -18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 2, -1, -1, 0], -18), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, -1, 2, 1, -1, -1, 0], -9), ([1, -1, 2, 1, 0, -1, -1], -18), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 0, 0, -1, 0], -18), ([1, 0, 1, 1, 0, -2, 0], 18)]

def combined114 : Sparse := combined114_part0 ++ combined114_part1

def combined115_part0 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -18), ([0, -2, 1, 1, 1, -1, 0], -18), ([0, -2, 1, 2, 0, -1, 0], -18), ([0, -2, 2, 1, 0, -1, 0], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], -18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 1, 1, 0, -2, 1], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 1, 1, -2, 0], -18), ([0, -1, 1, 2, -1, -1, 0], -18), ([0, -1, 1, 2, 0, -2, 0], -18), ([0, -1, 1, 2, 0, -1, -1], -18), ([0, -1, 2, 1, -1, -1, 0], -18), ([0, -1, 2, 1, 0, -2, 0], -18), ([0, -1, 2, 1, 0, -1, -1], -18), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -18)]

def combined115_part1 : Sparse := [([1, -2, 1, 1, 0, -1, 1], -18), ([1, -2, 1, 1, 1, -1, 0], -18), ([1, -1, 0, 1, 0, 0, 0], -18), ([1, -1, 1, 0, 0, 0, 0], -18), ([1, -1, 1, 1, 0, -2, 1], -18), ([1, -1, 1, 1, 1, -2, 0], -18), ([1, -1, 1, 2, -1, -1, 0], -18), ([1, -1, 1, 2, 0, -1, -1], -18), ([1, -1, 2, 1, -1, -1, 0], -18), ([1, -1, 2, 1, 0, -1, -1], -18), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 0, 0, -1, 0], -18)]

def combined115 : Sparse := combined115_part0 ++ combined115_part1

def combined116_part0 : Sparse := [([0, -2, 2, 1, 0, 0, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], -27), ([0, -1, 2, 0, 0, 0, -1], -27), ([0, -1, 2, 1, 0, 0, -2], 27), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 0, 0, -2], -36), ([1, -2, 1, 1, 0, 0, 0], 18), ([1, -2, 1, 2, 0, 0, -1], -36), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 2, 0, 0, -1], 27), ([1, -1, 1, 0, 0, 1, -1], 27)]

def combined116_part1 : Sparse := [([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], -27), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], 27), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, 0, -2], -36)]

def combined116 : Sparse := combined116_part0 ++ combined116_part1

def combined117_part0 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 1, 0, 0, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 0, 1, -2], -18), ([0, -1, 1, 1, 1, 0, -2], 18), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], -18), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 1, 0, 0, -2], 27), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 0, 0, -2], -27), ([1, -2, 1, 1, 0, 0, 0], 9), ([1, -2, 1, 1, 0, 1, -1], 9)]

def combined117_part1 : Sparse := [([1, -2, 1, 1, 1, 0, -1], 9), ([1, -2, 1, 2, 0, 0, -1], -27), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 2, 0, 0, -1], 27), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], 27), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], -27)]

def combined117 : Sparse := combined117_part0 ++ combined117_part1

def combined118_part0 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 2, 1, 0, 0, -1], -27), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 1, -2], -18), ([0, -1, 1, 1, 1, 0, -2], 18), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], -18), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 1, -1, 0, -1], -9), ([0, -1, 2, 1, 0, -1, -1], 9), ([0, -1, 2, 1, 0, 0, -2], 18), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 0, 0, -2], -18), ([1, -2, 1, 1, 1, 0, -1], 9)]

def combined118_part1 : Sparse := [([1, -2, 1, 2, 0, 0, -1], -27), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 2, 0, 0, -1], 9), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 0, 1, -2], -18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, -1, 2, 1, -1, 0, -1], -18), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], 18), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 1, 0, 0, -2], -18)]

def combined118 : Sparse := combined118_part0 ++ combined118_part1

def combined119_part0 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 18), ([0, -2, 2, 1, 0, 0, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 1, 0, 0, 0, 0], 18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 1, 1, 0, 1, -2], -18), ([0, -1, 1, 1, 1, 0, -2], 18), ([0, -1, 1, 2, -1, 0, -1], 18), ([0, -1, 1, 2, 0, 0, -2], -18), ([0, -1, 2, 1, -1, 0, -1], -18), ([0, -1, 2, 1, 0, -1, -1], 18), ([0, -1, 2, 1, 0, 0, -2], 18), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([1, -2, 1, 1, 1, 0, -1], 18), ([1, -2, 1, 2, 0, 0, -1], -18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 1, 1, 0, -1, 0], -18)]

def combined119_part1 : Sparse := [([1, -1, 1, 1, 0, 1, -2], -18), ([1, -1, 1, 2, 0, -1, -1], 18), ([1, -1, 2, 1, -1, 0, -1], -18), ([1, -1, 2, 1, 0, 0, -2], 18), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined119 : Sparse := combined119_part0 ++ combined119_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined120_part0 : Sparse := [([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, 0, -2, -1, 0, 1, 2], -36), ([0, 0, -2, -1, 0, 2, 1], 36), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -2, 0, 2, 1], -27), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 2, 0], -27), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 27), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, 0, -2, -1, 0, 2, 1], 36)]

def combined120_part1 : Sparse := [([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -2, 0, 1, 2], -27), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, -1, 0, 0, 2], 27), ([1, 0, -1, -1, 0, 2, 0], -27), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, 0, -2, 0, 1, 1], 36), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 0, 1, 0], 36)]

def combined120 : Sparse := combined120_part0 ++ combined120_part1

def combined121_part0 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, 0, -2, -1, 0, 1, 2], -27), ([0, 0, -2, -1, 0, 2, 1], 27), ([0, 0, -2, -1, 1, 1, 1], 9), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -2, 0, 2, 1], -27), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -2, -1, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 27), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -27)]

def combined121_part1 : Sparse := [([1, 0, -2, -1, 0, 2, 1], 27), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -2, 0, 1, 2], -27), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], 18), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, -1, 0, 1, 0], 27)]

def combined121 : Sparse := combined121_part0 ++ combined121_part1

def combined122_part0 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, 0, -2, -1, 0, 1, 2], -18), ([0, 0, -2, -1, 0, 2, 1], 27), ([0, 0, -2, -1, 1, 1, 1], 18), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -1, -2, 0, 2, 1], -27), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -1, -1, 1, 2], 18), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -2, -1, 0, 1, 1], -18), ([0, 1, -1, -2, 0, 1, 1], 18), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 0, 1, 0], 27), ([1, -1, -1, -1, 0, 1, 2], 18), ([1, -1, -1, -1, 1, 1, 1], 9)]

def combined122_part1 : Sparse := [([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, 0, -2, -1, 0, 2, 1], 27), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -1, -2, 0, 1, 2], -18), ([1, 0, -1, -2, 1, 1, 1], 18), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, 0, 0, 1], 18), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, -1, 0, 1, 0], 27)]

def combined122 : Sparse := combined122_part0 ++ combined122_part1

def combined123_part0 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, 0, -2, -1, 0, 1, 2], -18), ([0, 0, -2, -1, 0, 2, 1], 18), ([0, 0, -2, -1, 1, 1, 1], 18), ([0, 0, -1, -2, 0, 2, 1], -18), ([0, 0, -1, -1, -1, 1, 2], 18), ([0, 0, -1, -1, -1, 2, 1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 1, 0], 18), ([0, 1, -2, -1, 0, 1, 1], -18), ([0, 1, -1, -2, 0, 1, 1], 18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([1, -1, -1, -1, 0, 1, 2], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, 0, -2, -1, 0, 2, 1], 18), ([1, 0, -1, -2, 0, 1, 2], -18), ([1, 0, -1, -2, 1, 1, 1], 18), ([1, 0, -1, -1, -1, 2, 1], -18)]

def combined123_part1 : Sparse := [([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, 0, -1, 0, 0, 1], 18), ([1, 1, -2, -1, 0, 1, 1], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined123 : Sparse := combined123_part0 ++ combined123_part1

def combined124_part0 : Sparse := [([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, 0, -2, -1, 1, 0, 2], -36), ([0, 0, -2, -1, 2, 0, 1], -36), ([0, 0, -1, -2, 1, 0, 2], -27), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 1, 0, 0], -27), ([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, 0, -2, 0, 1, 0, 1], 18), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 27), ([1, 0, -1, -1, 0, 1, 1], 9)]

def combined124_part1 : Sparse := [([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, -1, 2, 0, 0], 27), ([1, 0, 0, -2, 1, 0, 1], 36), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, -1, 1, 0, 0], 9)]

def combined124 : Sparse := combined124_part0 ++ combined124_part1

def combined125_part0 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -9), ([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, 0, -2, -1, 1, 0, 2], -27), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 2, 0, 1], -27), ([0, 0, -1, -2, 1, 0, 2], -27), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 1, 0, 0], -27)]

def combined125_part1 : Sparse := [([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], 18), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, -1, 2, 0, 0], 18), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], 18), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -2, -1, 1, 0, 1], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], 18)]

def combined125 : Sparse := combined125_part0 ++ combined125_part1

def combined126_part0 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -18), ([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, 0, -2, -1, 1, 0, 2], -18), ([0, 0, -2, -1, 1, 1, 1], -18), ([0, 0, -2, -1, 2, 0, 1], -27), ([0, 0, -1, -2, 1, 0, 2], -18), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, -1, 2], -18), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -2, 1, 0, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 1, 0, 0], -27)]

def combined126_part1 : Sparse := [([1, -1, -1, -1, 1, 0, 2], -18), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -1, -2, 1, 1, 1], -18), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, -1, 2], -18), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], 9), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -2, -1, 1, 0, 1], -18), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], 9)]

def combined126 : Sparse := combined126_part0 ++ combined126_part1

def combined127_part0 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -18), ([0, -1, -1, -1, 2, 0, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, 0, -2, -1, 1, 0, 2], -18), ([0, 0, -2, -1, 1, 1, 1], -18), ([0, 0, -2, -1, 2, 0, 1], -18), ([0, 0, -1, -2, 1, 0, 2], -18), ([0, 0, -1, -2, 1, 1, 1], -18), ([0, 0, -1, -2, 2, 0, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, -1, 2], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, -1, 2, -1, 1], -18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, -1, 1, 0, 0], -18), ([0, 1, -2, -1, 1, 0, 1], -18), ([0, 1, -1, -2, 1, 0, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 1, 0, 0], -18)]

def combined127_part1 : Sparse := [([1, -1, -1, -1, 1, 0, 2], -18), ([1, -1, -1, -1, 2, 0, 1], -18), ([1, 0, -2, -1, 1, 1, 1], -18), ([1, 0, -1, -2, 1, 1, 1], -18), ([1, 0, -1, -1, 1, -1, 2], -18), ([1, 0, -1, -1, 2, -1, 1], -18), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, -1, 0, 1, 0, 0], -18), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 0, -1, 1, 0, 0], -18), ([1, 1, -2, -1, 1, 0, 1], -18), ([1, 1, -1, -2, 1, 0, 1], -18)]

def combined127 : Sparse := combined127_part0 ++ combined127_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined128_part0 : Sparse := [([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 2, 0], -36), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 27), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 2, 0], -27), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -27), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, 0, -2, -1, 2, 1, 0], -36), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, -2, 1, 2, 0], 27)]

def combined128_part1 : Sparse := [([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 2, 0], -27), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], 27), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], -27)]

def combined128 : Sparse := combined128_part0 ++ combined128_part1

def combined129_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 2, 0], -27), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 27), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -18), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -18), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27)]

def combined129_part1 : Sparse := [([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], -27), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, -2, 1, 2, 0], 27), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], 18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, 0, -2, 1, 1, 0], -18), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, 1, -1], -18)]

def combined129 : Sparse := combined129_part0 ++ combined129_part1

def combined130_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 18), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 1, 2, 0], -18), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 2, -1], -18), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -9), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -9), ([1, -1, -1, -1, 1, 1, 1], 9)]

def combined130_part1 : Sparse := [([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], -27), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -2, 1, 2, 0], 18), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 2, -1], -18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], -9), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -1, -2, 1, 1, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18), ([1, 1, -1, -1, 1, 1, -1], -9)]

def combined130 : Sparse := combined130_part0 ++ combined130_part1

def combined131_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, 0, -2, -1, 1, 2, 0], -18), ([0, 0, -1, -2, 1, 1, 1], 18), ([0, 0, -1, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 2, 1, 0], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, 2, -1], -18), ([0, 0, -1, -1, 2, 1, -1], 18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, -1, 1, 0, 0], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 1, -2, -1, 1, 1, 0], 18), ([0, 1, -1, -2, 1, 1, 0], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -18), ([1, -1, -1, -1, 2, 1, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, 0, -2, -1, 1, 1, 1], 18), ([1, 0, -2, -1, 2, 1, 0], -18), ([1, 0, -1, -2, 1, 2, 0], 18), ([1, 0, -1, -1, 1, 0, 1], -18)]

def combined131_part1 : Sparse := [([1, 0, -1, -1, 1, 2, -1], -18), ([1, 0, -1, 0, 1, 0, 0], 18), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 1, -1, -2, 1, 1, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined131 : Sparse := combined131_part0 ++ combined131_part1

def combined132_part0 : Sparse := [([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -2, 0, -1, 1, 2], -36), ([0, 0, -2, 0, -1, 2, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -2, 1, 2], -27), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -27)]

def combined132_part1 : Sparse := [([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, 0, -2, 1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9)]

def combined132 : Sparse := combined132_part0 ++ combined132_part1

def combined133_part0 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -2, 0, -1, 1, 2], -27), ([0, 0, -2, 0, -1, 2, 1], -27), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -2, 1, 2], -27), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 0, -1, 2, 0], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -18), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 1, 2], 9), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -2, 1, -1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9)]

def combined133_part1 : Sparse := [([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, -1, 2, 0], -18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, 0, -2, 1, 1], -18), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, 0, -2, 1, 1], 9)]

def combined133 : Sparse := combined133_part0 ++ combined133_part1

def combined134_part0 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -2, 0, -1, 1, 2], -18), ([0, 0, -2, 0, -1, 2, 1], -27), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -2, 1, 2], -18), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -9), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 1, 2], 18), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 0, 0, 1, 1], -9)]

def combined134_part1 : Sparse := [([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -2, 1, -1, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 18), ([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, 0, -2, 1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, 0, -2, 1, 1], 18)]

def combined134 : Sparse := combined134_part0 ++ combined134_part1

def combined135 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -2, 0, -1, 1, 2], -18), ([0, 0, -2, 0, -1, 2, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -2, 1, 2], -18), ([0, 0, -1, 0, -2, 2, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([1, -1, -1, 0, -1, 1, 2], 18), ([1, -1, -1, 0, -1, 2, 1], 18), ([1, 0, -2, 1, -1, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 18), ([1, 0, -1, -1, -1, 2, 1], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, -2, 1, 1], 18), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 1, -2, 0, -1, 1, 1], 18), ([1, 1, -1, 0, -2, 1, 1], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined136_part0 : Sparse := [([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, 0, -2, 0, 2, -1, 1], -36), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, 0, 1, -2, 2], -27), ([0, 0, -1, 0, 2, -2, 1], 27), ([0, 0, -1, 0, 2, -1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 1, 1, -2, 1], -9), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 1, -2, 1], -36), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 1, -2, 1], 9), ([0, 1, -1, 0, 1, -1, 0], -36), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, -1, 2], -36), ([1, 0, -2, 0, 1, 0, 1], 18)]

def combined136_part1 : Sparse := [([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 2, -2, 1], 27), ([1, 0, -1, 0, 2, -1, 0], -27), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, 0, 1, -2, 1], -36), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 0, 1, -1, 0], -9)]

def combined136 : Sparse := combined136_part0 ++ combined136_part1

def combined137_part0 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 9), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -2, 0, 2, -1, 1], -36), ([0, 0, -2, 1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, 0, 1, -2, 2], -18), ([0, 0, -1, 0, 2, -2, 1], 27), ([0, 0, -1, 0, 2, -1, 0], -9), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 1, -2, 1], -18), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 0, 1, -2, 1], -27), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 1, -1, 0], -36), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 1, 0, 1], 9)]

def combined137_part1 : Sparse := [([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, -1, 2], -27), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], 9), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 2, -2, 1], 27), ([1, 0, -1, 0, 2, -1, 0], -9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], -27), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -2, 0, 1, -1, 1], 9), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, -1, 0, 1, -2, 1], 9), ([1, 1, -1, 0, 1, -1, 0], -9)]

def combined137 : Sparse := combined137_part0 ++ combined137_part1

def combined138_part0 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 2, -1, 1], -9), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -2, 0, 2, -1, 1], -27), ([0, 0, -2, 1, 1, -1, 1], 18), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 2, -1, 1], 9), ([0, 0, -1, 0, 1, -2, 2], -18), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 2, -2, 1], 27), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 1, -2, 1], -18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 0, 1, -2, 1], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -1, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 1, -1, 0], -27), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 2, -1, 1], -9)]

def combined138_part1 : Sparse := [([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, -1, 2], -18), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 0, -1, 2], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 2, -2, 1], 27), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -2, 0, 1, -1, 1], 18), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 0, 1, -2, 1], 9)]

def combined138 : Sparse := combined138_part0 ++ combined138_part1

def combined139_part0 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 2, -1, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -2, 0, 2, -1, 1], -18), ([0, 0, -2, 1, 1, -1, 1], 18), ([0, 0, -1, -1, 2, -1, 1], 18), ([0, 0, -1, 0, 1, -2, 2], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 0, 2, -2, 1], 18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 1, -2, 1], -18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 0, 1, -1, 0], -18), ([0, 1, -1, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 1, -1, 0], -18), ([1, -1, -1, 0, 2, -1, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -2, 0, 1, -1, 2], -18), ([1, 0, -1, -1, 1, -1, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 0, 0, 1], 18)]

def combined139_part1 : Sparse := [([1, 0, -1, 0, 2, -2, 1], 18), ([1, 0, -1, 1, 1, -2, 1], -18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 1, -1, 0], -18), ([1, 1, -2, 0, 1, -1, 1], 18), ([1, 1, -1, 0, 0, -1, 1], -18)]

def combined139 : Sparse := combined139_part0 ++ combined139_part1

def combined140_part0 : Sparse := [([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -2, 0, 2, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, 2, -2], -27), ([0, 0, -1, 0, 2, 0, -1], -27), ([0, 0, -1, 0, 2, 1, -2], 27), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 1, 1, -2], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 0, 1, 1, -2], -36), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 1, 1, -2], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -2, 0, 1, 2, -1], -36), ([1, 0, -1, -1, 1, 2, -1], -9)]

def combined140_part1 : Sparse := [([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 2, 0, -1], -27), ([1, 0, -1, 0, 2, 1, -2], 27), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 1, -2], -36), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 1, 1, -2], -9)]

def combined140 : Sparse := combined140_part0 ++ combined140_part1

def combined141_part0 : Sparse := [([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -2, 0, 2, 1, -1], -36), ([0, 0, -2, 1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, 0, 1, 2, -2], -18), ([0, 0, -1, 0, 2, 0, -1], -9), ([0, 0, -1, 0, 2, 1, -2], 27), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 1, 1, -2], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 0, 1, 1, -2], -27), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 1, 1, -2], -18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 1, 2, -1], 9)]

def combined141_part1 : Sparse := [([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -2, 0, 1, 2, -1], -27), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 2, 0, -1], -9), ([1, 0, -1, 0, 2, 1, -2], 27), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 1, -2], -27), ([1, 1, -2, 0, 1, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 1, 1, -2], -9)]

def combined141 : Sparse := combined141_part0 ++ combined141_part1

def combined142_part0 : Sparse := [([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, -1, 0, 2, 1, -1], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -2, 0, 2, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, -1, 2, 1, -1], -9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 1, 2, -2], -18), ([0, 0, -1, 0, 2, 0, -1], -9), ([0, 0, -1, 0, 2, 1, -2], 18), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 1, 1, -2], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 0, 1, 1, -2], -18), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 0, 1, 1, -2], -18), ([1, -1, -1, 0, 1, 1, 0], -27)]

def combined142_part1 : Sparse := [([1, -1, -1, 0, 1, 2, -1], 9), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, 0, -2, 0, 1, 2, -1], -27), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 1, -1], -18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 2, -1], 9), ([1, 0, -1, 0, 2, 0, -1], -9), ([1, 0, -1, 0, 2, 1, -2], 18), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 0, 0, 1, 1, -2], -18), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 0, 1, 1, -2], -18)]

def combined142 : Sparse := combined142_part0 ++ combined142_part1

def combined143_part0 : Sparse := [([0, -1, -1, 0, 2, 1, -1], 18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -2, 0, 2, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, -1, 1, 2, -1], 18), ([0, 0, -1, -1, 2, 1, -1], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 0, 1, 2, -2], -18), ([0, 0, -1, 0, 2, 1, -2], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 1, 1, -2], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 1, -2, 0, 1, 1, -1], 18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 1, 1, -2], -18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 0, 1, 2, -1], 18), ([1, 0, -2, 0, 1, 2, -1], -18), ([1, 0, -2, 1, 1, 1, -1], 18), ([1, 0, -1, -1, 2, 1, -1], -18), ([1, 0, -1, 0, 0, 1, 0], 18)]

def combined143_part1 : Sparse := [([1, 0, -1, 0, 2, 1, -2], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 0, 1, 1, -2], -18)]

def combined143 : Sparse := combined143_part0 ++ combined143_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined144_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, 0, -2, 1, -1, 0, 2], 36), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -2, 2, -1, 0, 1], -36), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 1, -2, 0, 2], -27), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 1, -1, 0, 0], 9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, 0, -2, 1, -1, 0, 2], 36), ([1, 0, -2, 1, 0, 0, 1], -18)]

def combined144_part1 : Sparse := [([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 2, -2, 0, 1], -27), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, -1, 0, 0], 27), ([1, 0, 0, 1, -2, 0, 1], 36), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined144 : Sparse := combined144_part0 ++ combined144_part1

def combined145_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -18), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, 0, -2, 1, -1, 0, 2], 27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 2, -1, 0, 1], -36), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 1, -2, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 1, -2, 0, 1], -9), ([0, 1, -1, 1, -1, 0, 0], 9), ([1, -1, -1, 1, -1, 0, 2], -9), ([1, -1, -1, 1, -1, 1, 1], -18)]

def combined145_part1 : Sparse := [([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, 0, -2, 1, -1, 0, 2], 27), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 2, -2, 0, 1], -27), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, -1, 0, 0], 9), ([1, 0, 0, 1, -2, 0, 1], 27), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined145 : Sparse := combined145_part0 ++ combined145_part1

def combined146_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, 0, -2, 1, -1, 0, 2], 18), ([0, 0, -2, 1, -1, 1, 1], -9), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 2, -1, 0, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 1, -2, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 1, -2, 1, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 1, -2, 0, 1], -9), ([1, -1, -1, 1, -1, 0, 2], -18)]

def combined146_part1 : Sparse := [([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, 0, -2, 1, -1, 0, 2], 18), ([1, 0, -2, 1, -1, 1, 1], -18), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 2, -2, 0, 1], -27), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, 0, 1, -2, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined146 : Sparse := combined146_part0 ++ combined146_part1

def combined147_part0 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, -1, 0, 1], 18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, 0, -2, 1, -1, 0, 2], 18), ([0, 0, -2, 1, -1, 1, 1], -18), ([0, 0, -2, 2, -1, 0, 1], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 1, -2, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], 18), ([0, 0, -1, 1, -1, -1, 2], 18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 0, 0, 0], 18), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 1, -2, 1, -1, 0, 1], 18), ([0, 1, -1, 0, -1, 0, 1], -18), ([1, -1, -1, 1, -1, 0, 2], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, 0, -2, 1, -1, 0, 2], 18), ([1, 0, -2, 1, -1, 1, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18)]

def combined147_part1 : Sparse := [([1, 0, -1, 2, -2, 0, 1], -18), ([1, 0, -1, 2, -1, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, -1, 0, 0], 18), ([1, 1, -1, 1, -2, 0, 1], 18), ([1, 1, -1, 1, -1, 0, 0], -18)]

def combined147 : Sparse := combined147_part0 ++ combined147_part1

def combined148_part0 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, 0, -2, 1, -1, 2, 0], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], 27), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 2, -2, 1, 0], -27), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 0, 1, -2, 1, 0], -36), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 1, -2, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, -1, 2, 0], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, 0, -2, 1, 0, 1, 0], 18), ([1, 0, -2, 2, -1, 1, 0], -36)]

def combined148_part1 : Sparse := [([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, -2, 2, 0], 27), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, -1, 0, 0], 27), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 0, 1, -2, 1, 0], -36), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 27)]

def combined148 : Sparse := combined148_part0 ++ combined148_part1

def combined149_part0 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], -9), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, 0, -2, 1, -1, 2, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], 18), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 2, -2, 1, 0], -27), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 0, 1, -2, 1, 0], -27), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 1, -2, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([1, -1, -1, 1, -1, 1, 1], -18)]

def combined149_part1 : Sparse := [([1, -1, -1, 1, -1, 2, 0], -18), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -2, 2, -1, 1, 0], -36), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], -18), ([1, 0, -1, 1, -2, 2, 0], 18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, -1, 0, 0], 9), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 0, 1, -2, 1, 0], -27), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 18)]

def combined149 : Sparse := combined149_part0 ++ combined149_part1

def combined150_part0 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, -1, 2, 0], -18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 2, -1, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -2, 1, -1, 2, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, -1, 2, 0], -18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], 18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 2, -1], 18), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 2, -2, 1, 0], -27), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 0, 1, -2, 1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 1, -2, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], -9)]

def combined150_part1 : Sparse := [([1, -1, -1, 1, -1, 2, 0], -18), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -2, 2, -1, 1, 0], -27), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, -1, 2, 0], -18), ([1, 0, -1, 1, -2, 1, 1], -18), ([1, 0, -1, 1, -2, 2, 0], 18), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 0, 1, -2, 1, 0], -9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 1, -2, 1, -1, 1, 0], 9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 1, -1, 1, -1], 9)]

def combined150 : Sparse := combined150_part0 ++ combined150_part1

def combined151_part0 : Sparse := [([0, -1, -1, 1, -1, 2, 0], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 2, -1, 1, 0], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, 0, -2, 1, -1, 1, 1], 18), ([0, 0, -2, 1, -1, 2, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 1, -2, 1, 1], -18), ([0, 0, -1, 1, -2, 2, 0], 18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 2, -1], 18), ([0, 0, -1, 2, -2, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 0, 1, -1, 0, 0], 18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 1, -2, 1, 0], 18), ([1, -1, -1, 1, -1, 2, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, 0, -2, 2, -1, 1, 0], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 1, -2, 1, 1], -18), ([1, 0, -1, 1, -2, 2, 0], 18)]

def combined151_part1 : Sparse := [([1, 0, -1, 1, 0, 0, 0], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, -1, 2, -1, 1, -1], 18), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 1, -2, 1, -1, 1, 0], 18), ([1, 1, -1, 1, -1, 0, 0], -18)]

def combined151 : Sparse := combined151_part0 ++ combined151_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined152_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 9), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, -1, 2], -36), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -2, 2, 0, -1, 1], 36), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 1, -2, 1], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], -27), ([0, 0, -1, 2, 0, -1, 0], -27), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 1, 0, -1, 0], -27), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, 0, -2, 1, 0, 0, 1], -18), ([1, 0, -2, 2, 0, -1, 1], 36)]

def combined152_part1 : Sparse := [([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, 0, -2, 2], -27), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, 0, -1, 0], -27), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, 0, -2, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, 0, -2, 1], 9), ([1, 1, -1, 1, 0, -1, 0], 9)]

def combined152 : Sparse := combined152_part0 ++ combined152_part1

def combined153_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -2, 1, 0, -1, 2], -27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 1, 1, -1, 1], -9), ([0, 0, -2, 2, 0, -1, 1], 36), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 1, -2, 1], 18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], -27), ([0, 0, -1, 2, 0, -1, 0], -9), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -2, 1, 0, -1, 1], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 1, 0, -2, 1], 9), ([0, 1, -1, 1, 0, -1, 0], -27)]

def combined153_part1 : Sparse := [([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -2, 2, 0, -1, 1], 36), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 1, -1, -1, 2], 18), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -2, 2], -18), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, 0, -1, 0], -9), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -2, 1], 27), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, 0, -2, 1], 18), ([1, 1, -1, 1, 0, -1, 0], 9)]

def combined153 : Sparse := combined153_part0 ++ combined153_part1

def combined154_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -2, 1, 0, -1, 2], -18), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -2, 1, 1, -1, 1], -18), ([0, 0, -2, 2, 0, -1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -2, 1], 18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], -27), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -2, 1, 0, -1, 1], 18), ([0, 1, -1, 1, 0, -2, 1], 9), ([0, 1, -1, 1, 0, -1, 0], -27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -9)]

def combined154_part1 : Sparse := [([1, -1, -1, 2, 0, -1, 1], -9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -2, 1, 1, -1, 1], -9), ([1, 0, -2, 2, 0, -1, 1], 27), ([1, 0, -1, 0, 0, -1, 2], 18), ([1, 0, -1, 1, -1, -1, 2], 18), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -2, 2], -18), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -2, 1], 9), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, 0, -2, 1], 18)]

def combined154 : Sparse := combined154_part0 ++ combined154_part1

def combined155_part0 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, 0, -1, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -2, 1, 0, -1, 2], -18), ([0, 0, -2, 1, 1, -1, 1], -18), ([0, 0, -2, 2, 0, -1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, -1, 1, 1, -2, 1], 18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 2, -1, -1, 1], 18), ([0, 0, -1, 2, 0, -2, 1], -18), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 1, -2, 1, 0, -1, 1], 18), ([0, 1, -1, 1, 0, -1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, -1, 2, 0, -1, 1], -18), ([1, 0, -2, 1, 1, -1, 1], -18), ([1, 0, -2, 2, 0, -1, 1], 18), ([1, 0, -1, 1, -1, -1, 2], 18), ([1, 0, -1, 1, 0, -2, 2], -18)]

def combined155_part1 : Sparse := [([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 1, 0, -2, 1], 18)]

def combined155 : Sparse := combined155_part0 ++ combined155_part1

def combined156_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 0, 2, -1], -9), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, 0, -2, 1, 0, 2, -1], -36), ([0, 0, -2, 2, 0, 1, -1], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, -1, 1, 0, 2, -2], -27), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 1, 1, -2], -9), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, -1, 2, 0, 1, -2], -27), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 0, 1, -2], -9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], 18), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 2, -1], -9)]

def combined156_part1 : Sparse := [([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, -1, 2, 0, 0, -1], 27), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], 36), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -9)]

def combined156 : Sparse := combined156_part0 ++ combined156_part1

def combined157_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 0, 2, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, 0, -2, 1, 0, 2, -1], -27), ([0, 0, -2, 2, 0, 1, -1], -36), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, -1, 1, 0, 2, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 1, 1, -2], -18), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, -1, 2, 0, 1, -2], -27), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 0, 1, -2], -9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 18)]

def combined157_part1 : Sparse := [([1, -1, -1, 2, 0, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 1, -1, 2, -1], -18), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, -1, 2, 0, 0, -1], 9), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], 27), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -18)]

def combined157 : Sparse := combined157_part0 ++ combined157_part1

def combined158_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 0, 2, -1], -18), ([0, -1, -1, 2, 0, 1, -1], -9), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -2, 1, 0, 2, -1], -27), ([0, 0, -2, 1, 1, 1, -1], -9), ([0, 0, -2, 2, 0, 1, -1], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 0, 2, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 1, 1, -2], -18), ([0, 0, -1, 2, -1, 1, -1], -18), ([0, 0, -1, 2, 0, 1, -2], -18), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 0, 1, -2], -18)]

def combined158_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 2, 0, 1, -1], -18), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 2, -1], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 2, -1], -18), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -18), ([1, 0, -1, 2, -1, 1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], 9), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 0, 1, 0, 1, -2], 18), ([1, 1, -2, 1, 0, 1, -1], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -18)]

def combined158 : Sparse := combined158_part0 ++ combined158_part1

def combined159_part0 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 0, 2, -1], -18), ([0, -1, -1, 2, 0, 1, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -2, 1, 0, 2, -1], -18), ([0, 0, -2, 1, 1, 1, -1], -18), ([0, 0, -2, 2, 0, 1, -1], -18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, -1, 2, -1], -18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, -1, 1, 0, 2, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 1, 1, -2], -18), ([0, 0, -1, 2, -1, 1, -1], -18), ([0, 0, -1, 2, 0, 1, -2], -18), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 1, -2, 1, 0, 1, -1], -18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 1, 0, 1, -2], -18)]

def combined159_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], -18), ([1, -1, -1, 2, 0, 1, -1], -18), ([1, 0, -2, 1, 1, 1, -1], -18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 1, -1, 2, -1], -18), ([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, -1, 1, 1, 1, -2], -18), ([1, 0, -1, 2, -1, 1, -1], -18), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 1, -2, 1, 0, 1, -1], -18), ([1, 1, -1, 1, 0, 1, -2], -18)]

def combined159 : Sparse := combined159_part0 ++ combined159_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined160_part0 : Sparse := [([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, 0, -2, 1, 1, 0, 0], -18), ([0, 0, -2, 1, 2, -1, 0], -36), ([0, 0, -2, 2, 1, -1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, -1, 0, 2, -1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 2, -2, 0], -27), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 2, 0, -1, 0], -27), ([0, 0, -1, 2, 1, -2, 0], -27), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 1, 1, -2, 0], -36), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 1, -1, -1], -27), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 2, -1, 0], 9)]

def combined160_part1 : Sparse := [([1, 0, -2, 1, 1, 0, 0], -18), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 2, -1, 0], -27), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 2, 0, -1, 0], -27), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 1, -2, 0], -36), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 1, -2, 0], 9), ([1, 1, -1, 1, 1, -1, -1], -27)]

def combined160 : Sparse := combined160_part0 ++ combined160_part1

def combined161_part0 : Sparse := [([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, 0, -2, 1, 1, -1, 1], -9), ([0, 0, -2, 1, 1, 0, 0], -9), ([0, 0, -2, 1, 2, -1, 0], -27), ([0, 0, -2, 2, 1, -1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 0, 2, -1, 0], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 1, -2, 1], 9), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 2, -2, 0], -18), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 2, 0, -1, 0], -9), ([0, 0, -1, 2, 1, -2, 0], -27), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 1, 1, -2, 0], -27), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 1, -2, 1, 1, -1, 0], 9), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -36)]

def combined161_part1 : Sparse := [([0, 1, -1, 1, 1, -2, 0], -9), ([0, 1, -1, 1, 1, -1, -1], -18), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 2, -1, 0], 18), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, 0, -2, 1, 1, 0, 0], -9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 2, -1, 0], -27), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 1, -2, 1], 18), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 1, 2, -1, -1], 9), ([1, 0, -1, 2, 0, -1, 0], -9), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 1, -2, 0], -27), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 1, -2, 1, 1, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 1, -2, 0], 9)]

def combined161_part2 : Sparse := [([1, 1, -1, 1, 1, -1, -1], -18)]

def combined161 : Sparse := combined161_part0 ++ combined161_part1 ++ combined161_part2

def combined162_part0 : Sparse := [([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, 0, -2, 1, 2, -1, 0], -27), ([0, 0, -2, 2, 1, -1, 0], -27), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 0, 2, -1, 0], -9), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 2, -2, 0], -18), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 2, 0, -1, 0], -9), ([0, 0, -1, 2, 1, -2, 0], -18), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 1, 1, -2, 0], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, -1, 1, 1, -1, -1], -9), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 1, 2, -1, 0], 18), ([1, -1, -1, 2, 1, -1, 0], 9)]

def combined162_part1 : Sparse := [([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 2, -1, 0], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 1, -2, 1], 18), ([1, 0, -1, 1, 2, -1, -1], 9), ([1, 0, -1, 2, 0, -1, 0], -9), ([1, 0, -1, 2, 1, -1, -1], 18), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 0, 1, 0, -1, 0], 18), ([1, 0, 0, 1, 1, -2, 0], -18), ([1, 1, -2, 1, 1, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 1, -2, 0], 18), ([1, 1, -1, 1, 1, -1, -1], -9)]

def combined162 : Sparse := combined162_part0 ++ combined162_part1

def combined163 : Sparse := [([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, 0, -2, 1, 2, -1, 0], -18), ([0, 0, -2, 2, 1, -1, 0], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 2, -2, 0], -18), ([0, 0, -1, 2, 1, -2, 0], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([1, -1, -1, 1, 2, -1, 0], 18), ([1, -1, -1, 2, 1, -1, 0], 18), ([1, 0, -2, 1, 1, -1, 1], 18), ([1, 0, -1, 0, 1, 0, 0], 18), ([1, 0, -1, 1, 0, 0, 0], 18), ([1, 0, -1, 1, 1, -2, 1], 18), ([1, 0, -1, 1, 2, -1, -1], 18), ([1, 0, -1, 2, 1, -1, -1], 18), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 0, 1, 0, -1, 0], 18), ([1, 1, -2, 1, 1, -1, 0], 18), ([1, 1, -1, 1, 1, -2, 0], 18)]

def combined164_part0 : Sparse := [([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 1, 2, 0, -1], 9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 0, 0], -18), ([0, 0, -2, 1, 2, 0, -1], 36), ([0, 0, -2, 2, 1, 0, -1], -36), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 0, 2, 0, -1], -27), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 1, 2, 0, -2], -27), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, -1, 1, 1, 0, -2], 9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, 0, -2, 1, 1, 0, 0], -18)]

def combined164_part1 : Sparse := [([1, 0, -2, 1, 2, 0, -1], 36), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 0, 2, 0, -1], -27), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, -1, 2, 0, 0, -1], 27), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, -1, 2, 1, 0, -2], -27), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 1, 0, -2], 36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], -27)]

def combined164 : Sparse := combined164_part0 ++ combined164_part1

def combined165_part0 : Sparse := [([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 1, 2, 0, -1], 18), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, 0, -2, 1, 1, 0, 0], -9), ([0, 0, -2, 1, 2, 0, -1], 27), ([0, 0, -2, 2, 1, 0, -1], -36), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 0, 2, 0, -1], -27), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 1, 1, 1, -2], -9), ([0, 0, -1, 1, 2, -1, -1], -18), ([0, 0, -1, 1, 2, 0, -2], -18), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 1, -1, -1], -18), ([0, 1, -1, 1, 1, 0, -2], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], 18)]

def combined165_part1 : Sparse := [([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, 0, -2, 1, 1, 0, 0], -9), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -2, 1, 2, 0, -1], 27), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 0, 2, 0, -1], -27), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, -1, 1, 2, -1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], 9), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, -1, 2, 1, 0, -2], -27), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 1, 0, -2], 27), ([1, 1, -2, 1, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], -18), ([1, 1, -1, 1, 1, 0, -2], -9)]

def combined165 : Sparse := combined165_part0 ++ combined165_part1

def combined166_part0 : Sparse := [([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 1, 2, 0, -1], 18), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 1, -1], 9), ([0, 0, -2, 1, 2, 0, -1], 27), ([0, 0, -2, 2, 1, 0, -1], -27), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 0, 2, 0, -1], -9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 2, -1, -1], -18), ([0, 0, -1, 1, 2, 0, -2], -18), ([0, 0, -1, 2, 1, -1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 1, -2, 1, 1, 0, -1], -9), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 1, 1, -1, -1], -9), ([0, 1, -1, 1, 1, 0, -2], 18), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 1, 2, 0, -1], 9)]

def combined166_part1 : Sparse := [([1, -1, -1, 2, 1, 0, -1], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, 0, -2, 1, 2, 0, -1], 27), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 0, 2, 0, -1], -9), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 1, 1, 1, -2], 18), ([1, 0, -1, 1, 2, -1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], 9), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, -1, 2, 1, 0, -2], -18), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 0, 1, 1, 0, -2], 18), ([1, 1, -2, 1, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], -9)]

def combined166 : Sparse := combined166_part0 ++ combined166_part1

def combined167_part0 : Sparse := [([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, -1, 1, 2, 0, -1], 18), ([0, 0, -2, 1, 1, 1, -1], 18), ([0, 0, -2, 1, 2, 0, -1], 18), ([0, 0, -2, 2, 1, 0, -1], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 1, 0, 0, 0], 18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 1, 2, -1, -1], -18), ([0, 0, -1, 1, 2, 0, -2], -18), ([0, 0, -1, 2, 1, -1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 1, -2, 1, 1, 0, -1], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 1, 1, 0, -2], 18), ([1, -1, -1, 2, 1, 0, -1], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, 0, -2, 1, 2, 0, -1], 18), ([1, 0, -1, 0, 1, 0, 0], -18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, -1, 1, 1, -1, 0], 18)]

def combined167_part1 : Sparse := [([1, 0, -1, 1, 1, 1, -2], 18), ([1, 0, -1, 1, 2, -1, -1], -18), ([1, 0, -1, 2, 1, 0, -2], -18), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 1, -2, 1, 1, 0, -1], -18), ([1, 1, -1, 0, 1, 0, -1], 18)]

def combined167 : Sparse := combined167_part0 ++ combined167_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined168_part0 : Sparse := [([0, -1, 0, -1, -1, 2, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, 0, -2, -1, 1, 2], -36), ([0, 0, 0, -1, -2, 1, 2], 27), ([0, 0, 0, -1, -2, 2, 1], -27), ([0, 0, 0, -1, -1, 0, 2], -27), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, -1, -2, 1, 1], 9), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, 0, -1, -2, 1, 1], -9), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([1, -1, 0, -1, -1, 1, 2], -9), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, 0, -1, -1, -1, 1, 2], -9), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, 0, -1, 1, 1], 27)]

def combined168_part1 : Sparse := [([1, 0, 0, -2, -1, 2, 1], -36), ([1, 0, 0, -2, 0, 1, 1], 18), ([1, 0, 0, -1, -2, 1, 2], 27), ([1, 0, 0, -1, -1, 0, 2], -27), ([1, 0, 0, -1, -1, 2, 0], 27), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, 0, -1, -2, 1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 0, -1, -1, 1, 0], -9)]

def combined168 : Sparse := combined168_part0 ++ combined168_part1

def combined169_part0 : Sparse := [([0, -1, 0, -1, -1, 1, 2], 9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -1, -1, -1, 1, 2], -9), ([0, 0, -1, -1, -1, 2, 1], 9), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, 0, -2, -1, 1, 2], -27), ([0, 0, 0, -1, -2, 1, 2], 27), ([0, 0, 0, -1, -2, 2, 1], -27), ([0, 0, 0, -1, -1, 0, 2], -18), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 0, 0, -2, 1, 1], -18), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, -1, -2, 1, 1], 9), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, 0, -2, -1, 1, 1], 9), ([0, 1, 0, -1, -2, 1, 1], -9), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 0, -1, -1, 1, 0], -27), ([1, -1, 0, -1, -1, 2, 1], 9), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 1, -1, -1, 1, 1], 18)]

def combined169_part1 : Sparse := [([1, 0, -1, -1, -1, 1, 2], -9), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, 0, -2, -1, 2, 1], -27), ([1, 0, 0, -2, 0, 1, 1], 18), ([1, 0, 0, -1, -2, 1, 2], 27), ([1, 0, 0, -1, -1, 0, 2], -18), ([1, 0, 0, -1, -1, 2, 0], 18), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, 0, -2, 1, 1], -18), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, -2, -1, 1, 1], 9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, 0, -1, -2, 1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], 27)]

def combined169 : Sparse := combined169_part0 ++ combined169_part1

def combined170_part0 : Sparse := [([0, -1, 0, -1, -1, 1, 2], 18), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -1, -1, -1, 1, 2], -18), ([0, 0, -1, -1, -1, 2, 1], 9), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, 0, -2, -1, 1, 2], -18), ([0, 0, 0, -1, -2, 1, 2], 18), ([0, 0, 0, -1, -2, 2, 1], -27), ([0, 0, 0, -1, -1, 0, 2], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 0, 0, -2, 1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, -2, -1, 1, 1], -9), ([0, 0, 1, -1, -2, 1, 1], 9), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, 0, -2, -1, 1, 1], 9), ([0, 1, 0, -1, -2, 1, 1], -9), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, -1, -1, 1, 0], -27), ([1, -1, 0, -1, -1, 2, 1], 9)]

def combined170_part1 : Sparse := [([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], -18), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, 0, -2, -1, 2, 1], -27), ([1, 0, 0, -2, 0, 1, 1], 9), ([1, 0, 0, -1, -2, 1, 2], 18), ([1, 0, 0, -1, -1, 0, 2], -18), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, 0, -2, 1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 1, -2, -1, 1, 1], 9), ([1, 0, 1, -1, -2, 1, 1], -9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, 0, -2, -1, 1, 1], -9), ([1, 1, 0, -1, -2, 1, 1], -18), ([1, 1, 0, -1, -1, 0, 1], 18)]

def combined170 : Sparse := combined170_part0 ++ combined170_part1

def combined171_part0 : Sparse := [([0, -1, 0, -1, -1, 1, 2], 18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -1, -1, -1, 1, 2], -18), ([0, 0, -1, -1, -1, 2, 1], 18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, 0, -2, -1, 1, 2], -18), ([0, 0, 0, -1, -2, 1, 2], 18), ([0, 0, 0, -1, -2, 2, 1], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 0, 1, -1, -2, 1, 1], 18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 1, 0, -2, -1, 1, 1], 18), ([0, 1, 0, -1, -2, 1, 1], -18), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, -1, -1, 1, 0], -18), ([1, -1, 0, -1, -1, 2, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, 0, -1, -1, -1, 1, 2], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, 0, -2, -1, 2, 1], -18), ([1, 0, 0, -1, -2, 1, 2], 18)]

def combined171_part1 : Sparse := [([1, 0, 0, -1, 0, 1, 0], 18), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 1, -2, -1, 1, 1], 18), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 1, 0, -1, -2, 1, 1], -18), ([1, 1, 0, -1, -1, 0, 1], 18)]

def combined171 : Sparse := combined171_part0 ++ combined171_part1

def combined172_part0 : Sparse := [([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, 0, -2, 1, -1, 2], -36), ([0, 0, 0, -1, 0, -1, 2], -27), ([0, 0, 0, -1, 1, -2, 2], 27), ([0, 0, 0, -1, 2, -2, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 0, 0, 1, -2, 1], -36), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, -1, 1, -2, 1], -9), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, -1, 1, -2, 1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([1, -1, 0, -1, 1, -1, 2], -9), ([1, -1, 0, -1, 2, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 1, -1, 1, -1, 1], -27), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, -1, -1, 1, 0, 1], -36)]

def combined172_part1 : Sparse := [([1, 0, 0, -2, 1, 0, 1], 18), ([1, 0, 0, -2, 2, -1, 1], -36), ([1, 0, 0, -1, 0, -1, 2], -27), ([1, 0, 0, -1, 1, -2, 2], 27), ([1, 0, 0, -1, 2, -1, 0], 27), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 0, 0, 1, -2, 1], -36), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, -1, 1, -2, 1], -9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, -1, 1, -1, 0], -36)]

def combined172 : Sparse := combined172_part0 ++ combined172_part1

def combined173_part0 : Sparse := [([0, -1, 0, -1, 1, -1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, 0, -1, -1, 1, -1, 2], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, 0, -2, 1, -1, 2], -27), ([0, 0, 0, -1, 0, -1, 2], -27), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 0, -1, 1, -2, 2], 18), ([0, 0, 0, -1, 2, -2, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 0, 0, 1, -2, 1], -27), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 1, -2, 1], -9), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 1, 0, -2, 1, -1, 1], -9), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 1, 0, -1, 1, -2, 1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([1, -1, 0, -1, 1, -1, 2], -18)]

def combined173_part1 : Sparse := [([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 2, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, 0, -2, 1, 0, 1], 9), ([1, 0, 0, -2, 2, -1, 1], -36), ([1, 0, 0, -1, 0, -1, 2], -27), ([1, 0, 0, -1, 1, -2, 2], 18), ([1, 0, 0, -1, 2, -1, 0], 9), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 0, 0, 1, -2, 1], -27), ([1, 0, 1, -2, 1, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, -1, 1, -2, 1], -18), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, -1, 1, -2, 1], -9), ([1, 1, 0, -1, 1, -1, 0], -36)]

def combined173 : Sparse := combined173_part0 ++ combined173_part1

def combined174_part0 : Sparse := [([0, -1, 0, -1, 1, -1, 2], -18), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, -1, 2, -1, 1], 9), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, 0, -1, -1, 1, -1, 2], 18), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, 0, -2, 1, -1, 2], -18), ([0, 0, 0, -1, 0, -1, 2], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 0, -1, 1, -2, 2], 18), ([0, 0, 0, -1, 2, -2, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 0, 0, 1, -2, 1], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -2, 1, -1, 1], 9), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 1, -2, 1], -9), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 1, 0, -2, 1, -1, 1], -9), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, -1, 1, -2, 1], 9), ([1, -1, 0, -1, 1, -1, 2], -18)]

def combined174_part1 : Sparse := [([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 2, -1, 1], 9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, 0, -2, 1, 0, 1], 9), ([1, 0, 0, -2, 2, -1, 1], -27), ([1, 0, 0, -1, 0, -1, 2], -18), ([1, 0, 0, -1, 1, -2, 2], 18), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 0, 0, 1, -2, 1], -9), ([1, 0, 1, -2, 1, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, -1, 1, -2, 1], -18), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, 0, -2, 1, -1, 1], 9), ([1, 1, 0, -1, 1, -2, 1], -9), ([1, 1, 0, -1, 1, -1, 0], -27)]

def combined174 : Sparse := combined174_part0 ++ combined174_part1

def combined175_part0 : Sparse := [([0, -1, 0, -1, 1, -1, 2], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 2, -1, 1], 18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, 0, -1, -1, 1, -1, 2], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, 0, -2, 1, -1, 2], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 0, -1, 1, -2, 2], 18), ([0, 0, 0, -1, 2, -2, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 1, -2, 1, -1, 1], 18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 1, -2, 1], -18), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, -1, 1, -2, 1], 18), ([1, -1, 0, -1, 1, -1, 2], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, -1, 2, -1, 1], 18), ([1, 0, 0, -2, 2, -1, 1], -18), ([1, 0, 0, -1, 1, -2, 2], 18)]

def combined175_part1 : Sparse := [([1, 0, 0, -1, 1, 0, 0], 18), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, -1, 1, -2, 1], -18), ([1, 1, 0, -2, 1, -1, 1], 18), ([1, 1, 0, -1, 1, -1, 0], -18)]

def combined175 : Sparse := combined175_part0 ++ combined175_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined176_part0 : Sparse := [([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -18), ([0, 0, 0, -2, 1, 2, -1], -36), ([0, 0, 0, -2, 2, 1, -1], -36), ([0, 0, 0, -1, 0, 2, -1], -27), ([0, 0, 0, -1, 1, 2, -2], -27), ([0, 0, 0, -1, 2, 0, -1], -27), ([0, 0, 0, -1, 2, 1, -2], -27), ([0, 0, 0, 0, 1, 1, -2], -36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 1, 0, -1, 1, 0, -1], -36), ([1, -1, 0, -1, 1, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], -27)]

def combined176_part1 : Sparse := [([1, 0, -1, -1, 2, 1, -1], 9), ([1, 0, 0, -2, 1, 1, 0], -18), ([1, 0, 0, -1, 0, 2, -1], -27), ([1, 0, 0, -1, 2, 0, -1], -27), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 1, -2], -36), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 1, 1, -2], 9), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, -1, 1, 1, -2], 9)]

def combined176 : Sparse := combined176_part0 ++ combined176_part1

def combined177_part0 : Sparse := [([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, 0, -2, 1, 1, 0], -9), ([0, 0, 0, -2, 1, 2, -1], -27), ([0, 0, 0, -2, 2, 1, -1], -36), ([0, 0, 0, -1, 0, 2, -1], -27), ([0, 0, 0, -1, 1, 2, -2], -18), ([0, 0, 0, -1, 2, 0, -1], -9), ([0, 0, 0, -1, 2, 1, -2], -27), ([0, 0, 0, 0, 1, 1, -2], -27), ([0, 0, 1, -2, 1, 1, -1], -9), ([0, 0, 1, -1, 0, 1, -1], -27), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, -1, 1, 1, -2], 9), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, 0, -2, 1, 1, -1], 9), ([0, 1, 0, -1, 0, 1, -1], -18)]

def combined177_part1 : Sparse := [([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, -1, 1, 1, -2], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 1, 2, -1], 18), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 1, 2, -1], 9), ([1, 0, -1, -1, 2, 1, -1], 9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, 0, -2, 1, 1, 0], -9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 2, -1], -27), ([1, 0, 0, -1, 2, 0, -1], -9), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 1, -2], -27), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 1, 1, -2], 18), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, 0, -2, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9)]

def combined177_part2 : Sparse := [([1, 1, 0, -1, 1, 1, -2], 9)]

def combined177 : Sparse := combined177_part0 ++ combined177_part1 ++ combined177_part2

def combined178_part0 : Sparse := [([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, 0, -2, 1, 2, -1], -27), ([0, 0, 0, -2, 2, 1, -1], -27), ([0, 0, 0, -1, 0, 2, -1], -9), ([0, 0, 0, -1, 1, 2, -2], -18), ([0, 0, 0, -1, 2, 0, -1], -9), ([0, 0, 0, -1, 2, 1, -2], -18), ([0, 0, 0, 0, 1, 1, -2], -18), ([0, 0, 1, -1, 0, 1, -1], -27), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 1, 0, -1, 1, 0, -1], -27), ([1, -1, 0, -1, 1, 2, -1], 18), ([1, -1, 0, -1, 2, 1, -1], 9), ([1, -1, 1, -1, 1, 1, -1], -9)]

def combined178_part1 : Sparse := [([1, 0, -1, -1, 1, 2, -1], 9), ([1, 0, -1, -1, 2, 1, -1], 18), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 2, -1], -9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 0, -1, 2, 0, -1], -9), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 0, 0, 1, 1, -2], -18), ([1, 0, 1, -2, 1, 1, -1], 9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 1, 1, -2], 18), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, 0, -2, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, -1, 1, 1, -2], 18)]

def combined178 : Sparse := combined178_part0 ++ combined178_part1

def combined179 : Sparse := [([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, 0, -2, 1, 2, -1], -18), ([0, 0, 0, -2, 2, 1, -1], -18), ([0, 0, 0, -1, 1, 2, -2], -18), ([0, 0, 0, -1, 2, 1, -2], -18), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 1, 0, -1, 1, 0, -1], -18), ([1, -1, 0, -1, 1, 2, -1], 18), ([1, -1, 0, -1, 2, 1, -1], 18), ([1, 0, -1, -1, 1, 2, -1], 18), ([1, 0, -1, -1, 2, 1, -1], 18), ([1, 0, 0, -1, 0, 1, 0], 18), ([1, 0, 0, -1, 1, 0, 0], 18), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 1, -2, 1, 1, -1], 18), ([1, 0, 1, -1, 1, 1, -2], 18), ([1, 1, 0, -2, 1, 1, -1], 18), ([1, 1, 0, -1, 1, 1, -2], 18)]

def combined180_part0 : Sparse := [([0, -1, 0, 1, -1, -1, 2], -9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -1, 1, -1, -1, 2], -9), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 0, 1, -2, -1, 2], -27), ([0, 0, 0, 1, -1, -2, 2], -27), ([0, 0, 0, 2, -2, -1, 1], -36), ([0, 0, 0, 2, -1, -2, 1], -36), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 1, -1, -2, 1], -9), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 0, 1, -2, -1, 1], -9), ([0, 1, 0, 1, -1, -1, 0], -36), ([1, -1, 0, 1, -1, -1, 2], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, 0, -1, 1, -1, -1, 2], -9), ([1, 0, -1, 1, -1, 0, 1], -9)]

def combined180_part1 : Sparse := [([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 0, -1, -1, 2], 36), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 0, 1, -2, 0, 1], 27), ([1, 0, 0, 1, 0, -2, 1], 27), ([1, 0, 0, 2, -1, -1, 0], 18), ([1, 0, 1, 1, -2, -1, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, 0, 1, -1, -2, 1], -9)]

def combined180 : Sparse := combined180_part0 ++ combined180_part1

def combined181_part0 : Sparse := [([0, -1, 0, 1, -1, -1, 2], -18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -1, 1, -1, -1, 2], -9), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 2, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 0, 1, -2, -1, 2], -27), ([0, 0, 0, 1, -1, -2, 2], -18), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 2, -2, -1, 1], -36), ([0, 0, 0, 2, -1, -2, 1], -27), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 1, -1, -2, 1], -18), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 1, -2, -1, 1], -9), ([0, 1, 0, 1, -1, -2, 1], -9), ([0, 1, 0, 1, -1, -1, 0], -36), ([1, -1, 0, 1, -1, -1, 2], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9)]

def combined181_part1 : Sparse := [([1, -1, 0, 2, -1, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, 0, -1, 1, -1, -1, 2], -18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 0, -1, -1, 2], 27), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 0, 1, -2, 0, 1], 9), ([1, 0, 0, 1, 0, -2, 1], 27), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 0, 2, -1, -1, 0], 9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 1, -2, -1, 1], -9), ([1, 0, 1, 1, -1, -2, 1], -9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 1, -1, -2, 1], -18), ([1, 1, 0, 1, -1, -1, 0], -9)]

def combined181 : Sparse := combined181_part0 ++ combined181_part1

def combined182_part0 : Sparse := [([0, -1, 0, 1, -1, -1, 2], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, -1, 0, 2, -1, -1, 1], -9), ([0, 0, -1, 1, -1, -1, 2], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 2, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 0, 1, -2, -1, 2], -18), ([0, 0, 0, 1, -1, -2, 2], -18), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 2, -2, -1, 1], -27), ([0, 0, 0, 2, -1, -2, 1], -27), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 1, -2, -1, 1], -9), ([0, 0, 1, 1, -1, -2, 1], -18), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 1, -2, -1, 1], -18), ([0, 1, 0, 1, -1, -2, 1], -9), ([0, 1, 0, 1, -1, -1, 0], -27)]

def combined182_part1 : Sparse := [([1, -1, 0, 1, -1, -1, 2], -18), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 2, -1, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, 0, -1, 1, -1, -1, 2], -18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 2, -1, -1, 1], -9), ([1, 0, 0, 0, -1, -1, 2], 18), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 0, 1, -2, 0, 1], 9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 0, 1, 0, -2, 1], 9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 1, -2, -1, 1], -18), ([1, 0, 1, 1, -1, -2, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, 0, 1, -2, -1, 1], -9), ([1, 1, 0, 1, -1, -2, 1], -18)]

def combined182 : Sparse := combined182_part0 ++ combined182_part1

def combined183_part0 : Sparse := [([0, -1, 0, 1, -1, -1, 2], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 2, -1, -1, 1], -18), ([0, 0, -1, 1, -1, -1, 2], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, -1, 2, -1, -1, 1], -18), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 0, 1, -2, -1, 2], -18), ([0, 0, 0, 1, -1, -2, 2], -18), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 0, 2, -2, -1, 1], -18), ([0, 0, 0, 2, -1, -2, 1], -18), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 1, -2, -1, 1], -18), ([0, 0, 1, 1, -1, -2, 1], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 1, -2, -1, 1], -18), ([0, 1, 0, 1, -1, -2, 1], -18), ([0, 1, 0, 1, -1, -1, 0], -18)]

def combined183_part1 : Sparse := [([1, -1, 0, 1, -1, -1, 2], -18), ([1, -1, 0, 2, -1, -1, 1], -18), ([1, 0, -1, 1, -1, -1, 2], -18), ([1, 0, -1, 2, -1, -1, 1], -18), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 0, 0, 1, 0, -1, 0], -18), ([1, 0, 1, 1, -2, -1, 1], -18), ([1, 0, 1, 1, -1, -2, 1], -18), ([1, 1, 0, 1, -2, -1, 1], -18), ([1, 1, 0, 1, -1, -2, 1], -18)]

def combined183 : Sparse := combined183_part0 ++ combined183_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined184_part0 : Sparse := [([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, -1, 2, -1], 9), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 0, 1, -2, 1, 0], -27), ([0, 0, 0, 1, -2, 2, -1], -27), ([0, 0, 0, 2, -2, 1, -1], 36), ([0, 0, 0, 2, -1, 0, -1], -18), ([0, 0, 0, 2, -1, 1, -2], -36), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 1, -2, 1, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, -1, 1, -2], 9), ([0, 1, 0, 1, -2, 1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, -1, 1, -2], 9), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, -1, 2, -1], 9)]

def combined184_part1 : Sparse := [([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, 0, 0, -1, 2, -1], 36), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 0, 1, -2, 1, 0], -27), ([1, 0, 0, 1, -1, 2, -2], -27), ([1, 0, 0, 1, 0, 1, -2], 27), ([1, 0, 0, 2, -2, 1, -1], 36), ([1, 0, 0, 2, -1, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, -1, 1, -2], 9)]

def combined184 : Sparse := combined184_part0 ++ combined184_part1

def combined185_part0 : Sparse := [([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, -1, 2, -1], 18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 0, 2, -1, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 2, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 0, 1, -2, 1, 0], -9), ([0, 0, 0, 1, -2, 2, -1], -27), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 0, 2, -2, 1, -1], 36), ([0, 0, 0, 2, -1, 0, -1], -9), ([0, 0, 0, 2, -1, 1, -2], -27), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 1, -2, 1, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, -1, 1, -2], 18), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 1, -2, 1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 0, 1, -1, 1, -2], 9)]

def combined185_part1 : Sparse := [([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 1, -1, 2, -1], 9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, -1, 2, -1], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 2, -1], 27), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 0, 1, -2, 1, 0], -9), ([1, 0, 0, 1, -1, 2, -2], -18), ([1, 0, 0, 1, 0, 1, -2], 27), ([1, 0, 0, 2, -2, 1, -1], 36), ([1, 0, 0, 2, -1, 0, -1], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 1, -2], 18)]

def combined185 : Sparse := combined185_part0 ++ combined185_part1

def combined186_part0 : Sparse := [([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, -1, 2, -1], 18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 0, 2, -1, 1, -1], -18), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 2, -1, 1, -1], 18), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 0, 1, -2, 2, -1], -27), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 0, 2, -2, 1, -1], 27), ([0, 0, 0, 2, -1, 0, -1], -9), ([0, 0, 0, 2, -1, 1, -2], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 1, -2, 1, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, -1, 1, -2], 18), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 1, -2, 1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], -18), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, -1, 2, -1], 9)]

def combined186_part1 : Sparse := [([1, -1, 0, 2, -1, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, 0, -1, 1, -1, 2, -1], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 2, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 0, 1, -1, 2, -2], -18), ([1, 0, 0, 1, 0, 1, -2], 18), ([1, 0, 0, 2, -2, 1, -1], 27), ([1, 0, 0, 2, -1, 0, -1], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 1, 1, -2, 1, -1], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 1, -2], 18)]

def combined186 : Sparse := combined186_part0 ++ combined186_part1

def combined187_part0 : Sparse := [([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, -1, 2, -1], 18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 0, 2, -1, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 2, -1, 1, -1], 18), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 0, 0, 1, -2, 2, -1], -18), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 0, 2, -2, 1, -1], 18), ([0, 0, 0, 2, -1, 1, -2], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 1, -2, 1, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, -1, 1, -2], 18), ([0, 1, 0, 1, -2, 1, -1], 18), ([0, 1, 0, 1, -1, 0, -1], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 2, -1, 1, -1], -18), ([1, 0, -1, 1, -1, 2, -1], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 0, 1, -1, 0, 0], -18)]

def combined187_part1 : Sparse := [([1, 0, 0, 1, -1, 2, -2], -18), ([1, 0, 0, 2, -2, 1, -1], 18), ([1, 0, 1, 1, -2, 1, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 1, -1, 1, -2], 18)]

def combined187 : Sparse := combined187_part0 ++ combined187_part1

def combined188_part0 : Sparse := [([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 2, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 0, 1, 1, -2, 0], -27), ([0, 0, 0, 1, 2, -2, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -18), ([0, 0, 0, 2, 1, -2, -1], 36), ([0, 0, 0, 2, 1, -1, -2], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 1, 1, -2, -1], 9), ([0, 0, 1, 1, 1, -1, -2], 9), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 1, -2, -1], -9), ([0, 1, 0, 1, 1, -1, -2], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 1, 2, -1, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, 0, -1, 1, 1, -1, 0], 36)]

def combined188_part1 : Sparse := [([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 0, 1, 1, -2, 0], -27), ([1, 0, 0, 1, 1, 0, -2], 27), ([1, 0, 0, 1, 2, -1, -2], -27), ([1, 0, 0, 2, 0, -1, -1], -18), ([1, 0, 0, 2, 1, -2, -1], 36), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 1, 1, -1, -2], 9), ([1, 1, -1, 1, 1, -1, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 1, 1, -1, -2], 9)]

def combined188 : Sparse := combined188_part0 ++ combined188_part1

def combined189_part0 : Sparse := [([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 0, 2, 1, -1, -1], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, -1, 1, 2, -1, -1], 9), ([0, 0, -1, 2, 1, -1, -1], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 0, 1, 1, -2, 0], -18), ([0, 0, 0, 1, 2, -2, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -18), ([0, 0, 0, 2, 1, -2, -1], 27), ([0, 0, 0, 2, 1, -1, -2], -27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 1, -2, -1], 9), ([0, 1, -1, 1, 1, -1, -1], -18), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 0, 1, 1, -2, -1], -9), ([0, 1, 0, 1, 1, -1, -2], 9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 1, 2, -1, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 18)]

def combined189_part1 : Sparse := [([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 2, 1, -1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 2, -1, -1], 18), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 0, 1, 1, -2, 0], -18), ([1, 0, 0, 1, 1, 0, -2], 18), ([1, 0, 0, 1, 2, -1, -2], -27), ([1, 0, 0, 2, 0, -1, -1], -18), ([1, 0, 0, 2, 1, -2, -1], 27), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 1, 1, -1, -2], 9), ([1, 1, -1, 1, 1, -1, -1], -18), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 0, 1, 1, -2, -1], -9)]

def combined189 : Sparse := combined189_part0 ++ combined189_part1

def combined190_part0 : Sparse := [([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 0, 1, 2, -1, -1], 9), ([0, -1, 0, 2, 1, -1, -1], 18), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 2, -1, -1], 18), ([0, 0, -1, 2, 1, -1, -1], -18), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 0, 1, 2, -2, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -9), ([0, 0, 0, 2, 1, -2, -1], 27), ([0, 0, 0, 2, 1, -1, -2], -18), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 1, -2, -1], 9), ([0, 1, -1, 1, 1, -1, -1], -9), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 1, 1, -2, -1], -9), ([0, 1, 0, 1, 1, -1, -2], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 0, 1, 2, -1, -1], 18)]

def combined190_part1 : Sparse := [([1, -1, 0, 2, 1, -1, -1], 9), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 1, 2, -1, -1], 9), ([1, 0, -1, 2, 1, -1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 0, 0, 2, -1, -1], 9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 0, 1, 1, 0, -2], 18), ([1, 0, 0, 1, 2, -1, -2], -18), ([1, 0, 0, 2, 0, -1, -1], -9), ([1, 0, 0, 2, 1, -2, -1], 27), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 1, -1, -2], 18), ([1, 1, -1, 1, 1, -1, -1], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 0, 1, 1, -2, -1], -9)]

def combined190 : Sparse := combined190_part0 ++ combined190_part1

def combined191_part0 : Sparse := [([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 0, 2, 1, -1, -1], 18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, -1, 1, 2, -1, -1], 18), ([0, 0, -1, 2, 1, -1, -1], -18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 0, 0, 1, 0, -1, 0], -18), ([0, 0, 0, 1, 0, 0, -1], 18), ([0, 0, 0, 1, 2, -2, -1], -18), ([0, 0, 0, 2, 1, -2, -1], 18), ([0, 0, 0, 2, 1, -1, -2], -18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 1, -2, -1], 18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 1, 1, -2, -1], -18), ([0, 1, 0, 1, 1, -1, -2], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 0, 1, 2, -1, -1], 18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, -1, 2, 1, -1, -1], -18), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 0, 1, 0, -1, 0], -18)]

def combined191_part1 : Sparse := [([1, 0, 0, 1, 2, -1, -2], -18), ([1, 0, 0, 2, 1, -2, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 1, 1, -1, -2], 18), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 1, 1, -2, -1], -18)]

def combined191 : Sparse := combined191_part0 ++ combined191_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined192_part0 : Sparse := [([0, -1, 1, -1, -1, 0, 2], 9), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, 0, 0, -1, -1, 0, 2], -36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 1, -2, -1, 0, 2], 27), ([0, 0, 1, -2, 0, 0, 1], -27), ([0, 0, 1, -1, -2, 0, 2], -27), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -1, -1, 2], -9), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 2, -2, -1, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 1, -1, -1, -1, 1], -27), ([0, 1, 1, -1, -1, 0, 0], -36), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, 0, 0, -1, -1, 0, 2], -36), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 1, -2, -1, 0, 2], 27)]

def combined192_part1 : Sparse := [([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 0, 1], -27), ([1, 0, 1, -1, -1, -1, 2], -9), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, -2, 0, 1], 27), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 2, -1, -2, 0, 1], -36), ([1, 0, 2, -1, -1, 0, 0], 18), ([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 1, -2, -1, 0, 1], -9), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], -27)]

def combined192 : Sparse := combined192_part0 ++ combined192_part1

def combined193_part0 : Sparse := [([0, -1, 1, -1, -1, 0, 2], 18), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 2, -1, -1, 0, 1], 9), ([0, 0, 0, -1, -1, 0, 2], -27), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 1, -2, -1, 0, 2], 27), ([0, 0, 1, -2, 0, 0, 1], -9), ([0, 0, 1, -1, -2, 0, 2], -18), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -1, -1, 2], -18), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 2, -2, -1, 0, 1], -36), ([0, 0, 2, -1, -1, -1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 1, -1, -2, 0, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -18), ([0, 1, 1, -1, -1, 0, 0], -27), ([1, -1, 1, -1, -1, 0, 2], 9), ([1, -1, 1, -1, -1, 1, 1], 18)]

def combined193_part1 : Sparse := [([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 2, -1, -1, 0, 1], 9), ([1, 0, 0, -1, -1, 0, 2], -27), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 1, -2, -1, 0, 2], 27), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 0, 1], -9), ([1, 0, 1, -1, -2, 1, 1], 9), ([1, 0, 1, -1, -1, -1, 2], -9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, -2, 0, 1], 27), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 2, -1, -2, 0, 1], -27), ([1, 0, 2, -1, -1, -1, 1], 9), ([1, 0, 2, -1, -1, 0, 0], 9), ([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 1, -2, -1, 0, 1], -9), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], -18), ([1, 1, 1, -1, -1, 0, 0], 9)]

def combined193 : Sparse := combined193_part0 ++ combined193_part1

def combined194_part0 : Sparse := [([0, -1, 1, -1, -1, 0, 2], 18), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, 0, 0, -1, -1, 0, 2], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 1, -2, -1, 0, 2], 18), ([0, 0, 1, -2, -1, 1, 1], 9), ([0, 0, 1, -2, 0, 0, 1], -9), ([0, 0, 1, -1, -2, 0, 2], -18), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -1, -1, 2], -18), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 2, -2, -1, 0, 1], -27), ([0, 0, 2, -1, -1, -1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 1, -2, -1, 0, 1], -9), ([0, 1, 1, -1, -2, 0, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -9), ([0, 1, 1, -1, -1, 0, 0], -27), ([1, -1, 1, -1, -1, 1, 1], 9)]

def combined194_part1 : Sparse := [([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 2, -1, -1, 0, 1], 9), ([1, 0, 0, -1, -1, 0, 2], -18), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 1, -2, -1, 0, 2], 18), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 0, 1], -9), ([1, 0, 1, -1, -2, 1, 1], 9), ([1, 0, 1, -1, -1, -1, 2], -18), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, 0, -2, 0, 1], 9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 2, -1, -2, 0, 1], -27), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 1, -2, -1, 0, 1], -18), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], -9)]

def combined194 : Sparse := combined194_part0 ++ combined194_part1

def combined195_part0 : Sparse := [([0, -1, 1, -1, -1, 0, 2], 18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], -18), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 1, -2, -1, 0, 2], 18), ([0, 0, 1, -2, -1, 1, 1], 18), ([0, 0, 1, -1, -2, 0, 2], -18), ([0, 0, 1, -1, -1, -1, 2], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], 18), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 2, -2, -1, 0, 1], -18), ([0, 0, 2, -1, -1, -1, 1], 18), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 1, -2, -1, 0, 1], -18), ([0, 1, 1, -1, -2, 0, 1], 18), ([0, 1, 1, -1, -1, 0, 0], -18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 2, -1, -1, 0, 1], 18), ([1, 0, 0, -1, 0, 0, 1], -18), ([1, 0, 1, -2, -1, 0, 2], 18), ([1, 0, 1, -1, -2, 1, 1], 18), ([1, 0, 1, -1, -1, -1, 2], -18)]

def combined195_part1 : Sparse := [([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, 0, -1, 0, 0], 18), ([1, 0, 2, -1, -2, 0, 1], -18), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 1, -2, -1, 0, 1], -18)]

def combined195 : Sparse := combined195_part0 ++ combined195_part1

def combined196_part0 : Sparse := [([0, -1, 1, -1, -1, 2, 0], -9), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 1, -2, -1, 2, 0], -27), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -2, 2, 0], -27), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 2, -2, -1, 1, 0], -36), ([0, 0, 2, -1, -2, 1, 0], -36), ([0, 1, 0, -1, -1, 1, 0], -27), ([0, 1, 1, -2, -1, 1, 0], -9), ([0, 1, 1, -1, -1, 0, 0], -36), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, -1, -1, 2, 0], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, 0, 0, -1, -1, 2, 0], 36), ([1, 0, 0, -1, 0, 1, 0], -9)]

def combined196_part1 : Sparse := [([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 1, 0], 27), ([1, 0, 1, -1, -1, 2, -1], -9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], 27), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 2, -1, -1, 0, 0], 18), ([1, 1, 1, -1, -2, 1, 0], -9), ([1, 1, 1, -1, -1, 1, -1], 27)]

def combined196 : Sparse := combined196_part0 ++ combined196_part1

def combined197_part0 : Sparse := [([0, -1, 1, -1, -1, 2, 0], -18), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 1, -2, -1, 2, 0], -27), ([0, 0, 1, -1, -2, 1, 1], -18), ([0, 0, 1, -1, -2, 2, 0], -18), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 2, -2, -1, 1, 0], -36), ([0, 0, 2, -1, -2, 1, 0], -27), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 1, -2, -1, 1, 0], -9), ([0, 1, 1, -1, -2, 1, 0], -9), ([0, 1, 1, -1, -1, 0, 0], -36), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, -1, 1, -1, -1, 2, 0], -9), ([1, -1, 1, -1, 0, 1, 0], 9)]

def combined197_part1 : Sparse := [([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 2, -1, -1, 1, 0], -9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, -1, -1, 2, 0], 27), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 1, 0], 9), ([1, 0, 1, -1, -2, 1, 1], -9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, -1, 2, -1], -18), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], 27), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 2, -1, -1, 0, 0], 9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 1, -1, -2, 1, 0], -18), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], 18)]

def combined197 : Sparse := combined197_part0 ++ combined197_part1

def combined198_part0 : Sparse := [([0, -1, 1, -1, -1, 2, 0], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 2, -1, -1, 1, 0], -9), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 1, -2, -1, 1, 1], -9), ([0, 0, 1, -2, -1, 2, 0], -18), ([0, 0, 1, -1, -2, 1, 1], -18), ([0, 0, 1, -1, -2, 2, 0], -18), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, -1, 2, -1], -18), ([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 0, 1, -1], -27), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 2, -2, -1, 1, 0], -27), ([0, 0, 2, -1, -2, 1, 0], -27), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 1, -2, -1, 1, 0], -18), ([0, 1, 1, -1, -2, 1, 0], -9), ([0, 1, 1, -1, -1, 0, 0], -27)]

def combined198_part1 : Sparse := [([1, -1, 1, -1, -1, 1, 1], 9), ([1, -1, 1, -1, -1, 2, 0], -18), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 2, -1, -1, 1, 0], -9), ([1, 0, 0, -1, -1, 2, 0], 18), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 1, -2, -1, 1, 1], -18), ([1, 0, 1, -2, 0, 1, 0], 9), ([1, 0, 1, -1, -2, 1, 1], -9), ([1, 0, 1, -1, -1, 2, -1], -18), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], 9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 2, -1, -1, 1, -1], -9), ([1, 1, 1, -2, -1, 1, 0], -9), ([1, 1, 1, -1, -2, 1, 0], -18), ([1, 1, 1, -1, -1, 1, -1], 9)]

def combined198 : Sparse := combined198_part0 ++ combined198_part1

def combined199_part0 : Sparse := [([0, -1, 1, -1, -1, 2, 0], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 2, -1, -1, 1, 0], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], -18), ([0, 0, 1, -2, -1, 1, 1], -18), ([0, 0, 1, -2, -1, 2, 0], -18), ([0, 0, 1, -1, -2, 1, 1], -18), ([0, 0, 1, -1, -2, 2, 0], -18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, -1, 2, -1], -18), ([0, 0, 1, -1, 0, 0, 0], -18), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, 0, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 2, -2, -1, 1, 0], -18), ([0, 0, 2, -1, -2, 1, 0], -18), ([0, 0, 2, -1, -1, 1, -1], -18), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 1, -2, -1, 1, 0], -18), ([0, 1, 1, -1, -2, 1, 0], -18), ([0, 1, 1, -1, -1, 0, 0], -18)]

def combined199_part1 : Sparse := [([1, -1, 1, -1, -1, 2, 0], -18), ([1, -1, 2, -1, -1, 1, 0], -18), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, 0, -1, 1, 0], -18), ([1, 0, 1, -2, -1, 1, 1], -18), ([1, 0, 1, -1, -2, 1, 1], -18), ([1, 0, 1, -1, -1, 2, -1], -18), ([1, 0, 1, -1, 0, 0, 0], -18), ([1, 0, 1, 0, -1, 0, 0], -18), ([1, 0, 2, -1, -1, 1, -1], -18), ([1, 1, 1, -2, -1, 1, 0], -18), ([1, 1, 1, -1, -2, 1, 0], -18)]

def combined199 : Sparse := combined199_part0 ++ combined199_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined200_part0 : Sparse := [([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, 0, 0, -1, 0, -1, 2], -36), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 1, -2, 0, -1, 2], -27), ([0, 0, 1, -2, 0, 0, 1], -27), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, 0, -2, 2], -27), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 0, 0, -2, 1], -27), ([0, 0, 2, -2, 0, -1, 1], -36), ([0, 0, 2, -1, 0, -2, 1], -36), ([0, 0, 2, -1, 0, -1, 0], -18), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -27), ([0, 1, 1, -1, 0, -2, 1], -9), ([0, 1, 1, -1, 0, -1, 0], -36), ([1, -1, 1, -1, 0, -1, 2], 9), ([1, -1, 1, -1, 0, 0, 1], 9)]

def combined200_part1 : Sparse := [([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, 0, 0, -1, 0, -1, 2], -36), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 1, -2, 0, 0, 1], -27), ([1, 0, 1, -1, -1, -1, 2], 9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 1, -2, 1], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, 0, -2, 1], -27), ([1, 0, 2, -1, 0, -1, 0], -18), ([1, 1, 1, -2, 0, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], -27)]

def combined200 : Sparse := combined200_part0 ++ combined200_part1

def combined201_part0 : Sparse := [([0, -1, 1, -1, 0, -1, 2], 9), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 2, -1, 0, -1, 1], -9), ([0, 0, 0, -1, 0, -1, 2], -27), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 1, -2, 0, -1, 2], -27), ([0, 0, 1, -2, 0, 0, 1], -9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -1, -1, -1, 2], -9), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, 0, -2, 2], -18), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, 0, -2, 1], -27), ([0, 0, 2, -2, 0, -1, 1], -36), ([0, 0, 2, -1, -1, -1, 1], 9), ([0, 0, 2, -1, 0, -2, 1], -27), ([0, 0, 2, -1, 0, -1, 0], -9), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -18)]

def combined201_part1 : Sparse := [([0, 1, 1, -1, 0, -2, 1], -9), ([0, 1, 1, -1, 0, -1, 0], -36), ([1, -1, 1, -1, 0, -1, 2], 18), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, 0, 0, -1, 0, -1, 2], -27), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 1, -2, 0, 0, 1], -9), ([1, 0, 1, -1, -1, -1, 2], 9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 1, -2, 1], 18), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, 0, -2, 1], -27), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 2, -1, -1, -1, 1], 9), ([1, 0, 2, -1, 0, -1, 0], -9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 1, -2, 0, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], -18), ([1, 1, 1, -1, 0, -2, 1], 9)]

def combined201_part2 : Sparse := [([1, 1, 1, -1, 0, -1, 0], -9)]

def combined201 : Sparse := combined201_part0 ++ combined201_part1 ++ combined201_part2

def combined202_part0 : Sparse := [([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, 0, 0, -1, 0, -1, 2], -18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 1, -2, 0, -1, 2], -18), ([0, 0, 1, -2, 0, 0, 1], -9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, 0, -2, 2], -18), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, 0, -2, 1], -9), ([0, 0, 2, -2, 0, -1, 1], -27), ([0, 0, 2, -1, 0, -2, 1], -27), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -9), ([0, 1, 1, -1, 0, -2, 1], -9), ([0, 1, 1, -1, 0, -1, 0], -27), ([1, -1, 1, -1, 0, -1, 2], 18), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], -9)]

def combined202_part1 : Sparse := [([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 2, -1, 0, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], -18), ([1, 0, 0, -1, 0, 0, 1], 18), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 1, -2, 0, 0, 1], -9), ([1, 0, 1, -2, 1, -1, 1], 9), ([1, 0, 1, -1, -1, -1, 2], 18), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 1, -2, 1], 18), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, 0, -2, 1], -9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 2, -1, -1, -1, 1], 9), ([1, 1, 1, -2, 0, -1, 1], 18), ([1, 1, 1, -1, -1, -1, 1], -9), ([1, 1, 1, -1, 0, -2, 1], 9)]

def combined202 : Sparse := combined202_part0 ++ combined202_part1

def combined203 : Sparse := [([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 1, -2, 0, -1, 2], -18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, 0, -2, 2], -18), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 2, -2, 0, -1, 1], -18), ([0, 0, 2, -1, 0, -2, 1], -18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 1, -1, 0, -1, 0], -18), ([1, -1, 1, -1, 0, -1, 2], 18), ([1, -1, 2, -1, 0, -1, 1], 18), ([1, 0, 0, -1, 0, 0, 1], 18), ([1, 0, 0, 0, 0, -1, 1], 18), ([1, 0, 1, -2, 1, -1, 1], 18), ([1, 0, 1, -1, -1, -1, 2], 18), ([1, 0, 1, -1, 0, 0, 0], 18), ([1, 0, 1, -1, 1, -2, 1], 18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 2, -1, -1, -1, 1], 18), ([1, 1, 1, -2, 0, -1, 1], 18), ([1, 1, 1, -1, 0, -2, 1], 18)]

def combined204_part0 : Sparse := [([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 0, 2, -1], -9), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 0, 2, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 1, -2, 0, 2, -1], -27), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, -1, -1, 2, -1], 9), ([0, 0, 1, -1, 0, 2, -2], 27), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 0, 0, 1, -2], -27), ([0, 0, 2, -1, 0, 1, -2], -36), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 1, 1, -2, 0, 1, -1], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 0, 2, -1], -9), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, 0, 0, -1, 0, 2, -1], -36), ([1, 0, 0, -1, 1, 1, -1], 27)]

def combined204_part1 : Sparse := [([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 1, -2, 0, 1, 0], 27), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, -1, 0, 2, -2], 27), ([1, 0, 1, -1, 1, 1, -2], -9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 1, -2], -27), ([1, 0, 2, -2, 0, 1, -1], -36), ([1, 0, 2, -1, 0, 0, -1], 18), ([1, 1, 1, -1, -1, 1, -1], 27), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 0, 1, -2], -9)]

def combined204 : Sparse := combined204_part0 ++ combined204_part1

def combined205_part0 : Sparse := [([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 0, 2, -1], -9), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 0, 2, -1], -27), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 1, -2, 0, 2, -1], -27), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, -1, -1, 2, -1], 9), ([0, 0, 1, -1, 0, 2, -2], 18), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 0, 1, -1, 1, 1, -2], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 1, -2], -27), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 0, 2, -1, 0, 1, -2], -27), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 1, 1, -2, 0, 1, -1], -9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, -1, 0, 1, -2], 9), ([1, -1, 1, -1, 0, 1, 0], -9)]

def combined205_part1 : Sparse := [([1, -1, 1, -1, 0, 2, -1], -18), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 2, -1, 0, 1, -1], -9), ([1, 0, 0, -1, 0, 2, -1], -27), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 1, -2, 0, 1, 0], 9), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, -1, -1, 2, -1], -9), ([1, 0, 1, -1, 0, 2, -2], 18), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, -1, 1, 1, -2], -18), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 1, -2], -27), ([1, 0, 2, -2, 0, 1, -1], -36), ([1, 0, 2, -1, 0, 0, -1], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 1, -1, -1, 1, -1], 18), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 0, 1, -2], -9)]

def combined205 : Sparse := combined205_part0 ++ combined205_part1

def combined206_part0 : Sparse := [([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 0, 2, -1], -9), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 2, -1, 0, 1, -1], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 0, 2, -1], -9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 1, -2, 0, 2, -1], -27), ([0, 0, 1, -2, 1, 1, -1], 9), ([0, 0, 1, -1, -1, 2, -1], 9), ([0, 0, 1, -1, 0, 2, -2], 18), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, -1, 1, 1, -2], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 0, 0, 1, -2], -18), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 0, 2, -1, 0, 1, -2], -18), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, -1, 0, 1, -2], 18), ([1, -1, 1, -1, 0, 2, -1], -18)]

def combined206_part1 : Sparse := [([1, -1, 1, -1, 1, 1, -1], -9), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 2, -1, 0, 1, -1], -9), ([1, 0, 0, -1, 0, 2, -1], -9), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, -1, 2, -1], -9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 0, 2, -2], 18), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, -1, 1, 1, -2], -18), ([1, 0, 1, 0, 0, 1, -2], -18), ([1, 0, 2, -2, 0, 1, -1], -27), ([1, 0, 2, -1, -1, 1, -1], 9), ([1, 0, 2, -1, 0, 0, -1], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 1, -2, 0, 1, -1], 9), ([1, 1, 1, -1, -1, 1, -1], 9), ([1, 1, 1, -1, 0, 0, -1], -27)]

def combined206 : Sparse := combined206_part0 ++ combined206_part1

def combined207_part0 : Sparse := [([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, -1, 0, 2, -1], -18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 2, -1, 0, 1, -1], 18), ([0, 0, 0, -1, 0, 1, 0], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 0, 1, -1], -18), ([0, 0, 1, -2, 0, 2, -1], -18), ([0, 0, 1, -2, 1, 1, -1], 18), ([0, 0, 1, -1, -1, 2, -1], 18), ([0, 0, 1, -1, 0, 2, -2], 18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, -1, 1, 1, -2], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 2, -1, 0, 1, -2], -18), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 1, 1, -1, 0, 1, -2], 18), ([1, -1, 1, -1, 0, 2, -1], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 0, 0, 0, 1, -1], -18), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, -1, 0, 0, 0], 18)]

def combined207_part1 : Sparse := [([1, 0, 1, -1, 0, 2, -2], 18), ([1, 0, 1, -1, 1, 1, -2], -18), ([1, 0, 2, -2, 0, 1, -1], -18), ([1, 0, 2, -1, -1, 1, -1], 18), ([1, 1, 1, -2, 0, 1, -1], 18), ([1, 1, 1, -1, 0, 0, -1], -18)]

def combined207 : Sparse := combined207_part0 ++ combined207_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined208_part0 : Sparse := [([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 2, -1, 0], 9), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, 0, 0, -1, 1, -1, 1], -27), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -2, 1, 0, 0], -27), ([0, 0, 1, -2, 2, -1, 0], -27), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 2, -2, 1, -1, 0], 36), ([0, 0, 2, -1, 0, -1, 0], -18), ([0, 0, 2, -1, 1, -2, 0], -36), ([0, 1, 1, -2, 1, -1, 0], 9), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, -1, 1, -2, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, 0, 0, -1, 2, -1, 0], 36), ([1, 0, 0, 0, 1, -1, 0], 9)]

def combined208_part1 : Sparse := [([1, 0, 1, -2, 1, 0, 0], -27), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, -1, 1, -2, 1], 9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 2, -2, 0], -27), ([1, 0, 1, -1, 2, -1, -1], 9), ([1, 0, 1, 0, 1, -2, 0], 27), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 2, -2, 1, -1, 0], 36), ([1, 0, 2, -1, 0, -1, 0], -18), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, 1, -2, 0], 9), ([1, 1, 1, -1, 1, -1, -1], 27)]

def combined208 : Sparse := combined208_part0 ++ combined208_part1

def combined209_part0 : Sparse := [([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 2, -1, 0], 18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 2, -1, 1, -1, 0], -9), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -2, 1, 0, 0], -9), ([0, 0, 1, -2, 2, -1, 0], -27), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 1, -2, 1], 18), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, -1, 2, -1, -1], 9), ([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 2, -2, 1, -1, 0], 36), ([0, 0, 2, -1, 0, -1, 0], -9), ([0, 0, 2, -1, 1, -2, 0], -27), ([0, 0, 2, -1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 1, -2, 1, -1, 0], 9), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, -1, 1, -2, 0], 9)]

def combined209_part1 : Sparse := [([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 2, -1, 0], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, -1, 2, -1, 0], 27), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 1, -2, 1, 0, 0], -9), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, -1, 1, -2, 1], 9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 2, -2, 0], -18), ([1, 0, 1, -1, 2, -1, -1], 18), ([1, 0, 1, 0, 1, -2, 0], 27), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 2, -2, 1, -1, 0], 36), ([1, 0, 2, -1, 0, -1, 0], -9), ([1, 0, 2, -1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 1, -2, 0], 18), ([1, 1, 1, -1, 1, -1, -1], 18)]

def combined209 : Sparse := combined209_part0 ++ combined209_part1

def combined210_part0 : Sparse := [([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 2, -1, 0], 18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 2, -1, 1, -1, 0], -18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -2, 2, -1, 0], -27), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 1, -2, 1], 18), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, -1, 2, -1, -1], 9), ([0, 0, 1, 0, 0, -1, 0], 18), ([0, 0, 2, -2, 1, -1, 0], 27), ([0, 0, 2, -1, 0, -1, 0], -9), ([0, 0, 2, -1, 1, -2, 0], -18), ([0, 0, 2, -1, 1, -1, -1], 18), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 1, -2, 1, -1, 0], 9), ([0, 1, 1, -1, 0, -1, 0], -18), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, -1, 1, -1, 1, 0, 0], 27)]

def combined210_part1 : Sparse := [([1, -1, 1, -1, 2, -1, 0], 9), ([1, -1, 2, -1, 1, -1, 0], -9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, -1, 2, -1, 0], 9), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 1, -2, 1, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, -1, 2, -2, 0], -18), ([1, 0, 1, -1, 2, -1, -1], 18), ([1, 0, 1, 0, 1, -2, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 2, -2, 1, -1, 0], 27), ([1, 0, 2, -1, 0, -1, 0], -9), ([1, 0, 2, -1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 1, -2, 0], 18), ([1, 1, 1, -1, 1, -1, -1], 9)]

def combined210 : Sparse := combined210_part0 ++ combined210_part1

def combined211_part0 : Sparse := [([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, -1, 2, -1, 0], 18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 2, -1, 1, -1, 0], -18), ([0, 0, 0, -1, 1, -1, 1], -18), ([0, 0, 0, -1, 1, 0, 0], 18), ([0, 0, 1, -2, 1, -1, 1], -18), ([0, 0, 1, -2, 2, -1, 0], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], -18), ([0, 0, 1, -1, 1, -2, 1], 18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, 0, 0, -1, 0], 18), ([0, 0, 2, -2, 1, -1, 0], 18), ([0, 0, 2, -1, 1, -2, 0], -18), ([0, 0, 2, -1, 1, -1, -1], 18), ([0, 1, 1, -2, 1, -1, 0], 18), ([0, 1, 1, -1, 0, -1, 0], -18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 2, -1, 1, -1, 0], -18), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 1, -2, 1, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, -1, 0, 0, 0], -18)]

def combined211_part1 : Sparse := [([1, 0, 1, -1, 2, -2, 0], -18), ([1, 0, 1, -1, 2, -1, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 2, -2, 1, -1, 0], 18), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 1, -1, 1, -2, 0], 18)]

def combined211 : Sparse := combined211_part0 ++ combined211_part1

def combined212_part0 : Sparse := [([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, -1, 2, 0, -1], -9), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 0, 0, -1, 2, 0, -1], -36), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 1, -2, 1, 0, 0], -27), ([0, 0, 1, -2, 2, 0, -1], 27), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, -1, 2, -1, -1], 9), ([0, 0, 1, -1, 2, 0, -2], -27), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 2, -2, 1, 0, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -27), ([0, 1, 1, -1, 1, 0, -2], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, -1, 2, 0, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27)]

def combined212_part1 : Sparse := [([1, 0, 0, -1, 2, 0, -1], -36), ([1, 0, 1, -2, 1, 0, 0], -27), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -2, 2, 0, -1], 27), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, -1, 1, 1, -2], -9), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 1, 0, 1, 0, -2], 27), ([1, 0, 2, -1, 0, 0, -1], 18), ([1, 0, 2, -1, 1, 0, -2], -36), ([1, 1, 1, -2, 1, 0, -1], -9), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 27)]

def combined212 : Sparse := combined212_part0 ++ combined212_part1

def combined213_part0 : Sparse := [([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, -1, 2, 0, -1], -18), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 2, -1, 1, 0, -1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, -1, 2, 0, -1], -27), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 1, -2, 1, 0, 0], -9), ([0, 0, 1, -2, 2, 0, -1], 27), ([0, 0, 1, -1, 0, 1, -1], -27), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, -1, 1, 1, -2], 9), ([0, 0, 1, -1, 2, -1, -1], 18), ([0, 0, 1, -1, 2, 0, -2], -18), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 2, -2, 1, 0, -1], -36), ([0, 0, 2, -1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, -1, 1, 0, -2], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -18)]

def combined213_part1 : Sparse := [([1, -1, 1, -1, 2, 0, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 2, -1, 1, 0, -1], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 0, 0, -1, 2, 0, -1], -27), ([1, 0, 1, -2, 1, 0, 0], -9), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -2, 2, 0, -1], 27), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, -1, 1, 1, -2], -9), ([1, 0, 1, -1, 2, -1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 0, 1, 0, -2], 27), ([1, 0, 2, -1, 0, 0, -1], 9), ([1, 0, 2, -1, 1, -1, -1], 9), ([1, 0, 2, -1, 1, 0, -2], -27), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 1, -2, 1, 0, -1], -9), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, -1, 1, -1, -1], 18), ([1, 1, 1, -1, 1, 0, -2], 9)]

def combined213 : Sparse := combined213_part0 ++ combined213_part1

def combined214_part0 : Sparse := [([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, -1, 2, 0, -1], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 2, -1, 1, 0, -1], 18), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, -1, 2, 0, -1], -9), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 1, -2, 1, 1, -1], -9), ([0, 0, 1, -2, 2, 0, -1], 27), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, -1, 1, 1, -2], 18), ([0, 0, 1, -1, 2, -1, -1], 18), ([0, 0, 1, -1, 2, 0, -2], -18), ([0, 0, 2, -2, 1, 0, -1], -27), ([0, 0, 2, -1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 1, -2, 1, 0, -1], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -9)]

def combined214_part1 : Sparse := [([1, -1, 1, -1, 2, 0, -1], -9), ([1, -1, 2, -1, 1, 0, -1], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 0, 0, -1, 2, 0, -1], -9), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -2, 2, 0, -1], 27), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, -1, 2, -1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 0, 1, 0, -2], 18), ([1, 0, 2, -1, 0, 0, -1], 9), ([1, 0, 2, -1, 1, -1, -1], 18), ([1, 0, 2, -1, 1, 0, -2], -18), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, -1, 1, -1, -1], 9), ([1, 1, 1, -1, 1, 0, -2], 18)]

def combined214 : Sparse := combined214_part0 ++ combined214_part1

def combined215_part0 : Sparse := [([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, -1, 2, 0, -1], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 2, -1, 1, 0, -1], 18), ([0, 0, 0, -1, 1, 0, 0], -18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 1, -2, 1, 1, -1], -18), ([0, 0, 1, -2, 2, 0, -1], 18), ([0, 0, 1, -1, 0, 0, 0], 18), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, -1, 1, 1, -2], 18), ([0, 0, 1, -1, 2, -1, -1], 18), ([0, 0, 1, -1, 2, 0, -2], -18), ([0, 0, 2, -2, 1, 0, -1], -18), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 1, -2, 1, 0, -1], 18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, -1, 2, 0, -1], -18), ([1, 0, 0, -1, 1, 0, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 0, 1, -2, 1, 1, -1], -18), ([1, 0, 1, -2, 2, 0, -1], 18)]

def combined215_part1 : Sparse := [([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 2, -1, 1, -1, -1], 18), ([1, 0, 2, -1, 1, 0, -2], -18), ([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, -1, 1, 0, -2], 18)]

def combined215 : Sparse := combined215_part0 ++ combined215_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined216_part0 : Sparse := [([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 1, -1, -1, -1, 2], 9), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, 0, -1, -2, 2], -27), ([0, 0, 1, 0, 0, -2, 1], -27), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -1, -2, 1], 9), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 2, 0, -2, -1, 1], -36), ([0, 0, 2, 0, -1, -2, 1], 36), ([0, 0, 2, 0, -1, -1, 0], -18), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 1, -1, -1, -1, 1], -27), ([0, 1, 1, 0, -2, -1, 1], 9), ([0, 1, 1, 0, -1, -2, 1], -9), ([0, 1, 1, 0, -1, -1, 0], 36), ([1, -1, 1, 0, -1, -1, 2], 9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, 0, 0, 0, -1, -1, 2], 36)]

def combined216_part1 : Sparse := [([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, 0, -2, -1, 2], -27), ([1, 0, 1, 0, -2, 0, 1], 27), ([1, 0, 1, 0, 0, -2, 1], -27), ([1, 0, 1, 1, -2, -1, 1], 9), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 2, 0, -1, -2, 1], 36), ([1, 0, 2, 0, -1, -1, 0], -18), ([1, 1, 1, -1, -1, -1, 1], -27), ([1, 1, 1, 0, -2, -1, 1], 9), ([1, 1, 1, 0, -1, -1, 0], 36)]

def combined216 : Sparse := combined216_part0 ++ combined216_part1

def combined217_part0 : Sparse := [([0, -1, 1, 0, -1, -1, 2], -9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 1, -1, -1, -1, 2], 9), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, 0, -1, -2, 2], -18), ([0, 0, 1, 0, 0, -2, 1], -27), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -1, -2, 1], 18), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 2, 0, -2, -1, 1], -36), ([0, 0, 2, 0, -1, -2, 1], 27), ([0, 0, 2, 0, -1, -1, 0], -9), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 1, -1, -1, -1, 1], -18), ([0, 1, 1, 0, -2, -1, 1], 9), ([0, 1, 1, 0, -1, -2, 1], -18), ([0, 1, 1, 0, -1, -1, 0], 36), ([1, -1, 1, 0, -1, -1, 2], 9), ([1, -1, 1, 0, -1, 0, 1], -27)]

def combined217_part1 : Sparse := [([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 2, 0, -1, -1, 1], -9), ([1, 0, 0, 0, -1, -1, 2], 27), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 1, -1, -1, -1, 2], -9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, -2, -1, 2], -27), ([1, 0, 1, 0, -2, 0, 1], 9), ([1, 0, 1, 0, 0, -2, 1], -27), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -2, -1, 1], 9), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 2, -1, -1, -1, 1], -9), ([1, 0, 2, 0, -1, -2, 1], 27), ([1, 0, 2, 0, -1, -1, 0], -9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 1, -1, -1, -1, 1], -18), ([1, 1, 1, 0, -2, -1, 1], 9), ([1, 1, 1, 0, -1, -2, 1], -9), ([1, 1, 1, 0, -1, -1, 0], 27)]

def combined217 : Sparse := combined217_part0 ++ combined217_part1

def combined218_part0 : Sparse := [([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 2, 0, -1, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 1, -1, -1, -1, 2], 18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, 0, -1, -2, 2], -18), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 0, 0, -2, 1], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -1, -2, 1], 18), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 2, -1, -1, -1, 1], -9), ([0, 0, 2, 0, -2, -1, 1], -27), ([0, 0, 2, 0, -1, -2, 1], 27), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 1, -1, -1, -1, 1], -9), ([0, 1, 1, 0, -2, -1, 1], 18), ([0, 1, 1, 0, -1, -2, 1], -18), ([0, 1, 1, 0, -1, -1, 0], 27), ([1, -1, 1, 0, -1, -1, 2], 18), ([1, -1, 1, 0, -1, 0, 1], -18)]

def combined218_part1 : Sparse := [([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, 0, 0, 0, -1, -1, 2], 18), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, -2, -1, 2], -18), ([1, 0, 1, 0, -2, 0, 1], 9), ([1, 0, 1, 0, 0, -2, 1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -2, -1, 1], 18), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 2, -1, -1, -1, 1], -9), ([1, 0, 2, 0, -1, -2, 1], 27), ([1, 1, 1, -1, -1, -1, 1], -9), ([1, 1, 1, 0, -2, -1, 1], 9), ([1, 1, 1, 0, -1, -2, 1], -9), ([1, 1, 1, 0, -1, -1, 0], 27)]

def combined218 : Sparse := combined218_part0 ++ combined218_part1

def combined219_part0 : Sparse := [([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 2, 0, -1, -1, 1], 18), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 1, -1, -1, -1, 2], 18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, 0, -1, -2, 2], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 1, 1, -1, -2, 1], 18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 2, -1, -1, -1, 1], -18), ([0, 0, 2, 0, -2, -1, 1], -18), ([0, 0, 2, 0, -1, -2, 1], 18), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 1, 0, -2, -1, 1], 18), ([0, 1, 1, 0, -1, -2, 1], -18), ([0, 1, 1, 0, -1, -1, 0], 18), ([1, -1, 1, 0, -1, -1, 2], 18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, 0, -2, -1, 2], -18)]

def combined219_part1 : Sparse := [([1, 0, 1, 0, 0, -1, 0], -18), ([1, 0, 1, 1, -2, -1, 1], 18), ([1, 0, 2, -1, -1, -1, 1], -18), ([1, 0, 2, 0, -1, -2, 1], 18), ([1, 1, 1, 0, -1, -2, 1], -18), ([1, 1, 1, 0, -1, -1, 0], 18)]

def combined219 : Sparse := combined219_part0 ++ combined219_part1

def combined220_part0 : Sparse := [([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, -1, 2, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 0, 1, -1], -27), ([0, 0, 1, 0, -1, 2, -2], -27), ([0, 0, 1, 0, 0, 1, -2], -27), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, -1, 1, -2], -9), ([0, 0, 2, 0, -2, 1, -1], -36), ([0, 0, 2, 0, -1, 0, -1], -18), ([0, 0, 2, 0, -1, 1, -2], 36), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, -1, 1, -2], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 0, -1, 2, -1], 36)]

def combined220_part1 : Sparse := [([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, -1, 2, -1], 9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, 0, -2, 1, 0], 27), ([1, 0, 1, 0, -2, 2, -1], -27), ([1, 0, 1, 0, 0, 1, -2], -27), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 2, 0, -1, 0, -1], -18), ([1, 0, 2, 0, -1, 1, -2], 36), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 1, -1, -1, 1, -1], 27), ([1, 1, 1, 0, -2, 1, -1], 9), ([1, 1, 1, 0, -1, 1, -2], 9)]

def combined220 : Sparse := combined220_part0 ++ combined220_part1

def combined221_part0 : Sparse := [([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, -1, 2, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, 0, -1, 2, -2], -18), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 0, 0, 1, -2], -27), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, -1, 1, -2], -18), ([0, 0, 2, 0, -2, 1, -1], -36), ([0, 0, 2, 0, -1, 0, -1], -9), ([0, 0, 2, 0, -1, 1, -2], 27), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, -1, 1, -2], 18), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, -1, 2, -1], -9)]

def combined221_part1 : Sparse := [([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 2, 0, -1, 1, -1], -9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 0, -1, 2, -1], 27), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, -1, 2, -1], 9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, 0, -2, 1, 0], 9), ([1, 0, 1, 0, -2, 2, -1], -27), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 0, 0, 1, -2], -27), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, -1, 1, -2], -9), ([1, 0, 2, -1, -1, 1, -1], -9), ([1, 0, 2, 0, -1, 0, -1], -9), ([1, 0, 2, 0, -1, 1, -2], 27), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 1, -1, -1, 1, -1], 18), ([1, 1, 1, 0, -2, 1, -1], 9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 0, -1, 1, -2], 9)]

def combined221 : Sparse := combined221_part0 ++ combined221_part1

def combined222_part0 : Sparse := [([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, -1, 2, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 2, 0, -1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 0, -1, 2, -2], -18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 0, 0, 1, -2], -18), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, -1, 1, -2], -18), ([0, 0, 2, -1, -1, 1, -1], 9), ([0, 0, 2, 0, -2, 1, -1], -27), ([0, 0, 2, 0, -1, 0, -1], -9), ([0, 0, 2, 0, -1, 1, -2], 18), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 1, -2], 18), ([1, -1, 1, 0, -1, 2, -1], -9)]

def combined222_part1 : Sparse := [([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 2, 0, -1, 1, -1], -18), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 0, -1, 2, -1], 9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, -1, 2, -1], 9), ([1, 0, 1, 0, -2, 2, -1], -27), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 0, 0, 1, -2], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 1, -1, 1, -2], -18), ([1, 0, 2, -1, -1, 1, -1], -9), ([1, 0, 2, 0, -1, 0, -1], -9), ([1, 0, 2, 0, -1, 1, -2], 18), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 1, -1, -1, 1, -1], 9), ([1, 1, 1, 0, -2, 1, -1], 9), ([1, 1, 1, 0, -1, 0, -1], -9)]

def combined222 : Sparse := combined222_part0 ++ combined222_part1

def combined223_part0 : Sparse := [([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 0, -1, 2, -1], 18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 2, 0, -1, 1, -1], -18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 0, 1, 0, -1, 2, -2], -18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 1, -2, 1, -1], 18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, -1, 1, -2], -18), ([0, 0, 2, -1, -1, 1, -1], 18), ([0, 0, 2, 0, -2, 1, -1], -18), ([0, 0, 2, 0, -1, 1, -2], 18), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 1, 0, -1, 1, -2], 18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 2, 0, -1, 1, -1], -18), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, -1, -1, 2, -1], 18), ([1, 0, 1, 0, -2, 2, -1], -18)]

def combined223_part1 : Sparse := [([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 1, -1, 1, -2], -18), ([1, 0, 2, 0, -1, 1, -2], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 1, 0, -2, 1, -1], 18)]

def combined223 : Sparse := combined223_part0 ++ combined223_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined224_part0 : Sparse := [([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 0, 2, -1, -1], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 0, 1, -1, 2, -1, -1], -9), ([0, 0, 1, 0, 2, -2, -1], -27), ([0, 0, 1, 0, 2, -1, -2], -27), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 2, 0, 1, -2, -1], -36), ([0, 0, 2, 0, 1, -1, -2], -36), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 0, 1, -1, -2], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 0, 2, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 0, 1, 0, -1], -9)]

def combined224_part1 : Sparse := [([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, -1, 2, -1, -1], -9), ([1, 0, 1, 0, 1, -2, 0], 27), ([1, 0, 1, 0, 1, 0, -2], 27), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 2, 0, 0, -1, -1], 18), ([1, 1, 1, -1, 1, -1, -1], 27), ([1, 1, 1, 0, 1, -2, -1], -9)]

def combined224 : Sparse := combined224_part0 ++ combined224_part1

def combined225_part0 : Sparse := [([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 0, 2, -1, -1], -9), ([0, -1, 2, 0, 1, -1, -1], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, -1, 1, 0, -1], -27), ([0, 0, 1, -1, 2, -1, -1], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 0, 2, -2, -1], -27), ([0, 0, 1, 0, 2, -1, -2], -27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 1, 1, 1, -1, -2], -9), ([0, 0, 2, -1, 1, -1, -1], -9), ([0, 0, 2, 0, 1, -2, -1], -27), ([0, 0, 2, 0, 1, -1, -2], -27), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 0, 1, -2, -1], -9), ([0, 1, 1, 0, 1, -1, -2], -9)]

def combined225_part1 : Sparse := [([1, -1, 1, 0, 2, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 2, 0, 1, -1, -1], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 2, -1, -1], 18), ([1, 0, 1, -1, 2, -1, -1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 0, 1, -2, 0], 18), ([1, 0, 1, 0, 1, 0, -2], 18), ([1, 0, 1, 1, 1, -2, -1], -9), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 2, -1, 1, -1, -1], -9), ([1, 0, 2, 0, 0, -1, -1], 18), ([1, 1, 1, -1, 1, -1, -1], 18), ([1, 1, 1, 0, 1, -2, -1], -9), ([1, 1, 1, 0, 1, -1, -2], -9)]

def combined225 : Sparse := combined225_part0 ++ combined225_part1

def combined226_part0 : Sparse := [([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 0, 2, -1, -1], -9), ([0, -1, 2, 0, 1, -1, -1], -18), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, -1, 2, -1, -1], -18), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 0, 2, -2, -1], -27), ([0, 0, 1, 0, 2, -1, -2], -18), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 1, 1, 1, -1, -2], -18), ([0, 0, 2, -1, 1, -1, -1], -9), ([0, 0, 2, 0, 1, -2, -1], -27), ([0, 0, 2, 0, 1, -1, -2], -18), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 0, 1, -2, -1], -9), ([0, 1, 1, 0, 1, -1, -2], -18)]

def combined226_part1 : Sparse := [([1, -1, 1, 0, 2, -1, -1], -18), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 2, 0, 1, -1, -1], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 0, 0, 2, -1, -1], 9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 1, -1, 2, -1, -1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 0, 1, 0, -2], 18), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 1, 1, 1, -2, -1], -9), ([1, 0, 1, 1, 1, -1, -2], -18), ([1, 0, 2, -1, 1, -1, -1], -18), ([1, 0, 2, 0, 0, -1, -1], 9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 1, -1, 1, -1, -1], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 0, 1, -2, -1], -9), ([1, 1, 1, 0, 1, -1, -2], -18)]

def combined226 : Sparse := combined226_part0 ++ combined226_part1

def combined227_part0 : Sparse := [([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 0, 2, -1, -1], -18), ([0, -1, 2, 0, 1, -1, -1], -18), ([0, 0, 0, 0, 1, -1, 0], -18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([0, 0, 1, -1, 2, -1, -1], -18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 1, 0, 0, 0, -1], -18), ([0, 0, 1, 0, 2, -2, -1], -18), ([0, 0, 1, 0, 2, -1, -2], -18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 1, -2, -1], -18), ([0, 0, 1, 1, 1, -1, -2], -18), ([0, 0, 2, -1, 1, -1, -1], -18), ([0, 0, 2, 0, 1, -2, -1], -18), ([0, 0, 2, 0, 1, -1, -2], -18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 0, 1, -2, -1], -18), ([0, 1, 1, 0, 1, -1, -2], -18)]

def combined227_part1 : Sparse := [([1, -1, 1, 0, 2, -1, -1], -18), ([1, -1, 2, 0, 1, -1, -1], -18), ([1, 0, 0, 0, 1, -1, 0], -18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 1, -1, 2, -1, -1], -18), ([1, 0, 1, 0, 0, -1, 0], -18), ([1, 0, 1, 0, 0, 0, -1], -18), ([1, 0, 1, 1, 1, -2, -1], -18), ([1, 0, 1, 1, 1, -1, -2], -18), ([1, 0, 2, -1, 1, -1, -1], -18), ([1, 1, 1, 0, 1, -2, -1], -18), ([1, 1, 1, 0, 1, -1, -2], -18)]

def combined227 : Sparse := combined227_part0 ++ combined227_part1

def combined228_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -2, 0, 0], -27), ([0, 0, 1, 1, -1, -2, 1], 9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 2, -2, -1, 0], -27), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 2, 0, -1, -1, 0], -18), ([0, 0, 2, 1, -2, -1, 0], 36), ([0, 0, 2, 1, -1, -2, 0], -36), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -1, -2, 0], 9), ([0, 1, 1, 1, -1, -1, -1], -27), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 2, -1, -1, 0], 9), ([1, 0, 0, 1, -1, -1, 1], -27)]

def combined228_part1 : Sparse := [([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 2, -1, -1, 0], 36), ([1, 0, 1, 1, -2, -1, 1], 9), ([1, 0, 1, 1, -2, 0, 0], -27), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 1, 1, 0, -2, 0], 27), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 2, -1, -2, 0], -27), ([1, 0, 2, 0, -1, -1, 0], -18), ([1, 0, 2, 1, -2, -1, 0], 36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 1, -1, -2, 0], 9), ([1, 1, 1, 1, -1, -1, -1], -27)]

def combined228 : Sparse := combined228_part0 ++ combined228_part1

def combined229_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 2, 1, -1, -1, 0], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -2, 0, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 2, -2, -1, 0], -27), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 2, 0, -1, -1, 0], -18), ([0, 0, 2, 1, -2, -1, 0], 27), ([0, 0, 2, 1, -1, -2, 0], -27), ([0, 0, 2, 1, -1, -1, -1], -9), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -1, -2, 0], 9), ([0, 1, 1, 1, -1, -1, -1], -18), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 2, -1, -1, 0], 9)]

def combined229_part1 : Sparse := [([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 2, -1, -1, 0], 18), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -2, 0, 0], -18), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -2, 0], 18), ([1, 0, 1, 2, -1, -2, 0], -27), ([1, 0, 2, 0, -1, -1, 0], -18), ([1, 0, 2, 1, -2, -1, 0], 27), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 1, -2, -1, 0], -9), ([1, 1, 1, 1, -1, -1, -1], -18)]

def combined229 : Sparse := combined229_part0 ++ combined229_part1

def combined230_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 2, 1, -1, -1, 0], 18), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, 0, -1, 0], 18), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 2, -2, -1, 0], -27), ([0, 0, 1, 2, -1, -1, -1], 18), ([0, 0, 2, 0, -1, -1, 0], -9), ([0, 0, 2, 1, -2, -1, 0], 27), ([0, 0, 2, 1, -1, -2, 0], -18), ([0, 0, 2, 1, -1, -1, -1], -18), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -1, -2, 0], 18), ([0, 1, 1, 1, -1, -1, -1], -9), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, 0, -1, 0], -18)]

def combined230_part1 : Sparse := [([1, -1, 1, 2, -1, -1, 0], 18), ([1, -1, 2, 1, -1, -1, 0], 9), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -1, 0], 18), ([1, 0, 0, 2, -1, -1, 0], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -1, -2, 1], 18), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -2, 0], 18), ([1, 0, 1, 2, -1, -2, 0], -18), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, -1, 0], -9), ([1, 0, 2, 1, -2, -1, 0], 27), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 1, -2, -1, 0], -9), ([1, 1, 1, 1, -1, -1, -1], -9)]

def combined230 : Sparse := combined230_part0 ++ combined230_part1

def combined231_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 2, 1, -1, -1, 0], 18), ([0, 0, 0, 1, -1, 0, 0], 18), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, -1, 0, 0], -18), ([0, 0, 1, 0, 0, -1, 0], 18), ([0, 0, 1, 1, -2, -1, 1], 18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 2, -2, -1, 0], -18), ([0, 0, 1, 2, -1, -1, -1], 18), ([0, 0, 2, 1, -2, -1, 0], 18), ([0, 0, 2, 1, -1, -2, 0], -18), ([0, 0, 2, 1, -1, -1, -1], -18), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 1, -2, -1, 0], -18), ([0, 1, 1, 1, -1, -2, 0], 18), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 1, 2, -1, -1, 0], 18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -1, 0], 18), ([1, 0, 1, 0, -1, 0, 0], -18), ([1, 0, 1, 1, -1, -2, 1], 18)]

def combined231_part1 : Sparse := [([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 2, -1, -2, 0], -18), ([1, 0, 2, 1, -2, -1, 0], 18), ([1, 0, 2, 1, -1, -1, -1], -18), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 1, 1, -2, -1, 0], -18)]

def combined231 : Sparse := combined231_part0 ++ combined231_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined232_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 1, -2, 0, 0], -27), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 1, -2], -9), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 1, 0, 0, -2], -27), ([0, 0, 1, 2, -2, 0, -1], -27), ([0, 0, 1, 2, -1, 0, -2], -27), ([0, 0, 2, 0, -1, 0, -1], -18), ([0, 0, 2, 1, -2, 0, -1], -36), ([0, 0, 2, 1, -1, 0, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 1, 1, 1, -1, 0, -2], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], -27)]

def combined232_part1 : Sparse := [([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -2, 0, 0], -27), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 1, 1, 0, 0, -2], -27), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], -18), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, -1, 0, -2], 9)]

def combined232 : Sparse := combined232_part0 ++ combined232_part1

def combined233_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 2, -1, 0, -1], -18), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 1, -2, 0, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 2, -2, 0, -1], -27), ([0, 0, 1, 2, -1, 0, -2], -27), ([0, 0, 2, 0, -1, 0, -1], -18), ([0, 0, 2, 1, -2, 0, -1], -27), ([0, 0, 2, 1, -1, 0, -2], -27), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -18), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, -1, 2, 1, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 2, -1, 0, -1], -18)]

def combined233_part1 : Sparse := [([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 1, -2, 0, 0], -18), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], -18), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, -1, 0, -2], 9)]

def combined233 : Sparse := combined233_part0 ++ combined233_part1

def combined234_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 2, -1, 0, -1], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 2, -2, 0, -1], -27), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 1, 2, -1, 0, -2], -18), ([0, 0, 2, 0, -1, 0, -1], -9), ([0, 0, 2, 1, -2, 0, -1], -27), ([0, 0, 2, 1, -1, -1, -1], -9), ([0, 0, 2, 1, -1, 0, -2], -18), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 1, 1, -1, -1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, -1, 2, 1, -1, 0, -1], 18)]

def combined234_part1 : Sparse := [([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 0, 2, -1, 0, -1], -9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, 1, -2], 18), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 2, -1, -1, -1], 18), ([1, 0, 2, 0, -1, 0, -1], -9), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, -1, 0, -2], 18)]

def combined234 : Sparse := combined234_part0 ++ combined234_part1

def combined235 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 2, -2, 0, -1], -18), ([0, 0, 1, 2, -1, 0, -2], -18), ([0, 0, 2, 1, -2, 0, -1], -18), ([0, 0, 2, 1, -1, 0, -2], -18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 1, 0, -1, 0, -1], -18), ([1, -1, 1, 2, -1, 0, -1], 18), ([1, -1, 2, 1, -1, 0, -1], 18), ([1, 0, 0, 1, -1, 0, 0], 18), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 1, 0, -1, 0, 0], 18), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 1, -2, 1, -1], 18), ([1, 0, 1, 1, -1, 1, -2], 18), ([1, 0, 1, 2, -1, -1, -1], 18), ([1, 0, 2, 1, -1, -1, -1], 18), ([1, 1, 1, 1, -2, 0, -1], 18), ([1, 1, 1, 1, -1, 0, -2], 18)]

def combined236_part0 : Sparse := [([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, 0, 0, -2], -27), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], -27), ([0, 0, 1, 2, 0, -1, -2], 27), ([0, 0, 2, 1, 0, -1, -2], -36), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, 0, -1, -1], -36), ([1, 0, 1, 0, 1, -1, -1], -36)]

def combined236_part1 : Sparse := [([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -2, 0], 27), ([1, 0, 1, 1, 0, 0, -2], -27), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 1, 2, 0, -1, -2], 27), ([1, 0, 2, 0, 0, -1, -1], 18), ([1, 0, 2, 1, 0, -2, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 1, 1, 0, -1, -2], -9)]

def combined236 : Sparse := combined236_part0 ++ combined236_part1

def combined237_part0 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 1, 1, -1, -2], 9), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], -27), ([0, 0, 1, 2, 0, -1, -2], 27), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 0, 2, 1, 0, -1, -2], -27), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 1, 1, 1, 0, -2, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 2, 1, 0, -1, -1], 9)]

def combined237_part1 : Sparse := [([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, 0, -1, -1], -18), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -2, 0], 18), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 1, 2, 0, -1, -2], 27), ([1, 0, 2, 0, 0, -1, -1], 18), ([1, 0, 2, 1, 0, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, 0, -1, -2], -9)]

def combined237 : Sparse := combined237_part0 ++ combined237_part1

def combined238_part0 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, -1, 2, 1, 0, -1, -1], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -9), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 1, 1, -1, -2], 18), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], -27), ([0, 0, 1, 2, 0, -1, -2], 18), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 0, 2, 1, 0, -1, -2], -18), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 1, 1, 1, 0, -2, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -18), ([1, -1, 1, 1, 0, -1, 0], -27)]

def combined238_part1 : Sparse := [([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 1, 0, -1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 2, 0, -1, -1], -9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 2, -1, -1, -1], -18), ([1, 0, 1, 2, 0, -1, -2], 18), ([1, 0, 2, 0, 0, -1, -1], 9), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 0, 2, 1, 0, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, 0, -1, -2], -18)]

def combined238 : Sparse := combined238_part0 ++ combined238_part1

def combined239_part0 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, 0, -1, -1], 18), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 1, -1, -2], 18), ([0, 0, 1, 2, -1, -1, -1], -18), ([0, 0, 1, 2, 0, -2, -1], -18), ([0, 0, 1, 2, 0, -1, -2], 18), ([0, 0, 2, 1, -1, -1, -1], 18), ([0, 0, 2, 1, 0, -1, -2], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 1, 0, -2, -1], 18), ([0, 1, 1, 1, 0, -1, -2], -18), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 2, 1, 0, -1, -1], 18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined239_part1 : Sparse := [([1, 0, 1, 1, 1, -2, -1], 18), ([1, 0, 1, 2, -1, -1, -1], -18), ([1, 0, 1, 2, 0, -1, -2], 18), ([1, 0, 2, 1, 0, -2, -1], -18), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 1, 1, 0, -1, -2], -18)]

def combined239 : Sparse := combined239_part0 ++ combined239_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined240_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -1, -2, 0, 0, 2], -27), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -1, -1, 0, 2], 9), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, 0, -2, 0, 0, 1], -27), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 2, -2, -1, 0, 0, 1], -36), ([0, 2, -1, -2, 0, 0, 1], 36), ([0, 2, -1, -1, 0, 0, 0], -18), ([1, 0, -1, -1, 0, 0, 2], 36), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 0, 2], -27), ([1, 1, -2, -1, 0, 1, 1], 9)]

def combined240_part1 : Sparse := [([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 0, 0, 1], 27), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, -1, 0, -1, 2], 9), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, 0, -2, 0, 0, 1], -27), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 2, -1, -2, 0, 0, 1], 36), ([1, 2, -1, -1, 0, 0, 0], -18)]

def combined240 : Sparse := combined240_part0 ++ combined240_part1

def combined241_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -1, -2, 0, 0, 2], -18), ([0, 1, -1, -2, 0, 1, 1], -18), ([0, 1, -1, -2, 1, 0, 1], 18), ([0, 1, -1, -1, -1, 0, 2], 9), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, -1, 0, -1, 2], -9), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, 0, -2, 0, 0, 1], -27), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 2, -2, -1, 0, 0, 1], -36), ([0, 2, -1, -2, 0, 0, 1], 27), ([0, 2, -1, -1, 0, 0, 0], -9), ([1, 0, -1, -1, 0, 0, 2], 27), ([1, 0, -1, -1, 0, 1, 1], -9)]

def combined241_part1 : Sparse := [([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 0, 2], -27), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 0, 0, 1], 9), ([1, 1, -1, -2, 0, 1, 1], -9), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -1, -1, 0, 2], -9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, -1, 0, -1, 2], 9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, 0, -2, 0, 0, 1], -27), ([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 2, -1, -2, 0, 0, 1], 27), ([1, 2, -1, -1, -1, 0, 1], -9), ([1, 2, -1, -1, 0, -1, 1], -9), ([1, 2, -1, -1, 0, 0, 0], -9)]

def combined241 : Sparse := combined241_part0 ++ combined241_part1

def combined242_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 1, -2, -1, 0, 1, 1], 18), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -1, -2, 0, 0, 2], -18), ([0, 1, -1, -2, 0, 1, 1], -18), ([0, 1, -1, -2, 1, 0, 1], 18), ([0, 1, -1, -1, -1, 0, 2], 18), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, 0, -2, 0, 0, 1], -9), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 2, -2, -1, 0, 0, 1], -27), ([0, 2, -1, -2, 0, 0, 1], 27), ([0, 2, -1, -1, -1, 0, 1], -9), ([0, 2, -1, -1, 0, -1, 1], 9), ([1, 0, -1, -1, 0, 0, 2], 18), ([1, 0, -1, -1, 1, 0, 1], -18)]

def combined242_part1 : Sparse := [([1, 0, -1, 0, 0, 0, 1], 18), ([1, 1, -2, -1, 0, 0, 2], -18), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, -1, 1, 0, 1], 18), ([1, 1, -2, 0, 0, 0, 1], 9), ([1, 1, -1, -2, 0, 1, 1], -9), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], 18), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, 0, -2, 0, 0, 1], -9), ([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 2, -1, -2, 0, 0, 1], 27), ([1, 2, -1, -1, -1, 0, 1], -9)]

def combined242 : Sparse := combined242_part0 ++ combined242_part1

def combined243_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 1, -2, -1, 0, 1, 1], 18), ([0, 1, -1, -2, 0, 0, 2], -18), ([0, 1, -1, -2, 0, 1, 1], -18), ([0, 1, -1, -2, 1, 0, 1], 18), ([0, 1, -1, -1, -1, 0, 2], 18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, 0, 0, 0], 18), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, -1, 0, 0, 0], -18), ([0, 2, -2, -1, 0, 0, 1], -18), ([0, 2, -1, -2, 0, 0, 1], 18), ([0, 2, -1, -1, -1, 0, 1], -18), ([0, 2, -1, -1, 0, -1, 1], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 1, -2, -1, 0, 0, 2], -18), ([1, 1, -2, -1, 1, 0, 1], 18), ([1, 1, -1, -2, 0, 1, 1], -18), ([1, 1, -1, -1, 0, -1, 2], 18)]

def combined243_part1 : Sparse := [([1, 1, -1, -1, 0, 1, 0], 18), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 0, -1, 0, 0, 0], -18), ([1, 2, -1, -2, 0, 0, 1], 18), ([1, 2, -1, -1, -1, 0, 1], -18)]

def combined243 : Sparse := combined243_part0 ++ combined243_part1

def combined244_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 0, 2, 0], -36), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 0, 2, 0], -27), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, 0, 0, 1, 0], -27), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 2, 0], -27), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, 0, -2, 0, 1, 0], -27), ([0, 1, 0, -1, -1, 1, 0], -27), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 2, -2, -1, 0, 1, 0], -36), ([0, 2, -1, -2, 0, 1, 0], -36), ([0, 2, -1, -1, 0, 0, 0], -18), ([1, 0, -1, -1, 0, 2, 0], -36), ([1, 0, -1, 0, 0, 1, 0], 9)]

def combined244_part1 : Sparse := [([1, 0, 0, -1, 0, 1, 0], 9), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, 0, 0, 1, 0], -27), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, -1, -1, 2, 0], 9), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], -27), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 2, -1, -1, 0, 0, 0], -18)]

def combined244 : Sparse := combined244_part0 ++ combined244_part1

def combined245_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 2, 0], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 0, 2, 0], -27), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, 0, 0, 1, 0], -9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 2, 0], -18), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, -1, -1, 2, 0], -9), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, 0, -2, 0, 1, 0], -27), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 2, -2, -1, 0, 1, 0], -36), ([0, 2, -1, -2, 0, 1, 0], -27), ([0, 2, -1, -1, -1, 1, 0], 9)]

def combined245_part1 : Sparse := [([0, 2, -1, -1, 0, 0, 0], -9), ([0, 2, -1, -1, 0, 1, -1], -9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, -1, 0, 2, 0], -27), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 1, 0], 18), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, 0, 0, 1, 0], -9), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -2, 1, 1, 0], 18), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, -1, -1, 2, 0], 9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 0, 2, -1], 18), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], -27), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 2, -1, -1, -1, 1, 0], 9)]

def combined245_part2 : Sparse := [([1, 2, -1, -1, 0, 0, 0], -9)]

def combined245 : Sparse := combined245_part0 ++ combined245_part1 ++ combined245_part2

def combined246_part0 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 0, 2, 0], -18), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, 0, 0, 1, 0], -9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 2, 0], -18), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, 0, -2, 0, 1, 0], -9), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 2, -2, -1, 0, 1, 0], -27), ([0, 2, -1, -2, 0, 1, 0], -27), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, 0, -1, 0, 1, 0], 18)]

def combined246_part1 : Sparse := [([1, 1, -2, -1, 0, 1, 1], 18), ([1, 1, -2, -1, 1, 1, 0], 9), ([1, 1, -2, 0, 0, 1, 0], -9), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -2, 1, 1, 0], 18), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, -1, -1, 2, 0], 18), ([1, 1, -1, -1, 0, 2, -1], 18), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], -9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 2, -1, -1, -1, 1, 0], 9), ([1, 2, -1, -1, 0, 1, -1], 9)]

def combined246 : Sparse := combined246_part0 ++ combined246_part1

def combined247 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 1, -2, -1, 0, 2, 0], -18), ([0, 1, -1, -2, 0, 2, 0], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 1, 0, 0], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 2, -2, -1, 0, 1, 0], -18), ([0, 2, -1, -2, 0, 1, 0], -18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, 0, -1, 0, 1, 0], 18), ([1, 1, -2, -1, 0, 1, 1], 18), ([1, 1, -2, -1, 1, 1, 0], 18), ([1, 1, -1, -2, 0, 1, 1], 18), ([1, 1, -1, -2, 1, 1, 0], 18), ([1, 1, -1, -1, -1, 2, 0], 18), ([1, 1, -1, -1, 0, 2, -1], 18), ([1, 1, -1, 0, 0, 0, 0], 18), ([1, 1, 0, -1, 0, 0, 0], 18), ([1, 2, -1, -1, -1, 1, 0], 18), ([1, 2, -1, -1, 0, 1, -1], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined248_part0 : Sparse := [([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, -1, 2, 0, 0], -27), ([0, 1, -2, 0, 1, 0, 0], -27), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], -27), ([0, 2, -2, -1, 1, 0, 0], 36), ([0, 2, -1, -2, 1, 0, 0], -36), ([0, 2, -1, -1, 0, 0, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 2, 0, 0], 36), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 1, 0, 0], -27)]

def combined248_part1 : Sparse := [([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -2, 2, 0, 0], -27), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, 0, -2, 1, 0, 0], 27), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 2, -2, -1, 1, 0, 0], 36), ([1, 2, -1, -1, 0, 0, 0], -18)]

def combined248 : Sparse := combined248_part0 ++ combined248_part1

def combined249_part0 : Sparse := [([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, -1, 2, 0, 0], -27), ([0, 1, -2, 0, 1, 0, 0], -9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -2, 1, 1, 0], 18), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, -1, -1, 2, -1, 0], 9), ([0, 1, -1, -1, 2, 0, -1], 18), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 2, -2, -1, 1, 0, 0], 36), ([0, 2, -1, -2, 1, 0, 0], -27), ([0, 2, -1, -1, 0, 0, 0], -9), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, -1, 1, 0, -1], -9)]

def combined249_part1 : Sparse := [([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, -1, 2, 0, 0], 27), ([1, 0, 0, -1, 1, 0, 0], 18), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 1, 0, 0], -9), ([1, 1, -1, -2, 1, 0, 1], 18), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -2, 2, 0, 0], -18), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, -1, -1, 2, -1, 0], 18), ([1, 1, -1, -1, 2, 0, -1], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, 0, -2, 1, 0, 0], 27), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 2, -2, -1, 1, 0, 0], 36), ([1, 2, -1, -1, 0, 0, 0], -9), ([1, 2, -1, -1, 1, -1, 0], 9)]

def combined249 : Sparse := combined249_part0 ++ combined249_part1

def combined250_part0 : Sparse := [([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 1, -2, -1, 1, 0, 1], 18), ([0, 1, -2, -1, 1, 1, 0], -18), ([0, 1, -2, -1, 2, 0, 0], -18), ([0, 1, -2, 0, 1, 0, 0], -9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -2, 1, 1, 0], 18), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, -1, -1, 2, 0, -1], 18), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 2, -2, -1, 1, 0, 0], 27), ([0, 2, -1, -2, 1, 0, 0], -27), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, -1, 1, 0, -1], -9), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, -1, 2, 0, 0], 18)]

def combined250_part1 : Sparse := [([1, 0, 0, -1, 1, 0, 0], 18), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -2, 0, 1, 0, 0], -9), ([1, 1, -1, -2, 1, 0, 1], 18), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -2, 2, 0, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, -1, -1, 2, -1, 0], 18), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, 0, -2, 1, 0, 0], 9), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 2, -2, -1, 1, 0, 0], 27), ([1, 2, -1, -1, 1, 0, -1], -9)]

def combined250 : Sparse := combined250_part0 ++ combined250_part1

def combined251_part0 : Sparse := [([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 1, -2, -1, 1, 0, 1], 18), ([0, 1, -2, -1, 1, 1, 0], -18), ([0, 1, -2, -1, 2, 0, 0], -18), ([0, 1, -1, -2, 1, 1, 0], 18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 2, 0, -1], 18), ([0, 1, -1, 0, 0, 0, 0], -18), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, 0, -1, 0, 0, 0], 18), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 2, -2, -1, 1, 0, 0], 18), ([0, 2, -1, -2, 1, 0, 0], -18), ([0, 2, -1, -1, 1, -1, 0], 18), ([0, 2, -1, -1, 1, 0, -1], -18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, 0, -1, 1, 0, 0], 18), ([1, 1, -2, -1, 1, 1, 0], -18), ([1, 1, -1, -2, 1, 0, 1], 18), ([1, 1, -1, -2, 2, 0, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined251_part1 : Sparse := [([1, 1, -1, -1, 2, -1, 0], 18), ([1, 1, -1, 0, 0, 0, 0], -18), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 2, -2, -1, 1, 0, 0], 18), ([1, 2, -1, -1, 1, 0, -1], -18)]

def combined251 : Sparse := combined251_part0 ++ combined251_part1

def combined252_part0 : Sparse := [([0, 0, -1, 0, -1, 0, 2], -36), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 1, -2, 0, -1, 0, 2], -27), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -1, -1, -1, 0, 2], -9), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, 0, -2, 0, 2], 27), ([0, 1, -1, 0, -1, -1, 2], 9), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, 0, -2, 0, 1], -27), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 2, -1, 0, -2, 0, 1], -36), ([1, 0, -1, 0, -1, 0, 2], -36), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], 27), ([1, 1, -1, -1, -1, 0, 2], -9)]

def combined252_part1 : Sparse := [([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, 0, -2, 0, 2], 27), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 0, 0, -2, 0, 1], -27), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 2, -2, 0, -1, 0, 1], -36), ([1, 2, -1, 0, -1, 0, 0], 18)]

def combined252 : Sparse := combined252_part0 ++ combined252_part1

def combined253_part0 : Sparse := [([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 1, -2, 0, -1, 0, 2], -27), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -1, -1, -1, 0, 2], -9), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, 0, -2, 0, 2], 18), ([0, 1, -1, 0, -2, 1, 1], -9), ([0, 1, -1, 0, -1, -1, 2], 9), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 1, -2, 0, 1], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 0, 0, -2, 0, 1], -27), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 2, -1, 0, -2, 0, 1], -27), ([0, 2, -1, 0, -1, -1, 1], -9), ([1, 0, -1, 0, -1, 0, 2], -27)]

def combined253_part1 : Sparse := [([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], 9), ([1, 1, -1, -1, -1, 0, 2], -18), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, 0, -2, 0, 2], 18), ([1, 1, -1, 0, -2, 1, 1], -18), ([1, 1, -1, 0, -1, -1, 2], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 0, 0, -2, 0, 1], -27), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 2, -2, 0, -1, 0, 1], -36), ([1, 2, -1, -1, -1, 0, 1], -9), ([1, 2, -1, 0, -1, 0, 0], 9)]

def combined253 : Sparse := combined253_part0 ++ combined253_part1

def combined254_part0 : Sparse := [([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 1, -2, 0, -1, 0, 2], -18), ([0, 1, -2, 0, -1, 1, 1], 9), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -1, -1, -1, 0, 2], -18), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, 0, -2, 0, 2], 18), ([0, 1, -1, 0, -2, 1, 1], -9), ([0, 1, -1, 0, -1, -1, 2], 18), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 1, -2, 0, 1], 9), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 0, 0, -2, 0, 1], -9), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 2, -1, -1, -1, 0, 1], 9), ([0, 2, -1, 0, -2, 0, 1], -27), ([1, 0, -1, 0, -1, 0, 2], -18)]

def combined254_part1 : Sparse := [([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], 9), ([1, 1, -2, 1, -1, 0, 1], 9), ([1, 1, -1, -1, -1, 0, 2], -18), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, 0, -2, 0, 2], 18), ([1, 1, -1, 0, -2, 1, 1], -18), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 0, 0, -2, 0, 1], -9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 2, -2, 0, -1, 0, 1], -27), ([1, 2, -1, 0, -1, -1, 1], 9)]

def combined254 : Sparse := combined254_part0 ++ combined254_part1

def combined255_part0 : Sparse := [([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 1, -2, 0, -1, 0, 2], -18), ([0, 1, -2, 0, -1, 1, 1], 18), ([0, 1, -1, -1, -1, 0, 2], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, 0, -2, 0, 2], 18), ([0, 1, -1, 0, -2, 1, 1], -18), ([0, 1, -1, 0, -1, -1, 2], 18), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 1, -2, 0, 1], 18), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 0, -1, 0, 0], 18), ([0, 2, -1, -1, -1, 0, 1], 18), ([0, 2, -1, 0, -2, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 1, -2, 1, -1, 0, 1], 18), ([1, 1, -1, -1, -1, 0, 2], -18), ([1, 1, -1, 0, -2, 0, 2], 18), ([1, 1, -1, 0, -2, 1, 1], -18)]

def combined255_part1 : Sparse := [([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 0, 0, 0, 0], 18), ([1, 1, -1, 1, -1, 0, 0], -18), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 2, -2, 0, -1, 0, 1], -18), ([1, 2, -1, 0, -1, -1, 1], 18)]

def combined255 : Sparse := combined255_part0 ++ combined255_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined256_part0 : Sparse := [([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, -1, 2, 0], -36), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 1, -2, 0, -1, 2, 0], 27), ([0, 1, -2, 0, 0, 1, 0], -27), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, -1, -1, 2, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, 0, -2, 2, 0], -27), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 2, -2, 0, -1, 1, 0], -36), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, -1, 2, 0], -36), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, -1, 2, 0], 27), ([1, 1, -2, 0, 0, 1, 0], -27)]

def combined256_part1 : Sparse := [([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, -1, -1, 2, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -2, 1, 0], 27), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 2, -1, 0, -2, 1, 0], -36), ([1, 2, -1, 0, -1, 0, 0], 18)]

def combined256 : Sparse := combined256_part0 ++ combined256_part1

def combined257_part0 : Sparse := [([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 1, -2, 0, -1, 2, 0], 27), ([0, 1, -2, 0, 0, 1, 0], -9), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, -1, -1, 2, 0], -18), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -2, 2, 0], -18), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, -1, 2, -1], 18), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, 0, -1, -1, 1, 0], -27), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 2, -2, 0, -1, 1, 0], -36), ([0, 2, -1, -1, -1, 1, 0], 9), ([0, 2, -1, 0, -1, 1, -1], 9), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, -1, 2, 0], -27)]

def combined257_part1 : Sparse := [([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, -1, 2, 0], 27), ([1, 1, -2, 0, 0, 1, 0], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, -1, -1, 2, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, -1, 2, -1], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -2, 1, 0], 9), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -2, 1, 0], 27), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 2, -1, -1, -1, 1, 0], 9), ([1, 2, -1, 0, -2, 1, 0], -27), ([1, 2, -1, 0, -1, 0, 0], 9), ([1, 2, -1, 0, -1, 1, -1], 9)]

def combined257 : Sparse := combined257_part0 ++ combined257_part1

def combined258_part0 : Sparse := [([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, -1, 2, 0], -18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -2, 0, -1, 2, 0], 18), ([0, 1, -2, 0, 0, 1, 0], -9), ([0, 1, -2, 1, -1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, -1, -1, 2, 0], -18), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -2, 2, 0], -18), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, -1, 2, -1], 18), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, 0, -1, -1, 1, 0], -27), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 2, -2, 0, -1, 1, 0], -27), ([0, 2, -1, -1, -1, 1, 0], 9), ([1, 0, -1, 0, -1, 1, 1], 18)]

def combined258_part1 : Sparse := [([1, 0, -1, 0, -1, 2, 0], -18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 1, -2, 0, -1, 1, 1], -18), ([1, 1, -2, 0, -1, 2, 0], 18), ([1, 1, -2, 0, 0, 1, 0], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, -1, -1, 2, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -2, 1, 0], 9), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -2, 1, 0], 9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 2, -1, 0, -2, 1, 0], -27), ([1, 2, -1, 0, -1, 1, -1], 9)]

def combined258 : Sparse := combined258_part0 ++ combined258_part1

def combined259_part0 : Sparse := [([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 1, -2, 0, -1, 1, 1], -18), ([0, 1, -2, 0, -1, 2, 0], 18), ([0, 1, -2, 1, -1, 1, 0], 18), ([0, 1, -1, -1, -1, 2, 0], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, 0, -2, 1, 1], 18), ([0, 1, -1, 0, -2, 2, 0], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 2, -1], 18), ([0, 1, -1, 0, 0, 0, 0], 18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 2, -2, 0, -1, 1, 0], -18), ([0, 2, -1, -1, -1, 1, 0], 18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 1, -2, 0, -1, 1, 1], -18), ([1, 1, -2, 0, -1, 2, 0], 18), ([1, 1, -1, -1, -1, 2, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined259_part1 : Sparse := [([1, 1, -1, 1, -2, 1, 0], 18), ([1, 1, -1, 1, -1, 0, 0], -18), ([1, 1, 0, 0, -1, 0, 0], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 2, -1, 0, -2, 1, 0], -18), ([1, 2, -1, 0, -1, 1, -1], 18)]

def combined259 : Sparse := combined259_part0 ++ combined259_part1

def combined260_part0 : Sparse := [([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 1, -2, 0, 0, -1, 2], -27), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -1, -1, 0, -1, 2], -9), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, 0, -1, -1, 2], -9), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, 0, -2, 2], -27), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 2, -2, 0, 0, -1, 1], -36), ([0, 2, -1, 0, 0, -2, 1], -36), ([1, 0, -1, 0, 0, -1, 2], 36), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], 27), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], -9)]

def combined260_part1 : Sparse := [([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, 0, -1, -1, 2], -9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, 0, -2, 1], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 0, 0, -2, 1], 27), ([1, 2, -1, 0, 0, -1, 0], 18)]

def combined260 : Sparse := combined260_part0 ++ combined260_part1

def combined261_part0 : Sparse := [([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 1, -2, 0, 0, -1, 2], -27), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -1, -1, 0, -1, 2], -18), ([0, 1, -1, -1, 0, 0, 1], -27), ([0, 1, -1, 0, -1, -1, 2], -9), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, 0, -2, 2], -18), ([0, 1, -1, 0, 1, -2, 1], -18), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 1, 0, -2, 1], -9), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 2, -2, 0, 0, -1, 1], -36), ([0, 2, -1, 0, -1, -1, 1], -9), ([0, 2, -1, 0, 0, -2, 1], -27), ([1, 0, -1, 0, 0, -1, 2], 27), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 0, 1, -1, 1], -9)]

def combined261_part1 : Sparse := [([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 1, -2, 0, 0, 0, 1], 9), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], -9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, -1, 0, -1, -1, 2], -18), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, 1, -2, 1], -9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, 0, -2, 1], -18), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 0, 0, -2, 1], 27), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 2, -1, -1, 0, -1, 1], -9), ([1, 2, -1, 0, 0, -1, 0], 9)]

def combined261 : Sparse := combined261_part0 ++ combined261_part1

def combined262_part0 : Sparse := [([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 1, -2, 0, 0, -1, 2], -18), ([0, 1, -2, 0, 1, -1, 1], -9), ([0, 1, -2, 1, 0, -1, 1], -18), ([0, 1, -1, -1, 0, -1, 2], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, 0, -1, -1, 2], -18), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, 0, -2, 2], -18), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 0, 1, -2, 1], -18), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 1, 0, -2, 1], -9), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 2, -2, 0, 0, -1, 1], -27), ([0, 2, -1, -1, 0, -1, 1], -9), ([0, 2, -1, 0, -1, -1, 1], -9), ([0, 2, -1, 0, 0, -2, 1], -27)]

def combined262_part1 : Sparse := [([1, 0, -1, 0, 0, -1, 2], 18), ([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 1, -2, 0, 0, 0, 1], 9), ([1, 1, -2, 0, 1, -1, 1], -18), ([1, 1, -2, 1, 0, -1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], -18), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, -1, 0, -1, -1, 2], -18), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, -2, 1], -9), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, 0, -2, 1], -18), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 0, 0, -2, 1], 9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 2, -1, -1, 0, -1, 1], -9), ([1, 2, -1, 0, -1, -1, 1], -9)]

def combined262 : Sparse := combined262_part0 ++ combined262_part1

def combined263_part0 : Sparse := [([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 1, -2, 0, 0, -1, 2], -18), ([0, 1, -2, 0, 1, -1, 1], -18), ([0, 1, -2, 1, 0, -1, 1], -18), ([0, 1, -1, -1, 0, -1, 2], -18), ([0, 1, -1, -1, 0, 0, 1], -18), ([0, 1, -1, 0, -1, -1, 2], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, 0, -2, 2], -18), ([0, 1, -1, 0, 0, 0, 0], -18), ([0, 1, -1, 0, 1, -2, 1], -18), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 1, 0, -2, 1], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 0, 0, -1, 0], -18), ([0, 2, -2, 0, 0, -1, 1], -18), ([0, 2, -1, -1, 0, -1, 1], -18), ([0, 2, -1, 0, -1, -1, 1], -18), ([0, 2, -1, 0, 0, -2, 1], -18)]

def combined263_part1 : Sparse := [([1, 0, -1, 0, 0, 0, 1], -18), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 1, -2, 0, 1, -1, 1], -18), ([1, 1, -2, 1, 0, -1, 1], -18), ([1, 1, -1, -1, 0, -1, 2], -18), ([1, 1, -1, 0, -1, -1, 2], -18), ([1, 1, -1, 0, 0, 0, 0], -18), ([1, 1, -1, 0, 1, -2, 1], -18), ([1, 1, -1, 1, 0, -2, 1], -18), ([1, 1, 0, 0, 0, -1, 0], -18), ([1, 2, -1, -1, 0, -1, 1], -18), ([1, 2, -1, 0, -1, -1, 1], -18)]

def combined263 : Sparse := combined263_part0 ++ combined263_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined264_part0 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 1, -2, 0, 0, 1, 0], -27), ([0, 1, -2, 0, 0, 2, -1], -27), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, 0, -1, 0, 1, -1], -27), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 2, -2, 0, 0, 1, -1], 36), ([0, 2, -1, 0, 0, 0, -1], -18), ([0, 2, -1, 0, 0, 1, -2], -36), ([1, 0, -1, 0, 0, 2, -1], 36), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 1, -2, 0, 0, 1, 0], -27), ([1, 1, -2, 1, 0, 1, -1], 9)]

def combined264_part1 : Sparse := [([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, -1, 2, -1], 9), ([1, 1, -1, 0, 0, 2, -2], -27), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, -1, 1, 0, 1, -2], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 0, 0, 0, 1, -2], 27), ([1, 2, -2, 0, 0, 1, -1], 36), ([1, 2, -1, 0, 0, 0, -1], -18)]

def combined264 : Sparse := combined264_part0 ++ combined264_part1

def combined265_part0 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 1, -2, 0, 0, 1, 0], -9), ([0, 1, -2, 0, 0, 2, -1], -27), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 0, 2, -1], 18), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 0, 1, 1, -2], 18), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 2, -2, 0, 0, 1, -1], 36), ([0, 2, -1, -1, 0, 1, -1], -9), ([0, 2, -1, 0, -1, 1, -1], 9), ([0, 2, -1, 0, 0, 0, -1], -9), ([0, 2, -1, 0, 0, 1, -2], -27)]

def combined265_part1 : Sparse := [([1, 0, -1, 0, 0, 2, -1], 27), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 1, -2, 0, 0, 1, 0], -9), ([1, 1, -2, 1, 0, 1, -1], 9), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, -1, 2, -1], 18), ([1, 1, -1, 0, 0, 2, -2], -18), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 0, 1, -2], 18), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 0, 0, 1, -2], 27), ([1, 2, -2, 0, 0, 1, -1], 36), ([1, 2, -1, 0, -1, 1, -1], 9), ([1, 2, -1, 0, 0, 0, -1], -9)]

def combined265 : Sparse := combined265_part0 ++ combined265_part1

def combined266_part0 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 1, -2, 0, 0, 2, -1], -27), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 0, 2, -1], 18), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 1, 1, -2], 18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 1, 0, 0, 0, 0, -1], 18), ([0, 2, -2, 0, 0, 1, -1], 27), ([0, 2, -1, -1, 0, 1, -1], -18), ([0, 2, -1, 0, -1, 1, -1], 18), ([0, 2, -1, 0, 0, 0, -1], -9), ([0, 2, -1, 0, 0, 1, -2], -18), ([1, 0, -1, 0, 0, 2, -1], 9), ([1, 0, -1, 0, 1, 1, -1], 9)]

def combined266_part1 : Sparse := [([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 1, -2, 0, 1, 1, -1], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, -1, 0, -1, 2, -1], 18), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 0, 2, -2], -18), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 0, 1, -2], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 0, 0, 1, -2], 18), ([1, 2, -2, 0, 0, 1, -1], 27), ([1, 2, -1, -1, 0, 1, -1], -9), ([1, 2, -1, 0, -1, 1, -1], 9), ([1, 2, -1, 0, 0, 0, -1], -9)]

def combined266 : Sparse := combined266_part0 ++ combined266_part1

def combined267_part0 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 1, -2, 0, 0, 2, -1], -18), ([0, 1, -2, 0, 1, 1, -1], -18), ([0, 1, -2, 1, 0, 1, -1], 18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 0, 2, -1], 18), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 0, 0, 0, 0], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 1, 1, -2], 18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, 0, -1, 0, 1, -1], -18), ([0, 1, 0, 0, 0, 0, -1], 18), ([0, 2, -2, 0, 0, 1, -1], 18), ([0, 2, -1, -1, 0, 1, -1], -18), ([0, 2, -1, 0, -1, 1, -1], 18), ([0, 2, -1, 0, 0, 1, -2], -18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 1, -2, 0, 1, 1, -1], -18), ([1, 1, -1, -1, 0, 1, 0], 18), ([1, 1, -1, 0, -1, 2, -1], 18), ([1, 1, -1, 0, 0, 0, 0], -18)]

def combined267_part1 : Sparse := [([1, 1, -1, 0, 0, 2, -2], -18), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 1, 0, 1, -2], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 2, -2, 0, 0, 1, -1], 18), ([1, 2, -1, -1, 0, 1, -1], -18)]

def combined267 : Sparse := combined267_part0 ++ combined267_part1

def combined268_part0 : Sparse := [([0, 0, -1, 0, 1, -1, 1], -27), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 2, -1, 0], -36), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 1, -2, 0, 1, 0, 0], -27), ([0, 1, -2, 0, 2, -1, 0], 27), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 2, -1, 0], 9), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 2, -2, 0], -27), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 2, -2, 0, 1, -1, 0], -36), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 2, -1, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -2, 0, 1, 0, 0], -27), ([1, 1, -2, 0, 2, -1, 0], 27)]

def combined268_part1 : Sparse := [([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 27), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], -27), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, 0, 1, -2, 0], 27), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 2, -1, 0, 0, -1, 0], 18), ([1, 2, -1, 0, 1, -2, 0], -36)]

def combined268 : Sparse := combined268_part0 ++ combined268_part1

def combined269_part0 : Sparse := [([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 2, -1, 0], -27), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 1, -2, 0, 1, 0, 0], -9), ([0, 1, -2, 0, 2, -1, 0], 27), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 2, -1, 0], 18), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 2, -2, 0], -18), ([0, 1, -1, 0, 2, -1, -1], -18), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, -1, 1, 1, -2, 0], 9), ([0, 1, -1, 1, 1, -1, -1], -18), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 2, -2, 0, 1, -1, 0], -36), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, 0, 1, -1, -1], 9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 1, 0, 0], -9)]

def combined269_part1 : Sparse := [([1, 0, -1, 0, 2, -1, 0], -27), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -2, 0, 1, 0, 0], -9), ([1, 1, -2, 0, 2, -1, 0], 27), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 18), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, 0, 0, -1, 1], -27), ([1, 1, -1, 0, 1, -2, 1], 9), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], -18), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 0, 0, 1, -2, 0], 27), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 2, -1, -1, 1, -1, 0], 9), ([1, 2, -1, 0, 0, -1, 0], 9), ([1, 2, -1, 0, 1, -2, 0], -27), ([1, 2, -1, 0, 1, -1, -1], 9)]

def combined269 : Sparse := combined269_part0 ++ combined269_part1

def combined270_part0 : Sparse := [([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 2, -1, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -2, 0, 2, -1, 0], 27), ([0, 1, -2, 1, 1, -1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 2, -1, 0], 18), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 0, 2, -2, 0], -18), ([0, 1, -1, 0, 2, -1, -1], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, -1, 1, 1, -2, 0], 18), ([0, 1, -1, 1, 1, -1, -1], -9), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 2, -2, 0, 1, -1, 0], -27), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, 0, 1, -1, -1], 18), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 1, 0, 0], -9)]

def combined270_part1 : Sparse := [([1, 0, -1, 0, 2, -1, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 1, -2, 0, 2, -1, 0], 27), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], 9), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 0, 1, -2, 1], 18), ([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], -9), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 0, 0, 0, -1, 0], 18), ([1, 1, 0, 0, 1, -2, 0], 18), ([1, 2, -1, -1, 1, -1, 0], 18), ([1, 2, -1, 0, 0, -1, 0], 9), ([1, 2, -1, 0, 1, -2, 0], -18), ([1, 2, -1, 0, 1, -1, -1], 9)]

def combined270 : Sparse := combined270_part0 ++ combined270_part1

def combined271_part0 : Sparse := [([0, 0, -1, 0, 1, -1, 1], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], 18), ([0, 1, -2, 0, 1, -1, 1], 18), ([0, 1, -2, 0, 2, -1, 0], 18), ([0, 1, -2, 1, 1, -1, 0], -18), ([0, 1, -1, -1, 1, 0, 0], -18), ([0, 1, -1, -1, 2, -1, 0], 18), ([0, 1, -1, 0, 0, 0, 0], 18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 2, -2, 0], -18), ([0, 1, -1, 0, 2, -1, -1], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, -1, 1, 1, -2, 0], 18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 2, -2, 0, 1, -1, 0], -18), ([0, 2, -1, 0, 1, -1, -1], 18), ([1, 0, -1, 0, 1, 0, 0], -18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 1, -2, 0, 2, -1, 0], 18), ([1, 1, -2, 1, 1, -1, 0], -18), ([1, 1, -1, 0, 0, -1, 1], -18), ([1, 1, -1, 0, 1, -2, 1], 18)]

def combined271_part1 : Sparse := [([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 0, 2, -1, -1], -18), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 0, 0, 0, -1, 0], 18), ([1, 2, -1, -1, 1, -1, 0], 18), ([1, 2, -1, 0, 1, -2, 0], -18)]

def combined271 : Sparse := combined271_part0 ++ combined271_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined272_part0 : Sparse := [([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 0, 2, 0, -1], -36), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 1, -2, 0, 1, 0, 0], -27), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 0, 2, 0, -1], -27), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -27), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 0, 2, 0, -2], -27), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 0, 0, 1, 0, -2], -27), ([0, 2, -2, 0, 1, 0, -1], -36), ([0, 2, -1, 0, 0, 0, -1], -18), ([0, 2, -1, 0, 1, 0, -2], -36), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 2, 0, -1], -36)]

def combined272_part1 : Sparse := [([1, 0, 0, 0, 1, 0, -1], 9), ([1, 1, -2, 0, 1, 0, 0], -27), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], -27), ([1, 1, -1, -1, 2, 0, -1], 9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 1, -1, -1], -27), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], -27), ([1, 2, -1, 0, 0, 0, -1], -18)]

def combined272 : Sparse := combined272_part0 ++ combined272_part1

def combined273_part0 : Sparse := [([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 0, 2, 0, -1], -27), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 1, -2, 0, 1, 0, 0], -9), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 0, 2, 0, -1], -27), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -18), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, -1, 0, 0, 1, -1], -27), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 0, 2, 0, -2], -18), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -18), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, 0, -1, 1, 0, -1], -27), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 0, 1, 0, -2], -27), ([0, 2, -2, 0, 1, 0, -1], -36), ([0, 2, -1, -1, 1, 0, -1], -9), ([0, 2, -1, 0, 0, 0, -1], -9)]

def combined273_part1 : Sparse := [([0, 2, -1, 0, 1, -1, -1], 9), ([0, 2, -1, 0, 1, 0, -2], -27), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 0, 2, 0, -1], -27), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 1, -2, 0, 1, 0, 0], -9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], -18), ([1, 1, -1, -1, 2, 0, -1], 18), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 0, 1, 1, -2], 18), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], -18), ([1, 1, -1, 1, 1, 0, -2], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], -27), ([1, 2, -1, 0, 0, 0, -1], -9)]

def combined273_part2 : Sparse := [([1, 2, -1, 0, 1, -1, -1], 9)]

def combined273 : Sparse := combined273_part0 ++ combined273_part1 ++ combined273_part2

def combined274_part0 : Sparse := [([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, -1, 0, 2, 0, -1], -9), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 1, -2, 0, 2, 0, -1], -27), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -9), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 0, 2, 0, -2], -18), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 1, -1, -1], -9), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 0, 1, 0, -2], -18), ([0, 2, -2, 0, 1, 0, -1], -27), ([0, 2, -1, -1, 1, 0, -1], -9), ([0, 2, -1, 0, 0, 0, -1], -9), ([0, 2, -1, 0, 1, -1, -1], 9), ([0, 2, -1, 0, 1, 0, -2], -18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 0, 2, 0, -1], -9)]

def combined274_part1 : Sparse := [([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 1, -2, 0, 1, 1, -1], 9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 1, -1], -9), ([1, 1, -1, -1, 2, 0, -1], 18), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 0, 1, 1, -2], 18), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], -9), ([1, 1, -1, 1, 1, 0, -2], 18), ([1, 1, 0, 0, 0, 0, -1], 18), ([1, 1, 0, 0, 1, 0, -2], -18), ([1, 2, -1, -1, 1, 0, -1], 9), ([1, 2, -1, 0, 0, 0, -1], -9), ([1, 2, -1, 0, 1, -1, -1], 18)]

def combined274 : Sparse := combined274_part0 ++ combined274_part1

def combined275 : Sparse := [([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 1, -2, 0, 2, 0, -1], -18), ([0, 1, -1, -1, 1, 0, 0], -18), ([0, 1, -1, 0, 0, 1, -1], -18), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 0, 2, 0, -2], -18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 2, -2, 0, 1, 0, -1], -18), ([0, 2, -1, 0, 1, 0, -2], -18), ([1, 0, -1, 0, 1, 0, 0], 18), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 1, -2, 0, 1, 1, -1], 18), ([1, 1, -2, 1, 1, 0, -1], 18), ([1, 1, -1, -1, 2, 0, -1], 18), ([1, 1, -1, 0, 0, 0, 0], 18), ([1, 1, -1, 0, 1, 1, -2], 18), ([1, 1, -1, 0, 2, -1, -1], 18), ([1, 1, -1, 1, 1, 0, -2], 18), ([1, 1, 0, 0, 0, 0, -1], 18), ([1, 2, -1, -1, 1, 0, -1], 18), ([1, 2, -1, 0, 1, -1, -1], 18)]

def combined276_part0 : Sparse := [([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -2, 2, -1, 0, 0], -27), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 2, -2, 0, 0], -27), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, -1, 2, -1, 0, -1], -9), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 2, -2, 1, -1, 0, 0], -36), ([0, 2, -1, 1, -2, 0, 0], -36), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 2, -1, 0, 0], 36), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], 27), ([1, 1, -1, 1, -2, 0, 1], -9)]

def combined276_part1 : Sparse := [([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 2, -1, -1, 0], -9), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], 27), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 2, -1, 0, -1, 0, 0], 18)]

def combined276 : Sparse := combined276_part0 ++ combined276_part1

def combined277_part0 : Sparse := [([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -2, 2, -1, 0, 0], -27), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -27), ([0, 1, -1, 1, -2, 0, 1], -9), ([0, 1, -1, 1, -2, 1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 2, -2, 0, 0], -18), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, -1, 2, -1, 0, -1], -18), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 2, -2, 1, -1, 0, 0], -36), ([0, 2, -1, 1, -2, 0, 0], -27), ([0, 2, -1, 1, -1, -1, 0], -9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 1, 0, 0, 0], -9)]

def combined277_part1 : Sparse := [([1, 0, -1, 2, -1, 0, 0], 27), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], 9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 1, -2, 0, 1], -18), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 2, -1, -1, 0], -18), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 0, 1, -2, 0, 0], 27), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 2, -1, 0, -1, 0, 0], 9), ([1, 2, -1, 1, -1, 0, -1], -9)]

def combined277 : Sparse := combined277_part0 ++ combined277_part1

def combined278_part0 : Sparse := [([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -2, 2, -1, 0, 0], -27), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 1, -2, 0, 1], -18), ([0, 1, -1, 1, -2, 1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 2, -2, 0, 0], -18), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, -1, 2, -1, 0, -1], -18), ([0, 1, 0, 0, -1, 0, 0], -18), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 2, -2, 1, -1, 0, 0], -27), ([0, 2, -1, 1, -2, 0, 0], -18), ([0, 2, -1, 1, -1, -1, 0], -18), ([0, 2, -1, 1, -1, 0, -1], -9)]

def combined278_part1 : Sparse := [([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 2, -1, 0, 0], 9), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 1, -2, 0, 1], -18), ([1, 1, -1, 1, -2, 1, 0], -18), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, -1, 2, -1, -1, 0], -18), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 0, -1, 0, 0], -18), ([1, 1, 0, 1, -2, 0, 0], 18), ([1, 2, -1, 0, -1, 0, 0], 9), ([1, 2, -1, 1, -1, -1, 0], -9), ([1, 2, -1, 1, -1, 0, -1], -18)]

def combined278 : Sparse := combined278_part0 ++ combined278_part1

def combined279_part0 : Sparse := [([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, 0, 1, -1, 0, 0], -18), ([0, 1, -2, 1, -1, 0, 1], -18), ([0, 1, -2, 1, -1, 1, 0], -18), ([0, 1, -2, 2, -1, 0, 0], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([0, 1, -1, 0, 0, 0, 0], -18), ([0, 1, -1, 1, -2, 0, 1], -18), ([0, 1, -1, 1, -2, 1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 2, -2, 0, 0], -18), ([0, 1, -1, 2, -1, -1, 0], -18), ([0, 1, -1, 2, -1, 0, -1], -18), ([0, 1, 0, 0, -1, 0, 0], -18), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 2, -2, 1, -1, 0, 0], -18), ([0, 2, -1, 1, -2, 0, 0], -18), ([0, 2, -1, 1, -1, -1, 0], -18), ([0, 2, -1, 1, -1, 0, -1], -18)]

def combined279_part1 : Sparse := [([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, 0, 1, -1, 0, 0], -18), ([1, 1, -2, 1, -1, 0, 1], -18), ([1, 1, -2, 1, -1, 1, 0], -18), ([1, 1, -1, 0, 0, 0, 0], -18), ([1, 1, -1, 1, -2, 0, 1], -18), ([1, 1, -1, 1, -2, 1, 0], -18), ([1, 1, -1, 2, -1, -1, 0], -18), ([1, 1, -1, 2, -1, 0, -1], -18), ([1, 1, 0, 0, -1, 0, 0], -18), ([1, 2, -1, 1, -1, -1, 0], -18), ([1, 2, -1, 1, -1, 0, -1], -18)]

def combined279 : Sparse := combined279_part0 ++ combined279_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined280_part0 : Sparse := [([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 2, 0, -1, 0], -36), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -2, 2, 0, -1, 0], -27), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, -1, 2, -1, -1, 0], 9), ([0, 1, -1, 2, 0, -2, 0], 27), ([0, 1, -1, 2, 0, -1, -1], -9), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, 0, -2, 0], -27), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 2, -1, 1, 0, -2, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 2, 0, -1, 0], -36), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], 27), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, 0, 0, -1, 1], -36)]

def combined280_part1 : Sparse := [([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, 0, -2, 1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], -27), ([1, 1, -1, 2, 0, -2, 0], 27), ([1, 1, -1, 2, 0, -1, -1], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, 0, -2, 0], -27), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 2, -2, 1, 0, -1, 0], -36), ([1, 2, -1, 0, 0, -1, 0], 18)]

def combined280 : Sparse := combined280_part0 ++ combined280_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined289_part2 : Sparse := [([1, 2, 0, -1, -1, 0, 0], -9)]

end MUB6.TaoCertificate

end OAI
end


