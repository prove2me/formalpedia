-- Prove2me | Definitions.Def_OAIQ106E043
-- name    : OAIQ106E043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:01:13.49233+00:00
-- url     : https://prove2.me/theorems/0d298b04-226a-4e95-97aa-c0fe2131379f
-- title:
--   Definitions bundle OAIQ106E043 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2362 declarations of OpenAI's Lean: 2361 definitions and 1 theorem. The definitions and types are `OAI.MUB6.Certificate.Integer.Sparse.substitute`, `OAI.MUB6.Certificate.Integer.Sparse.toRational`, `OAI.MUB6.Certificate.MixedSemantics.Code.moment`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm0`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm10`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm100`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1000`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1001`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1003`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1004`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1005`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1006`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1008`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm101`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1012`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1013`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1015`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1016`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1017`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1018`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm102`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1020`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1021`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1022`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1023`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1024`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1025`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1026`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1027`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1029`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm103`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1030`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1031`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1032`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1033`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1036`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1039`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1040`, `OAI.MUB6.Certificate.MixedSemantics.sourceForm1041` and 2321 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Interpretation`, `MutuallyUnbiased_Certificate_MixedTargetBasic`, `MutuallyUnbiased_MixedSemantics_Meaning`, `MutuallyUnbiased_MixedSemantics_Sources0`, `MutuallyUnbiased_MixedSemantics_Sources1`, `MutuallyUnbiased_MixedSemantics_Sources10`, `MutuallyUnbiased_MixedSemantics_Sources11`, `MutuallyUnbiased_MixedSemantics_Sources12`, `MutuallyUnbiased_MixedSemantics_Sources13`, `MutuallyUnbiased_MixedSemantics_Sources14`, `MutuallyUnbiased_MixedSemantics_Sources15`, `MutuallyUnbiased_MixedSemantics_Sources16`, `MutuallyUnbiased_MixedSemantics_Sources17`, `MutuallyUnbiased_MixedSemantics_Sources18`, `MutuallyUnbiased_MixedSemantics_Sources19`, `MutuallyUnbiased_MixedSemantics_Sources2`, `MutuallyUnbiased_MixedSemantics_Sources20`, `MutuallyUnbiased_MixedSemantics_Sources21`, `MutuallyUnbiased_MixedSemantics_Sources22`, `MutuallyUnbiased_MixedSemantics_Sources23`, `MutuallyUnbiased_MixedSemantics_Sources24`, `MutuallyUnbiased_MixedSemantics_Sources25`, `MutuallyUnbiased_MixedSemantics_Sources26`, `MutuallyUnbiased_MixedSemantics_Sources27`, `MutuallyUnbiased_MixedSemantics_Sources28`, `MutuallyUnbiased_MixedSemantics_Sources29`, `MutuallyUnbiased_MixedSemantics_Sources3`, `MutuallyUnbiased_MixedSemantics_Sources30`, `MutuallyUnbiased_MixedSemantics_Sources31`, `MutuallyUnbiased_MixedSemantics_Sources32`, `MutuallyUnbiased_MixedSemantics_Sources33`, `MutuallyUnbiased_MixedSemantics_Sources34`, `MutuallyUnbiased_MixedSemantics_Sources35`, `MutuallyUnbiased_MixedSemantics_Sources36`, `MutuallyUnbiased_MixedSemantics_Sources37`, `MutuallyUnbiased_MixedSemantics_Sources38`, `MutuallyUnbiased_MixedSemantics_Sources39`, `MutuallyUnbiased_MixedSemantics_Sources4`, `MutuallyUnbiased_MixedSemantics_Sources40`, `MutuallyUnbiased_MixedSemantics_Sources41`, `MutuallyUnbiased_MixedSemantics_Sources42`, `MutuallyUnbiased_MixedSemantics_Sources43`, `MutuallyUnbiased_MixedSemantics_Sources44`, `MutuallyUnbiased_MixedSemantics_Sources45`, `MutuallyUnbiased_MixedSemantics_Sources46`, `MutuallyUnbiased_MixedSemantics_Sources47`, `MutuallyUnbiased_MixedSemantics_Sources48`, `MutuallyUnbiased_MixedSemantics_Sources49`, `MutuallyUnbiased_MixedSemantics_Sources5`, `MutuallyUnbiased_MixedSemantics_Sources50`, `MutuallyUnbiased_MixedSemantics_Sources51`, `MutuallyUnbiased_MixedSemantics_Sources52`, `MutuallyUnbiased_MixedSemantics_Sources53`, `MutuallyUnbiased_MixedSemantics_Sources54`, `MutuallyUnbiased_MixedSemantics_Sources55`, `MutuallyUnbiased_MixedSemantics_Sources56`, `MutuallyUnbiased_MixedSemantics_Sources57`, `MutuallyUnbiased_MixedSemantics_Sources58`, `MutuallyUnbiased_MixedSemantics_Sources59`, `MutuallyUnbiased_MixedSemantics_Sources6`, `MutuallyUnbiased_MixedSemantics_Sources60`, `MutuallyUnbiased_MixedSemantics_Sources61`, `MutuallyUnbiased_MixedSemantics_Sources62`, `MutuallyUnbiased_MixedSemantics_Sources63`, `MutuallyUnbiased_MixedSemantics_Sources64`, `MutuallyUnbiased_MixedSemantics_Sources65`, `MutuallyUnbiased_MixedSemantics_Sources66`, `MutuallyUnbiased_MixedSemantics_Sources67`, `MutuallyUnbiased_MixedSemantics_Sources68`, `MutuallyUnbiased_MixedSemantics_Sources69`, `MutuallyUnbiased_MixedSemantics_Sources7`, `MutuallyUnbiased_MixedSemantics_Sources70`, `MutuallyUnbiased_MixedSemantics_Sources71`, `MutuallyUnbiased_MixedSemantics_Sources72`, `MutuallyUnbiased_MixedSemantics_Sources73`, `MutuallyUnbiased_MixedSemantics_Sources74`, `MutuallyUnbiased_MixedSemantics_Sources75`, `MutuallyUnbiased_MixedSemantics_Sources76`, `MutuallyUnbiased_MixedSemantics_Sources77`, `MutuallyUnbiased_MixedSemantics_Sources78`, `MutuallyUnbiased_MixedSemantics_Sources79`, `MutuallyUnbiased_MixedSemantics_Sources8`, `MutuallyUnbiased_MixedSemantics_Sources80`, `MutuallyUnbiased_MixedSemantics_Sources81`, `MutuallyUnbiased_MixedSemantics_Sources82`, `MutuallyUnbiased_MixedSemantics_Sources83`, `MutuallyUnbiased_MixedSemantics_Sources84`, `MutuallyUnbiased_MixedSemantics_Sources85`, `MutuallyUnbiased_MixedSemantics_Sources86`, `MutuallyUnbiased_MixedSemantics_Sources9`, `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic6`, `MutuallyUnbiased_MixedSources_Arithmetic62`, `MutuallyUnbiased_MixedSources_Arithmetic63`, `MutuallyUnbiased_MixedSources_Arithmetic64`, `MutuallyUnbiased_MixedSources_Arithmetic65`, `MutuallyUnbiased_MixedSources_Arithmetic66`, `MutuallyUnbiased_MixedSources_Arithmetic67`, `MutuallyUnbiased_MixedSources_Arithmetic68`, `MutuallyUnbiased_MixedSources_Arithmetic69`, `MutuallyUnbiased_MixedSources_Arithmetic7`, `MutuallyUnbiased_MixedSources_Arithmetic70`, `MutuallyUnbiased_MixedSources_Arithmetic71`, `MutuallyUnbiased_MixedSources_Arithmetic72`, `MutuallyUnbiased_MixedSources_Arithmetic73`, `MutuallyUnbiased_MixedTargets_ReductionMergeData46`, `MutuallyUnbiased_Moments_GramNormalization`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106E002` and `OAIQ106E010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E044`, `OAIQ106E086`, `OAIQ106E120`, `OAIQ106E121`, `OAIQ106E122`, `OAIQ106E124`, `OAIQ106E125`, `OAIQ106E126`, `OAIQ106E127`, `OAIQ106E128`, `OAIQ106E129`, `OAIQ106E130`, `OAIQ106E133`, `OAIQ106E135`, `OAIQ106E138` and `OAIQ106E139`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.interpretation_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e` and `OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E010

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Integer.Sparse

variable {ι κ Ω : Type*}

def toRational (v : Integer.Sparse ι) : Certificate.Sparse ι :=
  v.map fun p => (p.1, (p.2 : ℚ))

@[simp] theorem eval_toRational (v : Integer.Sparse ι) (x : ι → ℝ) :
    Certificate.Sparse.eval (toRational v) x = eval v x := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    change ((p.2 : ℚ) : ℝ) * x p.1 + Certificate.Sparse.eval (toRational v) x =
      (p.2 : ℝ) * x p.1 + eval v x
    rw [ih]
    simp

end Integer.Sparse
end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Meaning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

noncomputable def Code.moment (B : Fin 7 → Basis) (c : Code) : ℝ :=
  mixedMoment B c.matrix c.label

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

def orderedKey (s t : Fin 2) (a v : Charge) : Key :=
  ⟨s, t, (rowOrder a v).map (fun i => (a i, v i))⟩

def normalize (s t : Fin 2) (a v : Charge) : Key :=
  if (compare s.val t.val |>.then (compare (List.ofFn a) (List.ofFn v))) == .gt then
    orderedKey t s v a
  else orderedKey s t a v

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.Integer.Sparse

variable {ι κ : Type*}

def substitute (v : Sparse κ) (rows : κ → Sparse ι) : Sparse ι :=
  v.flatMap fun p => scale p.2 (rows p.1)

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm0 : Integer.Sparse Master := [(Sum.inr 4898, 3), (Sum.inr 4899, 2), (Sum.inr 5302, 6), (Sum.inr 5310, 2), (Sum.inr 5412, 6), (Sum.inr 5443, 6), (Sum.inr 5453, 3), (Sum.inr 5455, 2)]

def sourceForm1 : Integer.Sparse Master := [(Sum.inr 4889, 2), (Sum.inr 4890, 1), (Sum.inr 4896, 2), (Sum.inr 5284, 2), (Sum.inr 5294, 2), (Sum.inr 5406, 2), (Sum.inr 5411, 4), (Sum.inr 5435, 4), (Sum.inr 5443, 2), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5452, 2), (Sum.inr 5454, 2), (Sum.inr 5493, 1)]

def sourceForm2 : Integer.Sparse Master := [(Sum.inr 2245, 2), (Sum.inr 2247, 1), (Sum.inr 2266, 2), (Sum.inr 3077, 2), (Sum.inr 3101, 2), (Sum.inr 3801, 2), (Sum.inr 3809, 4), (Sum.inr 3853, 4), (Sum.inr 3862, 2), (Sum.inr 3910, 2), (Sum.inr 3913, 2), (Sum.inr 4016, 1), (Sum.inr 4039, 2), (Sum.inr 4040, 2)]

def sourceForm3 : Integer.Sparse Master := [(Sum.inr 5301, 4), (Sum.inr 5302, 4), (Sum.inr 5306, 2), (Sum.inr 5412, 4), (Sum.inr 5437, 2), (Sum.inr 5439, 4), (Sum.inr 5453, 4), (Sum.inr 5455, 4), (Sum.inr 5456, 2)]

def sourceForm4 : Integer.Sparse Master := [(Sum.inr 5259, 4), (Sum.inr 5261, 1), (Sum.inr 5275, 2), (Sum.inr 5293, 2), (Sum.inr 5473, 4), (Sum.inr 5475, 1), (Sum.inr 5477, 2), (Sum.inr 5483, 4), (Sum.inr 5487, 1), (Sum.inr 5490, 4), (Sum.inr 5492, 2), (Sum.inr 5493, 2), (Sum.inr 5501, 1)]

def sourceForm5 : Integer.Sparse Master := [(Sum.inr 2723, 4), (Sum.inr 2726, 1), (Sum.inr 2743, 2), (Sum.inr 2767, 2), (Sum.inr 3958, 4), (Sum.inr 3963, 1), (Sum.inr 3971, 2), (Sum.inr 3981, 4), (Sum.inr 4000, 1), (Sum.inr 4013, 4), (Sum.inr 4015, 2), (Sum.inr 4018, 2), (Sum.inr 4055, 1)]

def sourceForm6 : Integer.Sparse Master := [(Sum.inr 7, -1), (Sum.inr 378, 1), (Sum.inr 514, 1), (Sum.inr 518, 1), (Sum.inr 521, 1), (Sum.inr 526, 1), (Sum.inr 527, 1)]

def sourceForm7 : Integer.Sparse Master := [(Sum.inr 5439, 8), (Sum.inr 5441, 2), (Sum.inr 5443, 4), (Sum.inr 5448, 4), (Sum.inr 5449, 1), (Sum.inr 5455, 4), (Sum.inr 5488, 2), (Sum.inr 5491, 4), (Sum.inr 5496, 1)]

def sourceForm8 : Integer.Sparse Master := [(Sum.inr 6, -1), (Sum.inr 494, 2), (Sum.inr 500, 1), (Sum.inr 524, 1), (Sum.inr 527, 2)]

def sourceForm9 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5293, 3), (Sum.inr 5294, 3), (Sum.inr 5296, 1), (Sum.inr 5309, 1), (Sum.inr 5310, 1), (Sum.inr 5434, 6), (Sum.inr 5442, 3), (Sum.inr 5451, 3), (Sum.inr 5454, 3), (Sum.inr 5492, 3), (Sum.inr 5494, 1), (Sum.inr 5495, 1)]

def sourceForm10 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 5306, 3), (Sum.inr 5308, 1), (Sum.inr 5310, 1), (Sum.inr 5439, 6), (Sum.inr 5441, 3), (Sum.inr 5443, 3), (Sum.inr 5453, 3), (Sum.inr 5455, 4), (Sum.inr 5456, 1), (Sum.inr 5491, 3), (Sum.inr 5496, 1)]

def sourceForm11 : Integer.Sparse Master := [(Sum.inr 4084, 8), (Sum.inr 4085, 1), (Sum.inr 4092, 12), (Sum.inr 4093, 8), (Sum.inr 4097, 1)]

def sourceForm12 : Integer.Sparse Master := [(Sum.inr 5283, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 2), (Sum.inr 5406, 2), (Sum.inr 5411, 4), (Sum.inr 5433, 2), (Sum.inr 5447, 2), (Sum.inr 5450, 2), (Sum.inr 5452, 2), (Sum.inr 5453, 2), (Sum.inr 5454, 4), (Sum.inr 5485, 2), (Sum.inr 5489, 1), (Sum.inr 5493, 2)]

def sourceForm13 : Integer.Sparse Master := [(Sum.inr 3076, 1), (Sum.inr 3077, 2), (Sum.inr 3100, 2), (Sum.inr 3801, 2), (Sum.inr 3809, 4), (Sum.inr 3912, 2), (Sum.inr 4009, 1), (Sum.inr 4010, 2), (Sum.inr 4016, 2), (Sum.inr 4025, 2), (Sum.inr 4029, 2), (Sum.inr 4033, 2), (Sum.inr 4039, 2), (Sum.inr 4040, 4)]

def sourceForm14 : Integer.Sparse Master := [(Sum.inr 4887, 1), (Sum.inr 4888, 4), (Sum.inr 5405, 4), (Sum.inr 5433, 4), (Sum.inr 5434, 8), (Sum.inr 5439, 4), (Sum.inr 5498, 1), (Sum.inr 5499, 4)]

def sourceForm15 : Integer.Sparse Master := [(Sum.inr 5290, 2), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5304, 1), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5454, 1), (Sum.inr 5455, 1), (Sum.inr 5481, 2), (Sum.inr 5484, 2), (Sum.inr 5485, 2), (Sum.inr 5490, 2), (Sum.inr 5492, 2), (Sum.inr 5493, 1), (Sum.inr 5494, 1), (Sum.inr 5495, 1)]

def sourceForm16 : Integer.Sparse Master := [(Sum.inr 2764, 2), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 2782, 1), (Sum.inr 3876, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 3910, 2), (Sum.inr 3913, 1), (Sum.inr 3914, 1), (Sum.inr 3979, 2), (Sum.inr 3982, 2), (Sum.inr 3983, 2), (Sum.inr 3998, 2), (Sum.inr 4001, 1), (Sum.inr 4013, 2), (Sum.inr 4017, 2), (Sum.inr 4018, 1), (Sum.inr 4019, 1), (Sum.inr 4020, 1), (Sum.inr 4021, 1)]

def sourceForm17 : Integer.Sparse Master := [(Sum.inr 5271, 4), (Sum.inr 5272, 1), (Sum.inr 5275, 2), (Sum.inr 5306, 2), (Sum.inr 5473, 4), (Sum.inr 5475, 1), (Sum.inr 5478, 2), (Sum.inr 5485, 4), (Sum.inr 5490, 4), (Sum.inr 5491, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 2), (Sum.inr 5501, 1)]

def sourceForm18 : Integer.Sparse Master := [(Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 1), (Sum.inr 5292, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5477, 1), (Sum.inr 5478, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 1), (Sum.inr 5485, 1), (Sum.inr 5486, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 3), (Sum.inr 5491, 1), (Sum.inr 5492, 1), (Sum.inr 5493, 1), (Sum.inr 5499, 2), (Sum.inr 5500, 1), (Sum.inr 5501, 1)]

def sourceForm19 : Integer.Sparse Master := [(Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2739, 1), (Sum.inr 2766, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3852, 1), (Sum.inr 3902, 1), (Sum.inr 3957, 1), (Sum.inr 3958, 1), (Sum.inr 3961, 1), (Sum.inr 3971, 1), (Sum.inr 3974, 1), (Sum.inr 3980, 1), (Sum.inr 3981, 1), (Sum.inr 3992, 1), (Sum.inr 3999, 1), (Sum.inr 4009, 1), (Sum.inr 4010, 1), (Sum.inr 4013, 2), (Sum.inr 4014, 1), (Sum.inr 4015, 1), (Sum.inr 4018, 1), (Sum.inr 4050, 1), (Sum.inr 4052, 1), (Sum.inr 4053, 1), (Sum.inr 4054, 1), (Sum.inr 4055, 1)]

def sourceForm20 : Integer.Sparse Master := [(Sum.inr 5431, 2), (Sum.inr 5432, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5440, 2), (Sum.inr 5450, 2), (Sum.inr 5454, 2), (Sum.inr 5481, 2), (Sum.inr 5484, 1), (Sum.inr 5489, 2), (Sum.inr 5490, 3), (Sum.inr 5492, 2), (Sum.inr 5493, 2), (Sum.inr 5495, 1)]

def sourceForm21 : Integer.Sparse Master := [(Sum.inr 5304, 6), (Sum.inr 5305, 1), (Sum.inr 5310, 2), (Sum.inr 5451, 6), (Sum.inr 5455, 2), (Sum.inr 5484, 6), (Sum.inr 5492, 6), (Sum.inr 5495, 1)]

def sourceForm22 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 2), (Sum.inr 5306, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 4), (Sum.inr 5485, 2), (Sum.inr 5486, 2), (Sum.inr 5487, 2), (Sum.inr 5490, 4), (Sum.inr 5491, 2), (Sum.inr 5492, 2), (Sum.inr 5499, 2), (Sum.inr 5501, 2)]

def sourceForm23 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5440, 2), (Sum.inr 5442, 2), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5452, 2), (Sum.inr 5453, 1), (Sum.inr 5454, 2), (Sum.inr 5485, 4), (Sum.inr 5489, 2), (Sum.inr 5490, 4), (Sum.inr 5492, 2), (Sum.inr 5493, 2), (Sum.inr 5495, 2)]

def sourceForm24 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5307, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 2), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 1), (Sum.inr 5452, 2), (Sum.inr 5453, 1), (Sum.inr 5454, 3), (Sum.inr 5455, 1), (Sum.inr 5490, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 1), (Sum.inr 5495, 1)]

def sourceForm25 : Integer.Sparse Master := [(Sum.inr 4083, 3), (Sum.inr 4084, 2), (Sum.inr 4091, 6), (Sum.inr 4092, 6), (Sum.inr 4093, 6), (Sum.inr 4094, 2), (Sum.inr 4096, 3), (Sum.inr 4097, 2)]

def sourceForm26 : Integer.Sparse Master := [(Sum.inr 5405, 8), (Sum.inr 5452, 2), (Sum.inr 5482, 8), (Sum.inr 5489, 4), (Sum.inr 5499, 8)]

def sourceForm27 : Integer.Sparse Master := [(Sum.inr 5423, 1), (Sum.inr 5424, 4), (Sum.inr 5433, 4), (Sum.inr 5477, 2), (Sum.inr 5478, 2), (Sum.inr 5482, 4), (Sum.inr 5490, 4), (Sum.inr 5497, 2), (Sum.inr 5499, 4), (Sum.inr 5500, 2), (Sum.inr 5501, 1)]

def sourceForm28 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1), (Sum.inr 5482, 3), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 2), (Sum.inr 5489, 1), (Sum.inr 5490, 4), (Sum.inr 5493, 1), (Sum.inr 5497, 1), (Sum.inr 5498, 1), (Sum.inr 5499, 4), (Sum.inr 5500, 2), (Sum.inr 5501, 2)]

def sourceForm29 : Integer.Sparse Master := [(Sum.inr 4091, 8), (Sum.inr 4092, 4), (Sum.inr 4093, 4), (Sum.inr 4095, 2), (Sum.inr 4096, 8), (Sum.inr 4097, 4)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm32 : Integer.Sparse Master := [(Sum.inr 1092, 1), (Sum.inr 2063, 3), (Sum.inr 2285, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

def sourceForm33 : Integer.Sparse Master := [(Sum.inr 1067, 3), (Sum.inr 1069, 1), (Sum.inr 1092, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def sourceForm34 : Integer.Sparse Master := [(Sum.inr 1067, 2), (Sum.inr 2041, 2), (Sum.inr 2284, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def sourceForm35 : Integer.Sparse Master := [(Sum.inr 1459, 1), (Sum.inr 2041, 2), (Sum.inr 2063, 2), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def sourceForm36 : Integer.Sparse Master := [(Sum.inr 1069, 2), (Sum.inr 1459, 3), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def sourceForm38 : Integer.Sparse Master := [(Sum.inr 795, 2), (Sum.inr 797, 1), (Sum.inr 814, 1), (Sum.inr 829, 1), (Sum.inr 1355, 2), (Sum.inr 1369, 1), (Sum.inr 1408, 1), (Sum.inr 1903, 2), (Sum.inr 1916, 2), (Sum.inr 1927, 2), (Sum.inr 2037, 2), (Sum.inr 2063, 1), (Sum.inr 2092, 2), (Sum.inr 2113, 1), (Sum.inr 2254, 2), (Sum.inr 2267, 1), (Sum.inr 2280, 1), (Sum.inr 3054, 1), (Sum.inr 3222, 2), (Sum.inr 3224, 1), (Sum.inr 3225, 1)]

def sourceForm40 : Integer.Sparse Master := [(Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 3156, 2), (Sum.inr 3161, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

def sourceForm41 : Integer.Sparse Master := [(Sum.inr 1029, 2), (Sum.inr 1031, 1), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

def sourceForm42 : Integer.Sparse Master := [(Sum.inr 1029, 1), (Sum.inr 2013, 1), (Sum.inr 2096, 1), (Sum.inr 2125, 1), (Sum.inr 2253, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

def sourceForm43 : Integer.Sparse Master := [(Sum.inr 1458, 1), (Sum.inr 2013, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2255, 1), (Sum.inr 3156, 1), (Sum.inr 4084, -1)]

def sourceForm44 : Integer.Sparse Master := [(Sum.inr 1061, 1), (Sum.inr 2037, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

def sourceForm45 : Integer.Sparse Master := [(Sum.inr 1462, 1), (Sum.inr 2096, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 3161, 1), (Sum.inr 4084, -1)]

def sourceForm46 : Integer.Sparse Master := [(Sum.inr 1047, 1), (Sum.inr 2026, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

def sourceForm47 : Integer.Sparse Master := [(Sum.inr 1461, 1), (Sum.inr 2125, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 4084, -1)]

def sourceForm48 : Integer.Sparse Master := [(Sum.inr 1031, 1), (Sum.inr 1458, 2), (Sum.inr 1461, 1), (Sum.inr 1462, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

def sourceForm51 : Integer.Sparse Master := [(Sum.inr 1084, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 2290, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

def sourceForm52 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 1067, 1), (Sum.inr 1068, 1), (Sum.inr 1084, 1), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

def sourceForm53 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 2040, 1), (Sum.inr 2283, 1), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

def sourceForm54 : Integer.Sparse Master := [(Sum.inr 2040, 1), (Sum.inr 2041, 1), (Sum.inr 2042, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

def sourceForm55 : Integer.Sparse Master := [(Sum.inr 1068, 2), (Sum.inr 2042, 2), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

def sourceForm59 : Integer.Sparse Master := [(Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 3158, 3), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

def sourceForm60 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1016, 1), (Sum.inr 1024, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

def sourceForm61 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 2083, 3), (Sum.inr 2233, 1), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

def sourceForm62 : Integer.Sparse Master := [(Sum.inr 1457, 1), (Sum.inr 2010, 3), (Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 4083, -1)]

def sourceForm63 : Integer.Sparse Master := [(Sum.inr 1024, 1), (Sum.inr 2010, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm320 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2266, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def sourceForm321 : Integer.Sparse Master := [(Sum.inr 2266, 1), (Sum.inr 3535, 2), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def sourceForm322 : Integer.Sparse Master := [(Sum.inr 3159, 1), (Sum.inr 3377, 1), (Sum.inr 3379, 1), (Sum.inr 3395, 2), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def sourceForm323 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 3377, 1), (Sum.inr 3504, 1), (Sum.inr 3528, 1), (Sum.inr 3531, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def sourceForm324 : Integer.Sparse Master := [(Sum.inr 3153, 1), (Sum.inr 3388, 1), (Sum.inr 3488, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 2), (Sum.inr 4084, -1)]

def sourceForm325 : Integer.Sparse Master := [(Sum.inr 2026, 1), (Sum.inr 3153, 1), (Sum.inr 3156, 1), (Sum.inr 3157, 1), (Sum.inr 3159, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def sourceForm326 : Integer.Sparse Master := [(Sum.inr 3531, 1), (Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 2), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def sourceForm327 : Integer.Sparse Master := [(Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

def sourceForm328 : Integer.Sparse Master := [(Sum.inr 3157, 1), (Sum.inr 3392, 1), (Sum.inr 3504, 1), (Sum.inr 3506, 1), (Sum.inr 3535, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm329 : Integer.Sparse Master := [(Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 3488, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def sourceForm331 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 1179, 1), (Sum.inr 1182, 1), (Sum.inr 1185, 1), (Sum.inr 1261, 1), (Sum.inr 1992, 1), (Sum.inr 2004, 1), (Sum.inr 2035, 1), (Sum.inr 2197, 1), (Sum.inr 2833, 1), (Sum.inr 2835, 1), (Sum.inr 2838, 1), (Sum.inr 2905, 1), (Sum.inr 2907, 1), (Sum.inr 2933, 1), (Sum.inr 2974, 1), (Sum.inr 2979, 1), (Sum.inr 2997, 1), (Sum.inr 3016, 1), (Sum.inr 3025, 1), (Sum.inr 3037, 1), (Sum.inr 3039, 1), (Sum.inr 3051, 1), (Sum.inr 3086, 1), (Sum.inr 3109, 1), (Sum.inr 3541, 1), (Sum.inr 3814, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1)]

def sourceForm332 : Integer.Sparse Master := [(Sum.inr 2001, 1), (Sum.inr 2004, 1), (Sum.inr 2005, 1), (Sum.inr 2055, 1), (Sum.inr 2207, 1), (Sum.inr 2833, 1), (Sum.inr 2835, 1), (Sum.inr 2838, 1), (Sum.inr 3038, 1), (Sum.inr 3238, 1), (Sum.inr 3240, 1), (Sum.inr 3243, 1), (Sum.inr 3296, 1), (Sum.inr 3464, 1), (Sum.inr 3479, 1), (Sum.inr 3480, 1), (Sum.inr 3517, 1), (Sum.inr 3518, 1), (Sum.inr 3526, 1), (Sum.inr 3528, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3540, 1), (Sum.inr 3561, 1), (Sum.inr 3573, 1), (Sum.inr 3577, 1), (Sum.inr 3814, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1)]

def sourceForm333 : Integer.Sparse Master := [(Sum.inr 2732, 2), (Sum.inr 3814, 2), (Sum.inr 3841, 1), (Sum.inr 3906, 1), (Sum.inr 4092, -1)]

def sourceForm335 : Integer.Sparse Master := [(Sum.inr 1278, 1), (Sum.inr 2578, 1), (Sum.inr 2649, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

def sourceForm336 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2497, 1), (Sum.inr 2499, 1), (Sum.inr 2515, 1), (Sum.inr 2732, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def sourceForm341 : Integer.Sparse Master := [(Sum.inr 990, 1), (Sum.inr 991, 1), (Sum.inr 992, 1), (Sum.inr 1006, 1), (Sum.inr 1058, 1), (Sum.inr 2392, 1), (Sum.inr 2393, 1), (Sum.inr 2394, 1), (Sum.inr 2405, 1), (Sum.inr 2454, 1), (Sum.inr 2455, 1), (Sum.inr 2463, 1), (Sum.inr 2494, 1), (Sum.inr 2617, 1), (Sum.inr 2618, 1), (Sum.inr 2620, 1), (Sum.inr 2638, 1), (Sum.inr 2728, 1), (Sum.inr 2729, 1), (Sum.inr 2732, 1), (Sum.inr 2734, 1), (Sum.inr 2735, 1), (Sum.inr 2744, 1), (Sum.inr 2773, 1), (Sum.inr 2776, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3889, 1), (Sum.inr 4003, 1)]

def sourceForm342 : Integer.Sparse Master := [(Sum.inr 1609, 1), (Sum.inr 1610, 1), (Sum.inr 1611, 1), (Sum.inr 1624, 1), (Sum.inr 1715, 1), (Sum.inr 2906, 1), (Sum.inr 2910, 1), (Sum.inr 2952, 1), (Sum.inr 3052, 1), (Sum.inr 3347, 1), (Sum.inr 3348, 1), (Sum.inr 3358, 1), (Sum.inr 3430, 1), (Sum.inr 3437, 1), (Sum.inr 3464, 1), (Sum.inr 3505, 1), (Sum.inr 3506, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3549, 1), (Sum.inr 3573, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3839, 1), (Sum.inr 3845, 1), (Sum.inr 3862, 1), (Sum.inr 3877, 1), (Sum.inr 3993, 1)]

def sourceForm343 : Integer.Sparse Master := [(Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def sourceForm344 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 1359, 1), (Sum.inr 1362, 1), (Sum.inr 1367, 1), (Sum.inr 1422, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

def sourceForm345 : Integer.Sparse Master := [(Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3051, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

def sourceForm346 : Integer.Sparse Master := [(Sum.inr 2579, 1), (Sum.inr 2582, 1), (Sum.inr 3007, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

def sourceForm347 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 2861, 1), (Sum.inr 3007, 1), (Sum.inr 3036, 1), (Sum.inr 3038, 2), (Sum.inr 4092, -1)]

def sourceForm348 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2580, 1), (Sum.inr 2971, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

def sourceForm349 : Integer.Sparse Master := [(Sum.inr 2558, 1), (Sum.inr 2861, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 3038, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

def sourceForm350 : Integer.Sparse Master := [(Sum.inr 1362, 1), (Sum.inr 2867, 1), (Sum.inr 2971, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3040, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm353 : Integer.Sparse Master := [(Sum.inr 2036, 1), (Sum.inr 2037, 1), (Sum.inr 2038, 1), (Sum.inr 2059, 1), (Sum.inr 2254, 1), (Sum.inr 2661, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2677, 1), (Sum.inr 2722, 1), (Sum.inr 3015, 1), (Sum.inr 3016, 1), (Sum.inr 3018, 1), (Sum.inr 3028, 1), (Sum.inr 3029, 1), (Sum.inr 3035, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3042, 1), (Sum.inr 3044, 1), (Sum.inr 3052, 1), (Sum.inr 3054, 1), (Sum.inr 3064, 1), (Sum.inr 3086, 1), (Sum.inr 3088, 1), (Sum.inr 3101, 1), (Sum.inr 3196, 1), (Sum.inr 3198, 1), (Sum.inr 3210, 1), (Sum.inr 3224, 1)]

def sourceForm354 : Integer.Sparse Master := [(Sum.inr 2560, 1), (Sum.inr 3375, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3533, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def sourceForm355 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2037, 1), (Sum.inr 2039, 1), (Sum.inr 2058, 1), (Sum.inr 2279, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def sourceForm356 : Integer.Sparse Master := [(Sum.inr 3151, 1), (Sum.inr 3379, 1), (Sum.inr 3382, 1), (Sum.inr 3383, 1), (Sum.inr 3395, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def sourceForm357 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2555, 1), (Sum.inr 3382, 1), (Sum.inr 3528, 1), (Sum.inr 3539, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def sourceForm361 : Integer.Sparse Master := [(Sum.inr 3279, 1), (Sum.inr 3280, 1), (Sum.inr 3282, 1), (Sum.inr 3290, 2), (Sum.inr 3434, 2), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3476, 1), (Sum.inr 3529, 2), (Sum.inr 3532, 2), (Sum.inr 3536, 2), (Sum.inr 3539, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 2), (Sum.inr 3568, 2), (Sum.inr 3571, 1), (Sum.inr 3580, 1), (Sum.inr 3805, 1), (Sum.inr 3848, 2), (Sum.inr 3851, 1), (Sum.inr 3858, 1)]

def sourceForm362 : Integer.Sparse Master := [(Sum.inr 2709, 1), (Sum.inr 3800, 1), (Sum.inr 3871, 2), (Sum.inr 3901, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

def sourceForm363 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1208, 1), (Sum.inr 1213, 2), (Sum.inr 1247, 1), (Sum.inr 2709, 1), (Sum.inr 4091, -1)]

def sourceForm364 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 2622, 2), (Sum.inr 2709, 1), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

def sourceForm365 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 2), (Sum.inr 2709, 1), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

def sourceForm366 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 2615, 1), (Sum.inr 2709, 1), (Sum.inr 2721, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

def sourceForm367 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2612, 1), (Sum.inr 2615, 1), (Sum.inr 2622, 1), (Sum.inr 2709, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

def sourceForm368 : Integer.Sparse Master := [(Sum.inr 1208, 1), (Sum.inr 2473, 1), (Sum.inr 2612, 2), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 4091, -1)]

def sourceForm369 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4803, 2), (Sum.inr 4831, 1), (Sum.inr 4888, 1), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5223, 2), (Sum.inr 5241, 1), (Sum.inr 5242, 1), (Sum.inr 5244, 1), (Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5253, 2), (Sum.inr 5254, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 4), (Sum.inr 5266, 2), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5293, 2)]

def sourceForm370 : Integer.Sparse Master := [(Sum.inr 2190, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 2), (Sum.inr 2244, 1), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2665, 2), (Sum.inr 2708, 1), (Sum.inr 2710, 1), (Sum.inr 2713, 2), (Sum.inr 2714, 2), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2731, 2), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2767, 2), (Sum.inr 3029, 1), (Sum.inr 3080, 1), (Sum.inr 3081, 1), (Sum.inr 3088, 2)]

def sourceForm371 : Integer.Sparse Master := [(Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 2698, 1), (Sum.inr 2723, 2), (Sum.inr 3016, 2), (Sum.inr 3017, 2), (Sum.inr 3019, 2), (Sum.inr 3039, 2), (Sum.inr 3064, 1), (Sum.inr 3066, 1), (Sum.inr 3068, 1), (Sum.inr 3069, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 3088, 2), (Sum.inr 3089, 2), (Sum.inr 3102, 2), (Sum.inr 3202, 2), (Sum.inr 3205, 1), (Sum.inr 3209, 1), (Sum.inr 3227, 1)]

def sourceForm372 : Integer.Sparse Master := [(Sum.inr 3493, 1), (Sum.inr 3494, 1), (Sum.inr 3497, 1), (Sum.inr 3531, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

def sourceForm373 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2021, 2), (Sum.inr 2051, 1), (Sum.inr 2262, 1), (Sum.inr 3531, 1), (Sum.inr 4084, -1)]

def sourceForm374 : Integer.Sparse Master := [(Sum.inr 2262, 1), (Sum.inr 3531, 1), (Sum.inr 3580, 1), (Sum.inr 3625, 1), (Sum.inr 3627, 2), (Sum.inr 4084, -1)]

def sourceForm375 : Integer.Sparse Master := [(Sum.inr 3375, 1), (Sum.inr 3377, 2), (Sum.inr 3388, 1), (Sum.inr 3497, 1), (Sum.inr 3531, 1), (Sum.inr 4084, -1)]

def sourceForm376 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 3388, 1), (Sum.inr 3531, 1), (Sum.inr 3539, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

def sourceForm377 : Integer.Sparse Master := [(Sum.inr 3494, 1), (Sum.inr 3502, 1), (Sum.inr 3504, 2), (Sum.inr 3531, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def sourceForm378 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 3375, 1), (Sum.inr 3502, 1), (Sum.inr 3531, 1), (Sum.inr 3533, 2), (Sum.inr 4084, -1)]

def sourceForm381 : Integer.Sparse Master := [(Sum.inr 1995, 1), (Sum.inr 1998, 2), (Sum.inr 2050, 1), (Sum.inr 2201, 1), (Sum.inr 3278, 1), (Sum.inr 3280, 1), (Sum.inr 3288, 2), (Sum.inr 3476, 1), (Sum.inr 3477, 2), (Sum.inr 3531, 1), (Sum.inr 3532, 2), (Sum.inr 3536, 2), (Sum.inr 3537, 2), (Sum.inr 3539, 2), (Sum.inr 3571, 1), (Sum.inr 3574, 2), (Sum.inr 3576, 1), (Sum.inr 3812, 1), (Sum.inr 3840, 2), (Sum.inr 3851, 1), (Sum.inr 3855, 1)]

def sourceForm382 : Integer.Sparse Master := [(Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 2), (Sum.inr 3899, 1), (Sum.inr 3901, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm384 : Integer.Sparse Master := [(Sum.inr 1248, 1), (Sum.inr 2623, 2), (Sum.inr 2710, 1), (Sum.inr 2745, 1), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

def sourceForm385 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 2473, 1), (Sum.inr 2483, 2), (Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

def sourceForm386 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 2617, 1), (Sum.inr 2710, 2), (Sum.inr 2721, 1), (Sum.inr 4091, -1)]

def sourceForm387 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2612, 1), (Sum.inr 2617, 1), (Sum.inr 2623, 1), (Sum.inr 2710, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def sourceForm388 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 2710, 3), (Sum.inr 2745, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

def sourceForm389 : Integer.Sparse Master := [(Sum.inr 4391, 1), (Sum.inr 4392, 1), (Sum.inr 4400, 2), (Sum.inr 4439, 1), (Sum.inr 4992, 1), (Sum.inr 4993, 1), (Sum.inr 4999, 2), (Sum.inr 5128, 2), (Sum.inr 5129, 2), (Sum.inr 5138, 2), (Sum.inr 5149, 2), (Sum.inr 5249, 1), (Sum.inr 5252, 1), (Sum.inr 5255, 2), (Sum.inr 5260, 2), (Sum.inr 5281, 1), (Sum.inr 5284, 1), (Sum.inr 5424, 2), (Sum.inr 5429, 1), (Sum.inr 5439, 1), (Sum.inr 5481, 1)]

def sourceForm390 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 973, 1), (Sum.inr 981, 2), (Sum.inr 1021, 1), (Sum.inr 2378, 1), (Sum.inr 2379, 1), (Sum.inr 2384, 2), (Sum.inr 2543, 2), (Sum.inr 2545, 2), (Sum.inr 2557, 2), (Sum.inr 2570, 2), (Sum.inr 2708, 1), (Sum.inr 2712, 1), (Sum.inr 2718, 2), (Sum.inr 2724, 2), (Sum.inr 2750, 1), (Sum.inr 2753, 1), (Sum.inr 3954, 1), (Sum.inr 3979, 1), (Sum.inr 3990, 2), (Sum.inr 4012, 1)]

def sourceForm391 : Integer.Sparse Master := [(Sum.inr 1606, 1), (Sum.inr 1607, 2), (Sum.inr 1613, 1), (Sum.inr 1713, 1), (Sum.inr 3345, 1), (Sum.inr 3346, 2), (Sum.inr 3350, 1), (Sum.inr 3502, 1), (Sum.inr 3503, 2), (Sum.inr 3516, 2), (Sum.inr 3517, 2), (Sum.inr 3519, 2), (Sum.inr 3540, 2), (Sum.inr 3543, 1), (Sum.inr 3571, 1), (Sum.inr 3605, 2), (Sum.inr 3625, 1), (Sum.inr 3843, 2), (Sum.inr 3858, 1), (Sum.inr 3874, 1), (Sum.inr 3991, 1)]

def sourceForm392 : Integer.Sparse Master := [(Sum.inr 3064, 1), (Sum.inr 3838, 2), (Sum.inr 3846, 1), (Sum.inr 3902, 1), (Sum.inr 4008, 1), (Sum.inr 4091, -1)]

def sourceForm393 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 1380, 1), (Sum.inr 1383, 1), (Sum.inr 1392, 2), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

def sourceForm394 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 2924, 2), (Sum.inr 3064, 1), (Sum.inr 3074, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

def sourceForm395 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 3012, 1), (Sum.inr 3013, 2), (Sum.inr 3064, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

def sourceForm396 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 3064, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

def sourceForm397 : Integer.Sparse Master := [(Sum.inr 1380, 1), (Sum.inr 2916, 2), (Sum.inr 3012, 1), (Sum.inr 3064, 1), (Sum.inr 3066, 1), (Sum.inr 4091, -1)]

def sourceForm400 : Integer.Sparse Master := [(Sum.inr 2693, 1), (Sum.inr 2694, 1), (Sum.inr 2697, 1), (Sum.inr 2722, 2), (Sum.inr 3015, 2), (Sum.inr 3016, 2), (Sum.inr 3018, 2), (Sum.inr 3038, 2), (Sum.inr 3063, 1), (Sum.inr 3065, 1), (Sum.inr 3067, 1), (Sum.inr 3068, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 2), (Sum.inr 3088, 2), (Sum.inr 3101, 2), (Sum.inr 3196, 2), (Sum.inr 3197, 1), (Sum.inr 3209, 1), (Sum.inr 3223, 1)]

def sourceForm401 : Integer.Sparse Master := [(Sum.inr 2552, 1), (Sum.inr 3488, 1), (Sum.inr 3493, 1), (Sum.inr 3533, 2), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

def sourceForm402 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2034, 2), (Sum.inr 2051, 1), (Sum.inr 2277, 1), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

def sourceForm403 : Integer.Sparse Master := [(Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 3539, 1), (Sum.inr 3625, 1), (Sum.inr 3632, 2), (Sum.inr 4084, -1)]

def sourceForm405 : Integer.Sparse Master := [(Sum.inr 4619, 3), (Sum.inr 4621, 1), (Sum.inr 4627, 1), (Sum.inr 4871, 3), (Sum.inr 4899, 1), (Sum.inr 5170, 6), (Sum.inr 5176, 3), (Sum.inr 5302, 3), (Sum.inr 5306, 3), (Sum.inr 5308, 1), (Sum.inr 5443, 3), (Sum.inr 5455, 1), (Sum.inr 5456, 1)]

def sourceForm406 : Integer.Sparse Master := [(Sum.inr 1294, 3), (Sum.inr 1297, 1), (Sum.inr 1311, 1), (Sum.inr 2112, 3), (Sum.inr 2281, 1), (Sum.inr 2954, 6), (Sum.inr 2968, 3), (Sum.inr 3054, 3), (Sum.inr 3120, 3), (Sum.inr 3124, 1), (Sum.inr 3889, 3), (Sum.inr 3916, 1), (Sum.inr 4019, 1)]

def sourceForm407 : Integer.Sparse Master := [(Sum.inr 4503, 3), (Sum.inr 4507, 1), (Sum.inr 4510, 1), (Sum.inr 5105, 6), (Sum.inr 5109, 3), (Sum.inr 5110, 3), (Sum.inr 5294, 3), (Sum.inr 5296, 1), (Sum.inr 5304, 3), (Sum.inr 5305, 1), (Sum.inr 5451, 3), (Sum.inr 5455, 1), (Sum.inr 5494, 1)]

def sourceForm408 : Integer.Sparse Master := [(Sum.inr 1087, 3), (Sum.inr 1091, 1), (Sum.inr 1094, 1), (Sum.inr 2515, 6), (Sum.inr 2519, 3), (Sum.inr 2522, 3), (Sum.inr 2768, 3), (Sum.inr 2770, 1), (Sum.inr 2782, 3), (Sum.inr 2783, 1), (Sum.inr 3987, 3), (Sum.inr 4019, 1), (Sum.inr 4020, 1)]

def sourceForm409 : Integer.Sparse Master := [(Sum.inr 4896, 3), (Sum.inr 4899, 1), (Sum.inr 4901, 1), (Sum.inr 5260, 6), (Sum.inr 5275, 3), (Sum.inr 5276, 3), (Sum.inr 5291, 3), (Sum.inr 5294, 3), (Sum.inr 5295, 3), (Sum.inr 5305, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 1), (Sum.inr 5311, 1)]

def sourceForm410 : Integer.Sparse Master := [(Sum.inr 2266, 3), (Sum.inr 2293, 1), (Sum.inr 2294, 1), (Sum.inr 2724, 6), (Sum.inr 2743, 3), (Sum.inr 2744, 3), (Sum.inr 2768, 3), (Sum.inr 2769, 3), (Sum.inr 2787, 1), (Sum.inr 2789, 1), (Sum.inr 3103, 3), (Sum.inr 3124, 1), (Sum.inr 3125, 1)]

def sourceForm411 : Integer.Sparse Master := [(Sum.inr 2765, 3), (Sum.inr 2777, 3), (Sum.inr 2778, 1), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 2789, 1), (Sum.inr 3086, 6), (Sum.inr 3098, 3), (Sum.inr 3101, 3), (Sum.inr 3110, 3), (Sum.inr 3123, 1), (Sum.inr 3225, 3), (Sum.inr 3231, 1)]

def sourceForm412 : Integer.Sparse Master := [(Sum.inr 2783, 1), (Sum.inr 3582, 3), (Sum.inr 3629, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def sourceForm413 : Integer.Sparse Master := [(Sum.inr 3629, 1), (Sum.inr 3632, 3), (Sum.inr 3633, 1), (Sum.inr 3635, 1), (Sum.inr 4084, -1)]

def sourceForm414 : Integer.Sparse Master := [(Sum.inr 2293, 1), (Sum.inr 3548, 3), (Sum.inr 3633, 1), (Sum.inr 3635, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm417 : Integer.Sparse Master := [(Sum.inr 1088, 3), (Sum.inr 1092, 1), (Sum.inr 1093, 1), (Sum.inr 2516, 6), (Sum.inr 2520, 3), (Sum.inr 2521, 3), (Sum.inr 2761, 3), (Sum.inr 2777, 3), (Sum.inr 2778, 1), (Sum.inr 2780, 1), (Sum.inr 2783, 1), (Sum.inr 3098, 3), (Sum.inr 3121, 1)]

def sourceForm418 : Integer.Sparse Master := [(Sum.inr 1303, 3), (Sum.inr 1309, 1), (Sum.inr 1310, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def sourceForm419 : Integer.Sparse Master := [(Sum.inr 1303, 1), (Sum.inr 2134, 1), (Sum.inr 2597, 2), (Sum.inr 2781, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def sourceForm420 : Integer.Sparse Master := [(Sum.inr 1310, 1), (Sum.inr 2603, 3), (Sum.inr 2783, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def sourceForm421 : Integer.Sparse Master := [(Sum.inr 4606, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4624, 1), (Sum.inr 5078, 2), (Sum.inr 5109, 1), (Sum.inr 5148, 2), (Sum.inr 5152, 2), (Sum.inr 5169, 2), (Sum.inr 5203, 2), (Sum.inr 5207, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 2), (Sum.inr 5294, 1), (Sum.inr 5296, 1), (Sum.inr 5307, 1), (Sum.inr 5309, 1), (Sum.inr 5434, 2), (Sum.inr 5451, 1), (Sum.inr 5454, 1), (Sum.inr 5455, 1)]

def sourceForm422 : Integer.Sparse Master := [(Sum.inr 1240, 2), (Sum.inr 1242, 1), (Sum.inr 1246, 1), (Sum.inr 1301, 1), (Sum.inr 2485, 2), (Sum.inr 2519, 1), (Sum.inr 2770, 1), (Sum.inr 2884, 2), (Sum.inr 2889, 1), (Sum.inr 2927, 2), (Sum.inr 2931, 2), (Sum.inr 2960, 2), (Sum.inr 3100, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 2), (Sum.inr 3122, 1), (Sum.inr 3123, 1), (Sum.inr 3982, 2), (Sum.inr 3987, 1), (Sum.inr 4019, 1), (Sum.inr 4040, 1)]

def sourceForm423 : Integer.Sparse Master := [(Sum.inr 4458, 2), (Sum.inr 4460, 1), (Sum.inr 4467, 1), (Sum.inr 4499, 1), (Sum.inr 5073, 2), (Sum.inr 5075, 2), (Sum.inr 5081, 2), (Sum.inr 5102, 2), (Sum.inr 5169, 2), (Sum.inr 5171, 1), (Sum.inr 5177, 1), (Sum.inr 5259, 2), (Sum.inr 5261, 1), (Sum.inr 5275, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 1), (Sum.inr 5306, 1), (Sum.inr 5483, 2), (Sum.inr 5487, 1), (Sum.inr 5491, 1), (Sum.inr 5493, 1)]

def sourceForm424 : Integer.Sparse Master := [(Sum.inr 1041, 2), (Sum.inr 1043, 1), (Sum.inr 1050, 1), (Sum.inr 1083, 1), (Sum.inr 2480, 2), (Sum.inr 2482, 2), (Sum.inr 2489, 2), (Sum.inr 2512, 2), (Sum.inr 2595, 2), (Sum.inr 2598, 1), (Sum.inr 2605, 1), (Sum.inr 2723, 2), (Sum.inr 2726, 1), (Sum.inr 2743, 1), (Sum.inr 2766, 2), (Sum.inr 2767, 1), (Sum.inr 2784, 1), (Sum.inr 3981, 2), (Sum.inr 4000, 1), (Sum.inr 4014, 1), (Sum.inr 4018, 1)]

def sourceForm425 : Integer.Sparse Master := [(Sum.inr 4888, 2), (Sum.inr 4894, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 5250, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 4), (Sum.inr 5266, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5282, 2), (Sum.inr 5284, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 2), (Sum.inr 5294, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 2)]

def sourceForm426 : Integer.Sparse Master := [(Sum.inr 2244, 2), (Sum.inr 2264, 1), (Sum.inr 2265, 1), (Sum.inr 2278, 1), (Sum.inr 2709, 2), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2731, 2), (Sum.inr 2751, 2), (Sum.inr 2753, 2), (Sum.inr 2765, 1), (Sum.inr 2767, 2), (Sum.inr 2768, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 2786, 1), (Sum.inr 2787, 1), (Sum.inr 3088, 2), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3123, 1)]

def sourceForm427 : Integer.Sparse Master := [(Sum.inr 2723, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 2787, 1), (Sum.inr 3039, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3065, 2), (Sum.inr 3077, 2), (Sum.inr 3078, 2), (Sum.inr 3088, 2), (Sum.inr 3089, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 2), (Sum.inr 3103, 1), (Sum.inr 3123, 1), (Sum.inr 3124, 1), (Sum.inr 3225, 1), (Sum.inr 3227, 2), (Sum.inr 3229, 1), (Sum.inr 3230, 1)]

def sourceForm428 : Integer.Sparse Master := [(Sum.inr 3544, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3627, 1), (Sum.inr 3635, 1), (Sum.inr 4084, -1)]

def sourceForm429 : Integer.Sparse Master := [(Sum.inr 2262, 2), (Sum.inr 2264, 1), (Sum.inr 2266, 1), (Sum.inr 2291, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def sourceForm430 : Integer.Sparse Master := [(Sum.inr 3627, 3), (Sum.inr 3629, 1), (Sum.inr 3635, 2), (Sum.inr 4084, -1)]

def sourceForm431 : Integer.Sparse Master := [(Sum.inr 3548, 1), (Sum.inr 3580, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def sourceForm432 : Integer.Sparse Master := [(Sum.inr 2264, 1), (Sum.inr 3533, 2), (Sum.inr 3582, 1), (Sum.inr 3627, 1), (Sum.inr 3629, 1), (Sum.inr 4084, -1)]

def sourceForm433 : Integer.Sparse Master := [(Sum.inr 4602, 2), (Sum.inr 4605, 1), (Sum.inr 4612, 1), (Sum.inr 4623, 1), (Sum.inr 4807, 2), (Sum.inr 4843, 1), (Sum.inr 4890, 1), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5172, 2), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5307, 1), (Sum.inr 5435, 2), (Sum.inr 5443, 1), (Sum.inr 5453, 1), (Sum.inr 5454, 1)]

def sourceForm434 : Integer.Sparse Master := [(Sum.inr 1236, 2), (Sum.inr 1239, 1), (Sum.inr 1246, 1), (Sum.inr 1300, 1), (Sum.inr 2025, 2), (Sum.inr 2062, 1), (Sum.inr 2247, 1), (Sum.inr 2881, 2), (Sum.inr 2889, 1), (Sum.inr 2924, 2), (Sum.inr 2931, 2), (Sum.inr 2959, 2), (Sum.inr 3077, 2), (Sum.inr 3100, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3122, 1), (Sum.inr 3853, 2), (Sum.inr 3862, 1), (Sum.inr 3912, 1), (Sum.inr 4040, 1)]

def sourceForm435 : Integer.Sparse Master := [(Sum.inr 4461, 2), (Sum.inr 4463, 1), (Sum.inr 4466, 1), (Sum.inr 4503, 1), (Sum.inr 5076, 2), (Sum.inr 5078, 2), (Sum.inr 5080, 2), (Sum.inr 5105, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 1), (Sum.inr 5176, 1), (Sum.inr 5290, 2), (Sum.inr 5291, 1), (Sum.inr 5294, 2), (Sum.inr 5296, 1), (Sum.inr 5304, 1), (Sum.inr 5310, 1), (Sum.inr 5434, 2), (Sum.inr 5442, 1), (Sum.inr 5455, 1), (Sum.inr 5492, 1)]

def sourceForm436 : Integer.Sparse Master := [(Sum.inr 1044, 2), (Sum.inr 1046, 1), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 2483, 2), (Sum.inr 2485, 2), (Sum.inr 2488, 2), (Sum.inr 2515, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 1), (Sum.inr 2604, 1), (Sum.inr 2764, 2), (Sum.inr 2765, 1), (Sum.inr 2768, 2), (Sum.inr 2770, 1), (Sum.inr 2782, 1), (Sum.inr 2788, 1), (Sum.inr 3982, 2), (Sum.inr 4001, 1), (Sum.inr 4017, 1), (Sum.inr 4019, 1)]

def sourceForm437 : Integer.Sparse Master := [(Sum.inr 4889, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5251, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 2), (Sum.inr 5267, 2), (Sum.inr 5270, 2), (Sum.inr 5272, 1), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5284, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 2), (Sum.inr 5295, 1), (Sum.inr 5302, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 1), (Sum.inr 5310, 1)]

def sourceForm438 : Integer.Sparse Master := [(Sum.inr 2245, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2279, 1), (Sum.inr 2710, 2), (Sum.inr 2723, 2), (Sum.inr 2724, 2), (Sum.inr 2732, 2), (Sum.inr 2753, 2), (Sum.inr 2754, 2), (Sum.inr 2767, 1), (Sum.inr 2768, 2), (Sum.inr 2769, 1), (Sum.inr 2776, 1), (Sum.inr 2777, 1), (Sum.inr 2787, 1), (Sum.inr 2788, 1), (Sum.inr 3089, 2), (Sum.inr 3112, 1), (Sum.inr 3113, 1), (Sum.inr 3124, 1)]

def sourceForm440 : Integer.Sparse Master := [(Sum.inr 1229, 2), (Sum.inr 1231, 1), (Sum.inr 1245, 1), (Sum.inr 1292, 1), (Sum.inr 1639, 2), (Sum.inr 1651, 1), (Sum.inr 1716, 1), (Sum.inr 2875, 2), (Sum.inr 2888, 1), (Sum.inr 2921, 2), (Sum.inr 2930, 2), (Sum.inr 2952, 2), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3097, 2), (Sum.inr 3103, 1), (Sum.inr 3119, 1), (Sum.inr 3573, 2), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3987, 1)]

def sourceForm441 : Integer.Sparse Master := [(Sum.inr 1070, 2), (Sum.inr 1072, 1), (Sum.inr 1076, 1), (Sum.inr 1084, 1), (Sum.inr 2500, 2), (Sum.inr 2502, 2), (Sum.inr 2506, 2), (Sum.inr 2513, 2), (Sum.inr 2681, 2), (Sum.inr 2683, 1), (Sum.inr 2687, 1), (Sum.inr 2735, 2), (Sum.inr 2737, 1), (Sum.inr 2744, 1), (Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 3572, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3888, 1)]

def sourceForm442 : Integer.Sparse Master := [(Sum.inr 2769, 1), (Sum.inr 3051, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def sourceForm443 : Integer.Sparse Master := [(Sum.inr 1268, 2), (Sum.inr 1272, 1), (Sum.inr 1273, 1), (Sum.inr 1306, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def sourceForm444 : Integer.Sparse Master := [(Sum.inr 1268, 1), (Sum.inr 2571, 1), (Sum.inr 2639, 1), (Sum.inr 2759, 1), (Sum.inr 2763, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def sourceForm445 : Integer.Sparse Master := [(Sum.inr 1433, 1), (Sum.inr 2571, 1), (Sum.inr 2575, 1), (Sum.inr 2600, 1), (Sum.inr 2769, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

def sourceForm446 : Integer.Sparse Master := [(Sum.inr 1437, 1), (Sum.inr 2639, 2), (Sum.inr 2643, 1), (Sum.inr 2769, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def sourceForm447 : Integer.Sparse Master := [(Sum.inr 1273, 1), (Sum.inr 2575, 2), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm448 : Integer.Sparse Master := [(Sum.inr 1272, 1), (Sum.inr 1433, 2), (Sum.inr 1436, 1), (Sum.inr 1437, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def sourceForm451 : Integer.Sparse Master := [(Sum.inr 1656, 2), (Sum.inr 1657, 1), (Sum.inr 1661, 1), (Sum.inr 1745, 1), (Sum.inr 2259, 2), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2584, 2), (Sum.inr 2603, 1), (Sum.inr 2717, 2), (Sum.inr 2735, 2), (Sum.inr 2738, 2), (Sum.inr 2761, 1), (Sum.inr 2762, 2), (Sum.inr 2763, 2), (Sum.inr 2781, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 3096, 2), (Sum.inr 3118, 1), (Sum.inr 3119, 1)]

def sourceForm452 : Integer.Sparse Master := [(Sum.inr 3098, 1), (Sum.inr 3572, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def sourceForm453 : Integer.Sparse Master := [(Sum.inr 1404, 2), (Sum.inr 1408, 1), (Sum.inr 1418, 1), (Sum.inr 1440, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def sourceForm454 : Integer.Sparse Master := [(Sum.inr 1404, 1), (Sum.inr 2952, 1), (Sum.inr 2983, 1), (Sum.inr 3075, 1), (Sum.inr 3096, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def sourceForm455 : Integer.Sparse Master := [(Sum.inr 2090, 1), (Sum.inr 2962, 1), (Sum.inr 2983, 1), (Sum.inr 2995, 1), (Sum.inr 3098, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def sourceForm456 : Integer.Sparse Master := [(Sum.inr 1440, 1), (Sum.inr 2995, 2), (Sum.inr 3098, 2), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

def sourceForm457 : Integer.Sparse Master := [(Sum.inr 2112, 1), (Sum.inr 2952, 2), (Sum.inr 2967, 1), (Sum.inr 3098, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def sourceForm458 : Integer.Sparse Master := [(Sum.inr 1418, 1), (Sum.inr 2962, 2), (Sum.inr 2967, 2), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def sourceForm461 : Integer.Sparse Master := [(Sum.inr 2516, 2), (Sum.inr 2520, 1), (Sum.inr 2521, 1), (Sum.inr 2719, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 1), (Sum.inr 2783, 1), (Sum.inr 2789, 1), (Sum.inr 3035, 2), (Sum.inr 3049, 1), (Sum.inr 3052, 1), (Sum.inr 3063, 2), (Sum.inr 3072, 2), (Sum.inr 3075, 2), (Sum.inr 3086, 2), (Sum.inr 3098, 2), (Sum.inr 3101, 1), (Sum.inr 3121, 1), (Sum.inr 3158, 2), (Sum.inr 3161, 1), (Sum.inr 3225, 1)]

def sourceForm462 : Integer.Sparse Master := [(Sum.inr 1292, 1), (Sum.inr 2588, 2), (Sum.inr 2740, 1), (Sum.inr 2781, 1), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

def sourceForm463 : Integer.Sparse Master := [(Sum.inr 2132, 2), (Sum.inr 2134, 1), (Sum.inr 2138, 1), (Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

def sourceForm466 : Integer.Sparse Master := [(Sum.inr 1189, 2), (Sum.inr 1191, 1), (Sum.inr 1192, 1), (Sum.inr 1295, 1), (Sum.inr 2393, 2), (Sum.inr 2408, 1), (Sum.inr 2734, 1), (Sum.inr 2841, 2), (Sum.inr 2842, 1), (Sum.inr 2909, 2), (Sum.inr 2910, 2), (Sum.inr 2955, 2), (Sum.inr 3039, 2), (Sum.inr 3051, 2), (Sum.inr 3052, 1), (Sum.inr 3110, 1), (Sum.inr 3119, 1), (Sum.inr 3584, 1), (Sum.inr 3862, 1), (Sum.inr 3877, 2), (Sum.inr 3889, 1)]

def sourceForm467 : Integer.Sparse Master := [(Sum.inr 2405, 2), (Sum.inr 2408, 1), (Sum.inr 2409, 1), (Sum.inr 2744, 1), (Sum.inr 2841, 2), (Sum.inr 2842, 1), (Sum.inr 3055, 1), (Sum.inr 3246, 2), (Sum.inr 3247, 1), (Sum.inr 3306, 1), (Sum.inr 3358, 2), (Sum.inr 3535, 2), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3559, 2), (Sum.inr 3565, 2), (Sum.inr 3573, 2), (Sum.inr 3583, 1), (Sum.inr 3862, 1), (Sum.inr 3877, 2), (Sum.inr 3889, 1)]

def sourceForm468 : Integer.Sparse Master := [(Sum.inr 2774, 2), (Sum.inr 3854, 2), (Sum.inr 3907, 2), (Sum.inr 4092, -1)]

def sourceForm471 : Integer.Sparse Master := [(Sum.inr 1295, 1), (Sum.inr 2591, 2), (Sum.inr 2743, 1), (Sum.inr 2774, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

def sourceForm473 : Integer.Sparse Master := [(Sum.inr 1054, 2), (Sum.inr 1055, 1), (Sum.inr 1063, 1), (Sum.inr 1076, 1), (Sum.inr 2491, 2), (Sum.inr 2492, 2), (Sum.inr 2499, 2), (Sum.inr 2506, 2), (Sum.inr 2633, 2), (Sum.inr 2635, 1), (Sum.inr 2644, 1), (Sum.inr 2678, 2), (Sum.inr 2680, 1), (Sum.inr 2687, 1), (Sum.inr 2773, 2), (Sum.inr 2776, 1), (Sum.inr 2781, 1), (Sum.inr 3881, 2), (Sum.inr 3886, 1), (Sum.inr 3888, 1), (Sum.inr 4004, 1)]

def sourceForm474 : Integer.Sparse Master := [(Sum.inr 1649, 2), (Sum.inr 1651, 1), (Sum.inr 1652, 1), (Sum.inr 1740, 1), (Sum.inr 2875, 2), (Sum.inr 2888, 1), (Sum.inr 3098, 1), (Sum.inr 3385, 2), (Sum.inr 3395, 2), (Sum.inr 3396, 1), (Sum.inr 3447, 2), (Sum.inr 3480, 2), (Sum.inr 3573, 2), (Sum.inr 3578, 2), (Sum.inr 3579, 1), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3959, 2), (Sum.inr 3963, 1), (Sum.inr 3987, 1), (Sum.inr 4030, 1)]

def sourceForm475 : Integer.Sparse Master := [(Sum.inr 3055, 1), (Sum.inr 3884, 2), (Sum.inr 3886, 1), (Sum.inr 3913, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

def sourceForm476 : Integer.Sparse Master := [(Sum.inr 1368, 2), (Sum.inr 1373, 1), (Sum.inr 1375, 1), (Sum.inr 1437, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def sourceForm477 : Integer.Sparse Master := [(Sum.inr 1368, 1), (Sum.inr 2882, 1), (Sum.inr 2975, 1), (Sum.inr 3044, 1), (Sum.inr 3051, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def sourceForm478 : Integer.Sparse Master := [(Sum.inr 2639, 1), (Sum.inr 2871, 1), (Sum.inr 2975, 1), (Sum.inr 2979, 1), (Sum.inr 3055, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def sourceForm479 : Integer.Sparse Master := [(Sum.inr 2882, 2), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 3055, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm480 : Integer.Sparse Master := [(Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def sourceForm481 : Integer.Sparse Master := [(Sum.inr 2643, 1), (Sum.inr 3044, 2), (Sum.inr 3046, 1), (Sum.inr 3055, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

def sourceForm483 : Integer.Sparse Master := [(Sum.inr 2129, 2), (Sum.inr 2130, 1), (Sum.inr 2138, 1), (Sum.inr 2251, 2), (Sum.inr 2276, 1), (Sum.inr 2278, 1), (Sum.inr 2282, 1), (Sum.inr 2629, 2), (Sum.inr 2643, 1), (Sum.inr 2713, 2), (Sum.inr 2729, 2), (Sum.inr 2731, 2), (Sum.inr 2751, 2), (Sum.inr 2758, 2), (Sum.inr 2765, 1), (Sum.inr 2767, 1), (Sum.inr 2771, 1), (Sum.inr 2776, 1), (Sum.inr 3092, 2), (Sum.inr 3110, 1), (Sum.inr 3117, 1)]

def sourceForm485 : Integer.Sparse Master := [(Sum.inr 2888, 1), (Sum.inr 3392, 2), (Sum.inr 3397, 1), (Sum.inr 3548, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm486 : Integer.Sparse Master := [(Sum.inr 2108, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 2266, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm487 : Integer.Sparse Master := [(Sum.inr 2108, 1), (Sum.inr 2883, 1), (Sum.inr 3504, 1), (Sum.inr 3577, 1), (Sum.inr 3580, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm488 : Integer.Sparse Master := [(Sum.inr 2113, 1), (Sum.inr 2887, 1), (Sum.inr 3157, 2), (Sum.inr 3161, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm489 : Integer.Sparse Master := [(Sum.inr 2883, 2), (Sum.inr 2887, 1), (Sum.inr 2888, 1), (Sum.inr 3056, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm490 : Integer.Sparse Master := [(Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 3506, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def sourceForm493 : Integer.Sparse Master := [(Sum.inr 4475, 2), (Sum.inr 4476, 1), (Sum.inr 4480, 1), (Sum.inr 4500, 1), (Sum.inr 5086, 2), (Sum.inr 5087, 2), (Sum.inr 5090, 2), (Sum.inr 5103, 2), (Sum.inr 5109, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5267, 2), (Sum.inr 5268, 1), (Sum.inr 5276, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5411, 2), (Sum.inr 5413, 1), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

def sourceForm494 : Integer.Sparse Master := [(Sum.inr 1058, 2), (Sum.inr 1059, 1), (Sum.inr 1063, 1), (Sum.inr 1084, 1), (Sum.inr 2494, 2), (Sum.inr 2495, 2), (Sum.inr 2499, 2), (Sum.inr 2513, 2), (Sum.inr 2638, 2), (Sum.inr 2640, 1), (Sum.inr 2644, 1), (Sum.inr 2732, 2), (Sum.inr 2734, 1), (Sum.inr 2744, 1), (Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2781, 1), (Sum.inr 3883, 2), (Sum.inr 3888, 1), (Sum.inr 3889, 1), (Sum.inr 4006, 1)]

def sourceForm495 : Integer.Sparse Master := [(Sum.inr 1715, 2), (Sum.inr 1716, 1), (Sum.inr 1729, 1), (Sum.inr 1740, 1), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3098, 1), (Sum.inr 3464, 2), (Sum.inr 3472, 2), (Sum.inr 3480, 2), (Sum.inr 3486, 1), (Sum.inr 3541, 2), (Sum.inr 3549, 1), (Sum.inr 3573, 2), (Sum.inr 3584, 1), (Sum.inr 3624, 2), (Sum.inr 3631, 1), (Sum.inr 3809, 2), (Sum.inr 3817, 1), (Sum.inr 3862, 1), (Sum.inr 3987, 1)]

def sourceForm496 : Integer.Sparse Master := [(Sum.inr 3054, 1), (Sum.inr 3813, 2), (Sum.inr 3817, 1), (Sum.inr 3907, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def sourceForm497 : Integer.Sparse Master := [(Sum.inr 1367, 2), (Sum.inr 1372, 1), (Sum.inr 1375, 1), (Sum.inr 1436, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

def sourceForm498 : Integer.Sparse Master := [(Sum.inr 2495, 1), (Sum.inr 2759, 1), (Sum.inr 2974, 1), (Sum.inr 2979, 1), (Sum.inr 3054, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

def sourceForm499 : Integer.Sparse Master := [(Sum.inr 4880, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5103, 2), (Sum.inr 5110, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5254, 2), (Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5284, 2), (Sum.inr 5287, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5300, 1)]

def sourceForm500 : Integer.Sparse Master := [(Sum.inr 2254, 2), (Sum.inr 2255, 1), (Sum.inr 2267, 1), (Sum.inr 2280, 1), (Sum.inr 2672, 2), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2742, 1), (Sum.inr 3016, 2), (Sum.inr 3024, 2), (Sum.inr 3025, 2), (Sum.inr 3038, 2), (Sum.inr 3039, 2), (Sum.inr 3052, 1), (Sum.inr 3055, 1), (Sum.inr 3077, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3222, 2), (Sum.inr 3224, 1), (Sum.inr 3225, 1)]

def sourceForm503 : Integer.Sparse Master := [(Sum.inr 2396, 1), (Sum.inr 2397, 1), (Sum.inr 2401, 2), (Sum.inr 2738, 1), (Sum.inr 3282, 1), (Sum.inr 3283, 1), (Sum.inr 3294, 2), (Sum.inr 3350, 1), (Sum.inr 3355, 2), (Sum.inr 3531, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 2), (Sum.inr 3562, 2), (Sum.inr 3568, 2), (Sum.inr 3571, 1), (Sum.inr 3578, 2), (Sum.inr 3581, 2), (Sum.inr 3858, 1), (Sum.inr 3874, 1), (Sum.inr 3884, 2), (Sum.inr 3887, 1)]

def sourceForm504 : Integer.Sparse Master := [(Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 3881, 2), (Sum.inr 3902, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

def sourceForm505 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1249, 1), (Sum.inr 1253, 1), (Sum.inr 1262, 2), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

def sourceForm506 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 2564, 1), (Sum.inr 2567, 2), (Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

def sourceForm507 : Integer.Sparse Master := [(Sum.inr 1262, 1), (Sum.inr 2567, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 2751, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def sourceForm508 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2624, 1), (Sum.inr 2627, 1), (Sum.inr 2633, 1), (Sum.inr 2751, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

def sourceForm509 : Integer.Sparse Master := [(Sum.inr 1253, 1), (Sum.inr 2564, 1), (Sum.inr 2627, 2), (Sum.inr 2751, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

def sourceForm510 : Integer.Sparse Master := [(Sum.inr 4436, 1), (Sum.inr 4437, 1), (Sum.inr 4444, 1), (Sum.inr 4453, 2), (Sum.inr 5064, 1), (Sum.inr 5067, 1), (Sum.inr 5071, 2), (Sum.inr 5145, 2), (Sum.inr 5147, 2), (Sum.inr 5152, 2), (Sum.inr 5164, 2), (Sum.inr 5220, 1), (Sum.inr 5222, 1), (Sum.inr 5229, 2), (Sum.inr 5281, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 2), (Sum.inr 5448, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 2), (Sum.inr 5485, 1)]

def sourceForm511 : Integer.Sparse Master := [(Sum.inr 1018, 1), (Sum.inr 1019, 1), (Sum.inr 1026, 1), (Sum.inr 1036, 2), (Sum.inr 2469, 1), (Sum.inr 2473, 1), (Sum.inr 2478, 2), (Sum.inr 2567, 2), (Sum.inr 2569, 2), (Sum.inr 2576, 2), (Sum.inr 2591, 2), (Sum.inr 2662, 1), (Sum.inr 2664, 1), (Sum.inr 2673, 2), (Sum.inr 2750, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 2), (Sum.inr 3885, 1), (Sum.inr 3976, 1), (Sum.inr 3995, 2), (Sum.inr 3998, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm512 : Integer.Sparse Master := [(Sum.inr 1642, 1), (Sum.inr 1643, 1), (Sum.inr 1646, 2), (Sum.inr 1736, 1), (Sum.inr 3388, 1), (Sum.inr 3389, 1), (Sum.inr 3392, 2), (Sum.inr 3443, 1), (Sum.inr 3445, 2), (Sum.inr 3476, 1), (Sum.inr 3530, 2), (Sum.inr 3562, 2), (Sum.inr 3565, 2), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 3612, 2), (Sum.inr 3625, 1), (Sum.inr 3956, 1), (Sum.inr 3961, 2), (Sum.inr 3984, 1), (Sum.inr 4028, 1)]

def sourceForm513 : Integer.Sparse Master := [(Sum.inr 3078, 1), (Sum.inr 3885, 1), (Sum.inr 3953, 1), (Sum.inr 3958, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def sourceForm514 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 1389, 1), (Sum.inr 1391, 1), (Sum.inr 1407, 2), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def sourceForm515 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 2925, 2), (Sum.inr 3068, 1), (Sum.inr 3074, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def sourceForm516 : Integer.Sparse Master := [(Sum.inr 2857, 1), (Sum.inr 2981, 1), (Sum.inr 2985, 2), (Sum.inr 3078, 1), (Sum.inr 3953, 1), (Sum.inr 4091, -1)]

def sourceForm517 : Integer.Sparse Master := [(Sum.inr 1407, 1), (Sum.inr 2955, 1), (Sum.inr 2985, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

def sourceForm518 : Integer.Sparse Master := [(Sum.inr 2865, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 2955, 1), (Sum.inr 3078, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

def sourceForm519 : Integer.Sparse Master := [(Sum.inr 1391, 1), (Sum.inr 2931, 2), (Sum.inr 2981, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def sourceForm520 : Integer.Sparse Master := [(Sum.inr 3031, 1), (Sum.inr 3068, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def sourceForm521 : Integer.Sparse Master := [(Sum.inr 1389, 1), (Sum.inr 2857, 1), (Sum.inr 2865, 2), (Sum.inr 3031, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def sourceForm523 : Integer.Sparse Master := [(Sum.inr 2232, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2251, 2), (Sum.inr 2628, 1), (Sum.inr 2629, 2), (Sum.inr 2641, 1), (Sum.inr 2708, 1), (Sum.inr 2709, 1), (Sum.inr 2713, 2), (Sum.inr 2745, 1), (Sum.inr 2748, 1), (Sum.inr 2751, 2), (Sum.inr 2753, 1), (Sum.inr 2758, 2), (Sum.inr 2765, 2), (Sum.inr 2767, 2), (Sum.inr 2774, 2), (Sum.inr 3080, 1), (Sum.inr 3106, 1), (Sum.inr 3110, 2)]

def sourceForm525 : Integer.Sparse Master := [(Sum.inr 2879, 1), (Sum.inr 3494, 1), (Sum.inr 3498, 1), (Sum.inr 3548, 2), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def sourceForm526 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 2), (Sum.inr 2262, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def sourceForm527 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2877, 1), (Sum.inr 3576, 1), (Sum.inr 3580, 3), (Sum.inr 4084, -1)]

def sourceForm528 : Integer.Sparse Master := [(Sum.inr 2877, 1), (Sum.inr 2879, 1), (Sum.inr 2883, 2), (Sum.inr 3050, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def sourceForm529 : Integer.Sparse Master := [(Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 3502, 1), (Sum.inr 3580, 1), (Sum.inr 3582, 2), (Sum.inr 4084, -1)]

def sourceForm530 : Integer.Sparse Master := [(Sum.inr 4581, 1), (Sum.inr 4583, 1), (Sum.inr 4586, 1), (Sum.inr 4602, 2), (Sum.inr 4729, 1), (Sum.inr 4742, 2), (Sum.inr 4890, 1), (Sum.inr 5142, 1), (Sum.inr 5149, 2), (Sum.inr 5192, 2), (Sum.inr 5193, 2), (Sum.inr 5204, 2), (Sum.inr 5283, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 2), (Sum.inr 5294, 2), (Sum.inr 5406, 1), (Sum.inr 5411, 2), (Sum.inr 5452, 1), (Sum.inr 5453, 1)]

def sourceForm531 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 1202, 1), (Sum.inr 1205, 1), (Sum.inr 1236, 2), (Sum.inr 1898, 1), (Sum.inr 1915, 2), (Sum.inr 2247, 1), (Sum.inr 2853, 2), (Sum.inr 2856, 2), (Sum.inr 2881, 2), (Sum.inr 2913, 1), (Sum.inr 2924, 2), (Sum.inr 3076, 1), (Sum.inr 3077, 2), (Sum.inr 3100, 2), (Sum.inr 3101, 2), (Sum.inr 3801, 1), (Sum.inr 3809, 2), (Sum.inr 3912, 1), (Sum.inr 4039, 1)]

def sourceForm532 : Integer.Sparse Master := [(Sum.inr 4439, 1), (Sum.inr 4440, 1), (Sum.inr 4444, 1), (Sum.inr 4459, 2), (Sum.inr 5065, 1), (Sum.inr 5067, 1), (Sum.inr 5074, 2), (Sum.inr 5078, 2), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5170, 2), (Sum.inr 5251, 1), (Sum.inr 5252, 1), (Sum.inr 5260, 2), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5289, 2), (Sum.inr 5405, 1), (Sum.inr 5410, 2), (Sum.inr 5439, 1), (Sum.inr 5485, 1)]

def sourceForm533 : Integer.Sparse Master := [(Sum.inr 1021, 1), (Sum.inr 1022, 1), (Sum.inr 1026, 1), (Sum.inr 1042, 2), (Sum.inr 2470, 1), (Sum.inr 2473, 1), (Sum.inr 2481, 2), (Sum.inr 2570, 2), (Sum.inr 2572, 2), (Sum.inr 2576, 2), (Sum.inr 2596, 2), (Sum.inr 2710, 1), (Sum.inr 2712, 1), (Sum.inr 2724, 2), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 2763, 2), (Sum.inr 3977, 1), (Sum.inr 3996, 2), (Sum.inr 3998, 1), (Sum.inr 4012, 1)]

def sourceForm534 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1714, 2), (Sum.inr 1723, 1), (Sum.inr 1736, 1), (Sum.inr 3463, 2), (Sum.inr 3466, 1), (Sum.inr 3476, 1), (Sum.inr 3481, 2), (Sum.inr 3539, 1), (Sum.inr 3540, 2), (Sum.inr 3543, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 3580, 1), (Sum.inr 3605, 2), (Sum.inr 3606, 2), (Sum.inr 3612, 2), (Sum.inr 3805, 1), (Sum.inr 3816, 2), (Sum.inr 3858, 1), (Sum.inr 3984, 1)]

def sourceForm535 : Integer.Sparse Master := [(Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 3808, 2), (Sum.inr 3902, 1), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def sourceForm536 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1406, 2), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

def sourceForm537 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2981, 1), (Sum.inr 2984, 2), (Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

def sourceForm538 : Integer.Sparse Master := [(Sum.inr 4885, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4891, 2), (Sum.inr 5097, 1), (Sum.inr 5099, 1), (Sum.inr 5103, 2), (Sum.inr 5241, 1), (Sum.inr 5248, 1), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5254, 2), (Sum.inr 5270, 1), (Sum.inr 5274, 2), (Sum.inr 5277, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 2), (Sum.inr 5287, 2), (Sum.inr 5293, 2), (Sum.inr 5294, 2), (Sum.inr 5302, 2)]

def sourceForm539 : Integer.Sparse Master := [(Sum.inr 2233, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2253, 2), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 2714, 2), (Sum.inr 2745, 1), (Sum.inr 2746, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 2), (Sum.inr 2754, 1), (Sum.inr 2758, 2), (Sum.inr 2759, 2), (Sum.inr 2767, 2), (Sum.inr 2768, 2), (Sum.inr 2776, 2), (Sum.inr 3003, 1), (Sum.inr 3081, 1), (Sum.inr 3106, 1), (Sum.inr 3112, 2)]

def sourceForm540 : Integer.Sparse Master := [(Sum.inr 2694, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 1), (Sum.inr 2742, 2), (Sum.inr 3016, 2), (Sum.inr 3024, 2), (Sum.inr 3025, 2), (Sum.inr 3054, 2), (Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3064, 1), (Sum.inr 3065, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 2), (Sum.inr 3078, 1), (Sum.inr 3101, 2), (Sum.inr 3102, 2), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 1), (Sum.inr 3227, 1)]

def sourceForm541 : Integer.Sparse Master := [(Sum.inr 2509, 1), (Sum.inr 3493, 1), (Sum.inr 3498, 1), (Sum.inr 3547, 2), (Sum.inr 3625, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm544 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 997, 1), (Sum.inr 1001, 2), (Sum.inr 1078, 1), (Sum.inr 2396, 1), (Sum.inr 2397, 1), (Sum.inr 2401, 2), (Sum.inr 2457, 1), (Sum.inr 2460, 2), (Sum.inr 2507, 1), (Sum.inr 2700, 2), (Sum.inr 2702, 2), (Sum.inr 2706, 2), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 2738, 2), (Sum.inr 2775, 1), (Sum.inr 3571, 1), (Sum.inr 3580, 1), (Sum.inr 3581, 2), (Sum.inr 3887, 1)]

def sourceForm545 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 1252, 1), (Sum.inr 1253, 1), (Sum.inr 1270, 2), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

def sourceForm546 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 2625, 2), (Sum.inr 2746, 1), (Sum.inr 2750, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

def sourceForm547 : Integer.Sparse Master := [(Sum.inr 1421, 1), (Sum.inr 2564, 1), (Sum.inr 2573, 2), (Sum.inr 2754, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

def sourceForm548 : Integer.Sparse Master := [(Sum.inr 1270, 1), (Sum.inr 2573, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def sourceForm549 : Integer.Sparse Master := [(Sum.inr 4441, 1), (Sum.inr 4442, 1), (Sum.inr 4443, 1), (Sum.inr 4462, 2), (Sum.inr 4792, 1), (Sum.inr 4807, 2), (Sum.inr 4890, 1), (Sum.inr 5066, 1), (Sum.inr 5077, 2), (Sum.inr 5150, 2), (Sum.inr 5151, 2), (Sum.inr 5173, 2), (Sum.inr 5256, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 2), (Sum.inr 5278, 1), (Sum.inr 5279, 1), (Sum.inr 5288, 2), (Sum.inr 5290, 1), (Sum.inr 5295, 2), (Sum.inr 5306, 1)]

def sourceForm550 : Integer.Sparse Master := [(Sum.inr 1023, 1), (Sum.inr 1024, 1), (Sum.inr 1025, 1), (Sum.inr 1045, 2), (Sum.inr 2471, 1), (Sum.inr 2472, 1), (Sum.inr 2484, 2), (Sum.inr 2573, 2), (Sum.inr 2574, 2), (Sum.inr 2575, 2), (Sum.inr 2600, 2), (Sum.inr 2747, 1), (Sum.inr 2748, 1), (Sum.inr 2754, 1), (Sum.inr 2755, 1), (Sum.inr 2760, 2), (Sum.inr 2764, 1), (Sum.inr 2769, 2), (Sum.inr 3085, 1), (Sum.inr 3109, 2), (Sum.inr 3120, 1)]

def sourceForm551 : Integer.Sparse Master := [(Sum.inr 1654, 1), (Sum.inr 1655, 1), (Sum.inr 1656, 2), (Sum.inr 1744, 1), (Sum.inr 2201, 1), (Sum.inr 2224, 2), (Sum.inr 2290, 1), (Sum.inr 2668, 1), (Sum.inr 2681, 2), (Sum.inr 2700, 2), (Sum.inr 2717, 2), (Sum.inr 2720, 1), (Sum.inr 2735, 2), (Sum.inr 2738, 1), (Sum.inr 2739, 2), (Sum.inr 2781, 2), (Sum.inr 2784, 1), (Sum.inr 3050, 1), (Sum.inr 3073, 1), (Sum.inr 3096, 2), (Sum.inr 3099, 1)]

def sourceForm552 : Integer.Sparse Master := [(Sum.inr 3075, 1), (Sum.inr 3525, 1), (Sum.inr 3534, 2), (Sum.inr 3581, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def sourceForm553 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 1385, 1), (Sum.inr 1390, 1), (Sum.inr 1404, 2), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

def sourceForm554 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 2923, 2), (Sum.inr 3073, 1), (Sum.inr 3075, 2), (Sum.inr 4083, -1)]

def sourceForm555 : Integer.Sparse Master := [(Sum.inr 2009, 1), (Sum.inr 2980, 1), (Sum.inr 2983, 2), (Sum.inr 3075, 1), (Sum.inr 3525, 1), (Sum.inr 4083, -1)]

def sourceForm556 : Integer.Sparse Master := [(Sum.inr 2025, 1), (Sum.inr 2923, 1), (Sum.inr 2930, 1), (Sum.inr 2952, 1), (Sum.inr 3075, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

def sourceForm557 : Integer.Sparse Master := [(Sum.inr 1390, 1), (Sum.inr 2930, 2), (Sum.inr 2980, 1), (Sum.inr 3075, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

def sourceForm560 : Integer.Sparse Master := [(Sum.inr 2693, 1), (Sum.inr 2702, 1), (Sum.inr 2704, 1), (Sum.inr 2740, 2), (Sum.inr 3015, 2), (Sum.inr 3022, 2), (Sum.inr 3024, 2), (Sum.inr 3052, 2), (Sum.inr 3057, 1), (Sum.inr 3058, 1), (Sum.inr 3063, 1), (Sum.inr 3064, 1), (Sum.inr 3072, 1), (Sum.inr 3075, 2), (Sum.inr 3077, 1), (Sum.inr 3098, 2), (Sum.inr 3101, 2), (Sum.inr 3155, 1), (Sum.inr 3156, 2), (Sum.inr 3158, 1), (Sum.inr 3223, 1)]

def sourceForm561 : Integer.Sparse Master := [(Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 2552, 1), (Sum.inr 2738, 1), (Sum.inr 2740, 2), (Sum.inr 4084, -1)]

def sourceForm562 : Integer.Sparse Master := [(Sum.inr 2131, 1), (Sum.inr 2132, 1), (Sum.inr 2133, 2), (Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 4084, -1)]

def sourceForm564 : Integer.Sparse Master := [(Sum.inr 4607, 2), (Sum.inr 4609, 1), (Sum.inr 4611, 1), (Sum.inr 4619, 1), (Sum.inr 5144, 2), (Sum.inr 5147, 2), (Sum.inr 5151, 2), (Sum.inr 5163, 2), (Sum.inr 5198, 2), (Sum.inr 5201, 1), (Sum.inr 5206, 1), (Sum.inr 5258, 2), (Sum.inr 5261, 1), (Sum.inr 5274, 1), (Sum.inr 5289, 2), (Sum.inr 5295, 1), (Sum.inr 5304, 1), (Sum.inr 5432, 2), (Sum.inr 5441, 1), (Sum.inr 5449, 1), (Sum.inr 5451, 1)]

def sourceForm565 : Integer.Sparse Master := [(Sum.inr 1241, 2), (Sum.inr 1243, 1), (Sum.inr 1245, 1), (Sum.inr 1302, 1), (Sum.inr 2865, 2), (Sum.inr 2885, 2), (Sum.inr 2886, 1), (Sum.inr 2888, 1), (Sum.inr 2928, 2), (Sum.inr 2930, 2), (Sum.inr 2961, 2), (Sum.inr 3089, 2), (Sum.inr 3090, 1), (Sum.inr 3097, 2), (Sum.inr 3098, 1), (Sum.inr 3112, 1), (Sum.inr 3119, 1), (Sum.inr 3987, 1), (Sum.inr 4027, 2), (Sum.inr 4030, 1), (Sum.inr 4037, 1)]

def sourceForm566 : Integer.Sparse Master := [(Sum.inr 2681, 2), (Sum.inr 2683, 1), (Sum.inr 2687, 1), (Sum.inr 2781, 1), (Sum.inr 3296, 2), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3530, 2), (Sum.inr 3533, 2), (Sum.inr 3545, 1), (Sum.inr 3547, 1), (Sum.inr 3557, 2), (Sum.inr 3564, 2), (Sum.inr 3570, 2), (Sum.inr 3572, 2), (Sum.inr 3579, 1), (Sum.inr 3583, 1), (Sum.inr 3850, 2), (Sum.inr 3860, 1), (Sum.inr 3886, 1), (Sum.inr 3888, 1)]

def sourceForm567 : Integer.Sparse Master := [(Sum.inr 2765, 1), (Sum.inr 3850, 2), (Sum.inr 3886, 1), (Sum.inr 3905, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def sourceForm568 : Integer.Sparse Master := [(Sum.inr 1261, 2), (Sum.inr 1264, 1), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def sourceForm569 : Integer.Sparse Master := [(Sum.inr 1294, 1), (Sum.inr 2590, 2), (Sum.inr 2742, 1), (Sum.inr 2765, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

def sourceForm570 : Integer.Sparse Master := [(Sum.inr 2632, 2), (Sum.inr 2635, 1), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

def sourceForm571 : Integer.Sparse Master := [(Sum.inr 1261, 1), (Sum.inr 2566, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 2763, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def sourceForm572 : Integer.Sparse Master := [(Sum.inr 4452, 2), (Sum.inr 4454, 1), (Sum.inr 4466, 1), (Sum.inr 4491, 1), (Sum.inr 4827, 2), (Sum.inr 4845, 1), (Sum.inr 4868, 1), (Sum.inr 5070, 2), (Sum.inr 5080, 2), (Sum.inr 5095, 2), (Sum.inr 5163, 2), (Sum.inr 5176, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5290, 2), (Sum.inr 5294, 1), (Sum.inr 5304, 1), (Sum.inr 5438, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1), (Sum.inr 5492, 1)]

def sourceForm573 : Integer.Sparse Master := [(Sum.inr 1035, 2), (Sum.inr 1037, 1), (Sum.inr 1049, 1), (Sum.inr 1075, 1), (Sum.inr 2079, 2), (Sum.inr 2109, 1), (Sum.inr 2218, 1), (Sum.inr 2477, 2), (Sum.inr 2488, 2), (Sum.inr 2505, 2), (Sum.inr 2590, 2), (Sum.inr 2604, 1), (Sum.inr 2672, 2), (Sum.inr 2686, 1), (Sum.inr 2764, 2), (Sum.inr 2768, 1), (Sum.inr 2782, 1), (Sum.inr 3876, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 4017, 1)]

def sourceForm574 : Integer.Sparse Master := [(Sum.inr 4865, 2), (Sum.inr 4868, 1), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 5161, 2), (Sum.inr 5175, 1), (Sum.inr 5249, 2), (Sum.inr 5258, 2), (Sum.inr 5260, 2), (Sum.inr 5264, 2), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5279, 2), (Sum.inr 5282, 2), (Sum.inr 5291, 2), (Sum.inr 5293, 1), (Sum.inr 5297, 1), (Sum.inr 5300, 1), (Sum.inr 5305, 1), (Sum.inr 5308, 1), (Sum.inr 5310, 1)]

def sourceForm575 : Integer.Sparse Master := [(Sum.inr 2242, 2), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2276, 1), (Sum.inr 2708, 2), (Sum.inr 2719, 2), (Sum.inr 2722, 2), (Sum.inr 2729, 2), (Sum.inr 2748, 2), (Sum.inr 2751, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 2), (Sum.inr 2767, 1), (Sum.inr 2771, 1), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 3086, 2), (Sum.inr 3110, 1), (Sum.inr 3121, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm576 : Integer.Sparse Master := [(Sum.inr 2724, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 1), (Sum.inr 2788, 1), (Sum.inr 2964, 2), (Sum.inr 2966, 1), (Sum.inr 2967, 1), (Sum.inr 3040, 2), (Sum.inr 3055, 1), (Sum.inr 3056, 1), (Sum.inr 3066, 2), (Sum.inr 3078, 2), (Sum.inr 3079, 2), (Sum.inr 3089, 2), (Sum.inr 3102, 1), (Sum.inr 3103, 2), (Sum.inr 3124, 1), (Sum.inr 3125, 1), (Sum.inr 3185, 2), (Sum.inr 3187, 1), (Sum.inr 3230, 1)]

def sourceForm577 : Integer.Sparse Master := [(Sum.inr 2106, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 2264, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

def sourceForm578 : Integer.Sparse Master := [(Sum.inr 4590, 1), (Sum.inr 4591, 1), (Sum.inr 4593, 1), (Sum.inr 4603, 1), (Sum.inr 4606, 1), (Sum.inr 5073, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5104, 1), (Sum.inr 5128, 1), (Sum.inr 5130, 1), (Sum.inr 5137, 1), (Sum.inr 5139, 1), (Sum.inr 5145, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5199, 1), (Sum.inr 5250, 1), (Sum.inr 5252, 1), (Sum.inr 5257, 1), (Sum.inr 5259, 2), (Sum.inr 5273, 1), (Sum.inr 5282, 1), (Sum.inr 5290, 1), (Sum.inr 5410, 1), (Sum.inr 5424, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1)]

def sourceForm579 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1215, 1), (Sum.inr 1220, 1), (Sum.inr 1237, 1), (Sum.inr 1266, 1), (Sum.inr 2543, 1), (Sum.inr 2558, 1), (Sum.inr 2572, 1), (Sum.inr 2712, 1), (Sum.inr 2862, 1), (Sum.inr 2868, 1), (Sum.inr 2882, 1), (Sum.inr 2917, 1), (Sum.inr 2925, 1), (Sum.inr 2936, 1), (Sum.inr 2987, 1), (Sum.inr 2991, 1), (Sum.inr 3000, 1), (Sum.inr 3065, 1), (Sum.inr 3078, 1), (Sum.inr 3087, 1), (Sum.inr 3088, 2), (Sum.inr 3099, 1), (Sum.inr 3111, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1), (Sum.inr 3996, 1), (Sum.inr 4012, 1), (Sum.inr 4036, 1)]

def sourceForm580 : Integer.Sparse Master := [(Sum.inr 3290, 1), (Sum.inr 3291, 1), (Sum.inr 3294, 1), (Sum.inr 3297, 1), (Sum.inr 3299, 1), (Sum.inr 3467, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3483, 1), (Sum.inr 3519, 1), (Sum.inr 3520, 1), (Sum.inr 3521, 1), (Sum.inr 3523, 1), (Sum.inr 3529, 1), (Sum.inr 3531, 1), (Sum.inr 3532, 1), (Sum.inr 3542, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3562, 1), (Sum.inr 3578, 1), (Sum.inr 3580, 1), (Sum.inr 3581, 1), (Sum.inr 3816, 1), (Sum.inr 3843, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3859, 1)]

def sourceForm581 : Integer.Sparse Master := [(Sum.inr 2723, 1), (Sum.inr 3808, 1), (Sum.inr 3838, 1), (Sum.inr 3876, 1), (Sum.inr 3902, 1), (Sum.inr 3904, 1), (Sum.inr 4091, -1)]

def sourceForm582 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1217, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

def sourceForm583 : Integer.Sparse Master := [(Sum.inr 1240, 1), (Sum.inr 2514, 1), (Sum.inr 2556, 1), (Sum.inr 2723, 2), (Sum.inr 2741, 1), (Sum.inr 4091, -1)]

def sourceForm584 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 2618, 1), (Sum.inr 2621, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def sourceForm585 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2546, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 1), (Sum.inr 2723, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

def sourceForm586 : Integer.Sparse Master := [(Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 2489, 1), (Sum.inr 2514, 1), (Sum.inr 2723, 1), (Sum.inr 3808, 1), (Sum.inr 4091, -1)]

def sourceForm587 : Integer.Sparse Master := [(Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 2546, 1), (Sum.inr 2621, 1), (Sum.inr 2723, 2), (Sum.inr 4091, -1)]

def sourceForm588 : Integer.Sparse Master := [(Sum.inr 4399, 1), (Sum.inr 4401, 1), (Sum.inr 4404, 1), (Sum.inr 4424, 1), (Sum.inr 4458, 1), (Sum.inr 4998, 1), (Sum.inr 5000, 1), (Sum.inr 5003, 1), (Sum.inr 5018, 1), (Sum.inr 5047, 1), (Sum.inr 5050, 1), (Sum.inr 5059, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5169, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5261, 1), (Sum.inr 5271, 1), (Sum.inr 5275, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5490, 1), (Sum.inr 5491, 1)]

def sourceForm589 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1041, 1), (Sum.inr 2383, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2404, 1), (Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2462, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2595, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2726, 1), (Sum.inr 2739, 1), (Sum.inr 2743, 1), (Sum.inr 2766, 1), (Sum.inr 2767, 1), (Sum.inr 3958, 1), (Sum.inr 3971, 1), (Sum.inr 3981, 1), (Sum.inr 4013, 1), (Sum.inr 4014, 1)]

def sourceForm590 : Integer.Sparse Master := [(Sum.inr 4831, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4839, 1), (Sum.inr 4895, 1), (Sum.inr 5220, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5233, 1), (Sum.inr 5241, 1), (Sum.inr 5242, 1), (Sum.inr 5244, 1), (Sum.inr 5250, 2), (Sum.inr 5251, 1), (Sum.inr 5258, 2), (Sum.inr 5259, 3), (Sum.inr 5260, 1), (Sum.inr 5266, 2), (Sum.inr 5267, 1), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5293, 2), (Sum.inr 5294, 1), (Sum.inr 5309, 1)]

def sourceForm591 : Integer.Sparse Master := [(Sum.inr 2191, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 1), (Sum.inr 2216, 1), (Sum.inr 2265, 1), (Sum.inr 2662, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2678, 1), (Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 2698, 1), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 2), (Sum.inr 2724, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 2767, 1), (Sum.inr 2768, 1), (Sum.inr 2787, 1), (Sum.inr 3039, 1), (Sum.inr 3065, 1), (Sum.inr 3088, 1), (Sum.inr 3089, 1), (Sum.inr 3102, 1)]

def sourceForm592 : Integer.Sparse Master := [(Sum.inr 2709, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2731, 1), (Sum.inr 2767, 1), (Sum.inr 3029, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3044, 1), (Sum.inr 3064, 1), (Sum.inr 3065, 1), (Sum.inr 3068, 1), (Sum.inr 3080, 1), (Sum.inr 3081, 1), (Sum.inr 3086, 1), (Sum.inr 3088, 2), (Sum.inr 3089, 1), (Sum.inr 3092, 1), (Sum.inr 3094, 1), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3123, 1), (Sum.inr 3209, 1), (Sum.inr 3210, 1), (Sum.inr 3211, 1), (Sum.inr 3214, 1), (Sum.inr 3229, 1)]

def sourceForm593 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 2053, 1), (Sum.inr 2054, 1), (Sum.inr 2058, 1), (Sum.inr 2291, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

def sourceForm594 : Integer.Sparse Master := [(Sum.inr 4589, 1), (Sum.inr 4591, 1), (Sum.inr 4592, 1), (Sum.inr 4602, 1), (Sum.inr 4607, 1), (Sum.inr 5072, 1), (Sum.inr 5075, 1), (Sum.inr 5080, 1), (Sum.inr 5101, 1), (Sum.inr 5127, 1), (Sum.inr 5129, 1), (Sum.inr 5134, 1), (Sum.inr 5144, 1), (Sum.inr 5147, 1), (Sum.inr 5184, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5261, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1), (Sum.inr 5289, 1), (Sum.inr 5291, 1), (Sum.inr 5409, 1), (Sum.inr 5423, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5441, 1)]

def sourceForm595 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 1217, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1267, 1), (Sum.inr 2864, 1), (Sum.inr 2865, 1), (Sum.inr 2867, 1), (Sum.inr 2885, 1), (Sum.inr 2914, 1), (Sum.inr 2916, 1), (Sum.inr 2928, 1), (Sum.inr 2937, 1), (Sum.inr 2939, 1), (Sum.inr 2988, 1), (Sum.inr 2990, 1), (Sum.inr 3001, 1), (Sum.inr 3085, 1), (Sum.inr 3086, 1), (Sum.inr 3089, 1), (Sum.inr 3090, 1), (Sum.inr 3097, 1), (Sum.inr 3103, 1), (Sum.inr 3109, 1), (Sum.inr 3112, 1), (Sum.inr 3982, 1), (Sum.inr 4027, 1), (Sum.inr 4032, 1), (Sum.inr 4035, 1), (Sum.inr 4037, 1)]

def sourceForm596 : Integer.Sparse Master := [(Sum.inr 3288, 1), (Sum.inr 3291, 1), (Sum.inr 3293, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 1), (Sum.inr 3459, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3478, 1), (Sum.inr 3513, 1), (Sum.inr 3514, 1), (Sum.inr 3516, 1), (Sum.inr 3524, 1), (Sum.inr 3525, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3545, 1), (Sum.inr 3547, 1), (Sum.inr 3557, 1), (Sum.inr 3570, 1), (Sum.inr 3572, 1), (Sum.inr 3582, 1), (Sum.inr 3807, 1), (Sum.inr 3837, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3860, 1)]

def sourceForm597 : Integer.Sparse Master := [(Sum.inr 2722, 1), (Sum.inr 3807, 1), (Sum.inr 3837, 1), (Sum.inr 3850, 1), (Sum.inr 3903, 1), (Sum.inr 3905, 1), (Sum.inr 4092, -1)]

def sourceForm598 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1215, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 2722, 1), (Sum.inr 4092, -1)]

def sourceForm599 : Integer.Sparse Master := [(Sum.inr 1236, 1), (Sum.inr 2511, 1), (Sum.inr 2553, 1), (Sum.inr 2722, 1), (Sum.inr 2739, 1), (Sum.inr 2742, 1), (Sum.inr 4092, -1)]

def sourceForm600 : Integer.Sparse Master := [(Sum.inr 2569, 1), (Sum.inr 2614, 1), (Sum.inr 2620, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

def sourceForm601 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 2614, 1), (Sum.inr 2720, 1), (Sum.inr 2722, 2), (Sum.inr 4092, -1)]

def sourceForm602 : Integer.Sparse Master := [(Sum.inr 2542, 1), (Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2722, 1), (Sum.inr 3837, 1), (Sum.inr 4092, -1)]

def sourceForm603 : Integer.Sparse Master := [(Sum.inr 4396, 1), (Sum.inr 4398, 1), (Sum.inr 4404, 1), (Sum.inr 4419, 1), (Sum.inr 4457, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4804, 1), (Sum.inr 4832, 1), (Sum.inr 4996, 1), (Sum.inr 5003, 1), (Sum.inr 5015, 1), (Sum.inr 5050, 1), (Sum.inr 5056, 1), (Sum.inr 5072, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5168, 1), (Sum.inr 5241, 1), (Sum.inr 5248, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 1), (Sum.inr 5292, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5490, 1)]

def sourceForm604 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 979, 1), (Sum.inr 985, 1), (Sum.inr 1000, 1), (Sum.inr 1040, 1), (Sum.inr 1987, 1), (Sum.inr 2003, 1), (Sum.inr 2022, 1), (Sum.inr 2193, 1), (Sum.inr 2382, 1), (Sum.inr 2388, 1), (Sum.inr 2400, 1), (Sum.inr 2452, 1), (Sum.inr 2459, 1), (Sum.inr 2479, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 2594, 1), (Sum.inr 2694, 1), (Sum.inr 2705, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2739, 1), (Sum.inr 2766, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3852, 1), (Sum.inr 3902, 1), (Sum.inr 4013, 1)]

def sourceForm605 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4804, 1), (Sum.inr 4810, 1), (Sum.inr 4834, 1), (Sum.inr 4894, 1), (Sum.inr 5133, 1), (Sum.inr 5140, 1), (Sum.inr 5161, 1), (Sum.inr 5219, 1), (Sum.inr 5228, 1), (Sum.inr 5232, 1), (Sum.inr 5241, 1), (Sum.inr 5243, 1), (Sum.inr 5249, 1), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 1), (Sum.inr 5264, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5272, 1), (Sum.inr 5274, 1), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5308, 1)]

def sourceForm606 : Integer.Sparse Master := [(Sum.inr 2190, 1), (Sum.inr 2203, 1), (Sum.inr 2205, 1), (Sum.inr 2215, 1), (Sum.inr 2264, 1), (Sum.inr 2661, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2677, 1), (Sum.inr 2693, 1), (Sum.inr 2694, 1), (Sum.inr 2697, 1), (Sum.inr 2708, 1), (Sum.inr 2709, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 2), (Sum.inr 2723, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1), (Sum.inr 2740, 1), (Sum.inr 2742, 1), (Sum.inr 2765, 1), (Sum.inr 2767, 1), (Sum.inr 2786, 1), (Sum.inr 3038, 1), (Sum.inr 3064, 1), (Sum.inr 3086, 1), (Sum.inr 3088, 1), (Sum.inr 3101, 1)]

def sourceForm607 : Integer.Sparse Master := [(Sum.inr 2710, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2768, 1), (Sum.inr 2940, 1), (Sum.inr 2941, 1), (Sum.inr 2942, 1), (Sum.inr 2964, 1), (Sum.inr 3030, 1), (Sum.inr 3039, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3065, 1), (Sum.inr 3066, 1), (Sum.inr 3069, 1), (Sum.inr 3081, 1), (Sum.inr 3088, 1), (Sum.inr 3089, 2), (Sum.inr 3094, 1), (Sum.inr 3102, 1), (Sum.inr 3103, 1), (Sum.inr 3112, 1), (Sum.inr 3113, 1), (Sum.inr 3124, 1), (Sum.inr 3205, 1), (Sum.inr 3206, 1), (Sum.inr 3214, 1), (Sum.inr 3230, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm608 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 2053, 1), (Sum.inr 2264, 1), (Sum.inr 3533, 1), (Sum.inr 4084, -1)]

def sourceForm609 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 4624, 3), (Sum.inr 4625, 1), (Sum.inr 4628, 1), (Sum.inr 5169, 6), (Sum.inr 5174, 3), (Sum.inr 5177, 3), (Sum.inr 5293, 3), (Sum.inr 5296, 1), (Sum.inr 5307, 3), (Sum.inr 5309, 1), (Sum.inr 5442, 3), (Sum.inr 5455, 1)]

def sourceForm610 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 4623, 3), (Sum.inr 4625, 1), (Sum.inr 4627, 1), (Sum.inr 5168, 6), (Sum.inr 5171, 3), (Sum.inr 5176, 3), (Sum.inr 5306, 3), (Sum.inr 5308, 3), (Sum.inr 5310, 1), (Sum.inr 5312, 1), (Sum.inr 5441, 3), (Sum.inr 5455, 1)]

def sourceForm611 : Integer.Sparse Master := [(Sum.inr 4617, 3), (Sum.inr 4621, 1), (Sum.inr 4626, 1), (Sum.inr 4868, 3), (Sum.inr 4897, 1), (Sum.inr 5161, 6), (Sum.inr 5175, 3), (Sum.inr 5272, 3), (Sum.inr 5291, 3), (Sum.inr 5295, 3), (Sum.inr 5308, 1), (Sum.inr 5310, 1), (Sum.inr 5311, 1)]

def sourceForm612 : Integer.Sparse Master := [(Sum.inr 1306, 3), (Sum.inr 1308, 1), (Sum.inr 1310, 1), (Sum.inr 2769, 3), (Sum.inr 2788, 1), (Sum.inr 2789, 1), (Sum.inr 2964, 6), (Sum.inr 2966, 3), (Sum.inr 2967, 3), (Sum.inr 3103, 3), (Sum.inr 3113, 3), (Sum.inr 3114, 1), (Sum.inr 3124, 1)]

def sourceForm613 : Integer.Sparse Master := [(Sum.inr 2261, 3), (Sum.inr 2289, 1), (Sum.inr 2292, 1), (Sum.inr 2719, 6), (Sum.inr 2737, 3), (Sum.inr 2740, 3), (Sum.inr 2761, 3), (Sum.inr 2765, 3), (Sum.inr 2780, 1), (Sum.inr 2786, 1), (Sum.inr 2789, 1), (Sum.inr 3098, 3), (Sum.inr 3121, 1)]

def sourceForm614 : Integer.Sparse Master := [(Sum.inr 4490, 6), (Sum.inr 4493, 1), (Sum.inr 4510, 2), (Sum.inr 5094, 6), (Sum.inr 5110, 6), (Sum.inr 5304, 6), (Sum.inr 5310, 2), (Sum.inr 5494, 1)]

def sourceForm615 : Integer.Sparse Master := [(Sum.inr 4603, 2), (Sum.inr 4609, 1), (Sum.inr 4612, 1), (Sum.inr 4620, 1), (Sum.inr 5102, 2), (Sum.inr 5109, 1), (Sum.inr 5111, 1), (Sum.inr 5135, 2), (Sum.inr 5139, 2), (Sum.inr 5141, 2), (Sum.inr 5164, 2), (Sum.inr 5266, 2), (Sum.inr 5268, 1), (Sum.inr 5271, 2), (Sum.inr 5274, 1), (Sum.inr 5300, 1), (Sum.inr 5304, 1), (Sum.inr 5413, 1), (Sum.inr 5428, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1)]

def sourceForm616 : Integer.Sparse Master := [(Sum.inr 1262, 2), (Sum.inr 1264, 1), (Sum.inr 1274, 1), (Sum.inr 1295, 1), (Sum.inr 2618, 2), (Sum.inr 2640, 1), (Sum.inr 2734, 1), (Sum.inr 2934, 2), (Sum.inr 2943, 2), (Sum.inr 2955, 2), (Sum.inr 2998, 2), (Sum.inr 3006, 1), (Sum.inr 3039, 2), (Sum.inr 3055, 1), (Sum.inr 3109, 2), (Sum.inr 3112, 1), (Sum.inr 3119, 1), (Sum.inr 3889, 1), (Sum.inr 4001, 1), (Sum.inr 4003, 2), (Sum.inr 4006, 1)]

def sourceForm617 : Integer.Sparse Master := [(Sum.inr 3294, 2), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3306, 1), (Sum.inr 3471, 2), (Sum.inr 3485, 1), (Sum.inr 3486, 1), (Sum.inr 3515, 2), (Sum.inr 3522, 2), (Sum.inr 3523, 2), (Sum.inr 3534, 2), (Sum.inr 3535, 2), (Sum.inr 3547, 1), (Sum.inr 3549, 1), (Sum.inr 3565, 2), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 2), (Sum.inr 3861, 1), (Sum.inr 3862, 1)]

def sourceForm618 : Integer.Sparse Master := [(Sum.inr 2743, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 2), (Sum.inr 3907, 1), (Sum.inr 3908, 1), (Sum.inr 4092, -1)]

def sourceForm619 : Integer.Sparse Master := [(Sum.inr 2554, 1), (Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 2591, 1), (Sum.inr 2743, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

def sourceForm620 : Integer.Sparse Master := [(Sum.inr 2512, 2), (Sum.inr 2519, 1), (Sum.inr 2523, 1), (Sum.inr 2743, 1), (Sum.inr 3817, 1), (Sum.inr 4092, -1)]

def sourceForm621 : Integer.Sparse Master := [(Sum.inr 1246, 1), (Sum.inr 2523, 1), (Sum.inr 2561, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def sourceForm622 : Integer.Sparse Master := [(Sum.inr 4424, 2), (Sum.inr 4428, 1), (Sum.inr 4431, 1), (Sum.inr 4499, 1), (Sum.inr 5000, 2), (Sum.inr 5014, 2), (Sum.inr 5018, 2), (Sum.inr 5021, 1), (Sum.inr 5023, 1), (Sum.inr 5059, 2), (Sum.inr 5102, 2), (Sum.inr 5259, 2), (Sum.inr 5261, 1), (Sum.inr 5271, 2), (Sum.inr 5272, 1), (Sum.inr 5293, 1), (Sum.inr 5306, 1), (Sum.inr 5473, 2), (Sum.inr 5475, 1), (Sum.inr 5491, 1), (Sum.inr 5492, 1)]

def sourceForm623 : Integer.Sparse Master := [(Sum.inr 1005, 2), (Sum.inr 1009, 1), (Sum.inr 1012, 1), (Sum.inr 1083, 1), (Sum.inr 2385, 2), (Sum.inr 2404, 2), (Sum.inr 2407, 1), (Sum.inr 2410, 1), (Sum.inr 2462, 2), (Sum.inr 2467, 2), (Sum.inr 2512, 2), (Sum.inr 2723, 2), (Sum.inr 2726, 1), (Sum.inr 2739, 2), (Sum.inr 2740, 1), (Sum.inr 2767, 1), (Sum.inr 2784, 1), (Sum.inr 3958, 2), (Sum.inr 3963, 1), (Sum.inr 4014, 1), (Sum.inr 4015, 1)]

def sourceForm624 : Integer.Sparse Master := [(Sum.inr 4835, 2), (Sum.inr 4843, 1), (Sum.inr 4846, 1), (Sum.inr 4901, 1), (Sum.inr 5205, 2), (Sum.inr 5206, 1), (Sum.inr 5229, 2), (Sum.inr 5238, 1), (Sum.inr 5242, 2), (Sum.inr 5248, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 2), (Sum.inr 5276, 1), (Sum.inr 5282, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5300, 1), (Sum.inr 5309, 1), (Sum.inr 5310, 1)]

def sourceForm625 : Integer.Sparse Master := [(Sum.inr 2206, 2), (Sum.inr 2229, 1), (Sum.inr 2230, 1), (Sum.inr 2293, 1), (Sum.inr 2673, 2), (Sum.inr 2686, 1), (Sum.inr 2687, 1), (Sum.inr 2695, 2), (Sum.inr 2705, 2), (Sum.inr 2706, 2), (Sum.inr 2723, 2), (Sum.inr 2724, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 2), (Sum.inr 2744, 1), (Sum.inr 2787, 1), (Sum.inr 2788, 1), (Sum.inr 3055, 1), (Sum.inr 3078, 2), (Sum.inr 3102, 1), (Sum.inr 3103, 1)]

def sourceForm626 : Integer.Sparse Master := [(Sum.inr 2054, 2), (Sum.inr 2062, 1), (Sum.inr 2066, 1), (Sum.inr 2293, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

def sourceForm627 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4602, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4619, 1), (Sum.inr 5075, 2), (Sum.inr 5101, 2), (Sum.inr 5107, 1), (Sum.inr 5111, 1), (Sum.inr 5134, 2), (Sum.inr 5141, 2), (Sum.inr 5163, 2), (Sum.inr 5258, 2), (Sum.inr 5261, 1), (Sum.inr 5271, 2), (Sum.inr 5275, 1), (Sum.inr 5291, 1), (Sum.inr 5304, 1), (Sum.inr 5409, 2), (Sum.inr 5441, 1), (Sum.inr 5442, 1)]

def sourceForm628 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4834, 2), (Sum.inr 4841, 1), (Sum.inr 4846, 1), (Sum.inr 5099, 2), (Sum.inr 5110, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5241, 2), (Sum.inr 5248, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5272, 1), (Sum.inr 5274, 2), (Sum.inr 5275, 1), (Sum.inr 5284, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5302, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 1)]

def sourceForm629 : Integer.Sparse Master := [(Sum.inr 4600, 2), (Sum.inr 4605, 1), (Sum.inr 4611, 1), (Sum.inr 4617, 1), (Sum.inr 4804, 2), (Sum.inr 4841, 1), (Sum.inr 4897, 1), (Sum.inr 5099, 2), (Sum.inr 5110, 1), (Sum.inr 5133, 2), (Sum.inr 5140, 2), (Sum.inr 5161, 2), (Sum.inr 5258, 2), (Sum.inr 5270, 2), (Sum.inr 5272, 2), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5294, 1), (Sum.inr 5295, 1), (Sum.inr 5305, 1), (Sum.inr 5308, 1)]

def sourceForm630 : Integer.Sparse Master := [(Sum.inr 1270, 2), (Sum.inr 1271, 1), (Sum.inr 1273, 1), (Sum.inr 1306, 1), (Sum.inr 2754, 2), (Sum.inr 2768, 1), (Sum.inr 2769, 1), (Sum.inr 2777, 1), (Sum.inr 2940, 2), (Sum.inr 2941, 2), (Sum.inr 2942, 2), (Sum.inr 2964, 2), (Sum.inr 3003, 2), (Sum.inr 3004, 1), (Sum.inr 3005, 1), (Sum.inr 3089, 2), (Sum.inr 3112, 1), (Sum.inr 3113, 2), (Sum.inr 3114, 1), (Sum.inr 3124, 1), (Sum.inr 3125, 1)]

def sourceForm631 : Integer.Sparse Master := [(Sum.inr 2203, 2), (Sum.inr 2226, 1), (Sum.inr 2228, 1), (Sum.inr 2292, 1), (Sum.inr 2670, 2), (Sum.inr 2683, 1), (Sum.inr 2685, 1), (Sum.inr 2693, 2), (Sum.inr 2702, 2), (Sum.inr 2704, 2), (Sum.inr 2719, 2), (Sum.inr 2722, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 2), (Sum.inr 2742, 1), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 3052, 1), (Sum.inr 3075, 2), (Sum.inr 3098, 1), (Sum.inr 3101, 1)]

def sourceForm632 : Integer.Sparse Master := [(Sum.inr 4418, 4), (Sum.inr 4421, 1), (Sum.inr 4431, 2), (Sum.inr 4496, 2), (Sum.inr 5014, 4), (Sum.inr 5023, 1), (Sum.inr 5055, 2), (Sum.inr 5099, 4), (Sum.inr 5271, 4), (Sum.inr 5272, 1), (Sum.inr 5275, 2), (Sum.inr 5306, 2), (Sum.inr 5492, 1)]

def sourceForm633 : Integer.Sparse Master := [(Sum.inr 4475, 2), (Sum.inr 4478, 1), (Sum.inr 4480, 1), (Sum.inr 4503, 1), (Sum.inr 4816, 2), (Sum.inr 4819, 2), (Sum.inr 4821, 2), (Sum.inr 4839, 2), (Sum.inr 4844, 1), (Sum.inr 4880, 2), (Sum.inr 4884, 1), (Sum.inr 4889, 2), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 2), (Sum.inr 5267, 2), (Sum.inr 5276, 1), (Sum.inr 5294, 1), (Sum.inr 5302, 1)]

def sourceForm634 : Integer.Sparse Master := [(Sum.inr 1715, 2), (Sum.inr 1739, 1), (Sum.inr 1740, 1), (Sum.inr 1746, 1), (Sum.inr 2196, 2), (Sum.inr 2216, 2), (Sum.inr 2217, 2), (Sum.inr 2221, 2), (Sum.inr 2222, 1), (Sum.inr 2245, 2), (Sum.inr 2253, 2), (Sum.inr 2254, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2278, 1), (Sum.inr 2280, 1), (Sum.inr 2284, 1), (Sum.inr 2732, 2), (Sum.inr 2768, 1), (Sum.inr 2776, 1), (Sum.inr 2777, 1)]

def sourceForm635 : Integer.Sparse Master := [(Sum.inr 1087, 1), (Sum.inr 2058, 2), (Sum.inr 2266, 1), (Sum.inr 2279, 1), (Sum.inr 2291, 1), (Sum.inr 4084, -1)]

def sourceForm636 : Integer.Sparse Master := [(Sum.inr 4275, 2), (Sum.inr 4276, 2), (Sum.inr 4278, 1), (Sum.inr 4746, 2), (Sum.inr 4747, 4), (Sum.inr 4749, 2), (Sum.inr 4869, 4), (Sum.inr 4871, 2), (Sum.inr 4874, 2), (Sum.inr 4898, 2), (Sum.inr 4899, 2), (Sum.inr 5412, 2), (Sum.inr 5443, 2), (Sum.inr 5456, 1)]

def sourceForm637 : Integer.Sparse Master := [(Sum.inr 4474, 2), (Sum.inr 4476, 1), (Sum.inr 4480, 1), (Sum.inr 4499, 1), (Sum.inr 4815, 2), (Sum.inr 4817, 2), (Sum.inr 4821, 2), (Sum.inr 4835, 2), (Sum.inr 4879, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4889, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 2), (Sum.inr 4898, 1), (Sum.inr 4899, 1), (Sum.inr 4901, 1), (Sum.inr 5260, 2), (Sum.inr 5294, 1), (Sum.inr 5295, 1), (Sum.inr 5310, 1)]

def sourceForm638 : Integer.Sparse Master := [(Sum.inr 1370, 2), (Sum.inr 1372, 1), (Sum.inr 1375, 1), (Sum.inr 1443, 1), (Sum.inr 2497, 2), (Sum.inr 2520, 1), (Sum.inr 2778, 1), (Sum.inr 3086, 2), (Sum.inr 3098, 1), (Sum.inr 3101, 1), (Sum.inr 3121, 1), (Sum.inr 3158, 2), (Sum.inr 3161, 1), (Sum.inr 3197, 2), (Sum.inr 3198, 2), (Sum.inr 3211, 2), (Sum.inr 3223, 2), (Sum.inr 3224, 1), (Sum.inr 3225, 2), (Sum.inr 3229, 1), (Sum.inr 3231, 1)]

def sourceForm639 : Integer.Sparse Master := [(Sum.inr 1709, 2), (Sum.inr 1728, 1), (Sum.inr 1729, 1), (Sum.inr 1740, 1), (Sum.inr 2192, 2), (Sum.inr 2206, 2), (Sum.inr 2207, 2), (Sum.inr 2217, 2), (Sum.inr 2245, 2), (Sum.inr 2246, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 2), (Sum.inr 2267, 1), (Sum.inr 2279, 1), (Sum.inr 2280, 1), (Sum.inr 2293, 1), (Sum.inr 2294, 1), (Sum.inr 2724, 2), (Sum.inr 2768, 1), (Sum.inr 2769, 1), (Sum.inr 2788, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm64 : Integer.Sparse Master := [(Sum.inr 1460, 1), (Sum.inr 2083, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 3158, 1), (Sum.inr 4083, -1)]

def sourceForm65 : Integer.Sparse Master := [(Sum.inr 1016, 1), (Sum.inr 1457, 1), (Sum.inr 1460, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

def sourceForm68 : Integer.Sparse Master := [(Sum.inr 1078, 1), (Sum.inr 2050, 1), (Sum.inr 2283, 1), (Sum.inr 2290, 3), (Sum.inr 4085, -1)]

def sourceForm72 : Integer.Sparse Master := [(Sum.inr 991, 2), (Sum.inr 994, 1), (Sum.inr 1010, 1), (Sum.inr 1059, 1), (Sum.inr 1181, 2), (Sum.inr 1191, 1), (Sum.inr 1264, 1), (Sum.inr 2393, 2), (Sum.inr 2408, 1), (Sum.inr 2454, 2), (Sum.inr 2465, 2), (Sum.inr 2495, 2), (Sum.inr 2618, 2), (Sum.inr 2640, 1), (Sum.inr 2732, 2), (Sum.inr 2744, 1), (Sum.inr 2776, 1), (Sum.inr 3039, 2), (Sum.inr 3055, 1), (Sum.inr 3110, 1), (Sum.inr 3889, 1)]

def sourceForm73 : Integer.Sparse Master := [(Sum.inr 1624, 2), (Sum.inr 1628, 1), (Sum.inr 1629, 1), (Sum.inr 1729, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 3052, 1), (Sum.inr 3242, 2), (Sum.inr 3247, 1), (Sum.inr 3302, 1), (Sum.inr 3358, 2), (Sum.inr 3437, 2), (Sum.inr 3472, 2), (Sum.inr 3486, 1), (Sum.inr 3523, 2), (Sum.inr 3535, 2), (Sum.inr 3541, 2), (Sum.inr 3548, 1), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3862, 1)]

def sourceForm74 : Integer.Sparse Master := [(Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 2), (Sum.inr 3054, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def sourceForm75 : Integer.Sparse Master := [(Sum.inr 1224, 2), (Sum.inr 1227, 1), (Sum.inr 1243, 1), (Sum.inr 1279, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

def sourceForm76 : Integer.Sparse Master := [(Sum.inr 1279, 1), (Sum.inr 2579, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

def sourceForm77 : Integer.Sparse Master := [(Sum.inr 1372, 1), (Sum.inr 2495, 2), (Sum.inr 2519, 1), (Sum.inr 2734, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

def sourceForm78 : Integer.Sparse Master := [(Sum.inr 1224, 1), (Sum.inr 2495, 1), (Sum.inr 2547, 1), (Sum.inr 2647, 1), (Sum.inr 2731, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

def sourceForm79 : Integer.Sparse Master := [(Sum.inr 1359, 1), (Sum.inr 2547, 1), (Sum.inr 2558, 1), (Sum.inr 2579, 1), (Sum.inr 2734, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

def sourceForm80 : Integer.Sparse Master := [(Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 2), (Sum.inr 2734, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def sourceForm81 : Integer.Sparse Master := [(Sum.inr 1424, 1), (Sum.inr 2647, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def sourceForm82 : Integer.Sparse Master := [(Sum.inr 1227, 1), (Sum.inr 1359, 2), (Sum.inr 1372, 1), (Sum.inr 1424, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

def sourceForm85 : Integer.Sparse Master := [(Sum.inr 2065, 1), (Sum.inr 3389, 2), (Sum.inr 3396, 1), (Sum.inr 3545, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def sourceForm86 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 2294, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def sourceForm87 : Integer.Sparse Master := [(Sum.inr 2294, 2), (Sum.inr 3549, 3), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

def sourceForm88 : Integer.Sparse Master := [(Sum.inr 3160, 1), (Sum.inr 3393, 2), (Sum.inr 3396, 2), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def sourceForm89 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 3393, 1), (Sum.inr 3495, 1), (Sum.inr 3543, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def sourceForm90 : Integer.Sparse Master := [(Sum.inr 3154, 1), (Sum.inr 3389, 2), (Sum.inr 3495, 1), (Sum.inr 3549, 2), (Sum.inr 4085, -1)]

def sourceForm91 : Integer.Sparse Master := [(Sum.inr 2063, 2), (Sum.inr 3154, 2), (Sum.inr 3160, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def sourceForm94 : Integer.Sparse Master := [(Sum.inr 1613, 1), (Sum.inr 1615, 1), (Sum.inr 1619, 2), (Sum.inr 1723, 1), (Sum.inr 3279, 1), (Sum.inr 3283, 1), (Sum.inr 3291, 2), (Sum.inr 3350, 1), (Sum.inr 3355, 2), (Sum.inr 3434, 2), (Sum.inr 3466, 1), (Sum.inr 3481, 2), (Sum.inr 3519, 2), (Sum.inr 3523, 2), (Sum.inr 3531, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 2), (Sum.inr 3544, 2), (Sum.inr 3580, 1), (Sum.inr 3625, 1), (Sum.inr 3858, 1)]

def sourceForm95 : Integer.Sparse Master := [(Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 2), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm640 : Integer.Sparse Master := [(Sum.inr 1057, 2), (Sum.inr 1059, 1), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 2278, 1), (Sum.inr 4084, -1)]

def sourceForm641 : Integer.Sparse Master := [(Sum.inr 1083, 1), (Sum.inr 2054, 2), (Sum.inr 2278, 1), (Sum.inr 2291, 1), (Sum.inr 2293, 1), (Sum.inr 4084, -1)]

def sourceForm642 : Integer.Sparse Master := [(Sum.inr 4268, 2), (Sum.inr 4270, 1), (Sum.inr 4272, 1), (Sum.inr 4279, 1), (Sum.inr 4740, 2), (Sum.inr 4742, 2), (Sum.inr 4744, 2), (Sum.inr 4750, 2), (Sum.inr 4839, 2), (Sum.inr 4843, 1), (Sum.inr 4845, 1), (Sum.inr 4866, 2), (Sum.inr 4868, 1), (Sum.inr 4875, 1), (Sum.inr 4889, 2), (Sum.inr 4890, 1), (Sum.inr 4896, 1), (Sum.inr 5411, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1), (Sum.inr 5453, 1)]

def sourceForm643 : Integer.Sparse Master := [(Sum.inr 824, 2), (Sum.inr 826, 1), (Sum.inr 831, 1), (Sum.inr 853, 1), (Sum.inr 1922, 2), (Sum.inr 1924, 2), (Sum.inr 1929, 2), (Sum.inr 1946, 2), (Sum.inr 2107, 2), (Sum.inr 2109, 1), (Sum.inr 2116, 1), (Sum.inr 2216, 2), (Sum.inr 2218, 1), (Sum.inr 2230, 1), (Sum.inr 2277, 2), (Sum.inr 2278, 1), (Sum.inr 2290, 1), (Sum.inr 3813, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 3915, 1)]

def sourceForm644 : Integer.Sparse Master := [(Sum.inr 4459, 2), (Sum.inr 4464, 1), (Sum.inr 4466, 1), (Sum.inr 4503, 1), (Sum.inr 4803, 2), (Sum.inr 4808, 2), (Sum.inr 4810, 2), (Sum.inr 4839, 2), (Sum.inr 4867, 2), (Sum.inr 4872, 1), (Sum.inr 4874, 1), (Sum.inr 4888, 2), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4894, 1), (Sum.inr 4895, 1), (Sum.inr 4898, 1), (Sum.inr 5266, 2), (Sum.inr 5293, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1)]

def sourceForm645 : Integer.Sparse Master := [(Sum.inr 1714, 2), (Sum.inr 1738, 1), (Sum.inr 1739, 1), (Sum.inr 1745, 1), (Sum.inr 2195, 2), (Sum.inr 2215, 2), (Sum.inr 2216, 2), (Sum.inr 2220, 2), (Sum.inr 2244, 2), (Sum.inr 2251, 2), (Sum.inr 2253, 2), (Sum.inr 2264, 1), (Sum.inr 2265, 1), (Sum.inr 2276, 1), (Sum.inr 2279, 1), (Sum.inr 2282, 1), (Sum.inr 2284, 1), (Sum.inr 2731, 2), (Sum.inr 2767, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1)]

def sourceForm646 : Integer.Sparse Master := [(Sum.inr 1406, 2), (Sum.inr 1408, 1), (Sum.inr 1419, 1), (Sum.inr 1442, 1), (Sum.inr 2092, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 3039, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3102, 1), (Sum.inr 3180, 2), (Sum.inr 3187, 1), (Sum.inr 3202, 2), (Sum.inr 3206, 2), (Sum.inr 3210, 2), (Sum.inr 3222, 2), (Sum.inr 3224, 1), (Sum.inr 3227, 2), (Sum.inr 3229, 1), (Sum.inr 3230, 1)]

def sourceForm647 : Integer.Sparse Master := [(Sum.inr 1042, 2), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

def sourceForm648 : Integer.Sparse Master := [(Sum.inr 4439, 1), (Sum.inr 4442, 1), (Sum.inr 4444, 1), (Sum.inr 4461, 2), (Sum.inr 4793, 1), (Sum.inr 4795, 1), (Sum.inr 4805, 2), (Sum.inr 4808, 2), (Sum.inr 4852, 2), (Sum.inr 4856, 2), (Sum.inr 4869, 2), (Sum.inr 4885, 1), (Sum.inr 4886, 1), (Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 2), (Sum.inr 4893, 2), (Sum.inr 5265, 1), (Sum.inr 5292, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

def sourceForm649 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1736, 1), (Sum.inr 1737, 2), (Sum.inr 1744, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 2), (Sum.inr 2219, 1), (Sum.inr 2220, 2), (Sum.inr 2243, 1), (Sum.inr 2250, 2), (Sum.inr 2252, 1), (Sum.inr 2262, 1), (Sum.inr 2263, 2), (Sum.inr 2274, 2), (Sum.inr 2275, 2), (Sum.inr 2277, 2), (Sum.inr 2283, 1), (Sum.inr 2730, 1), (Sum.inr 2766, 1), (Sum.inr 2773, 2), (Sum.inr 2775, 1)]

def sourceForm650 : Integer.Sparse Master := [(Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 2), (Sum.inr 3619, 1), (Sum.inr 3622, 1), (Sum.inr 4083, -1)]

def sourceForm651 : Integer.Sparse Master := [(Sum.inr 1044, 1), (Sum.inr 2023, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 2), (Sum.inr 2263, 1), (Sum.inr 4083, -1)]

def sourceForm652 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2092, 1), (Sum.inr 2094, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm653 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 2012, 1), (Sum.inr 2023, 2), (Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def sourceForm654 : Integer.Sparse Master := [(Sum.inr 1026, 1), (Sum.inr 2012, 1), (Sum.inr 2094, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

def sourceForm655 : Integer.Sparse Master := [(Sum.inr 4252, 1), (Sum.inr 4253, 1), (Sum.inr 4255, 1), (Sum.inr 4268, 2), (Sum.inr 4729, 1), (Sum.inr 4731, 1), (Sum.inr 4740, 2), (Sum.inr 4805, 2), (Sum.inr 4807, 2), (Sum.inr 4810, 2), (Sum.inr 4839, 2), (Sum.inr 4864, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 1), (Sum.inr 4890, 1), (Sum.inr 4896, 2), (Sum.inr 5406, 1), (Sum.inr 5435, 2), (Sum.inr 5450, 1), (Sum.inr 5453, 1)]

def sourceForm656 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 787, 1), (Sum.inr 789, 1), (Sum.inr 811, 2), (Sum.inr 1898, 1), (Sum.inr 1900, 1), (Sum.inr 1913, 2), (Sum.inr 2023, 2), (Sum.inr 2025, 2), (Sum.inr 2028, 2), (Sum.inr 2058, 2), (Sum.inr 2241, 1), (Sum.inr 2242, 1), (Sum.inr 2245, 1), (Sum.inr 2247, 1), (Sum.inr 2260, 2), (Sum.inr 2266, 2), (Sum.inr 3801, 1), (Sum.inr 3853, 2), (Sum.inr 3910, 1), (Sum.inr 3912, 1)]

def sourceForm657 : Integer.Sparse Master := [(Sum.inr 4473, 1), (Sum.inr 4474, 1), (Sum.inr 4475, 2), (Sum.inr 4495, 1), (Sum.inr 4815, 1), (Sum.inr 4816, 2), (Sum.inr 4831, 1), (Sum.inr 4878, 1), (Sum.inr 4879, 1), (Sum.inr 4880, 2), (Sum.inr 4885, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 2), (Sum.inr 4891, 2), (Sum.inr 4895, 2), (Sum.inr 4896, 2), (Sum.inr 4898, 2), (Sum.inr 5251, 1), (Sum.inr 5270, 1), (Sum.inr 5284, 1), (Sum.inr 5294, 2)]

def sourceForm658 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 1708, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 2), (Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 2), (Sum.inr 2233, 1), (Sum.inr 2234, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 2), (Sum.inr 2246, 1), (Sum.inr 2253, 2), (Sum.inr 2254, 2), (Sum.inr 2265, 2), (Sum.inr 2266, 2), (Sum.inr 2279, 2), (Sum.inr 2710, 1), (Sum.inr 2753, 1), (Sum.inr 2754, 1), (Sum.inr 2768, 2)]

def sourceForm659 : Integer.Sparse Master := [(Sum.inr 1366, 1), (Sum.inr 1367, 2), (Sum.inr 1370, 1), (Sum.inr 1441, 1), (Sum.inr 3064, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1), (Sum.inr 3101, 2), (Sum.inr 3155, 1), (Sum.inr 3156, 2), (Sum.inr 3158, 1), (Sum.inr 3196, 2), (Sum.inr 3197, 1), (Sum.inr 3209, 1), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 2), (Sum.inr 3224, 2), (Sum.inr 3225, 2), (Sum.inr 3227, 1), (Sum.inr 3229, 2)]

def sourceForm660 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 1057, 1), (Sum.inr 1058, 2), (Sum.inr 1079, 1), (Sum.inr 2277, 1), (Sum.inr 4084, -1)]

def sourceForm661 : Integer.Sparse Master := [(Sum.inr 4438, 1), (Sum.inr 4440, 1), (Sum.inr 4444, 1), (Sum.inr 4458, 2), (Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4802, 2), (Sum.inr 4851, 2), (Sum.inr 4853, 2), (Sum.inr 4856, 2), (Sum.inr 4866, 2), (Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4890, 1), (Sum.inr 4893, 2), (Sum.inr 4895, 2), (Sum.inr 5256, 1), (Sum.inr 5289, 2), (Sum.inr 5292, 1), (Sum.inr 5306, 1)]

def sourceForm662 : Integer.Sparse Master := [(Sum.inr 1386, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1411, 2), (Sum.inr 2471, 1), (Sum.inr 2486, 2), (Sum.inr 2755, 1), (Sum.inr 3085, 1), (Sum.inr 3097, 2), (Sum.inr 3100, 1), (Sum.inr 3120, 1), (Sum.inr 3172, 2), (Sum.inr 3174, 2), (Sum.inr 3184, 2), (Sum.inr 3199, 1), (Sum.inr 3204, 2), (Sum.inr 3223, 1), (Sum.inr 3226, 1), (Sum.inr 3227, 1), (Sum.inr 3228, 2), (Sum.inr 3229, 2)]

def sourceForm663 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 1723, 1), (Sum.inr 1724, 2), (Sum.inr 1736, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2213, 1), (Sum.inr 2240, 2), (Sum.inr 2243, 1), (Sum.inr 2259, 2), (Sum.inr 2260, 2), (Sum.inr 2262, 1), (Sum.inr 2263, 2), (Sum.inr 2274, 2), (Sum.inr 2277, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 2), (Sum.inr 2720, 1), (Sum.inr 2763, 2), (Sum.inr 2766, 1), (Sum.inr 2784, 1)]

def sourceForm664 : Integer.Sparse Master := [(Sum.inr 2244, 1), (Sum.inr 3525, 1), (Sum.inr 3572, 2), (Sum.inr 3622, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def sourceForm665 : Integer.Sparse Master := [(Sum.inr 1020, 1), (Sum.inr 1022, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 2), (Sum.inr 2244, 1), (Sum.inr 4083, -1)]

def sourceForm666 : Integer.Sparse Master := [(Sum.inr 1041, 1), (Sum.inr 2020, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 2263, 1), (Sum.inr 2265, 1), (Sum.inr 4083, -1)]

def sourceForm667 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2090, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def sourceForm668 : Integer.Sparse Master := [(Sum.inr 1020, 1), (Sum.inr 2088, 2), (Sum.inr 2243, 1), (Sum.inr 2244, 2), (Sum.inr 4083, -1)]

def sourceForm669 : Integer.Sparse Master := [(Sum.inr 4249, 1), (Sum.inr 4251, 1), (Sum.inr 4256, 1), (Sum.inr 4265, 2), (Sum.inr 4728, 1), (Sum.inr 4732, 1), (Sum.inr 4737, 2), (Sum.inr 4802, 2), (Sum.inr 4804, 2), (Sum.inr 4811, 2), (Sum.inr 4831, 1), (Sum.inr 4832, 1), (Sum.inr 4835, 4), (Sum.inr 4887, 1), (Sum.inr 4888, 3), (Sum.inr 5405, 1), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1)]

def sourceForm670 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 785, 1), (Sum.inr 790, 1), (Sum.inr 807, 2), (Sum.inr 1897, 1), (Sum.inr 1901, 1), (Sum.inr 1909, 2), (Sum.inr 2020, 2), (Sum.inr 2022, 2), (Sum.inr 2029, 2), (Sum.inr 2054, 2), (Sum.inr 2191, 1), (Sum.inr 2193, 1), (Sum.inr 2206, 2), (Sum.inr 2243, 1), (Sum.inr 2244, 1), (Sum.inr 2262, 2), (Sum.inr 3800, 1), (Sum.inr 3852, 2), (Sum.inr 3902, 1), (Sum.inr 3911, 1)]

def sourceForm671 : Integer.Sparse Master := [(Sum.inr 4455, 1), (Sum.inr 4457, 1), (Sum.inr 4459, 2), (Sum.inr 4495, 1), (Sum.inr 4801, 1), (Sum.inr 4803, 2), (Sum.inr 4831, 1), (Sum.inr 4863, 1), (Sum.inr 4865, 1), (Sum.inr 4867, 2), (Sum.inr 4885, 1), (Sum.inr 4888, 2), (Sum.inr 4889, 1), (Sum.inr 4891, 2), (Sum.inr 4894, 2), (Sum.inr 4895, 2), (Sum.inr 4896, 2), (Sum.inr 5250, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5293, 2)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm672 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1707, 1), (Sum.inr 1708, 1), (Sum.inr 1714, 2), (Sum.inr 2190, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 2), (Sum.inr 2232, 1), (Sum.inr 2233, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 2), (Sum.inr 2245, 1), (Sum.inr 2251, 2), (Sum.inr 2253, 2), (Sum.inr 2264, 2), (Sum.inr 2265, 2), (Sum.inr 2278, 2), (Sum.inr 2709, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2767, 2)]

def sourceForm673 : Integer.Sparse Master := [(Sum.inr 1405, 1), (Sum.inr 1406, 2), (Sum.inr 1414, 1), (Sum.inr 1441, 1), (Sum.inr 3065, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 3102, 2), (Sum.inr 3179, 1), (Sum.inr 3180, 2), (Sum.inr 3185, 1), (Sum.inr 3202, 2), (Sum.inr 3205, 1), (Sum.inr 3209, 1), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 1), (Sum.inr 3225, 2), (Sum.inr 3227, 2), (Sum.inr 3229, 2), (Sum.inr 3230, 2)]

def sourceForm674 : Integer.Sparse Master := [(Sum.inr 1038, 1), (Sum.inr 1040, 1), (Sum.inr 1042, 2), (Sum.inr 1079, 1), (Sum.inr 2262, 1), (Sum.inr 4084, -1)]

def sourceForm675 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4458, 2), (Sum.inr 4463, 1), (Sum.inr 4467, 1), (Sum.inr 4502, 1), (Sum.inr 4802, 2), (Sum.inr 4807, 2), (Sum.inr 4811, 2), (Sum.inr 4838, 2), (Sum.inr 4866, 2), (Sum.inr 4871, 1), (Sum.inr 4875, 1), (Sum.inr 4888, 2), (Sum.inr 4890, 1), (Sum.inr 4893, 2), (Sum.inr 4895, 2), (Sum.inr 5271, 2), (Sum.inr 5304, 1), (Sum.inr 5306, 1), (Sum.inr 5307, 1)]

def sourceForm676 : Integer.Sparse Master := [(Sum.inr 1724, 2), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 1753, 1), (Sum.inr 2202, 2), (Sum.inr 2224, 2), (Sum.inr 2225, 2), (Sum.inr 2227, 2), (Sum.inr 2260, 2), (Sum.inr 2262, 2), (Sum.inr 2263, 2), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 2), (Sum.inr 2739, 2), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 2785, 1), (Sum.inr 4083, 1)]

def sourceForm677 : Integer.Sparse Master := [(Sum.inr 2107, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 2265, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def sourceForm678 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4503, 1), (Sum.inr 4831, 2), (Sum.inr 4834, 2), (Sum.inr 4835, 2), (Sum.inr 4839, 2), (Sum.inr 4888, 2), (Sum.inr 4889, 2), (Sum.inr 4894, 1), (Sum.inr 4895, 2), (Sum.inr 4896, 2), (Sum.inr 4898, 1), (Sum.inr 4901, 1), (Sum.inr 5259, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5309, 1)]

def sourceForm679 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4457, 2), (Sum.inr 4460, 1), (Sum.inr 4466, 1), (Sum.inr 4498, 1), (Sum.inr 4801, 2), (Sum.inr 4804, 2), (Sum.inr 4810, 2), (Sum.inr 4834, 2), (Sum.inr 4865, 2), (Sum.inr 4868, 1), (Sum.inr 4874, 1), (Sum.inr 4888, 2), (Sum.inr 4894, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4897, 1), (Sum.inr 5258, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5308, 1)]

def sourceForm680 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4499, 3), (Sum.inr 4507, 1), (Sum.inr 4511, 1), (Sum.inr 4835, 6), (Sum.inr 4843, 3), (Sum.inr 4846, 3), (Sum.inr 4895, 3), (Sum.inr 4896, 3), (Sum.inr 4899, 1), (Sum.inr 5275, 3), (Sum.inr 5309, 1), (Sum.inr 5310, 1)]

def sourceForm681 : Integer.Sparse Master := [(Sum.inr 4069, 3), (Sum.inr 4070, 1), (Sum.inr 4071, 1), (Sum.inr 4080, 6), (Sum.inr 4081, 3), (Sum.inr 4082, 3), (Sum.inr 4083, 3), (Sum.inr 4084, 4), (Sum.inr 4085, 1), (Sum.inr 4092, 3), (Sum.inr 4093, 1), (Sum.inr 4094, 1)]

def sourceForm683 : Integer.Sparse Master := [(Sum.inr 1210, 2), (Sum.inr 1216, 1), (Sum.inr 1228, 1), (Sum.inr 1260, 1), (Sum.inr 2860, 2), (Sum.inr 2864, 1), (Sum.inr 2874, 1), (Sum.inr 2984, 2), (Sum.inr 2988, 1), (Sum.inr 2996, 1), (Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 3037, 1), (Sum.inr 3086, 2), (Sum.inr 3089, 2), (Sum.inr 3097, 2), (Sum.inr 3109, 2), (Sum.inr 3801, 1), (Sum.inr 3954, 1), (Sum.inr 3977, 1), (Sum.inr 3982, 2)]

def sourceForm684 : Integer.Sparse Master := [(Sum.inr 3285, 2), (Sum.inr 3286, 1), (Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3459, 1), (Sum.inr 3460, 1), (Sum.inr 3463, 2), (Sum.inr 3524, 1), (Sum.inr 3526, 1), (Sum.inr 3527, 2), (Sum.inr 3528, 2), (Sum.inr 3533, 2), (Sum.inr 3534, 2), (Sum.inr 3540, 2), (Sum.inr 3566, 1), (Sum.inr 3567, 1), (Sum.inr 3572, 2), (Sum.inr 3800, 1), (Sum.inr 3846, 1), (Sum.inr 3847, 1), (Sum.inr 3852, 2)]

def sourceForm685 : Integer.Sparse Master := [(Sum.inr 2720, 1), (Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 3874, 1), (Sum.inr 3903, 2), (Sum.inr 4092, -1)]

def sourceForm686 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1214, 2), (Sum.inr 1233, 1), (Sum.inr 1259, 1), (Sum.inr 2720, 1), (Sum.inr 4092, -1)]

def sourceForm687 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 2630, 1), (Sum.inr 2720, 1), (Sum.inr 2757, 1), (Sum.inr 2763, 2), (Sum.inr 4092, -1)]

def sourceForm688 : Integer.Sparse Master := [(Sum.inr 2479, 1), (Sum.inr 2481, 2), (Sum.inr 2508, 1), (Sum.inr 2720, 1), (Sum.inr 3805, 1), (Sum.inr 4092, -1)]

def sourceForm689 : Integer.Sparse Master := [(Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 2720, 1), (Sum.inr 2730, 1), (Sum.inr 2739, 2), (Sum.inr 4092, -1)]

def sourceForm690 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 2616, 2), (Sum.inr 2630, 1), (Sum.inr 2720, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

def sourceForm691 : Integer.Sparse Master := [(Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4802, 2), (Sum.inr 4888, 1), (Sum.inr 5066, 1), (Sum.inr 5077, 2), (Sum.inr 5226, 2), (Sum.inr 5230, 1), (Sum.inr 5255, 4), (Sum.inr 5257, 3), (Sum.inr 5262, 2), (Sum.inr 5263, 1), (Sum.inr 5265, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 2), (Sum.inr 5289, 2), (Sum.inr 5290, 1), (Sum.inr 5292, 1), (Sum.inr 5306, 1)]

def sourceForm692 : Integer.Sparse Master := [(Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2213, 1), (Sum.inr 2262, 1), (Sum.inr 2668, 1), (Sum.inr 2669, 2), (Sum.inr 2675, 1), (Sum.inr 2717, 2), (Sum.inr 2718, 2), (Sum.inr 2721, 2), (Sum.inr 2727, 2), (Sum.inr 2730, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 2), (Sum.inr 2763, 2), (Sum.inr 2766, 1), (Sum.inr 2784, 1), (Sum.inr 3036, 1), (Sum.inr 3084, 2), (Sum.inr 3087, 1), (Sum.inr 3099, 1)]

def sourceForm693 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 2472, 1), (Sum.inr 2484, 2), (Sum.inr 2718, 2), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2754, 1), (Sum.inr 2764, 1), (Sum.inr 3034, 2), (Sum.inr 3037, 1), (Sum.inr 3041, 1), (Sum.inr 3084, 2), (Sum.inr 3087, 2), (Sum.inr 3091, 2), (Sum.inr 3097, 2), (Sum.inr 3100, 1), (Sum.inr 3109, 2), (Sum.inr 3120, 1), (Sum.inr 3199, 1), (Sum.inr 3204, 2), (Sum.inr 3227, 1)]

def sourceForm694 : Integer.Sparse Master := [(Sum.inr 3503, 2), (Sum.inr 3505, 1), (Sum.inr 3525, 1), (Sum.inr 3532, 1), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

def sourceForm695 : Integer.Sparse Master := [(Sum.inr 2980, 1), (Sum.inr 3373, 1), (Sum.inr 3376, 2), (Sum.inr 3505, 1), (Sum.inr 3525, 1), (Sum.inr 4083, -1)]

def sourceForm696 : Integer.Sparse Master := [(Sum.inr 2012, 1), (Sum.inr 3373, 1), (Sum.inr 3500, 2), (Sum.inr 3525, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def sourceForm697 : Integer.Sparse Master := [(Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 3503, 1), (Sum.inr 3525, 1), (Sum.inr 3532, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

def sourceForm698 : Integer.Sparse Master := [(Sum.inr 2983, 1), (Sum.inr 3500, 1), (Sum.inr 3503, 2), (Sum.inr 3525, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def sourceForm700 : Integer.Sparse Master := [(Sum.inr 1178, 2), (Sum.inr 1180, 1), (Sum.inr 1183, 1), (Sum.inr 1260, 1), (Sum.inr 2833, 2), (Sum.inr 2834, 1), (Sum.inr 2836, 1), (Sum.inr 2974, 2), (Sum.inr 2976, 1), (Sum.inr 2996, 1), (Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 3038, 2), (Sum.inr 3039, 2), (Sum.inr 3051, 2), (Sum.inr 3085, 1), (Sum.inr 3109, 2), (Sum.inr 3526, 1), (Sum.inr 3801, 1), (Sum.inr 3847, 1), (Sum.inr 3853, 2)]

def sourceForm701 : Integer.Sparse Master := [(Sum.inr 2833, 2), (Sum.inr 2834, 1), (Sum.inr 2836, 1), (Sum.inr 3037, 1), (Sum.inr 3238, 2), (Sum.inr 3239, 1), (Sum.inr 3241, 1), (Sum.inr 3289, 1), (Sum.inr 3460, 1), (Sum.inr 3461, 1), (Sum.inr 3464, 2), (Sum.inr 3525, 1), (Sum.inr 3528, 2), (Sum.inr 3534, 2), (Sum.inr 3535, 2), (Sum.inr 3541, 2), (Sum.inr 3567, 1), (Sum.inr 3573, 2), (Sum.inr 3801, 1), (Sum.inr 3847, 1), (Sum.inr 3853, 2)]

def sourceForm702 : Integer.Sparse Master := [(Sum.inr 2730, 2), (Sum.inr 3812, 2), (Sum.inr 3906, 2), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm704 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2757, 1), (Sum.inr 2773, 2), (Sum.inr 4092, -1)]

def sourceForm705 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2494, 2), (Sum.inr 2508, 1), (Sum.inr 2730, 1), (Sum.inr 3812, 1), (Sum.inr 4092, -1)]

def sourceForm706 : Integer.Sparse Master := [(Sum.inr 4406, 1), (Sum.inr 4407, 2), (Sum.inr 4414, 1), (Sum.inr 4473, 1), (Sum.inr 5004, 1), (Sum.inr 5005, 2), (Sum.inr 5011, 1), (Sum.inr 5150, 2), (Sum.inr 5184, 1), (Sum.inr 5185, 2), (Sum.inr 5202, 1), (Sum.inr 5243, 2), (Sum.inr 5244, 2), (Sum.inr 5265, 2), (Sum.inr 5266, 2), (Sum.inr 5270, 1), (Sum.inr 5301, 1), (Sum.inr 5429, 1), (Sum.inr 5431, 2), (Sum.inr 5450, 1), (Sum.inr 5472, 1)]

def sourceForm707 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 988, 2), (Sum.inr 995, 1), (Sum.inr 1056, 1), (Sum.inr 2389, 1), (Sum.inr 2390, 2), (Sum.inr 2396, 1), (Sum.inr 2614, 1), (Sum.inr 2615, 2), (Sum.inr 2636, 1), (Sum.inr 2697, 2), (Sum.inr 2698, 2), (Sum.inr 2700, 2), (Sum.inr 2730, 2), (Sum.inr 2731, 2), (Sum.inr 2738, 1), (Sum.inr 2775, 1), (Sum.inr 3874, 1), (Sum.inr 3875, 2), (Sum.inr 3887, 1), (Sum.inr 4002, 1)]

def sourceForm708 : Integer.Sparse Master := [(Sum.inr 1593, 1), (Sum.inr 1594, 1), (Sum.inr 1601, 2), (Sum.inr 1699, 1), (Sum.inr 2912, 1), (Sum.inr 2923, 2), (Sum.inr 3075, 1), (Sum.inr 3337, 1), (Sum.inr 3342, 2), (Sum.inr 3488, 2), (Sum.inr 3497, 2), (Sum.inr 3524, 1), (Sum.inr 3526, 2), (Sum.inr 3529, 2), (Sum.inr 3535, 2), (Sum.inr 3617, 1), (Sum.inr 3619, 1), (Sum.inr 3954, 1), (Sum.inr 3957, 1), (Sum.inr 4026, 2), (Sum.inr 4029, 1)]

def sourceForm709 : Integer.Sparse Master := [(Sum.inr 3037, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 2), (Sum.inr 3910, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def sourceForm710 : Integer.Sparse Master := [(Sum.inr 1358, 2), (Sum.inr 1360, 1), (Sum.inr 1366, 1), (Sum.inr 1421, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

def sourceForm711 : Integer.Sparse Master := [(Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 3), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

def sourceForm713 : Integer.Sparse Master := [(Sum.inr 2862, 2), (Sum.inr 2864, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def sourceForm714 : Integer.Sparse Master := [(Sum.inr 2573, 1), (Sum.inr 3029, 1), (Sum.inr 3030, 1), (Sum.inr 3037, 2), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

def sourceForm715 : Integer.Sparse Master := [(Sum.inr 4793, 1), (Sum.inr 4794, 1), (Sum.inr 4795, 1), (Sum.inr 4805, 2), (Sum.inr 4806, 2), (Sum.inr 4878, 1), (Sum.inr 4889, 1), (Sum.inr 5226, 2), (Sum.inr 5227, 1), (Sum.inr 5230, 1), (Sum.inr 5231, 3), (Sum.inr 5256, 1), (Sum.inr 5257, 3), (Sum.inr 5262, 2), (Sum.inr 5263, 2), (Sum.inr 5265, 2), (Sum.inr 5292, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

def sourceForm716 : Integer.Sparse Master := [(Sum.inr 2117, 1), (Sum.inr 2118, 2), (Sum.inr 2131, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 2), (Sum.inr 2219, 1), (Sum.inr 2277, 1), (Sum.inr 2675, 1), (Sum.inr 2676, 2), (Sum.inr 2720, 1), (Sum.inr 2721, 2), (Sum.inr 2727, 2), (Sum.inr 2728, 2), (Sum.inr 2730, 2), (Sum.inr 2766, 1), (Sum.inr 2773, 2), (Sum.inr 2775, 1), (Sum.inr 3043, 1), (Sum.inr 3087, 1), (Sum.inr 3091, 2), (Sum.inr 3093, 1)]

def sourceForm717 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 2011, 1), (Sum.inr 2024, 2), (Sum.inr 2234, 1), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2676, 1), (Sum.inr 2721, 1), (Sum.inr 3034, 2), (Sum.inr 3036, 2), (Sum.inr 3037, 2), (Sum.inr 3041, 1), (Sum.inr 3043, 2), (Sum.inr 3051, 2), (Sum.inr 3053, 1), (Sum.inr 3085, 1), (Sum.inr 3087, 2), (Sum.inr 3100, 1), (Sum.inr 3199, 1), (Sum.inr 3203, 2), (Sum.inr 3223, 1)]

def sourceForm718 : Integer.Sparse Master := [(Sum.inr 3376, 2), (Sum.inr 3378, 1), (Sum.inr 3390, 1), (Sum.inr 3526, 1), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

def sourceForm719 : Integer.Sparse Master := [(Sum.inr 3150, 1), (Sum.inr 3373, 1), (Sum.inr 3378, 3), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def sourceForm720 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 3149, 2), (Sum.inr 3150, 1), (Sum.inr 3155, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def sourceForm721 : Integer.Sparse Master := [(Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 2), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

def sourceForm722 : Integer.Sparse Master := [(Sum.inr 3149, 1), (Sum.inr 3376, 1), (Sum.inr 3500, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm723 : Integer.Sparse Master := [(Sum.inr 4618, 2), (Sum.inr 4619, 2), (Sum.inr 4623, 1), (Sum.inr 5166, 2), (Sum.inr 5168, 2), (Sum.inr 5170, 4), (Sum.inr 5301, 2), (Sum.inr 5302, 2), (Sum.inr 5306, 4), (Sum.inr 5308, 2), (Sum.inr 5310, 2), (Sum.inr 5439, 2), (Sum.inr 5453, 1), (Sum.inr 5455, 2)]

def sourceForm724 : Integer.Sparse Master := [(Sum.inr 1293, 2), (Sum.inr 1294, 2), (Sum.inr 1305, 1), (Sum.inr 2953, 2), (Sum.inr 2954, 4), (Sum.inr 2963, 2), (Sum.inr 3053, 2), (Sum.inr 3054, 2), (Sum.inr 3120, 4), (Sum.inr 3121, 2), (Sum.inr 3124, 2), (Sum.inr 3912, 1), (Sum.inr 4012, 2), (Sum.inr 4019, 2)]

def sourceForm725 : Integer.Sparse Master := [(Sum.inr 4495, 2), (Sum.inr 4496, 1), (Sum.inr 4499, 2), (Sum.inr 5098, 2), (Sum.inr 5099, 2), (Sum.inr 5102, 4), (Sum.inr 5271, 4), (Sum.inr 5272, 2), (Sum.inr 5275, 2), (Sum.inr 5292, 2), (Sum.inr 5293, 2), (Sum.inr 5485, 2), (Sum.inr 5492, 2), (Sum.inr 5493, 1)]

def sourceForm726 : Integer.Sparse Master := [(Sum.inr 1079, 2), (Sum.inr 1080, 1), (Sum.inr 1083, 2), (Sum.inr 2508, 2), (Sum.inr 2509, 2), (Sum.inr 2512, 4), (Sum.inr 2739, 4), (Sum.inr 2740, 2), (Sum.inr 2743, 2), (Sum.inr 2766, 2), (Sum.inr 2767, 2), (Sum.inr 3984, 2), (Sum.inr 4015, 2), (Sum.inr 4018, 1)]

def sourceForm727 : Integer.Sparse Master := [(Sum.inr 4888, 2), (Sum.inr 4890, 1), (Sum.inr 4895, 2), (Sum.inr 5256, 2), (Sum.inr 5270, 2), (Sum.inr 5271, 4), (Sum.inr 5289, 4), (Sum.inr 5290, 2), (Sum.inr 5292, 2), (Sum.inr 5295, 2), (Sum.inr 5304, 4), (Sum.inr 5307, 3)]

def sourceForm728 : Integer.Sparse Master := [(Sum.inr 2754, 2), (Sum.inr 2755, 1), (Sum.inr 2764, 2), (Sum.inr 2769, 2), (Sum.inr 2782, 2), (Sum.inr 2785, 1), (Sum.inr 3085, 2), (Sum.inr 3097, 4), (Sum.inr 3100, 2), (Sum.inr 3109, 4), (Sum.inr 3119, 2), (Sum.inr 3122, 2), (Sum.inr 3227, 2), (Sum.inr 3229, 2)]

def sourceForm729 : Integer.Sparse Master := [(Sum.inr 3581, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 3628, 1), (Sum.inr 4083, -1)]

def sourceForm731 : Integer.Sparse Master := [(Sum.inr 1228, 1), (Sum.inr 1229, 1), (Sum.inr 1230, 1), (Sum.inr 1241, 1), (Sum.inr 1291, 1), (Sum.inr 2874, 1), (Sum.inr 2875, 1), (Sum.inr 2876, 1), (Sum.inr 2885, 1), (Sum.inr 2921, 1), (Sum.inr 2922, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3023, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3051, 1), (Sum.inr 3085, 1), (Sum.inr 3086, 1), (Sum.inr 3089, 1), (Sum.inr 3097, 1), (Sum.inr 3098, 1), (Sum.inr 3103, 1), (Sum.inr 3109, 1), (Sum.inr 3119, 1), (Sum.inr 3809, 1), (Sum.inr 3959, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1)]

def sourceForm732 : Integer.Sparse Master := [(Sum.inr 2500, 1), (Sum.inr 2502, 1), (Sum.inr 2506, 1), (Sum.inr 2513, 1), (Sum.inr 2781, 1), (Sum.inr 3286, 1), (Sum.inr 3287, 1), (Sum.inr 3296, 1), (Sum.inr 3303, 1), (Sum.inr 3525, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3540, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3560, 1), (Sum.inr 3566, 1), (Sum.inr 3567, 1), (Sum.inr 3570, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 3575, 1), (Sum.inr 3577, 1), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3852, 1), (Sum.inr 3871, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3888, 1)]

def sourceForm733 : Integer.Sparse Master := [(Sum.inr 2763, 1), (Sum.inr 3813, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 3903, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def sourceForm734 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 1261, 1), (Sum.inr 1263, 1), (Sum.inr 1268, 1), (Sum.inr 1291, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

def sourceForm735 : Integer.Sparse Master := [(Sum.inr 2566, 1), (Sum.inr 2568, 1), (Sum.inr 2571, 1), (Sum.inr 2587, 1), (Sum.inr 2763, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm736 : Integer.Sparse Master := [(Sum.inr 1291, 1), (Sum.inr 2587, 1), (Sum.inr 2739, 1), (Sum.inr 2763, 1), (Sum.inr 2773, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

def sourceForm737 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2632, 1), (Sum.inr 2634, 1), (Sum.inr 2639, 1), (Sum.inr 2763, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def sourceForm738 : Integer.Sparse Master := [(Sum.inr 4449, 1), (Sum.inr 4450, 1), (Sum.inr 4453, 1), (Sum.inr 4459, 1), (Sum.inr 4487, 1), (Sum.inr 5069, 1), (Sum.inr 5071, 1), (Sum.inr 5074, 1), (Sum.inr 5092, 1), (Sum.inr 5140, 1), (Sum.inr 5160, 1), (Sum.inr 5161, 2), (Sum.inr 5164, 1), (Sum.inr 5170, 1), (Sum.inr 5226, 1), (Sum.inr 5229, 1), (Sum.inr 5236, 1), (Sum.inr 5255, 1), (Sum.inr 5260, 1), (Sum.inr 5269, 1), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 1), (Sum.inr 5438, 1), (Sum.inr 5480, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1)]

def sourceForm739 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 1033, 1), (Sum.inr 1036, 1), (Sum.inr 1042, 1), (Sum.inr 1071, 1), (Sum.inr 2476, 1), (Sum.inr 2478, 1), (Sum.inr 2481, 1), (Sum.inr 2501, 1), (Sum.inr 2587, 1), (Sum.inr 2588, 1), (Sum.inr 2591, 1), (Sum.inr 2596, 1), (Sum.inr 2669, 1), (Sum.inr 2670, 1), (Sum.inr 2673, 1), (Sum.inr 2682, 1), (Sum.inr 2718, 1), (Sum.inr 2719, 1), (Sum.inr 2724, 1), (Sum.inr 2736, 1), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 1), (Sum.inr 3857, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1)]

def sourceForm740 : Integer.Sparse Master := [(Sum.inr 1636, 1), (Sum.inr 1637, 1), (Sum.inr 1641, 1), (Sum.inr 1646, 1), (Sum.inr 1714, 1), (Sum.inr 2550, 1), (Sum.inr 2560, 1), (Sum.inr 2588, 1), (Sum.inr 2719, 1), (Sum.inr 3376, 1), (Sum.inr 3380, 1), (Sum.inr 3392, 1), (Sum.inr 3442, 1), (Sum.inr 3445, 1), (Sum.inr 3463, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3540, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 1), (Sum.inr 3580, 1), (Sum.inr 3606, 1), (Sum.inr 3625, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3993, 1), (Sum.inr 3997, 1)]

def sourceForm741 : Integer.Sparse Master := [(Sum.inr 3097, 1), (Sum.inr 3876, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def sourceForm743 : Integer.Sparse Master := [(Sum.inr 1403, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3084, 1), (Sum.inr 3091, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

def sourceForm746 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 2964, 1), (Sum.inr 3097, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def sourceForm747 : Integer.Sparse Master := [(Sum.inr 2942, 1), (Sum.inr 3091, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 3115, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def sourceForm749 : Integer.Sparse Master := [(Sum.inr 2240, 1), (Sum.inr 2259, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2274, 1), (Sum.inr 2583, 1), (Sum.inr 2584, 1), (Sum.inr 2585, 1), (Sum.inr 2600, 1), (Sum.inr 2717, 1), (Sum.inr 2718, 1), (Sum.inr 2720, 1), (Sum.inr 2727, 1), (Sum.inr 2749, 1), (Sum.inr 2750, 1), (Sum.inr 2760, 1), (Sum.inr 2762, 1), (Sum.inr 2763, 2), (Sum.inr 2764, 1), (Sum.inr 2766, 1), (Sum.inr 2772, 1), (Sum.inr 2773, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 3084, 1), (Sum.inr 3108, 1), (Sum.inr 3109, 1), (Sum.inr 3119, 1)]

def sourceForm751 : Integer.Sparse Master := [(Sum.inr 2952, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3534, 1), (Sum.inr 3572, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def sourceForm752 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2950, 1), (Sum.inr 3550, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

def sourceForm753 : Integer.Sparse Master := [(Sum.inr 2094, 1), (Sum.inr 2956, 1), (Sum.inr 3500, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm754 : Integer.Sparse Master := [(Sum.inr 2950, 1), (Sum.inr 2952, 1), (Sum.inr 2956, 1), (Sum.inr 2962, 1), (Sum.inr 3096, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def sourceForm755 : Integer.Sparse Master := [(Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 3503, 1), (Sum.inr 3572, 1), (Sum.inr 3581, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def sourceForm756 : Integer.Sparse Master := [(Sum.inr 2995, 1), (Sum.inr 3507, 1), (Sum.inr 3550, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

def sourceForm757 : Integer.Sparse Master := [(Sum.inr 4601, 1), (Sum.inr 4602, 2), (Sum.inr 4606, 1), (Sum.inr 4622, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 2), (Sum.inr 5167, 1), (Sum.inr 5202, 1), (Sum.inr 5203, 1), (Sum.inr 5204, 2), (Sum.inr 5283, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 3), (Sum.inr 5293, 2), (Sum.inr 5294, 2), (Sum.inr 5307, 2), (Sum.inr 5433, 1), (Sum.inr 5450, 1), (Sum.inr 5452, 1), (Sum.inr 5454, 2)]

def sourceForm758 : Integer.Sparse Master := [(Sum.inr 1235, 1), (Sum.inr 1236, 2), (Sum.inr 1240, 1), (Sum.inr 1299, 1), (Sum.inr 2880, 1), (Sum.inr 2881, 2), (Sum.inr 2884, 1), (Sum.inr 2924, 2), (Sum.inr 2927, 1), (Sum.inr 2958, 1), (Sum.inr 3076, 1), (Sum.inr 3077, 2), (Sum.inr 3100, 3), (Sum.inr 3101, 2), (Sum.inr 3102, 2), (Sum.inr 3122, 2), (Sum.inr 4029, 1), (Sum.inr 4033, 1), (Sum.inr 4039, 1), (Sum.inr 4040, 2)]

def sourceForm759 : Integer.Sparse Master := [(Sum.inr 4456, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4495, 1), (Sum.inr 5072, 1), (Sum.inr 5073, 2), (Sum.inr 5098, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5257, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5271, 2), (Sum.inr 5292, 1), (Sum.inr 5293, 2), (Sum.inr 5306, 1), (Sum.inr 5482, 1), (Sum.inr 5486, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1)]

def sourceForm760 : Integer.Sparse Master := [(Sum.inr 1039, 1), (Sum.inr 1040, 1), (Sum.inr 1041, 2), (Sum.inr 1079, 1), (Sum.inr 2479, 1), (Sum.inr 2480, 2), (Sum.inr 2508, 1), (Sum.inr 2593, 1), (Sum.inr 2594, 1), (Sum.inr 2595, 2), (Sum.inr 2721, 2), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2739, 2), (Sum.inr 2766, 1), (Sum.inr 2767, 2), (Sum.inr 2784, 1), (Sum.inr 3980, 1), (Sum.inr 3999, 1), (Sum.inr 4013, 2), (Sum.inr 4018, 1)]

def sourceForm761 : Integer.Sparse Master := [(Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4893, 2), (Sum.inr 5256, 1), (Sum.inr 5257, 3), (Sum.inr 5265, 1), (Sum.inr 5271, 2), (Sum.inr 5273, 1), (Sum.inr 5281, 2), (Sum.inr 5283, 1), (Sum.inr 5289, 2), (Sum.inr 5290, 2), (Sum.inr 5292, 3), (Sum.inr 5299, 2), (Sum.inr 5301, 1), (Sum.inr 5306, 1), (Sum.inr 5307, 3)]

def sourceForm762 : Integer.Sparse Master := [(Sum.inr 3532, 1), (Sum.inr 3534, 2), (Sum.inr 3546, 1), (Sum.inr 3622, 1), (Sum.inr 3628, 1), (Sum.inr 4083, -1)]

def sourceForm763 : Integer.Sparse Master := [(Sum.inr 2243, 1), (Sum.inr 3571, 2), (Sum.inr 3618, 1), (Sum.inr 3622, 2), (Sum.inr 4083, -1)]

def sourceForm765 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 1184, 1), (Sum.inr 1185, 1), (Sum.inr 1189, 1), (Sum.inr 1291, 1), (Sum.inr 2836, 1), (Sum.inr 2837, 1), (Sum.inr 2838, 1), (Sum.inr 2841, 1), (Sum.inr 2906, 1), (Sum.inr 2907, 1), (Sum.inr 2909, 1), (Sum.inr 2951, 1), (Sum.inr 3023, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3037, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3051, 1), (Sum.inr 3052, 1), (Sum.inr 3055, 1), (Sum.inr 3097, 1), (Sum.inr 3109, 1), (Sum.inr 3119, 1), (Sum.inr 3535, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1)]

def sourceForm766 : Integer.Sparse Master := [(Sum.inr 2463, 1), (Sum.inr 2465, 1), (Sum.inr 2466, 1), (Sum.inr 2513, 1), (Sum.inr 2744, 1), (Sum.inr 2834, 1), (Sum.inr 2835, 1), (Sum.inr 2841, 1), (Sum.inr 3039, 1), (Sum.inr 3239, 1), (Sum.inr 3240, 1), (Sum.inr 3246, 1), (Sum.inr 3303, 1), (Sum.inr 3526, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3558, 1), (Sum.inr 3559, 1), (Sum.inr 3561, 1), (Sum.inr 3567, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 3577, 1), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3853, 1), (Sum.inr 3872, 1), (Sum.inr 3883, 1), (Sum.inr 3889, 1)]

def sourceForm767 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 1277, 1), (Sum.inr 1278, 1), (Sum.inr 1280, 1), (Sum.inr 1291, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm768 : Integer.Sparse Master := [(Sum.inr 4469, 1), (Sum.inr 4470, 1), (Sum.inr 4471, 1), (Sum.inr 4475, 1), (Sum.inr 4486, 1), (Sum.inr 5082, 1), (Sum.inr 5083, 1), (Sum.inr 5086, 1), (Sum.inr 5091, 1), (Sum.inr 5151, 1), (Sum.inr 5173, 1), (Sum.inr 5197, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5204, 1), (Sum.inr 5231, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5263, 1), (Sum.inr 5264, 1), (Sum.inr 5267, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5438, 1), (Sum.inr 5451, 1), (Sum.inr 5473, 1)]

def sourceForm769 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 1053, 1), (Sum.inr 1054, 1), (Sum.inr 1058, 1), (Sum.inr 1070, 1), (Sum.inr 2490, 1), (Sum.inr 2491, 1), (Sum.inr 2494, 1), (Sum.inr 2500, 1), (Sum.inr 2631, 1), (Sum.inr 2632, 1), (Sum.inr 2633, 1), (Sum.inr 2638, 1), (Sum.inr 2676, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2681, 1), (Sum.inr 2728, 1), (Sum.inr 2729, 1), (Sum.inr 2732, 1), (Sum.inr 2735, 1), (Sum.inr 2773, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 2781, 1), (Sum.inr 3850, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3888, 1), (Sum.inr 3995, 1)]

def sourceForm770 : Integer.Sparse Master := [(Sum.inr 1638, 1), (Sum.inr 1639, 1), (Sum.inr 1640, 1), (Sum.inr 1649, 1), (Sum.inr 1715, 1), (Sum.inr 2921, 1), (Sum.inr 2930, 1), (Sum.inr 2952, 1), (Sum.inr 3098, 1), (Sum.inr 3378, 1), (Sum.inr 3379, 1), (Sum.inr 3395, 1), (Sum.inr 3441, 1), (Sum.inr 3447, 1), (Sum.inr 3464, 1), (Sum.inr 3505, 1), (Sum.inr 3506, 1), (Sum.inr 3541, 1), (Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3584, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3958, 1), (Sum.inr 3972, 1), (Sum.inr 3987, 1), (Sum.inr 3993, 1), (Sum.inr 4027, 1)]

def sourceForm771 : Integer.Sparse Master := [(Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 3850, 1), (Sum.inr 3857, 1), (Sum.inr 3913, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

def sourceForm772 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 1367, 1), (Sum.inr 1368, 1), (Sum.inr 1371, 1), (Sum.inr 1433, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

def sourceForm773 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 2878, 1), (Sum.inr 3036, 1), (Sum.inr 3043, 1), (Sum.inr 3051, 2), (Sum.inr 4092, -1)]

def sourceForm774 : Integer.Sparse Master := [(Sum.inr 2571, 1), (Sum.inr 2974, 1), (Sum.inr 2975, 1), (Sum.inr 2977, 1), (Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

def sourceForm775 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 2881, 1), (Sum.inr 2882, 1), (Sum.inr 2885, 1), (Sum.inr 3051, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

def sourceForm776 : Integer.Sparse Master := [(Sum.inr 2575, 1), (Sum.inr 3043, 1), (Sum.inr 3044, 1), (Sum.inr 3045, 1), (Sum.inr 3051, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

def sourceForm778 : Integer.Sparse Master := [(Sum.inr 2118, 1), (Sum.inr 2119, 1), (Sum.inr 2123, 1), (Sum.inr 2132, 1), (Sum.inr 2220, 1), (Sum.inr 2250, 1), (Sum.inr 2274, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 1), (Sum.inr 2565, 1), (Sum.inr 2575, 1), (Sum.inr 2585, 1), (Sum.inr 2727, 1), (Sum.inr 2728, 1), (Sum.inr 2730, 1), (Sum.inr 2748, 1), (Sum.inr 2750, 1), (Sum.inr 2756, 1), (Sum.inr 2757, 1), (Sum.inr 2763, 1), (Sum.inr 2764, 1), (Sum.inr 2766, 1), (Sum.inr 2772, 1), (Sum.inr 2773, 2), (Sum.inr 2775, 1), (Sum.inr 3091, 1), (Sum.inr 3109, 1), (Sum.inr 3115, 1), (Sum.inr 3116, 1)]

def sourceForm780 : Integer.Sparse Master := [(Sum.inr 2930, 1), (Sum.inr 3376, 1), (Sum.inr 3380, 1), (Sum.inr 3394, 1), (Sum.inr 3534, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm781 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2926, 1), (Sum.inr 3551, 1), (Sum.inr 3567, 1), (Sum.inr 3571, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm782 : Integer.Sparse Master := [(Sum.inr 2092, 1), (Sum.inr 2929, 1), (Sum.inr 3149, 1), (Sum.inr 3152, 1), (Sum.inr 3158, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm783 : Integer.Sparse Master := [(Sum.inr 2926, 1), (Sum.inr 2929, 1), (Sum.inr 2930, 1), (Sum.inr 2956, 1), (Sum.inr 3079, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def sourceForm784 : Integer.Sparse Master := [(Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 3505, 1), (Sum.inr 3573, 2), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

def sourceForm785 : Integer.Sparse Master := [(Sum.inr 3152, 1), (Sum.inr 3380, 1), (Sum.inr 3551, 1), (Sum.inr 3552, 1), (Sum.inr 3573, 2), (Sum.inr 4083, -1)]

def sourceForm788 : Integer.Sparse Master := [(Sum.inr 4473, 1), (Sum.inr 4474, 3), (Sum.inr 4494, 1), (Sum.inr 5085, 3), (Sum.inr 5097, 1), (Sum.inr 5202, 1), (Sum.inr 5203, 3), (Sum.inr 5265, 3), (Sum.inr 5266, 6), (Sum.inr 5270, 3), (Sum.inr 5447, 1), (Sum.inr 5450, 3), (Sum.inr 5474, 1)]

def sourceForm789 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 1700, 1), (Sum.inr 1709, 3), (Sum.inr 3058, 1), (Sum.inr 3075, 3), (Sum.inr 3461, 3), (Sum.inr 3526, 3), (Sum.inr 3535, 6), (Sum.inr 3617, 1), (Sum.inr 3621, 3), (Sum.inr 3962, 1), (Sum.inr 4025, 1), (Sum.inr 4029, 3)]

def sourceForm790 : Integer.Sparse Master := [(Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 3), (Sum.inr 3962, 1), (Sum.inr 4091, -1)]

def sourceForm791 : Integer.Sparse Master := [(Sum.inr 2746, 1), (Sum.inr 2976, 3), (Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 4091, -1)]

def sourceForm792 : Integer.Sparse Master := [(Sum.inr 4878, 1), (Sum.inr 4879, 3), (Sum.inr 4885, 1), (Sum.inr 4886, 1), (Sum.inr 4889, 3), (Sum.inr 5227, 1), (Sum.inr 5237, 3), (Sum.inr 5265, 3), (Sum.inr 5273, 1), (Sum.inr 5283, 1), (Sum.inr 5286, 3), (Sum.inr 5292, 3), (Sum.inr 5299, 6)]

def sourceForm793 : Integer.Sparse Master := [(Sum.inr 2234, 1), (Sum.inr 2235, 1), (Sum.inr 2246, 3), (Sum.inr 2671, 1), (Sum.inr 2684, 3), (Sum.inr 2741, 1), (Sum.inr 3023, 3), (Sum.inr 3037, 3), (Sum.inr 3051, 6), (Sum.inr 3076, 1), (Sum.inr 3100, 3), (Sum.inr 3221, 1), (Sum.inr 3223, 3)]

def sourceForm796 : Integer.Sparse Master := [(Sum.inr 2457, 1), (Sum.inr 2460, 2), (Sum.inr 2507, 1), (Sum.inr 2738, 1), (Sum.inr 3278, 1), (Sum.inr 3282, 1), (Sum.inr 3289, 2), (Sum.inr 3531, 1), (Sum.inr 3532, 2), (Sum.inr 3539, 1), (Sum.inr 3568, 2), (Sum.inr 3569, 2), (Sum.inr 3571, 2), (Sum.inr 3574, 2), (Sum.inr 3576, 1), (Sum.inr 3580, 1), (Sum.inr 3581, 2), (Sum.inr 3851, 1), (Sum.inr 3880, 2), (Sum.inr 3882, 1), (Sum.inr 3887, 1)]

def sourceForm797 : Integer.Sparse Master := [(Sum.inr 2750, 1), (Sum.inr 3880, 2), (Sum.inr 3901, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

def sourceForm798 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1248, 1), (Sum.inr 1250, 1), (Sum.inr 1260, 2), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

def sourceForm799 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm800 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2623, 1), (Sum.inr 2625, 1), (Sum.inr 2631, 1), (Sum.inr 2750, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

def sourceForm801 : Integer.Sparse Master := [(Sum.inr 4435, 1), (Sum.inr 4436, 1), (Sum.inr 4439, 1), (Sum.inr 4449, 2), (Sum.inr 5144, 2), (Sum.inr 5145, 2), (Sum.inr 5149, 2), (Sum.inr 5160, 2), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5226, 2), (Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5255, 2), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 2), (Sum.inr 5431, 1), (Sum.inr 5478, 2), (Sum.inr 5481, 1), (Sum.inr 5485, 1)]

def sourceForm802 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 1018, 1), (Sum.inr 1021, 1), (Sum.inr 1032, 2), (Sum.inr 2566, 2), (Sum.inr 2567, 2), (Sum.inr 2570, 2), (Sum.inr 2587, 2), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2669, 2), (Sum.inr 2708, 1), (Sum.inr 2710, 1), (Sum.inr 2718, 2), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 2), (Sum.inr 3849, 1), (Sum.inr 3979, 1), (Sum.inr 3994, 2), (Sum.inr 3998, 1)]

def sourceForm803 : Integer.Sparse Master := [(Sum.inr 1635, 1), (Sum.inr 1636, 2), (Sum.inr 1642, 1), (Sum.inr 1713, 1), (Sum.inr 3375, 1), (Sum.inr 3376, 2), (Sum.inr 3388, 1), (Sum.inr 3502, 1), (Sum.inr 3503, 2), (Sum.inr 3539, 1), (Sum.inr 3557, 2), (Sum.inr 3558, 2), (Sum.inr 3562, 2), (Sum.inr 3572, 2), (Sum.inr 3580, 1), (Sum.inr 3605, 2), (Sum.inr 3625, 1), (Sum.inr 3974, 2), (Sum.inr 3984, 1), (Sum.inr 3991, 1), (Sum.inr 4026, 1)]

def sourceForm804 : Integer.Sparse Master := [(Sum.inr 3074, 1), (Sum.inr 3875, 1), (Sum.inr 3974, 2), (Sum.inr 4008, 1), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def sourceForm805 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1384, 1), (Sum.inr 1387, 1), (Sum.inr 1403, 2), (Sum.inr 3074, 1), (Sum.inr 4091, -1)]

def sourceForm806 : Integer.Sparse Master := [(Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

def sourceForm807 : Integer.Sparse Master := [(Sum.inr 3068, 1), (Sum.inr 3069, 1), (Sum.inr 3074, 1), (Sum.inr 3091, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

def sourceForm809 : Integer.Sparse Master := [(Sum.inr 2240, 1), (Sum.inr 2241, 1), (Sum.inr 2243, 1), (Sum.inr 2250, 2), (Sum.inr 2565, 2), (Sum.inr 2573, 1), (Sum.inr 2583, 1), (Sum.inr 2747, 1), (Sum.inr 2749, 1), (Sum.inr 2750, 2), (Sum.inr 2752, 1), (Sum.inr 2756, 2), (Sum.inr 2757, 2), (Sum.inr 2763, 2), (Sum.inr 2764, 2), (Sum.inr 2766, 2), (Sum.inr 2773, 2), (Sum.inr 3104, 1), (Sum.inr 3105, 1), (Sum.inr 3109, 2)]

def sourceForm811 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 3489, 1), (Sum.inr 3496, 1), (Sum.inr 3534, 2), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

def sourceForm812 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2243, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

def sourceForm813 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 2926, 2), (Sum.inr 2950, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

def sourceForm814 : Integer.Sparse Master := [(Sum.inr 2105, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 2), (Sum.inr 3581, 2), (Sum.inr 4083, -1)]

def sourceForm815 : Integer.Sparse Master := [(Sum.inr 3489, 1), (Sum.inr 3550, 1), (Sum.inr 3551, 2), (Sum.inr 3571, 2), (Sum.inr 4083, -1)]

def sourceForm816 : Integer.Sparse Master := [(Sum.inr 4581, 3), (Sum.inr 4601, 2), (Sum.inr 5192, 6), (Sum.inr 5202, 2), (Sum.inr 5284, 6), (Sum.inr 5292, 6), (Sum.inr 5447, 2), (Sum.inr 5452, 3)]

def sourceForm817 : Integer.Sparse Master := [(Sum.inr 1200, 3), (Sum.inr 1235, 2), (Sum.inr 2853, 6), (Sum.inr 2880, 2), (Sum.inr 3077, 6), (Sum.inr 3100, 6), (Sum.inr 4025, 2), (Sum.inr 4039, 3)]

def sourceForm818 : Integer.Sparse Master := [(Sum.inr 4885, 2), (Sum.inr 4887, 3), (Sum.inr 5247, 3), (Sum.inr 5273, 2), (Sum.inr 5281, 6), (Sum.inr 5286, 6), (Sum.inr 5292, 6), (Sum.inr 5301, 2)]

def sourceForm819 : Integer.Sparse Master := [(Sum.inr 2703, 3), (Sum.inr 2741, 2), (Sum.inr 3023, 6), (Sum.inr 3053, 2), (Sum.inr 3074, 6), (Sum.inr 3100, 6), (Sum.inr 3221, 2), (Sum.inr 3226, 3)]

def sourceForm820 : Integer.Sparse Master := [(Sum.inr 4599, 1), (Sum.inr 4600, 1), (Sum.inr 4603, 2), (Sum.inr 4618, 1), (Sum.inr 5145, 2), (Sum.inr 5150, 1), (Sum.inr 5162, 1), (Sum.inr 5197, 1), (Sum.inr 5199, 2), (Sum.inr 5205, 1), (Sum.inr 5257, 1), (Sum.inr 5259, 2), (Sum.inr 5270, 2), (Sum.inr 5273, 1), (Sum.inr 5281, 2), (Sum.inr 5282, 2), (Sum.inr 5290, 2), (Sum.inr 5431, 1), (Sum.inr 5440, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 2)]

def sourceForm821 : Integer.Sparse Master := [(Sum.inr 1233, 1), (Sum.inr 1234, 1), (Sum.inr 1237, 2), (Sum.inr 1298, 1), (Sum.inr 2878, 1), (Sum.inr 2879, 1), (Sum.inr 2882, 2), (Sum.inr 2923, 1), (Sum.inr 2925, 2), (Sum.inr 2957, 1), (Sum.inr 3074, 2), (Sum.inr 3075, 2), (Sum.inr 3078, 2), (Sum.inr 3087, 1), (Sum.inr 3088, 2), (Sum.inr 3099, 2), (Sum.inr 3111, 1), (Sum.inr 4026, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 2), (Sum.inr 4036, 1)]

def sourceForm822 : Integer.Sparse Master := [(Sum.inr 2700, 1), (Sum.inr 2702, 1), (Sum.inr 2706, 1), (Sum.inr 2738, 2), (Sum.inr 3289, 1), (Sum.inr 3294, 2), (Sum.inr 3304, 1), (Sum.inr 3532, 1), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3562, 2), (Sum.inr 3563, 1), (Sum.inr 3569, 1), (Sum.inr 3571, 2), (Sum.inr 3578, 2), (Sum.inr 3580, 2), (Sum.inr 3581, 2), (Sum.inr 3859, 1), (Sum.inr 3875, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 2)]

def sourceForm823 : Integer.Sparse Master := [(Sum.inr 2764, 1), (Sum.inr 3849, 1), (Sum.inr 3885, 1), (Sum.inr 3904, 1), (Sum.inr 3910, 2), (Sum.inr 4091, -1)]

def sourceForm824 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 1262, 2), (Sum.inr 1270, 1), (Sum.inr 1293, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def sourceForm825 : Integer.Sparse Master := [(Sum.inr 1293, 1), (Sum.inr 2589, 1), (Sum.inr 2741, 1), (Sum.inr 2764, 3), (Sum.inr 4091, -1)]

def sourceForm826 : Integer.Sparse Master := [(Sum.inr 2631, 1), (Sum.inr 2633, 2), (Sum.inr 2641, 1), (Sum.inr 2764, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def sourceForm827 : Integer.Sparse Master := [(Sum.inr 4451, 1), (Sum.inr 4452, 2), (Sum.inr 4461, 1), (Sum.inr 4489, 1), (Sum.inr 5070, 2), (Sum.inr 5076, 1), (Sum.inr 5093, 1), (Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 1), (Sum.inr 5227, 1), (Sum.inr 5228, 2), (Sum.inr 5237, 1), (Sum.inr 5290, 2), (Sum.inr 5291, 2), (Sum.inr 5294, 2), (Sum.inr 5304, 2), (Sum.inr 5450, 1), (Sum.inr 5481, 1), (Sum.inr 5485, 1), (Sum.inr 5492, 2)]

def sourceForm828 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 1035, 2), (Sum.inr 1044, 1), (Sum.inr 1073, 1), (Sum.inr 2477, 2), (Sum.inr 2483, 1), (Sum.inr 2503, 1), (Sum.inr 2589, 1), (Sum.inr 2590, 2), (Sum.inr 2599, 1), (Sum.inr 2671, 1), (Sum.inr 2672, 2), (Sum.inr 2684, 1), (Sum.inr 2764, 2), (Sum.inr 2765, 2), (Sum.inr 2768, 2), (Sum.inr 2782, 2), (Sum.inr 3910, 1), (Sum.inr 3979, 1), (Sum.inr 3998, 1), (Sum.inr 4017, 2)]

def sourceForm829 : Integer.Sparse Master := [(Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4869, 1), (Sum.inr 4893, 1), (Sum.inr 5255, 2), (Sum.inr 5256, 1), (Sum.inr 5257, 1), (Sum.inr 5263, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 2), (Sum.inr 5278, 1), (Sum.inr 5279, 1), (Sum.inr 5281, 2), (Sum.inr 5288, 2), (Sum.inr 5289, 2), (Sum.inr 5290, 1), (Sum.inr 5292, 2), (Sum.inr 5299, 2), (Sum.inr 5304, 2), (Sum.inr 5306, 1), (Sum.inr 5307, 1)]

def sourceForm830 : Integer.Sparse Master := [(Sum.inr 2241, 1), (Sum.inr 2260, 2), (Sum.inr 2263, 1), (Sum.inr 2275, 1), (Sum.inr 2718, 2), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2747, 1), (Sum.inr 2748, 1), (Sum.inr 2750, 2), (Sum.inr 2754, 1), (Sum.inr 2760, 2), (Sum.inr 2763, 2), (Sum.inr 2764, 1), (Sum.inr 2766, 2), (Sum.inr 2773, 2), (Sum.inr 2782, 2), (Sum.inr 2785, 1), (Sum.inr 3085, 1), (Sum.inr 3109, 2), (Sum.inr 3120, 1)]

def sourceForm831 : Integer.Sparse Master := [(Sum.inr 4589, 1), (Sum.inr 4590, 2), (Sum.inr 4599, 1), (Sum.inr 4601, 1), (Sum.inr 5073, 2), (Sum.inr 5076, 1), (Sum.inr 5100, 1), (Sum.inr 5185, 2), (Sum.inr 5187, 1), (Sum.inr 5197, 1), (Sum.inr 5250, 2), (Sum.inr 5251, 2), (Sum.inr 5257, 2), (Sum.inr 5259, 2), (Sum.inr 5273, 1), (Sum.inr 5281, 2), (Sum.inr 5290, 1), (Sum.inr 5408, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 2), (Sum.inr 5440, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm832 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1213, 2), (Sum.inr 1233, 1), (Sum.inr 1265, 1), (Sum.inr 2861, 1), (Sum.inr 2862, 2), (Sum.inr 2878, 1), (Sum.inr 2986, 1), (Sum.inr 2987, 2), (Sum.inr 2999, 1), (Sum.inr 3064, 2), (Sum.inr 3065, 2), (Sum.inr 3074, 2), (Sum.inr 3087, 2), (Sum.inr 3088, 2), (Sum.inr 3099, 1), (Sum.inr 3111, 1), (Sum.inr 4026, 1), (Sum.inr 4033, 2), (Sum.inr 4036, 1), (Sum.inr 4038, 1)]

def sourceForm833 : Integer.Sparse Master := [(Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3290, 2), (Sum.inr 3292, 1), (Sum.inr 3467, 2), (Sum.inr 3469, 1), (Sum.inr 3477, 1), (Sum.inr 3529, 2), (Sum.inr 3531, 2), (Sum.inr 3532, 2), (Sum.inr 3537, 1), (Sum.inr 3539, 2), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3569, 1), (Sum.inr 3571, 2), (Sum.inr 3581, 1), (Sum.inr 3806, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 2), (Sum.inr 3859, 1)]

def sourceForm834 : Integer.Sparse Master := [(Sum.inr 1235, 1), (Sum.inr 2510, 1), (Sum.inr 2721, 3), (Sum.inr 2741, 1), (Sum.inr 4091, -1)]

def sourceForm835 : Integer.Sparse Master := [(Sum.inr 2615, 2), (Sum.inr 2617, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

def sourceForm836 : Integer.Sparse Master := [(Sum.inr 4396, 2), (Sum.inr 4399, 1), (Sum.inr 4417, 1), (Sum.inr 4456, 1), (Sum.inr 4996, 2), (Sum.inr 4998, 1), (Sum.inr 5013, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5167, 1), (Sum.inr 5241, 2), (Sum.inr 5247, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5271, 2), (Sum.inr 5292, 2), (Sum.inr 5472, 1), (Sum.inr 5482, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2)]

def sourceForm837 : Integer.Sparse Master := [(Sum.inr 977, 2), (Sum.inr 980, 1), (Sum.inr 998, 1), (Sum.inr 1039, 1), (Sum.inr 2382, 2), (Sum.inr 2383, 1), (Sum.inr 2398, 1), (Sum.inr 2553, 2), (Sum.inr 2556, 1), (Sum.inr 2593, 1), (Sum.inr 2694, 2), (Sum.inr 2703, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2739, 2), (Sum.inr 2766, 2), (Sum.inr 3957, 1), (Sum.inr 3992, 1), (Sum.inr 4009, 1), (Sum.inr 4013, 2)]

def sourceForm838 : Integer.Sparse Master := [(Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4833, 1), (Sum.inr 4893, 1), (Sum.inr 5226, 2), (Sum.inr 5227, 1), (Sum.inr 5231, 1), (Sum.inr 5255, 2), (Sum.inr 5256, 3), (Sum.inr 5257, 4), (Sum.inr 5263, 1), (Sum.inr 5265, 3), (Sum.inr 5271, 2), (Sum.inr 5273, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 3), (Sum.inr 5307, 1)]

def sourceForm839 : Integer.Sparse Master := [(Sum.inr 2202, 2), (Sum.inr 2204, 1), (Sum.inr 2214, 1), (Sum.inr 2263, 1), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2676, 1), (Sum.inr 2718, 2), (Sum.inr 2720, 2), (Sum.inr 2721, 2), (Sum.inr 2728, 1), (Sum.inr 2730, 2), (Sum.inr 2739, 2), (Sum.inr 2741, 1), (Sum.inr 2764, 1), (Sum.inr 2766, 2), (Sum.inr 2785, 1), (Sum.inr 3037, 1), (Sum.inr 3085, 1), (Sum.inr 3087, 2), (Sum.inr 3100, 1)]

def sourceForm840 : Integer.Sparse Master := [(Sum.inr 4616, 2), (Sum.inr 4617, 1), (Sum.inr 4619, 1), (Sum.inr 4620, 1), (Sum.inr 5160, 2), (Sum.inr 5163, 2), (Sum.inr 5164, 2), (Sum.inr 5173, 2), (Sum.inr 5271, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5289, 2), (Sum.inr 5291, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

def sourceForm841 : Integer.Sparse Master := [(Sum.inr 1291, 2), (Sum.inr 1292, 1), (Sum.inr 1295, 1), (Sum.inr 1302, 1), (Sum.inr 2951, 2), (Sum.inr 2952, 2), (Sum.inr 2955, 2), (Sum.inr 2961, 2), (Sum.inr 3051, 2), (Sum.inr 3052, 1), (Sum.inr 3055, 1), (Sum.inr 3097, 2), (Sum.inr 3098, 1), (Sum.inr 3103, 1), (Sum.inr 3109, 2), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3862, 1), (Sum.inr 3987, 1), (Sum.inr 3993, 2), (Sum.inr 4001, 1)]

def sourceForm842 : Integer.Sparse Master := [(Sum.inr 2735, 2), (Sum.inr 2737, 1), (Sum.inr 2744, 1), (Sum.inr 2781, 1), (Sum.inr 3303, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3534, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3558, 2), (Sum.inr 3564, 2), (Sum.inr 3565, 2), (Sum.inr 3572, 2), (Sum.inr 3573, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 3861, 1), (Sum.inr 3876, 2), (Sum.inr 3888, 1), (Sum.inr 3889, 1)]

def sourceForm843 : Integer.Sparse Master := [(Sum.inr 4489, 2), (Sum.inr 4490, 1), (Sum.inr 4491, 1), (Sum.inr 4503, 1), (Sum.inr 5093, 2), (Sum.inr 5094, 2), (Sum.inr 5095, 2), (Sum.inr 5105, 2), (Sum.inr 5110, 1), (Sum.inr 5237, 2), (Sum.inr 5238, 1), (Sum.inr 5290, 2), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5304, 2), (Sum.inr 5305, 1), (Sum.inr 5310, 1), (Sum.inr 5451, 1), (Sum.inr 5484, 2), (Sum.inr 5492, 1), (Sum.inr 5494, 1)]

def sourceForm844 : Integer.Sparse Master := [(Sum.inr 1073, 2), (Sum.inr 1074, 1), (Sum.inr 1075, 1), (Sum.inr 1087, 1), (Sum.inr 2503, 2), (Sum.inr 2504, 2), (Sum.inr 2505, 2), (Sum.inr 2515, 2), (Sum.inr 2684, 2), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2764, 2), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 2782, 2), (Sum.inr 2783, 1), (Sum.inr 2788, 1), (Sum.inr 3913, 1), (Sum.inr 3983, 2), (Sum.inr 4017, 1), (Sum.inr 4020, 1)]

def sourceForm845 : Integer.Sparse Master := [(Sum.inr 4866, 2), (Sum.inr 4871, 1), (Sum.inr 4875, 1), (Sum.inr 4895, 1), (Sum.inr 5173, 2), (Sum.inr 5175, 1), (Sum.inr 5255, 2), (Sum.inr 5269, 2), (Sum.inr 5271, 2), (Sum.inr 5288, 2), (Sum.inr 5289, 4), (Sum.inr 5290, 2), (Sum.inr 5295, 2), (Sum.inr 5303, 1), (Sum.inr 5304, 2), (Sum.inr 5306, 2), (Sum.inr 5307, 1)]

def sourceForm846 : Integer.Sparse Master := [(Sum.inr 2260, 2), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2291, 1), (Sum.inr 2718, 2), (Sum.inr 2735, 2), (Sum.inr 2736, 2), (Sum.inr 2739, 2), (Sum.inr 2760, 2), (Sum.inr 2761, 1), (Sum.inr 2763, 2), (Sum.inr 2764, 2), (Sum.inr 2769, 1), (Sum.inr 2779, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 2785, 1), (Sum.inr 3097, 2), (Sum.inr 3119, 1), (Sum.inr 3120, 1)]

def sourceForm847 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 4622, 2), (Sum.inr 4623, 1), (Sum.inr 4624, 2), (Sum.inr 5167, 2), (Sum.inr 5169, 4), (Sum.inr 5172, 2), (Sum.inr 5292, 4), (Sum.inr 5293, 2), (Sum.inr 5294, 2), (Sum.inr 5307, 2), (Sum.inr 5309, 2), (Sum.inr 5440, 2), (Sum.inr 5454, 2)]

def sourceForm848 : Integer.Sparse Master := [(Sum.inr 4599, 1), (Sum.inr 4602, 1), (Sum.inr 4603, 1), (Sum.inr 4607, 1), (Sum.inr 4616, 1), (Sum.inr 5098, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1), (Sum.inr 5105, 1), (Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5138, 1), (Sum.inr 5160, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5410, 1), (Sum.inr 5424, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5442, 1)]

def sourceForm849 : Integer.Sparse Master := [(Sum.inr 3289, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3303, 1), (Sum.inr 3460, 1), (Sum.inr 3470, 1), (Sum.inr 3471, 1), (Sum.inr 3479, 1), (Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 3517, 1), (Sum.inr 3525, 1), (Sum.inr 3526, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3558, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 3583, 1), (Sum.inr 3808, 1), (Sum.inr 3838, 1), (Sum.inr 3852, 1), (Sum.inr 3853, 1), (Sum.inr 3861, 1)]

def sourceForm850 : Integer.Sparse Master := [(Sum.inr 4417, 1), (Sum.inr 4418, 1), (Sum.inr 4419, 1), (Sum.inr 4424, 1), (Sum.inr 4495, 1), (Sum.inr 5013, 1), (Sum.inr 5014, 1), (Sum.inr 5015, 1), (Sum.inr 5018, 1), (Sum.inr 5055, 1), (Sum.inr 5056, 1), (Sum.inr 5059, 1), (Sum.inr 5098, 1), (Sum.inr 5099, 1), (Sum.inr 5247, 1), (Sum.inr 5248, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 2), (Sum.inr 5272, 1), (Sum.inr 5275, 1), (Sum.inr 5292, 1), (Sum.inr 5306, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1), (Sum.inr 5485, 1), (Sum.inr 5490, 1), (Sum.inr 5492, 1)]

def sourceForm851 : Integer.Sparse Master := [(Sum.inr 998, 1), (Sum.inr 999, 1), (Sum.inr 1000, 1), (Sum.inr 1005, 1), (Sum.inr 1079, 1), (Sum.inr 2398, 1), (Sum.inr 2399, 1), (Sum.inr 2400, 1), (Sum.inr 2404, 1), (Sum.inr 2458, 1), (Sum.inr 2459, 1), (Sum.inr 2462, 1), (Sum.inr 2508, 1), (Sum.inr 2703, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2739, 2), (Sum.inr 2740, 1), (Sum.inr 2743, 1), (Sum.inr 2766, 1), (Sum.inr 2784, 1), (Sum.inr 3961, 1), (Sum.inr 3974, 1), (Sum.inr 4010, 1), (Sum.inr 4013, 1), (Sum.inr 4015, 1)]

def sourceForm852 : Integer.Sparse Master := [(Sum.inr 4802, 1), (Sum.inr 4807, 1), (Sum.inr 4811, 1), (Sum.inr 4838, 1), (Sum.inr 4895, 1), (Sum.inr 5150, 1), (Sum.inr 5151, 1), (Sum.inr 5173, 1), (Sum.inr 5226, 1), (Sum.inr 5236, 1), (Sum.inr 5237, 1), (Sum.inr 5246, 1), (Sum.inr 5247, 1), (Sum.inr 5255, 1), (Sum.inr 5256, 1), (Sum.inr 5257, 1), (Sum.inr 5269, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 3), (Sum.inr 5273, 1), (Sum.inr 5281, 1), (Sum.inr 5289, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5306, 1), (Sum.inr 5307, 1)]

def sourceForm853 : Integer.Sparse Master := [(Sum.inr 2202, 1), (Sum.inr 2224, 1), (Sum.inr 2225, 1), (Sum.inr 2227, 1), (Sum.inr 2291, 1), (Sum.inr 2669, 1), (Sum.inr 2681, 1), (Sum.inr 2682, 1), (Sum.inr 2684, 1), (Sum.inr 2700, 1), (Sum.inr 2701, 1), (Sum.inr 2703, 1), (Sum.inr 2718, 1), (Sum.inr 2720, 1), (Sum.inr 2721, 1), (Sum.inr 2735, 1), (Sum.inr 2736, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 3), (Sum.inr 2741, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 2785, 1), (Sum.inr 3051, 1), (Sum.inr 3074, 1), (Sum.inr 3097, 1), (Sum.inr 3099, 1), (Sum.inr 3100, 1)]

def sourceForm854 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 4601, 1), (Sum.inr 4606, 3), (Sum.inr 4618, 1), (Sum.inr 5100, 1), (Sum.inr 5104, 3), (Sum.inr 5137, 3), (Sum.inr 5162, 1), (Sum.inr 5257, 3), (Sum.inr 5259, 6), (Sum.inr 5290, 3), (Sum.inr 5427, 1), (Sum.inr 5440, 3)]

def sourceForm855 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4833, 1), (Sum.inr 4838, 3), (Sum.inr 5227, 1), (Sum.inr 5237, 3), (Sum.inr 5247, 3), (Sum.inr 5257, 3), (Sum.inr 5271, 6), (Sum.inr 5273, 1), (Sum.inr 5283, 1), (Sum.inr 5292, 3), (Sum.inr 5301, 1), (Sum.inr 5307, 3)]

def sourceForm856 : Integer.Sparse Master := [(Sum.inr 4438, 1), (Sum.inr 4439, 2), (Sum.inr 4456, 2), (Sum.inr 4851, 2), (Sum.inr 4852, 4), (Sum.inr 4864, 2), (Sum.inr 4885, 2), (Sum.inr 4887, 2), (Sum.inr 4888, 2), (Sum.inr 4889, 2), (Sum.inr 4893, 4), (Sum.inr 5281, 2), (Sum.inr 5283, 1), (Sum.inr 5292, 2)]

def sourceForm857 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 1706, 2), (Sum.inr 1713, 2), (Sum.inr 2240, 2), (Sum.inr 2241, 2), (Sum.inr 2243, 2), (Sum.inr 2250, 4), (Sum.inr 2252, 2), (Sum.inr 2262, 2), (Sum.inr 2263, 4), (Sum.inr 2277, 2), (Sum.inr 2750, 2), (Sum.inr 2752, 1), (Sum.inr 2766, 2)]

def sourceForm858 : Integer.Sparse Master := [(Sum.inr 4248, 1), (Sum.inr 4249, 4), (Sum.inr 4801, 4), (Sum.inr 4802, 8), (Sum.inr 4831, 4), (Sum.inr 4888, 4), (Sum.inr 5433, 4), (Sum.inr 5452, 1)]

def sourceForm859 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4456, 1), (Sum.inr 4458, 2), (Sum.inr 4461, 1), (Sum.inr 4497, 1), (Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4833, 1), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4869, 1), (Sum.inr 4887, 2), (Sum.inr 4888, 2), (Sum.inr 4889, 2), (Sum.inr 4893, 3), (Sum.inr 4895, 2), (Sum.inr 5257, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 2), (Sum.inr 5307, 1)]

def sourceForm860 : Integer.Sparse Master := [(Sum.inr 4068, 2), (Sum.inr 4069, 3), (Sum.inr 4079, 2), (Sum.inr 4080, 6), (Sum.inr 4083, 6), (Sum.inr 4084, 6), (Sum.inr 4091, 2), (Sum.inr 4093, 3)]

def sourceForm862 : Integer.Sparse Master := [(Sum.inr 1902, 1), (Sum.inr 1904, 1), (Sum.inr 1910, 1), (Sum.inr 1923, 1), (Sum.inr 2253, 1), (Sum.inr 2970, 1), (Sum.inr 2974, 1), (Sum.inr 2984, 1), (Sum.inr 3016, 1), (Sum.inr 3463, 1), (Sum.inr 3464, 1), (Sum.inr 3473, 1), (Sum.inr 3528, 1), (Sum.inr 3648, 1), (Sum.inr 3658, 1), (Sum.inr 3761, 1), (Sum.inr 3762, 1), (Sum.inr 3780, 1), (Sum.inr 3783, 1), (Sum.inr 3788, 1), (Sum.inr 3800, 1), (Sum.inr 3801, 1), (Sum.inr 3802, 1), (Sum.inr 3803, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3847, 1), (Sum.inr 3856, 1), (Sum.inr 3883, 1), (Sum.inr 3977, 1)]

def sourceForm863 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 3691, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 3805, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm864 : Integer.Sparse Master := [(Sum.inr 2474, 1), (Sum.inr 2475, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

def sourceForm865 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3698, 1), (Sum.inr 3803, 1), (Sum.inr 3812, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def sourceForm866 : Integer.Sparse Master := [(Sum.inr 3217, 1), (Sum.inr 3686, 1), (Sum.inr 3691, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

def sourceForm867 : Integer.Sparse Master := [(Sum.inr 2475, 2), (Sum.inr 3686, 2), (Sum.inr 3803, 2), (Sum.inr 4092, -1)]

def sourceForm868 : Integer.Sparse Master := [(Sum.inr 4812, 1), (Sum.inr 4813, 1), (Sum.inr 4816, 1), (Sum.inr 4824, 1), (Sum.inr 4852, 1), (Sum.inr 5129, 1), (Sum.inr 5138, 1), (Sum.inr 5146, 1), (Sum.inr 5260, 1), (Sum.inr 5357, 1), (Sum.inr 5358, 1), (Sum.inr 5360, 1), (Sum.inr 5376, 1), (Sum.inr 5378, 1), (Sum.inr 5381, 2), (Sum.inr 5397, 2), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5420, 1), (Sum.inr 5421, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5426, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5445, 1), (Sum.inr 5477, 1)]

def sourceForm869 : Integer.Sparse Master := [(Sum.inr 2071, 1), (Sum.inr 2072, 1), (Sum.inr 2078, 1), (Sum.inr 2089, 1), (Sum.inr 2196, 1), (Sum.inr 2916, 1), (Sum.inr 2922, 1), (Sum.inr 2933, 1), (Sum.inr 3086, 1), (Sum.inr 3715, 1), (Sum.inr 3718, 1), (Sum.inr 3722, 1), (Sum.inr 3723, 1), (Sum.inr 3727, 1), (Sum.inr 3752, 1), (Sum.inr 3762, 1), (Sum.inr 3796, 1), (Sum.inr 3814, 1), (Sum.inr 3830, 1), (Sum.inr 3841, 1), (Sum.inr 3870, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3880, 1), (Sum.inr 3883, 1), (Sum.inr 3971, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3990, 1), (Sum.inr 4032, 1)]

def sourceForm870 : Integer.Sparse Master := [(Sum.inr 2030, 1), (Sum.inr 2031, 1), (Sum.inr 2034, 1), (Sum.inr 2043, 1), (Sum.inr 2250, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3540, 1), (Sum.inr 3560, 1), (Sum.inr 3695, 1), (Sum.inr 3696, 1), (Sum.inr 3698, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3813, 1), (Sum.inr 3826, 1), (Sum.inr 3827, 1), (Sum.inr 3830, 1), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3841, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3856, 1), (Sum.inr 3871, 1), (Sum.inr 3880, 1), (Sum.inr 3989, 1)]

def sourceForm871 : Integer.Sparse Master := [(Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3946, 1), (Sum.inr 4022, 1), (Sum.inr 4024, 1), (Sum.inr 4044, 1), (Sum.inr 4092, -1)]

def sourceForm872 : Integer.Sparse Master := [(Sum.inr 3168, 1), (Sum.inr 3715, 1), (Sum.inr 3722, 1), (Sum.inr 3725, 1), (Sum.inr 3839, 1), (Sum.inr 4022, 1), (Sum.inr 4092, -1)]

def sourceForm873 : Integer.Sparse Master := [(Sum.inr 2568, 1), (Sum.inr 3725, 1), (Sum.inr 3780, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

def sourceForm874 : Integer.Sparse Master := [(Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 3782, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

def sourceForm875 : Integer.Sparse Master := [(Sum.inr 2557, 1), (Sum.inr 3722, 1), (Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 3843, 1), (Sum.inr 4092, -1)]

def sourceForm876 : Integer.Sparse Master := [(Sum.inr 3175, 1), (Sum.inr 3723, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

def sourceForm877 : Integer.Sparse Master := [(Sum.inr 2545, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3723, 1), (Sum.inr 3837, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

def sourceForm878 : Integer.Sparse Master := [(Sum.inr 3196, 1), (Sum.inr 3780, 1), (Sum.inr 3782, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

def sourceForm879 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 3168, 1), (Sum.inr 3170, 1), (Sum.inr 3175, 1), (Sum.inr 3196, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

def sourceForm882 : Integer.Sparse Master := [(Sum.inr 1991, 1), (Sum.inr 1994, 1), (Sum.inr 1998, 1), (Sum.inr 2033, 1), (Sum.inr 2195, 1), (Sum.inr 2533, 1), (Sum.inr 2535, 1), (Sum.inr 2566, 1), (Sum.inr 2661, 1), (Sum.inr 3536, 1), (Sum.inr 3537, 1), (Sum.inr 3539, 1), (Sum.inr 3574, 1), (Sum.inr 3680, 1), (Sum.inr 3697, 1), (Sum.inr 3743, 1), (Sum.inr 3761, 1), (Sum.inr 3810, 1), (Sum.inr 3812, 1), (Sum.inr 3825, 1), (Sum.inr 3829, 1), (Sum.inr 3840, 2), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 1), (Sum.inr 3855, 1), (Sum.inr 3871, 1), (Sum.inr 3880, 1), (Sum.inr 3994, 1)]

def sourceForm883 : Integer.Sparse Master := [(Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3875, 1), (Sum.inr 3880, 1), (Sum.inr 3901, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

def sourceForm884 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2919, 1), (Sum.inr 3195, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def sourceForm885 : Integer.Sparse Master := [(Sum.inr 3197, 1), (Sum.inr 3872, 2), (Sum.inr 3878, 1), (Sum.inr 3899, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

def sourceForm886 : Integer.Sparse Master := [(Sum.inr 2612, 1), (Sum.inr 2945, 1), (Sum.inr 3783, 1), (Sum.inr 3863, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def sourceForm887 : Integer.Sparse Master := [(Sum.inr 3202, 1), (Sum.inr 3783, 1), (Sum.inr 3789, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

def sourceForm888 : Integer.Sparse Master := [(Sum.inr 2623, 1), (Sum.inr 2920, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

def sourceForm889 : Integer.Sparse Master := [(Sum.inr 3195, 1), (Sum.inr 3863, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 2), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

def sourceForm890 : Integer.Sparse Master := [(Sum.inr 2617, 1), (Sum.inr 3069, 1), (Sum.inr 3789, 1), (Sum.inr 3872, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

def sourceForm891 : Integer.Sparse Master := [(Sum.inr 2919, 1), (Sum.inr 2920, 1), (Sum.inr 2928, 1), (Sum.inr 2945, 1), (Sum.inr 3069, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def sourceForm893 : Integer.Sparse Master := [(Sum.inr 2906, 1), (Sum.inr 2907, 1), (Sum.inr 2909, 1), (Sum.inr 2951, 1), (Sum.inr 3051, 1), (Sum.inr 3430, 1), (Sum.inr 3437, 1), (Sum.inr 3464, 1), (Sum.inr 3515, 1), (Sum.inr 3518, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3559, 1), (Sum.inr 3712, 1), (Sum.inr 3714, 1), (Sum.inr 3730, 1), (Sum.inr 3762, 1), (Sum.inr 3794, 1), (Sum.inr 3809, 1), (Sum.inr 3832, 1), (Sum.inr 3838, 1), (Sum.inr 3841, 1), (Sum.inr 3845, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3972, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1)]

def sourceForm894 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2455, 1), (Sum.inr 2463, 1), (Sum.inr 2494, 1), (Sum.inr 2732, 1), (Sum.inr 2905, 1), (Sum.inr 2909, 1), (Sum.inr 2934, 1), (Sum.inr 3039, 1), (Sum.inr 3558, 1), (Sum.inr 3559, 1), (Sum.inr 3561, 1), (Sum.inr 3573, 1), (Sum.inr 3679, 1), (Sum.inr 3698, 1), (Sum.inr 3714, 1), (Sum.inr 3724, 1), (Sum.inr 3838, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3866, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3889, 1), (Sum.inr 3970, 1), (Sum.inr 3990, 1), (Sum.inr 4003, 1)]

def sourceForm895 : Integer.Sparse Master := [(Sum.inr 2587, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm896 : Integer.Sparse Master := [(Sum.inr 2577, 2), (Sum.inr 3729, 1), (Sum.inr 3840, 2), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

def sourceForm897 : Integer.Sparse Master := [(Sum.inr 2974, 1), (Sum.inr 3780, 1), (Sum.inr 3781, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

def sourceForm898 : Integer.Sparse Master := [(Sum.inr 2971, 1), (Sum.inr 3717, 1), (Sum.inr 3720, 1), (Sum.inr 3729, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

def sourceForm899 : Integer.Sparse Master := [(Sum.inr 2549, 1), (Sum.inr 2578, 1), (Sum.inr 3717, 1), (Sum.inr 3780, 1), (Sum.inr 3840, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

def sourceForm901 : Integer.Sparse Master := [(Sum.inr 1992, 1), (Sum.inr 1993, 1), (Sum.inr 2001, 1), (Sum.inr 2034, 1), (Sum.inr 2196, 1), (Sum.inr 2905, 1), (Sum.inr 2907, 1), (Sum.inr 2933, 1), (Sum.inr 3038, 1), (Sum.inr 3517, 1), (Sum.inr 3518, 1), (Sum.inr 3541, 1), (Sum.inr 3561, 1), (Sum.inr 3679, 1), (Sum.inr 3698, 1), (Sum.inr 3712, 1), (Sum.inr 3723, 1), (Sum.inr 3762, 1), (Sum.inr 3796, 1), (Sum.inr 3814, 1), (Sum.inr 3830, 1), (Sum.inr 3834, 1), (Sum.inr 3838, 1), (Sum.inr 3839, 1), (Sum.inr 3840, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1), (Sum.inr 3872, 2), (Sum.inr 3990, 1)]

def sourceForm903 : Integer.Sparse Master := [(Sum.inr 4869, 2), (Sum.inr 4871, 1), (Sum.inr 4874, 1), (Sum.inr 4898, 1), (Sum.inr 5170, 2), (Sum.inr 5176, 1), (Sum.inr 5310, 1), (Sum.inr 5384, 2), (Sum.inr 5387, 2), (Sum.inr 5389, 1), (Sum.inr 5403, 2), (Sum.inr 5412, 2), (Sum.inr 5439, 2), (Sum.inr 5441, 1), (Sum.inr 5443, 3), (Sum.inr 5448, 2), (Sum.inr 5449, 1), (Sum.inr 5455, 1), (Sum.inr 5456, 1), (Sum.inr 5491, 1)]

def sourceForm904 : Integer.Sparse Master := [(Sum.inr 2110, 2), (Sum.inr 2112, 1), (Sum.inr 2115, 1), (Sum.inr 2279, 1), (Sum.inr 2954, 2), (Sum.inr 2968, 1), (Sum.inr 3121, 1), (Sum.inr 3732, 2), (Sum.inr 3739, 2), (Sum.inr 3740, 1), (Sum.inr 3789, 2), (Sum.inr 3814, 2), (Sum.inr 3885, 2), (Sum.inr 3886, 1), (Sum.inr 3889, 2), (Sum.inr 3907, 1), (Sum.inr 3916, 1), (Sum.inr 4012, 2), (Sum.inr 4014, 1), (Sum.inr 4019, 1), (Sum.inr 4037, 1)]

def sourceForm905 : Integer.Sparse Master := [(Sum.inr 4839, 2), (Sum.inr 4843, 1), (Sum.inr 4845, 1), (Sum.inr 4896, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5370, 2), (Sum.inr 5397, 2), (Sum.inr 5411, 2), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5453, 1), (Sum.inr 5454, 1), (Sum.inr 5492, 1)]

def sourceForm906 : Integer.Sparse Master := [(Sum.inr 2058, 2), (Sum.inr 2062, 1), (Sum.inr 2065, 1), (Sum.inr 2266, 1), (Sum.inr 2881, 2), (Sum.inr 2889, 1), (Sum.inr 3101, 1), (Sum.inr 3391, 2), (Sum.inr 3397, 1), (Sum.inr 3582, 1), (Sum.inr 3706, 2), (Sum.inr 3782, 2), (Sum.inr 3809, 2), (Sum.inr 3853, 2), (Sum.inr 3857, 2), (Sum.inr 3912, 1), (Sum.inr 3913, 1), (Sum.inr 3987, 1), (Sum.inr 4015, 1), (Sum.inr 4029, 2), (Sum.inr 4040, 1)]

def sourceForm907 : Integer.Sparse Master := [(Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5268, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 2), (Sum.inr 5302, 1), (Sum.inr 5304, 1), (Sum.inr 5411, 2), (Sum.inr 5413, 1), (Sum.inr 5425, 2), (Sum.inr 5428, 2), (Sum.inr 5435, 2), (Sum.inr 5436, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

def sourceForm908 : Integer.Sparse Master := [(Sum.inr 2732, 2), (Sum.inr 2734, 1), (Sum.inr 2744, 1), (Sum.inr 2776, 1), (Sum.inr 3039, 2), (Sum.inr 3055, 1), (Sum.inr 3110, 1), (Sum.inr 3573, 2), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3853, 2), (Sum.inr 3861, 1), (Sum.inr 3862, 1), (Sum.inr 3872, 2), (Sum.inr 3876, 2), (Sum.inr 3877, 2), (Sum.inr 3883, 2), (Sum.inr 3888, 1), (Sum.inr 4001, 1), (Sum.inr 4003, 2), (Sum.inr 4006, 1)]

def sourceForm909 : Integer.Sparse Master := [(Sum.inr 5076, 1), (Sum.inr 5078, 1), (Sum.inr 5080, 1), (Sum.inr 5105, 1), (Sum.inr 5148, 1), (Sum.inr 5152, 1), (Sum.inr 5169, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5354, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5380, 1), (Sum.inr 5388, 1), (Sum.inr 5416, 1), (Sum.inr 5422, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5440, 1), (Sum.inr 5442, 1), (Sum.inr 5451, 1), (Sum.inr 5454, 1), (Sum.inr 5455, 1), (Sum.inr 5481, 1), (Sum.inr 5484, 1), (Sum.inr 5490, 1), (Sum.inr 5492, 1)]

def sourceForm910 : Integer.Sparse Master := [(Sum.inr 2483, 1), (Sum.inr 2485, 1), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2768, 1), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2960, 1), (Sum.inr 3102, 1), (Sum.inr 3692, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3721, 1), (Sum.inr 3737, 1), (Sum.inr 3853, 1), (Sum.inr 3876, 1), (Sum.inr 3964, 1), (Sum.inr 3967, 1), (Sum.inr 3979, 1), (Sum.inr 3982, 2), (Sum.inr 3983, 1), (Sum.inr 3987, 1), (Sum.inr 4001, 1), (Sum.inr 4013, 1), (Sum.inr 4017, 1), (Sum.inr 4019, 1), (Sum.inr 4033, 1), (Sum.inr 4036, 1), (Sum.inr 4040, 1)]

def sourceForm911 : Integer.Sparse Master := [(Sum.inr 4802, 1), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4835, 1), (Sum.inr 4888, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5368, 1), (Sum.inr 5393, 1), (Sum.inr 5395, 1), (Sum.inr 5405, 1), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5439, 2), (Sum.inr 5452, 1), (Sum.inr 5482, 1), (Sum.inr 5483, 1), (Sum.inr 5486, 1), (Sum.inr 5490, 1), (Sum.inr 5499, 1)]

def sourceForm912 : Integer.Sparse Master := [(Sum.inr 2020, 1), (Sum.inr 2022, 1), (Sum.inr 2029, 1), (Sum.inr 2054, 1), (Sum.inr 2244, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 2594, 1), (Sum.inr 2722, 1), (Sum.inr 3690, 1), (Sum.inr 3694, 1), (Sum.inr 3705, 1), (Sum.inr 3779, 1), (Sum.inr 3781, 1), (Sum.inr 3800, 1), (Sum.inr 3821, 1), (Sum.inr 3824, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3851, 1), (Sum.inr 3852, 2), (Sum.inr 3858, 1), (Sum.inr 3902, 1), (Sum.inr 3911, 1), (Sum.inr 3981, 1), (Sum.inr 3992, 1), (Sum.inr 3999, 1), (Sum.inr 4013, 1), (Sum.inr 4054, 1)]

def sourceForm913 : Integer.Sparse Master := [(Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5271, 1), (Sum.inr 5289, 1), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5412, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5436, 1), (Sum.inr 5441, 1), (Sum.inr 5442, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5487, 1)]

def sourceForm914 : Integer.Sparse Master := [(Sum.inr 3085, 1), (Sum.inr 3086, 1), (Sum.inr 3089, 1), (Sum.inr 3097, 1), (Sum.inr 3109, 1), (Sum.inr 3801, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3853, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3971, 1), (Sum.inr 3972, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 1), (Sum.inr 3982, 1), (Sum.inr 3986, 1), (Sum.inr 3987, 1), (Sum.inr 3990, 1), (Sum.inr 3996, 1), (Sum.inr 4001, 1), (Sum.inr 4027, 1), (Sum.inr 4032, 1), (Sum.inr 4035, 1), (Sum.inr 4037, 1)]

def sourceForm915 : Integer.Sparse Master := [(Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4810, 1), (Sum.inr 4839, 1), (Sum.inr 4889, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5172, 1), (Sum.inr 5294, 1), (Sum.inr 5354, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5387, 1), (Sum.inr 5397, 1), (Sum.inr 5406, 1), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 2), (Sum.inr 5438, 1), (Sum.inr 5440, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 1), (Sum.inr 5453, 1), (Sum.inr 5454, 1), (Sum.inr 5490, 1)]

def sourceForm916 : Integer.Sparse Master := [(Sum.inr 2023, 1), (Sum.inr 2025, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2245, 1), (Sum.inr 2924, 1), (Sum.inr 2931, 1), (Sum.inr 2959, 1), (Sum.inr 3101, 1), (Sum.inr 3692, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3719, 1), (Sum.inr 3736, 1), (Sum.inr 3782, 1), (Sum.inr 3801, 1), (Sum.inr 3823, 1), (Sum.inr 3849, 1), (Sum.inr 3850, 1), (Sum.inr 3853, 2), (Sum.inr 3857, 1), (Sum.inr 3862, 1), (Sum.inr 3910, 1), (Sum.inr 3912, 1), (Sum.inr 3982, 1), (Sum.inr 4013, 1), (Sum.inr 4033, 1), (Sum.inr 4036, 1), (Sum.inr 4040, 1)]

def sourceForm917 : Integer.Sparse Master := [(Sum.inr 5265, 2), (Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5271, 2), (Sum.inr 5299, 2), (Sum.inr 5406, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5412, 2), (Sum.inr 5424, 2), (Sum.inr 5425, 2), (Sum.inr 5426, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 1), (Sum.inr 5442, 2), (Sum.inr 5443, 2)]

def sourceForm919 : Integer.Sparse Master := [(Sum.inr 2392, 1), (Sum.inr 2393, 1), (Sum.inr 2394, 1), (Sum.inr 2405, 1), (Sum.inr 2732, 1), (Sum.inr 2909, 1), (Sum.inr 2910, 1), (Sum.inr 2955, 1), (Sum.inr 3055, 1), (Sum.inr 3347, 1), (Sum.inr 3348, 1), (Sum.inr 3358, 1), (Sum.inr 3541, 1), (Sum.inr 3559, 1), (Sum.inr 3565, 1), (Sum.inr 3584, 1), (Sum.inr 3714, 1), (Sum.inr 3733, 1), (Sum.inr 3839, 1), (Sum.inr 3845, 1), (Sum.inr 3862, 1), (Sum.inr 3868, 1), (Sum.inr 3869, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3889, 1), (Sum.inr 3949, 1), (Sum.inr 3993, 1), (Sum.inr 4003, 1)]

def sourceForm920 : Integer.Sparse Master := [(Sum.inr 2591, 1), (Sum.inr 3733, 1), (Sum.inr 3819, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

def sourceForm923 : Integer.Sparse Master := [(Sum.inr 2031, 1), (Sum.inr 2032, 1), (Sum.inr 2039, 1), (Sum.inr 2049, 1), (Sum.inr 2251, 1), (Sum.inr 2606, 1), (Sum.inr 2608, 1), (Sum.inr 2632, 1), (Sum.inr 2677, 1), (Sum.inr 3527, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3575, 1), (Sum.inr 3696, 1), (Sum.inr 3699, 1), (Sum.inr 3780, 1), (Sum.inr 3802, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3827, 1), (Sum.inr 3831, 1), (Sum.inr 3834, 1), (Sum.inr 3840, 1), (Sum.inr 3846, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3856, 1), (Sum.inr 3881, 2), (Sum.inr 3995, 1)]

def sourceForm924 : Integer.Sparse Master := [(Sum.inr 2078, 1), (Sum.inr 2080, 1), (Sum.inr 2081, 1), (Sum.inr 2108, 1), (Sum.inr 2217, 1), (Sum.inr 2860, 1), (Sum.inr 2867, 1), (Sum.inr 2876, 1), (Sum.inr 3086, 1), (Sum.inr 3374, 1), (Sum.inr 3379, 1), (Sum.inr 3386, 1), (Sum.inr 3570, 1), (Sum.inr 3722, 1), (Sum.inr 3738, 1), (Sum.inr 3752, 1), (Sum.inr 3762, 1), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3788, 1), (Sum.inr 3814, 1), (Sum.inr 3872, 1), (Sum.inr 3873, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3982, 1), (Sum.inr 4027, 1)]

def sourceForm925 : Integer.Sparse Master := [(Sum.inr 2619, 1), (Sum.inr 2872, 1), (Sum.inr 3175, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def sourceForm926 : Integer.Sparse Master := [(Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 3788, 1), (Sum.inr 3809, 1), (Sum.inr 3877, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def sourceForm927 : Integer.Sparse Master := [(Sum.inr 2634, 1), (Sum.inr 2873, 1), (Sum.inr 3699, 1), (Sum.inr 3828, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm928 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2870, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3874, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def sourceForm929 : Integer.Sparse Master := [(Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 3959, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

def sourceForm930 : Integer.Sparse Master := [(Sum.inr 3198, 1), (Sum.inr 3698, 1), (Sum.inr 3699, 1), (Sum.inr 3706, 1), (Sum.inr 3814, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def sourceForm931 : Integer.Sparse Master := [(Sum.inr 2620, 1), (Sum.inr 3045, 1), (Sum.inr 3723, 1), (Sum.inr 3732, 1), (Sum.inr 3850, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def sourceForm932 : Integer.Sparse Master := [(Sum.inr 4746, 1), (Sum.inr 4747, 2), (Sum.inr 4749, 1), (Sum.inr 4898, 1), (Sum.inr 5155, 2), (Sum.inr 5156, 2), (Sum.inr 5170, 2), (Sum.inr 5302, 2), (Sum.inr 5328, 1), (Sum.inr 5329, 1), (Sum.inr 5374, 1), (Sum.inr 5384, 2), (Sum.inr 5403, 2), (Sum.inr 5412, 3), (Sum.inr 5437, 1), (Sum.inr 5439, 2), (Sum.inr 5443, 2), (Sum.inr 5453, 1), (Sum.inr 5456, 1)]

def sourceForm933 : Integer.Sparse Master := [(Sum.inr 4816, 1), (Sum.inr 4817, 1), (Sum.inr 4821, 1), (Sum.inr 4836, 1), (Sum.inr 4891, 1), (Sum.inr 5086, 1), (Sum.inr 5090, 1), (Sum.inr 5105, 1), (Sum.inr 5254, 1), (Sum.inr 5260, 1), (Sum.inr 5267, 2), (Sum.inr 5287, 1), (Sum.inr 5360, 2), (Sum.inr 5361, 1), (Sum.inr 5370, 1), (Sum.inr 5397, 1), (Sum.inr 5406, 1), (Sum.inr 5407, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 3), (Sum.inr 5412, 1), (Sum.inr 5425, 1), (Sum.inr 5426, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5436, 1)]

def sourceForm934 : Integer.Sparse Master := [(Sum.inr 2196, 1), (Sum.inr 2197, 1), (Sum.inr 2207, 1), (Sum.inr 2217, 1), (Sum.inr 2253, 1), (Sum.inr 3016, 1), (Sum.inr 3025, 1), (Sum.inr 3038, 1), (Sum.inr 3086, 1), (Sum.inr 3464, 1), (Sum.inr 3479, 1), (Sum.inr 3480, 1), (Sum.inr 3541, 1), (Sum.inr 3762, 2), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3796, 1), (Sum.inr 3801, 1), (Sum.inr 3803, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3813, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3982, 1)]

def sourceForm935 : Integer.Sparse Master := [(Sum.inr 4992, 1), (Sum.inr 4993, 1), (Sum.inr 4999, 2), (Sum.inr 5004, 1), (Sum.inr 5005, 2), (Sum.inr 5011, 1), (Sum.inr 5145, 2), (Sum.inr 5251, 1), (Sum.inr 5265, 1), (Sum.inr 5282, 1), (Sum.inr 5379, 2), (Sum.inr 5414, 1), (Sum.inr 5421, 2), (Sum.inr 5424, 2), (Sum.inr 5431, 2), (Sum.inr 5439, 1), (Sum.inr 5446, 2), (Sum.inr 5450, 1), (Sum.inr 5470, 2), (Sum.inr 5472, 1), (Sum.inr 5481, 1)]

def sourceForm936 : Integer.Sparse Master := [(Sum.inr 2378, 1), (Sum.inr 2379, 1), (Sum.inr 2384, 2), (Sum.inr 2710, 1), (Sum.inr 2912, 1), (Sum.inr 2925, 2), (Sum.inr 3078, 1), (Sum.inr 3337, 1), (Sum.inr 3342, 2), (Sum.inr 3526, 1), (Sum.inr 3720, 2), (Sum.inr 3869, 1), (Sum.inr 3946, 2), (Sum.inr 3955, 2), (Sum.inr 3957, 1), (Sum.inr 3959, 2), (Sum.inr 3979, 1), (Sum.inr 3990, 2), (Sum.inr 4012, 1), (Sum.inr 4026, 2), (Sum.inr 4029, 1)]

def sourceForm937 : Integer.Sparse Master := [(Sum.inr 2389, 1), (Sum.inr 2390, 2), (Sum.inr 2396, 1), (Sum.inr 2730, 1), (Sum.inr 3345, 1), (Sum.inr 3346, 2), (Sum.inr 3350, 1), (Sum.inr 3539, 1), (Sum.inr 3562, 2), (Sum.inr 3580, 1), (Sum.inr 3819, 1), (Sum.inr 3832, 2), (Sum.inr 3843, 2), (Sum.inr 3858, 1), (Sum.inr 3873, 2), (Sum.inr 3875, 2), (Sum.inr 3884, 2), (Sum.inr 3887, 1), (Sum.inr 3947, 2), (Sum.inr 3991, 1), (Sum.inr 4002, 1)]

def sourceForm938 : Integer.Sparse Master := [(Sum.inr 3846, 1), (Sum.inr 3947, 2), (Sum.inr 3949, 1), (Sum.inr 3957, 1), (Sum.inr 4008, 1), (Sum.inr 4091, -1)]

def sourceForm940 : Integer.Sparse Master := [(Sum.inr 2567, 1), (Sum.inr 3724, 1), (Sum.inr 3827, 1), (Sum.inr 3838, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

def sourceForm941 : Integer.Sparse Master := [(Sum.inr 4791, 1), (Sum.inr 4795, 1), (Sum.inr 4799, 2), (Sum.inr 4863, 1), (Sum.inr 5181, 1), (Sum.inr 5184, 2), (Sum.inr 5243, 1), (Sum.inr 5348, 1), (Sum.inr 5350, 2), (Sum.inr 5354, 2), (Sum.inr 5379, 2), (Sum.inr 5383, 1), (Sum.inr 5406, 1), (Sum.inr 5414, 2), (Sum.inr 5429, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5447, 1), (Sum.inr 5471, 1), (Sum.inr 5472, 2), (Sum.inr 5482, 1)]

def sourceForm942 : Integer.Sparse Master := [(Sum.inr 2008, 1), (Sum.inr 2012, 1), (Sum.inr 2017, 2), (Sum.inr 2232, 1), (Sum.inr 2609, 1), (Sum.inr 2614, 2), (Sum.inr 2697, 1), (Sum.inr 3685, 1), (Sum.inr 3688, 2), (Sum.inr 3818, 2), (Sum.inr 3819, 2), (Sum.inr 3832, 2), (Sum.inr 3846, 2), (Sum.inr 3847, 1), (Sum.inr 3848, 2), (Sum.inr 3867, 1), (Sum.inr 3875, 1), (Sum.inr 3909, 1), (Sum.inr 3976, 1), (Sum.inr 3992, 1), (Sum.inr 4002, 2)]

def sourceForm943 : Integer.Sparse Master := [(Sum.inr 2074, 1), (Sum.inr 2076, 2), (Sum.inr 2104, 1), (Sum.inr 2213, 1), (Sum.inr 3488, 1), (Sum.inr 3491, 1), (Sum.inr 3524, 2), (Sum.inr 3720, 2), (Sum.inr 3734, 1), (Sum.inr 3750, 2), (Sum.inr 3768, 1), (Sum.inr 3769, 2), (Sum.inr 3812, 1), (Sum.inr 3869, 2), (Sum.inr 3871, 2), (Sum.inr 3874, 2), (Sum.inr 3882, 1), (Sum.inr 3956, 1), (Sum.inr 3957, 2), (Sum.inr 3980, 1), (Sum.inr 4026, 1)]

def sourceForm944 : Integer.Sparse Master := [(Sum.inr 3849, 1), (Sum.inr 3953, 1), (Sum.inr 3954, 1), (Sum.inr 3957, 2), (Sum.inr 4046, 1), (Sum.inr 4091, -1)]

def sourceForm945 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 3176, 2), (Sum.inr 3179, 1), (Sum.inr 3199, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def sourceForm946 : Integer.Sparse Master := [(Sum.inr 3179, 1), (Sum.inr 3731, 1), (Sum.inr 3954, 3), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

def sourceForm947 : Integer.Sparse Master := [(Sum.inr 2859, 1), (Sum.inr 3685, 1), (Sum.inr 3935, 2), (Sum.inr 3953, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def sourceForm948 : Integer.Sparse Master := [(Sum.inr 3176, 1), (Sum.inr 3724, 1), (Sum.inr 3935, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

def sourceForm949 : Integer.Sparse Master := [(Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 2), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def sourceForm950 : Integer.Sparse Master := [(Sum.inr 3199, 1), (Sum.inr 3685, 1), (Sum.inr 3692, 2), (Sum.inr 3801, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def sourceForm951 : Integer.Sparse Master := [(Sum.inr 3030, 1), (Sum.inr 3724, 2), (Sum.inr 3731, 1), (Sum.inr 3849, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def sourceForm952 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 2859, 1), (Sum.inr 2864, 2), (Sum.inr 3030, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def sourceForm954 : Integer.Sparse Master := [(Sum.inr 2606, 2), (Sum.inr 2607, 1), (Sum.inr 2631, 1), (Sum.inr 2676, 1), (Sum.inr 3524, 1), (Sum.inr 3525, 1), (Sum.inr 3527, 2), (Sum.inr 3566, 1), (Sum.inr 3780, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3802, 2), (Sum.inr 3847, 1), (Sum.inr 3850, 2), (Sum.inr 3852, 2), (Sum.inr 3854, 2), (Sum.inr 3878, 1), (Sum.inr 3881, 2), (Sum.inr 3938, 1), (Sum.inr 3976, 1), (Sum.inr 3995, 2)]

def sourceForm955 : Integer.Sparse Master := [(Sum.inr 2860, 2), (Sum.inr 2864, 1), (Sum.inr 2874, 1), (Sum.inr 3085, 1), (Sum.inr 3374, 2), (Sum.inr 3378, 1), (Sum.inr 3384, 1), (Sum.inr 3569, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 2), (Sum.inr 3788, 2), (Sum.inr 3801, 1), (Sum.inr 3877, 2), (Sum.inr 3953, 1), (Sum.inr 3958, 2), (Sum.inr 3959, 2), (Sum.inr 3977, 1), (Sum.inr 3982, 2), (Sum.inr 4023, 1), (Sum.inr 4027, 2)]

def sourceForm956 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 3703, 1), (Sum.inr 3874, 1), (Sum.inr 3956, 1), (Sum.inr 3961, 2), (Sum.inr 4092, -1)]

def sourceForm957 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2869, 1), (Sum.inr 3697, 1), (Sum.inr 3874, 1), (Sum.inr 3884, 2), (Sum.inr 4092, -1)]

def sourceForm958 : Integer.Sparse Master := [(Sum.inr 3786, 1), (Sum.inr 3788, 2), (Sum.inr 3805, 1), (Sum.inr 3874, 1), (Sum.inr 3956, 1), (Sum.inr 4092, -1)]

def sourceForm959 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2870, 2), (Sum.inr 2878, 1), (Sum.inr 3043, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm96 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1209, 1), (Sum.inr 1217, 2), (Sum.inr 1249, 1), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

def sourceForm97 : Integer.Sparse Master := [(Sum.inr 1249, 1), (Sum.inr 2562, 1), (Sum.inr 2624, 2), (Sum.inr 2712, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

def sourceForm98 : Integer.Sparse Master := [(Sum.inr 1388, 1), (Sum.inr 2470, 1), (Sum.inr 2485, 2), (Sum.inr 2712, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

def sourceForm99 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 2470, 1), (Sum.inr 2610, 2), (Sum.inr 2709, 1), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

def sourceForm100 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 2543, 2), (Sum.inr 2562, 1), (Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

def sourceForm101 : Integer.Sparse Master := [(Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2618, 1), (Sum.inr 2712, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

def sourceForm102 : Integer.Sparse Master := [(Sum.inr 1394, 1), (Sum.inr 2610, 1), (Sum.inr 2618, 1), (Sum.inr 2624, 1), (Sum.inr 2712, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def sourceForm103 : Integer.Sparse Master := [(Sum.inr 1209, 1), (Sum.inr 1378, 1), (Sum.inr 1388, 1), (Sum.inr 1394, 2), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

def sourceForm106 : Integer.Sparse Master := [(Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 3492, 1), (Sum.inr 3543, 1), (Sum.inr 3545, 2), (Sum.inr 4085, -1)]

def sourceForm107 : Integer.Sparse Master := [(Sum.inr 2050, 1), (Sum.inr 2052, 1), (Sum.inr 2055, 2), (Sum.inr 2290, 1), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

def sourceForm108 : Integer.Sparse Master := [(Sum.inr 2290, 2), (Sum.inr 3543, 2), (Sum.inr 3634, 2), (Sum.inr 4085, -1)]

def sourceForm109 : Integer.Sparse Master := [(Sum.inr 3387, 1), (Sum.inr 3389, 2), (Sum.inr 3393, 2), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

def sourceForm110 : Integer.Sparse Master := [(Sum.inr 2050, 2), (Sum.inr 3387, 1), (Sum.inr 3543, 3), (Sum.inr 4085, -1)]

def sourceForm111 : Integer.Sparse Master := [(Sum.inr 4463, 3), (Sum.inr 4468, 1), (Sum.inr 4507, 1), (Sum.inr 4608, 3), (Sum.inr 4625, 1), (Sum.inr 5078, 6), (Sum.inr 5109, 3), (Sum.inr 5174, 3), (Sum.inr 5293, 3), (Sum.inr 5294, 3), (Sum.inr 5309, 1), (Sum.inr 5310, 1), (Sum.inr 5455, 1)]

def sourceForm112 : Integer.Sparse Master := [(Sum.inr 1046, 3), (Sum.inr 1051, 1), (Sum.inr 1091, 1), (Sum.inr 1242, 3), (Sum.inr 1304, 1), (Sum.inr 2485, 6), (Sum.inr 2519, 3), (Sum.inr 2601, 3), (Sum.inr 2768, 3), (Sum.inr 2788, 1), (Sum.inr 3102, 3), (Sum.inr 3123, 1), (Sum.inr 4019, 1)]

def sourceForm113 : Integer.Sparse Master := [(Sum.inr 4890, 6), (Sum.inr 4897, 2), (Sum.inr 4899, 2), (Sum.inr 5252, 6), (Sum.inr 5261, 6), (Sum.inr 5268, 3), (Sum.inr 5296, 3), (Sum.inr 5312, 2)]

def sourceForm114 : Integer.Sparse Master := [(Sum.inr 2247, 3), (Sum.inr 2268, 1), (Sum.inr 2281, 1), (Sum.inr 2712, 6), (Sum.inr 2726, 3), (Sum.inr 2734, 3), (Sum.inr 2755, 3), (Sum.inr 2770, 3), (Sum.inr 2778, 1), (Sum.inr 2790, 1), (Sum.inr 3090, 3), (Sum.inr 3114, 1), (Sum.inr 3126, 1)]

def sourceForm115 : Integer.Sparse Master := [(Sum.inr 2292, 1), (Sum.inr 3545, 3), (Sum.inr 3634, 1), (Sum.inr 3636, 1), (Sum.inr 4085, -1)]

def sourceForm116 : Integer.Sparse Master := [(Sum.inr 2290, 3), (Sum.inr 2292, 1), (Sum.inr 2294, 1), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

def sourceForm117 : Integer.Sparse Master := [(Sum.inr 4276, 3), (Sum.inr 4280, 1), (Sum.inr 4285, 1), (Sum.inr 4572, 3), (Sum.inr 4621, 1), (Sum.inr 4747, 6), (Sum.inr 4754, 3), (Sum.inr 4871, 3), (Sum.inr 4898, 3), (Sum.inr 4899, 1), (Sum.inr 5302, 3), (Sum.inr 5310, 1), (Sum.inr 5456, 1)]

def sourceForm118 : Integer.Sparse Master := [(Sum.inr 828, 3), (Sum.inr 832, 1), (Sum.inr 860, 1), (Sum.inr 1190, 3), (Sum.inr 1297, 1), (Sum.inr 1926, 6), (Sum.inr 1951, 3), (Sum.inr 2112, 3), (Sum.inr 2279, 3), (Sum.inr 2294, 1), (Sum.inr 3054, 3), (Sum.inr 3121, 1), (Sum.inr 3916, 1)]

def sourceForm119 : Integer.Sparse Master := [(Sum.inr 4476, 3), (Sum.inr 4478, 3), (Sum.inr 4481, 1), (Sum.inr 4507, 1), (Sum.inr 4508, 1), (Sum.inr 4817, 6), (Sum.inr 4843, 3), (Sum.inr 4881, 3), (Sum.inr 4896, 3), (Sum.inr 4901, 1), (Sum.inr 5276, 3), (Sum.inr 5310, 1), (Sum.inr 5311, 1)]

def sourceForm120 : Integer.Sparse Master := [(Sum.inr 1061, 3), (Sum.inr 1064, 1), (Sum.inr 1092, 1), (Sum.inr 1372, 3), (Sum.inr 1445, 1), (Sum.inr 2497, 6), (Sum.inr 2520, 3), (Sum.inr 2642, 3), (Sum.inr 2777, 3), (Sum.inr 2789, 1), (Sum.inr 3121, 1), (Sum.inr 3225, 3), (Sum.inr 3231, 1)]

def sourceForm121 : Integer.Sparse Master := [(Sum.inr 1729, 3), (Sum.inr 1746, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 1757, 1), (Sum.inr 2207, 6), (Sum.inr 2230, 3), (Sum.inr 2266, 3), (Sum.inr 2267, 3), (Sum.inr 2293, 1), (Sum.inr 2744, 3), (Sum.inr 2788, 1), (Sum.inr 2789, 1)]

def sourceForm122 : Integer.Sparse Master := [(Sum.inr 2278, 3), (Sum.inr 2281, 1), (Sum.inr 2293, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def sourceForm123 : Integer.Sparse Master := [(Sum.inr 1064, 1), (Sum.inr 1369, 3), (Sum.inr 1438, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def sourceForm124 : Integer.Sparse Master := [(Sum.inr 1369, 1), (Sum.inr 2035, 2), (Sum.inr 2062, 1), (Sum.inr 2281, 1), (Sum.inr 3052, 1), (Sum.inr 4084, -1)]

def sourceForm125 : Integer.Sparse Master := [(Sum.inr 1059, 1), (Sum.inr 2035, 2), (Sum.inr 2134, 1), (Sum.inr 2278, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def sourceForm126 : Integer.Sparse Master := [(Sum.inr 1438, 1), (Sum.inr 2134, 3), (Sum.inr 2281, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def sourceForm127 : Integer.Sparse Master := [(Sum.inr 1091, 1), (Sum.inr 2062, 3), (Sum.inr 2281, 1), (Sum.inr 2293, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm960 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 3043, 1), (Sum.inr 3786, 1), (Sum.inr 3850, 2), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

def sourceForm963 : Integer.Sparse Master := [(Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4803, 2), (Sum.inr 4885, 1), (Sum.inr 5067, 1), (Sum.inr 5076, 2), (Sum.inr 5251, 1), (Sum.inr 5348, 1), (Sum.inr 5353, 2), (Sum.inr 5354, 2), (Sum.inr 5403, 2), (Sum.inr 5405, 1), (Sum.inr 5406, 2), (Sum.inr 5408, 2), (Sum.inr 5425, 2), (Sum.inr 5429, 1), (Sum.inr 5430, 2), (Sum.inr 5433, 1), (Sum.inr 5437, 1), (Sum.inr 5447, 1), (Sum.inr 5482, 1)]

def sourceForm964 : Integer.Sparse Master := [(Sum.inr 2009, 1), (Sum.inr 2012, 1), (Sum.inr 2021, 2), (Sum.inr 2233, 1), (Sum.inr 2981, 1), (Sum.inr 2986, 2), (Sum.inr 3064, 1), (Sum.inr 3685, 1), (Sum.inr 3691, 2), (Sum.inr 3818, 2), (Sum.inr 3822, 2), (Sum.inr 3839, 2), (Sum.inr 3846, 1), (Sum.inr 3847, 2), (Sum.inr 3848, 2), (Sum.inr 3899, 1), (Sum.inr 3909, 1), (Sum.inr 3977, 1), (Sum.inr 3992, 1), (Sum.inr 4033, 1), (Sum.inr 4038, 2)]

def sourceForm965 : Integer.Sparse Master := [(Sum.inr 2195, 2), (Sum.inr 2201, 1), (Sum.inr 2213, 1), (Sum.inr 2252, 1), (Sum.inr 3476, 1), (Sum.inr 3477, 2), (Sum.inr 3539, 1), (Sum.inr 3761, 2), (Sum.inr 3768, 1), (Sum.inr 3769, 2), (Sum.inr 3805, 1), (Sum.inr 3806, 2), (Sum.inr 3810, 2), (Sum.inr 3812, 2), (Sum.inr 3840, 2), (Sum.inr 3851, 1), (Sum.inr 3855, 1), (Sum.inr 3871, 2), (Sum.inr 3874, 1), (Sum.inr 3882, 1), (Sum.inr 3980, 1)]

def sourceForm966 : Integer.Sparse Master := [(Sum.inr 5085, 1), (Sum.inr 5086, 2), (Sum.inr 5098, 1), (Sum.inr 5254, 2), (Sum.inr 5256, 1), (Sum.inr 5265, 2), (Sum.inr 5286, 1), (Sum.inr 5359, 1), (Sum.inr 5360, 2), (Sum.inr 5365, 1), (Sum.inr 5405, 2), (Sum.inr 5406, 1), (Sum.inr 5407, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5412, 2), (Sum.inr 5429, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 2)]

def sourceForm967 : Integer.Sparse Master := [(Sum.inr 2974, 2), (Sum.inr 2976, 1), (Sum.inr 2996, 1), (Sum.inr 3037, 1), (Sum.inr 3525, 1), (Sum.inr 3526, 1), (Sum.inr 3528, 2), (Sum.inr 3567, 1), (Sum.inr 3780, 2), (Sum.inr 3800, 1), (Sum.inr 3801, 1), (Sum.inr 3803, 2), (Sum.inr 3846, 1), (Sum.inr 3852, 2), (Sum.inr 3853, 2), (Sum.inr 3856, 2), (Sum.inr 3878, 1), (Sum.inr 3883, 2), (Sum.inr 3938, 1), (Sum.inr 3977, 1), (Sum.inr 3996, 2)]

def sourceForm968 : Integer.Sparse Master := [(Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 3037, 1), (Sum.inr 3085, 1), (Sum.inr 3460, 1), (Sum.inr 3461, 1), (Sum.inr 3464, 2), (Sum.inr 3526, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 2), (Sum.inr 3800, 1), (Sum.inr 3803, 2), (Sum.inr 3808, 2), (Sum.inr 3809, 2), (Sum.inr 3814, 2), (Sum.inr 3847, 1), (Sum.inr 3853, 2), (Sum.inr 3954, 1), (Sum.inr 3977, 1), (Sum.inr 3982, 2)]

def sourceForm969 : Integer.Sparse Master := [(Sum.inr 2508, 1), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 3816, 2), (Sum.inr 4092, -1)]

def sourceForm972 : Integer.Sparse Master := [(Sum.inr 2534, 1), (Sum.inr 2535, 1), (Sum.inr 2537, 1), (Sum.inr 2587, 1), (Sum.inr 2669, 1), (Sum.inr 3431, 1), (Sum.inr 3434, 1), (Sum.inr 3463, 1), (Sum.inr 3529, 1), (Sum.inr 3531, 1), (Sum.inr 3536, 1), (Sum.inr 3540, 1), (Sum.inr 3568, 1), (Sum.inr 3743, 1), (Sum.inr 3761, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3879, 1), (Sum.inr 3880, 1), (Sum.inr 3884, 1), (Sum.inr 3927, 1), (Sum.inr 3978, 1), (Sum.inr 3994, 1), (Sum.inr 3997, 1)]

def sourceForm973 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 3871, 1), (Sum.inr 3927, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def sourceForm976 : Integer.Sparse Master := [(Sum.inr 2984, 1), (Sum.inr 3783, 1), (Sum.inr 3787, 1), (Sum.inr 3800, 1), (Sum.inr 3871, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

def sourceForm977 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 3091, 1), (Sum.inr 3787, 1), (Sum.inr 3871, 1), (Sum.inr 3875, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def sourceForm978 : Integer.Sparse Master := [(Sum.inr 4797, 1), (Sum.inr 4799, 1), (Sum.inr 4803, 1), (Sum.inr 4825, 1), (Sum.inr 4851, 1), (Sum.inr 5129, 1), (Sum.inr 5132, 1), (Sum.inr 5144, 1), (Sum.inr 5249, 1), (Sum.inr 5350, 1), (Sum.inr 5353, 1), (Sum.inr 5362, 1), (Sum.inr 5377, 1), (Sum.inr 5379, 1), (Sum.inr 5380, 1), (Sum.inr 5403, 1), (Sum.inr 5406, 1), (Sum.inr 5414, 1), (Sum.inr 5419, 1), (Sum.inr 5422, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 2), (Sum.inr 5447, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 1)]

def sourceForm979 : Integer.Sparse Master := [(Sum.inr 2070, 1), (Sum.inr 2073, 1), (Sum.inr 2076, 1), (Sum.inr 2088, 1), (Sum.inr 2195, 1), (Sum.inr 2545, 1), (Sum.inr 2551, 1), (Sum.inr 2566, 1), (Sum.inr 2708, 1), (Sum.inr 3716, 1), (Sum.inr 3720, 1), (Sum.inr 3726, 1), (Sum.inr 3748, 1), (Sum.inr 3750, 1), (Sum.inr 3761, 1), (Sum.inr 3810, 1), (Sum.inr 3812, 1), (Sum.inr 3825, 1), (Sum.inr 3829, 1), (Sum.inr 3840, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2), (Sum.inr 3874, 1), (Sum.inr 3882, 1), (Sum.inr 3978, 1), (Sum.inr 3979, 1), (Sum.inr 3980, 1), (Sum.inr 3990, 1), (Sum.inr 3994, 1)]

def sourceForm980 : Integer.Sparse Master := [(Sum.inr 2015, 1), (Sum.inr 2017, 1), (Sum.inr 2021, 1), (Sum.inr 2044, 1), (Sum.inr 2240, 1), (Sum.inr 3499, 1), (Sum.inr 3502, 1), (Sum.inr 3516, 1), (Sum.inr 3557, 1), (Sum.inr 3688, 1), (Sum.inr 3691, 1), (Sum.inr 3700, 1), (Sum.inr 3819, 1), (Sum.inr 3822, 1), (Sum.inr 3832, 1), (Sum.inr 3835, 1), (Sum.inr 3836, 1), (Sum.inr 3839, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 1), (Sum.inr 3846, 1), (Sum.inr 3847, 1), (Sum.inr 3848, 2), (Sum.inr 3900, 1), (Sum.inr 3909, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3991, 1), (Sum.inr 3992, 1)]

def sourceForm982 : Integer.Sparse Master := [(Sum.inr 2916, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 1), (Sum.inr 3724, 1), (Sum.inr 3838, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

def sourceForm983 : Integer.Sparse Master := [(Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 3964, 1), (Sum.inr 3972, 2), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

def sourceForm986 : Integer.Sparse Master := [(Sum.inr 3066, 1), (Sum.inr 3789, 1), (Sum.inr 3949, 1), (Sum.inr 3972, 2), (Sum.inr 4008, 1), (Sum.inr 4091, -1)]

def sourceForm987 : Integer.Sparse Master := [(Sum.inr 5082, 1), (Sum.inr 5083, 1), (Sum.inr 5086, 1), (Sum.inr 5091, 1), (Sum.inr 5144, 1), (Sum.inr 5146, 1), (Sum.inr 5160, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5357, 1), (Sum.inr 5358, 1), (Sum.inr 5360, 1), (Sum.inr 5381, 1), (Sum.inr 5382, 1), (Sum.inr 5395, 1), (Sum.inr 5411, 1), (Sum.inr 5420, 1), (Sum.inr 5421, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 2), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1), (Sum.inr 5468, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1)]

def sourceForm988 : Integer.Sparse Master := [(Sum.inr 2490, 1), (Sum.inr 2491, 1), (Sum.inr 2494, 1), (Sum.inr 2500, 1), (Sum.inr 2773, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3560, 1), (Sum.inr 3572, 1), (Sum.inr 3695, 1), (Sum.inr 3696, 1), (Sum.inr 3698, 1), (Sum.inr 3827, 1), (Sum.inr 3834, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3866, 1), (Sum.inr 3870, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3888, 1), (Sum.inr 3968, 1), (Sum.inr 3970, 1), (Sum.inr 3989, 1), (Sum.inr 3995, 1)]

def sourceForm989 : Integer.Sparse Master := [(Sum.inr 2921, 1), (Sum.inr 2922, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3097, 1), (Sum.inr 3441, 1), (Sum.inr 3447, 1), (Sum.inr 3464, 1), (Sum.inr 3573, 1), (Sum.inr 3718, 1), (Sum.inr 3722, 1), (Sum.inr 3730, 1), (Sum.inr 3752, 1), (Sum.inr 3762, 1), (Sum.inr 3794, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 3872, 1), (Sum.inr 3873, 1), (Sum.inr 3950, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3971, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1), (Sum.inr 4022, 1), (Sum.inr 4027, 1), (Sum.inr 4032, 1)]

def sourceForm990 : Integer.Sparse Master := [(Sum.inr 3781, 1), (Sum.inr 3848, 1), (Sum.inr 3944, 1), (Sum.inr 3946, 1), (Sum.inr 3961, 1), (Sum.inr 4044, 1), (Sum.inr 4092, -1)]

def sourceForm991 : Integer.Sparse Master := [(Sum.inr 2977, 1), (Sum.inr 3723, 1), (Sum.inr 3725, 1), (Sum.inr 3730, 1), (Sum.inr 3848, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm992 : Integer.Sparse Master := [(Sum.inr 2975, 1), (Sum.inr 3826, 1), (Sum.inr 3828, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 3944, 1), (Sum.inr 4092, -1)]

def sourceForm993 : Integer.Sparse Master := [(Sum.inr 5105, 2), (Sum.inr 5109, 1), (Sum.inr 5110, 1), (Sum.inr 5203, 2), (Sum.inr 5207, 1), (Sum.inr 5237, 2), (Sum.inr 5238, 1), (Sum.inr 5293, 1), (Sum.inr 5304, 1), (Sum.inr 5310, 1), (Sum.inr 5370, 2), (Sum.inr 5422, 2), (Sum.inr 5434, 2), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5454, 1), (Sum.inr 5455, 1), (Sum.inr 5484, 2), (Sum.inr 5492, 1), (Sum.inr 5494, 1)]

def sourceForm994 : Integer.Sparse Master := [(Sum.inr 2515, 2), (Sum.inr 2519, 1), (Sum.inr 2522, 1), (Sum.inr 2788, 1), (Sum.inr 2884, 2), (Sum.inr 2889, 1), (Sum.inr 3102, 1), (Sum.inr 3394, 2), (Sum.inr 3397, 1), (Sum.inr 3583, 1), (Sum.inr 3706, 2), (Sum.inr 3862, 1), (Sum.inr 3964, 2), (Sum.inr 3982, 2), (Sum.inr 3983, 2), (Sum.inr 3987, 2), (Sum.inr 4015, 1), (Sum.inr 4019, 1), (Sum.inr 4020, 1), (Sum.inr 4029, 2), (Sum.inr 4040, 1)]

def sourceForm995 : Integer.Sparse Master := [(Sum.inr 4866, 2), (Sum.inr 4868, 1), (Sum.inr 4875, 1), (Sum.inr 4896, 1), (Sum.inr 5163, 2), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5401, 2), (Sum.inr 5404, 2), (Sum.inr 5411, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 1), (Sum.inr 5453, 1), (Sum.inr 5485, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 1)]

def sourceForm996 : Integer.Sparse Master := [(Sum.inr 2107, 2), (Sum.inr 2109, 1), (Sum.inr 2116, 1), (Sum.inr 2278, 1), (Sum.inr 2590, 2), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 3737, 2), (Sum.inr 3741, 1), (Sum.inr 3787, 2), (Sum.inr 3790, 2), (Sum.inr 3813, 2), (Sum.inr 3876, 2), (Sum.inr 3887, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 3915, 1), (Sum.inr 3998, 2), (Sum.inr 4001, 1), (Sum.inr 4017, 1), (Sum.inr 4018, 1)]

def sourceForm997 : Integer.Sparse Master := [(Sum.inr 5289, 2), (Sum.inr 5291, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5304, 1), (Sum.inr 5411, 2), (Sum.inr 5413, 1), (Sum.inr 5430, 2), (Sum.inr 5432, 2), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5441, 1), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 2), (Sum.inr 5449, 1), (Sum.inr 5473, 2), (Sum.inr 5475, 1), (Sum.inr 5487, 1)]

def sourceForm1000 : Integer.Sparse Master := [(Sum.inr 2390, 1), (Sum.inr 2391, 1), (Sum.inr 2395, 1), (Sum.inr 2401, 1), (Sum.inr 2537, 1), (Sum.inr 2538, 1), (Sum.inr 2591, 1), (Sum.inr 2673, 1), (Sum.inr 2731, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3355, 1), (Sum.inr 3540, 1), (Sum.inr 3568, 1), (Sum.inr 3578, 1), (Sum.inr 3580, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3873, 1), (Sum.inr 3874, 1), (Sum.inr 3879, 1), (Sum.inr 3880, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 1), (Sum.inr 3929, 1), (Sum.inr 3947, 1), (Sum.inr 3995, 1), (Sum.inr 3997, 1)]

def sourceForm1001 : Integer.Sparse Master := [(Sum.inr 2955, 1), (Sum.inr 3881, 1), (Sum.inr 3929, 1), (Sum.inr 3947, 1), (Sum.inr 3958, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def sourceForm1003 : Integer.Sparse Master := [(Sum.inr 2633, 1), (Sum.inr 3092, 1), (Sum.inr 3827, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def sourceForm1004 : Integer.Sparse Master := [(Sum.inr 4849, 1), (Sum.inr 4850, 1), (Sum.inr 4856, 1), (Sum.inr 4861, 1), (Sum.inr 4867, 1), (Sum.inr 5183, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5264, 1), (Sum.inr 5353, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5379, 1), (Sum.inr 5382, 1), (Sum.inr 5384, 1), (Sum.inr 5385, 2), (Sum.inr 5399, 1), (Sum.inr 5402, 1), (Sum.inr 5411, 2), (Sum.inr 5421, 1), (Sum.inr 5428, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1)]

def sourceForm1005 : Integer.Sparse Master := [(Sum.inr 2086, 1), (Sum.inr 2087, 1), (Sum.inr 2094, 1), (Sum.inr 2102, 1), (Sum.inr 2251, 1), (Sum.inr 2613, 1), (Sum.inr 2620, 1), (Sum.inr 2632, 1), (Sum.inr 2729, 1), (Sum.inr 3724, 1), (Sum.inr 3728, 1), (Sum.inr 3733, 1), (Sum.inr 3783, 1), (Sum.inr 3785, 1), (Sum.inr 3802, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3827, 1), (Sum.inr 3831, 1), (Sum.inr 3854, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3876, 1), (Sum.inr 3880, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3976, 1), (Sum.inr 3981, 1), (Sum.inr 3995, 1), (Sum.inr 4003, 1)]

def sourceForm1006 : Integer.Sparse Master := [(Sum.inr 2098, 1), (Sum.inr 2099, 1), (Sum.inr 2102, 1), (Sum.inr 2108, 1), (Sum.inr 2274, 1), (Sum.inr 3501, 1), (Sum.inr 3506, 1), (Sum.inr 3538, 1), (Sum.inr 3570, 1), (Sum.inr 3730, 1), (Sum.inr 3733, 1), (Sum.inr 3738, 1), (Sum.inr 3761, 1), (Sum.inr 3770, 1), (Sum.inr 3771, 1), (Sum.inr 3785, 1), (Sum.inr 3788, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3845, 1), (Sum.inr 3868, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3953, 1), (Sum.inr 3958, 1), (Sum.inr 3981, 1), (Sum.inr 3993, 1)]

def sourceForm1008 : Integer.Sparse Master := [(Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 3720, 1), (Sum.inr 3733, 1), (Sum.inr 3845, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def sourceForm1012 : Integer.Sparse Master := [(Sum.inr 3174, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3809, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def sourceForm1013 : Integer.Sparse Master := [(Sum.inr 3040, 1), (Sum.inr 3730, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 3857, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def sourceForm1015 : Integer.Sparse Master := [(Sum.inr 2491, 1), (Sum.inr 2492, 1), (Sum.inr 2499, 1), (Sum.inr 2506, 1), (Sum.inr 2607, 1), (Sum.inr 2608, 1), (Sum.inr 2633, 1), (Sum.inr 2678, 1), (Sum.inr 2774, 1), (Sum.inr 3566, 1), (Sum.inr 3570, 1), (Sum.inr 3572, 1), (Sum.inr 3575, 1), (Sum.inr 3696, 1), (Sum.inr 3699, 1), (Sum.inr 3846, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3870, 1), (Sum.inr 3871, 1), (Sum.inr 3878, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3886, 1), (Sum.inr 3888, 1), (Sum.inr 3939, 1), (Sum.inr 3968, 1), (Sum.inr 3995, 1), (Sum.inr 4004, 1)]

def sourceForm1016 : Integer.Sparse Master := [(Sum.inr 2874, 1), (Sum.inr 2875, 1), (Sum.inr 2876, 1), (Sum.inr 2885, 1), (Sum.inr 3097, 1), (Sum.inr 3384, 1), (Sum.inr 3385, 1), (Sum.inr 3386, 1), (Sum.inr 3395, 1), (Sum.inr 3447, 1), (Sum.inr 3480, 1), (Sum.inr 3578, 1), (Sum.inr 3584, 1), (Sum.inr 3752, 1), (Sum.inr 3759, 1), (Sum.inr 3767, 1), (Sum.inr 3772, 1), (Sum.inr 3809, 1), (Sum.inr 3877, 1), (Sum.inr 3950, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1), (Sum.inr 4022, 1), (Sum.inr 4027, 1), (Sum.inr 4030, 1)]

def sourceForm1017 : Integer.Sparse Master := [(Sum.inr 2882, 1), (Sum.inr 3705, 1), (Sum.inr 3884, 1), (Sum.inr 3944, 1), (Sum.inr 3961, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

def sourceForm1018 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2871, 1), (Sum.inr 2873, 1), (Sum.inr 2882, 1), (Sum.inr 3044, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def sourceForm1020 : Integer.Sparse Master := [(Sum.inr 1913, 1), (Sum.inr 1915, 1), (Sum.inr 1917, 1), (Sum.inr 1949, 1), (Sum.inr 2266, 1), (Sum.inr 2853, 1), (Sum.inr 2856, 1), (Sum.inr 2881, 1), (Sum.inr 3077, 1), (Sum.inr 3370, 1), (Sum.inr 3372, 1), (Sum.inr 3391, 1), (Sum.inr 3564, 1), (Sum.inr 3653, 1), (Sum.inr 3666, 1), (Sum.inr 3778, 1), (Sum.inr 3782, 1), (Sum.inr 3801, 1), (Sum.inr 3804, 1), (Sum.inr 3809, 3), (Sum.inr 3815, 1), (Sum.inr 3862, 1), (Sum.inr 3912, 1), (Sum.inr 3913, 1), (Sum.inr 4010, 1), (Sum.inr 4025, 1), (Sum.inr 4029, 1), (Sum.inr 4039, 1)]

def sourceForm1021 : Integer.Sparse Master := [(Sum.inr 4852, 1), (Sum.inr 4853, 1), (Sum.inr 4856, 1), (Sum.inr 4867, 1), (Sum.inr 4891, 1), (Sum.inr 5074, 1), (Sum.inr 5080, 1), (Sum.inr 5105, 1), (Sum.inr 5260, 1), (Sum.inr 5353, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5384, 1), (Sum.inr 5397, 1), (Sum.inr 5402, 1), (Sum.inr 5405, 1), (Sum.inr 5407, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 2), (Sum.inr 5425, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 2), (Sum.inr 5483, 1)]

def sourceForm1022 : Integer.Sparse Master := [(Sum.inr 2250, 1), (Sum.inr 2251, 1), (Sum.inr 2253, 1), (Sum.inr 2259, 1), (Sum.inr 2274, 1), (Sum.inr 3463, 1), (Sum.inr 3478, 1), (Sum.inr 3479, 1), (Sum.inr 3540, 1), (Sum.inr 3761, 1), (Sum.inr 3770, 1), (Sum.inr 3771, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3800, 1), (Sum.inr 3802, 1), (Sum.inr 3803, 1), (Sum.inr 3807, 1), (Sum.inr 3808, 1), (Sum.inr 3811, 1), (Sum.inr 3814, 1), (Sum.inr 3840, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3856, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3981, 1)]

def sourceForm1023 : Integer.Sparse Master := [(Sum.inr 5085, 1), (Sum.inr 5086, 1), (Sum.inr 5087, 1), (Sum.inr 5090, 2), (Sum.inr 5102, 1), (Sum.inr 5103, 1), (Sum.inr 5266, 1), (Sum.inr 5286, 1), (Sum.inr 5287, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5302, 1), (Sum.inr 5359, 1), (Sum.inr 5360, 1), (Sum.inr 5361, 1), (Sum.inr 5368, 1), (Sum.inr 5395, 1), (Sum.inr 5406, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5413, 1), (Sum.inr 5425, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1024 : Integer.Sparse Master := [(Sum.inr 3023, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3051, 1), (Sum.inr 3097, 1), (Sum.inr 3461, 1), (Sum.inr 3464, 1), (Sum.inr 3471, 1), (Sum.inr 3472, 1), (Sum.inr 3480, 2), (Sum.inr 3535, 1), (Sum.inr 3626, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 1), (Sum.inr 3767, 1), (Sum.inr 3772, 1), (Sum.inr 3794, 1), (Sum.inr 3801, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3817, 1), (Sum.inr 3839, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1), (Sum.inr 3959, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1)]

def sourceForm1025 : Integer.Sparse Master := [(Sum.inr 5064, 1), (Sum.inr 5067, 1), (Sum.inr 5071, 2), (Sum.inr 5181, 1), (Sum.inr 5185, 2), (Sum.inr 5244, 1), (Sum.inr 5282, 1), (Sum.inr 5348, 1), (Sum.inr 5350, 2), (Sum.inr 5352, 2), (Sum.inr 5405, 1), (Sum.inr 5421, 2), (Sum.inr 5429, 1), (Sum.inr 5431, 1), (Sum.inr 5448, 1), (Sum.inr 5470, 2), (Sum.inr 5472, 2), (Sum.inr 5473, 2), (Sum.inr 5480, 2), (Sum.inr 5482, 1), (Sum.inr 5485, 1)]

def sourceForm1026 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2473, 1), (Sum.inr 2478, 2), (Sum.inr 2609, 1), (Sum.inr 2615, 2), (Sum.inr 2698, 1), (Sum.inr 2751, 1), (Sum.inr 3685, 1), (Sum.inr 3688, 2), (Sum.inr 3846, 1), (Sum.inr 3873, 2), (Sum.inr 3875, 1), (Sum.inr 3885, 1), (Sum.inr 3936, 2), (Sum.inr 3947, 2), (Sum.inr 3977, 1), (Sum.inr 3978, 2), (Sum.inr 3992, 1), (Sum.inr 3995, 2), (Sum.inr 3998, 1), (Sum.inr 4002, 2)]

def sourceForm1027 : Integer.Sparse Master := [(Sum.inr 3443, 1), (Sum.inr 3445, 2), (Sum.inr 3476, 1), (Sum.inr 3491, 1), (Sum.inr 3497, 1), (Sum.inr 3529, 2), (Sum.inr 3580, 1), (Sum.inr 3750, 2), (Sum.inr 3764, 2), (Sum.inr 3768, 1), (Sum.inr 3805, 1), (Sum.inr 3874, 1), (Sum.inr 3946, 2), (Sum.inr 3955, 2), (Sum.inr 3957, 2), (Sum.inr 3961, 2), (Sum.inr 3978, 2), (Sum.inr 3980, 1), (Sum.inr 3984, 1), (Sum.inr 4026, 1), (Sum.inr 4028, 1)]

def sourceForm1029 : Integer.Sparse Master := [(Sum.inr 2981, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 2), (Sum.inr 3800, 1), (Sum.inr 3953, 1), (Sum.inr 4091, -1)]

def sourceForm1030 : Integer.Sparse Master := [(Sum.inr 5183, 2), (Sum.inr 5187, 1), (Sum.inr 5197, 1), (Sum.inr 5263, 1), (Sum.inr 5351, 1), (Sum.inr 5353, 2), (Sum.inr 5365, 1), (Sum.inr 5399, 2), (Sum.inr 5400, 1), (Sum.inr 5402, 2), (Sum.inr 5405, 2), (Sum.inr 5414, 2), (Sum.inr 5428, 2), (Sum.inr 5429, 1), (Sum.inr 5438, 2), (Sum.inr 5446, 2), (Sum.inr 5471, 1), (Sum.inr 5473, 2), (Sum.inr 5483, 2)]

def sourceForm1031 : Integer.Sparse Master := [(Sum.inr 3501, 2), (Sum.inr 3505, 1), (Sum.inr 3537, 1), (Sum.inr 3569, 1), (Sum.inr 3757, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 2), (Sum.inr 3785, 2), (Sum.inr 3788, 2), (Sum.inr 3800, 1), (Sum.inr 3845, 2), (Sum.inr 3869, 1), (Sum.inr 3884, 2), (Sum.inr 3949, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 2), (Sum.inr 3976, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 2), (Sum.inr 3993, 2), (Sum.inr 4023, 1)]

def sourceForm1032 : Integer.Sparse Master := [(Sum.inr 2613, 2), (Sum.inr 2617, 1), (Sum.inr 2631, 1), (Sum.inr 2728, 1), (Sum.inr 3783, 2), (Sum.inr 3785, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3802, 2), (Sum.inr 3846, 1), (Sum.inr 3869, 1), (Sum.inr 3876, 2), (Sum.inr 3881, 2), (Sum.inr 3937, 1), (Sum.inr 3938, 1), (Sum.inr 3949, 1), (Sum.inr 3953, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 2), (Sum.inr 3995, 2), (Sum.inr 4003, 2)]

def sourceForm1033 : Integer.Sparse Master := [(Sum.inr 3689, 1), (Sum.inr 3691, 2), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 3956, 1), (Sum.inr 4092, -1)]

def sourceForm1036 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2456, 1), (Sum.inr 2460, 1), (Sum.inr 2493, 1), (Sum.inr 2533, 1), (Sum.inr 2537, 1), (Sum.inr 2567, 1), (Sum.inr 2662, 1), (Sum.inr 2731, 1), (Sum.inr 3568, 1), (Sum.inr 3569, 1), (Sum.inr 3571, 1), (Sum.inr 3574, 1), (Sum.inr 3680, 1), (Sum.inr 3697, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 1), (Sum.inr 3879, 1), (Sum.inr 3880, 2), (Sum.inr 3882, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 1), (Sum.inr 3923, 1), (Sum.inr 3969, 1), (Sum.inr 3994, 1), (Sum.inr 3995, 1)]

def sourceForm1039 : Integer.Sparse Master := [(Sum.inr 2976, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 2), (Sum.inr 3909, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

def sourceForm1040 : Integer.Sparse Master := [(Sum.inr 4848, 1), (Sum.inr 4849, 2), (Sum.inr 4852, 2), (Sum.inr 5378, 2), (Sum.inr 5379, 2), (Sum.inr 5381, 2), (Sum.inr 5382, 2), (Sum.inr 5397, 2), (Sum.inr 5411, 2), (Sum.inr 5420, 2), (Sum.inr 5421, 2), (Sum.inr 5424, 2), (Sum.inr 5425, 2), (Sum.inr 5446, 2), (Sum.inr 5477, 2), (Sum.inr 5483, 1)]

def sourceForm1041 : Integer.Sparse Master := [(Sum.inr 2085, 1), (Sum.inr 2086, 1), (Sum.inr 2089, 1), (Sum.inr 2098, 1), (Sum.inr 2250, 1), (Sum.inr 3723, 1), (Sum.inr 3724, 1), (Sum.inr 3727, 1), (Sum.inr 3730, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3813, 1), (Sum.inr 3826, 1), (Sum.inr 3827, 1), (Sum.inr 3830, 1), (Sum.inr 3832, 1), (Sum.inr 3834, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3866, 1), (Sum.inr 3870, 1), (Sum.inr 3872, 1), (Sum.inr 3873, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3971, 1), (Sum.inr 3981, 1), (Sum.inr 3989, 1), (Sum.inr 3990, 1)]

def sourceForm1043 : Integer.Sparse Master := [(Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5081, 1), (Sum.inr 5102, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5169, 1), (Sum.inr 5259, 1), (Sum.inr 5293, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5368, 1), (Sum.inr 5434, 1), (Sum.inr 5460, 1), (Sum.inr 5465, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 1), (Sum.inr 5476, 1), (Sum.inr 5477, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 1), (Sum.inr 5487, 1), (Sum.inr 5490, 1), (Sum.inr 5491, 1), (Sum.inr 5493, 1), (Sum.inr 5499, 1)]

def sourceForm1044 : Integer.Sparse Master := [(Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2489, 1), (Sum.inr 2512, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2595, 1), (Sum.inr 2723, 1), (Sum.inr 2767, 1), (Sum.inr 3690, 1), (Sum.inr 3694, 1), (Sum.inr 3705, 1), (Sum.inr 3852, 1), (Sum.inr 3921, 1), (Sum.inr 3931, 1), (Sum.inr 3945, 1), (Sum.inr 3958, 1), (Sum.inr 3965, 1), (Sum.inr 3971, 1), (Sum.inr 3980, 1), (Sum.inr 3981, 2), (Sum.inr 3984, 1), (Sum.inr 3992, 1), (Sum.inr 3999, 1), (Sum.inr 4000, 1), (Sum.inr 4013, 1), (Sum.inr 4014, 1), (Sum.inr 4018, 1), (Sum.inr 4054, 1)]

def sourceForm1045 : Integer.Sparse Master := [(Sum.inr 5405, 2), (Sum.inr 5409, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5424, 2), (Sum.inr 5428, 2), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 2), (Sum.inr 5445, 1), (Sum.inr 5446, 2), (Sum.inr 5471, 2), (Sum.inr 5473, 2), (Sum.inr 5477, 2), (Sum.inr 5483, 1), (Sum.inr 5487, 2)]

def sourceForm1048 : Integer.Sparse Master := [(Sum.inr 5065, 1), (Sum.inr 5067, 2), (Sum.inr 5073, 2), (Sum.inr 5074, 2), (Sum.inr 5250, 1), (Sum.inr 5284, 1), (Sum.inr 5348, 1), (Sum.inr 5352, 2), (Sum.inr 5353, 2), (Sum.inr 5401, 2), (Sum.inr 5406, 1), (Sum.inr 5408, 2), (Sum.inr 5410, 2), (Sum.inr 5430, 2), (Sum.inr 5433, 1), (Sum.inr 5439, 1), (Sum.inr 5471, 1), (Sum.inr 5480, 2), (Sum.inr 5482, 1), (Sum.inr 5485, 1)]

def sourceForm1049 : Integer.Sparse Master := [(Sum.inr 3463, 2), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3476, 2), (Sum.inr 3531, 1), (Sum.inr 3625, 1), (Sum.inr 3761, 2), (Sum.inr 3764, 2), (Sum.inr 3768, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 2), (Sum.inr 3812, 1), (Sum.inr 3816, 2), (Sum.inr 3848, 2), (Sum.inr 3851, 1), (Sum.inr 3858, 1), (Sum.inr 3956, 1), (Sum.inr 3978, 2), (Sum.inr 3980, 1), (Sum.inr 3984, 1)]

def sourceForm1050 : Integer.Sparse Master := [(Sum.inr 5072, 1), (Sum.inr 5074, 2), (Sum.inr 5098, 1), (Sum.inr 5256, 1), (Sum.inr 5351, 1), (Sum.inr 5353, 2), (Sum.inr 5365, 1), (Sum.inr 5400, 1), (Sum.inr 5402, 2), (Sum.inr 5405, 1), (Sum.inr 5406, 2), (Sum.inr 5407, 2), (Sum.inr 5409, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5429, 1), (Sum.inr 5434, 2), (Sum.inr 5471, 2), (Sum.inr 5483, 2)]

def sourceForm1051 : Integer.Sparse Master := [(Sum.inr 3459, 1), (Sum.inr 3460, 1), (Sum.inr 3463, 2), (Sum.inr 3525, 1), (Sum.inr 3757, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 2), (Sum.inr 3799, 1), (Sum.inr 3801, 1), (Sum.inr 3802, 2), (Sum.inr 3803, 2), (Sum.inr 3807, 2), (Sum.inr 3808, 2), (Sum.inr 3813, 2), (Sum.inr 3846, 1), (Sum.inr 3847, 1), (Sum.inr 3852, 2), (Sum.inr 3953, 1), (Sum.inr 3976, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 2)]

def sourceForm1052 : Integer.Sparse Master := [(Sum.inr 5138, 1), (Sum.inr 5139, 1), (Sum.inr 5140, 1), (Sum.inr 5170, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5199, 1), (Sum.inr 5226, 1), (Sum.inr 5229, 1), (Sum.inr 5236, 1), (Sum.inr 5259, 1), (Sum.inr 5260, 1), (Sum.inr 5289, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 1), (Sum.inr 5419, 1), (Sum.inr 5421, 1), (Sum.inr 5424, 1), (Sum.inr 5430, 1), (Sum.inr 5431, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1), (Sum.inr 5446, 1), (Sum.inr 5448, 1), (Sum.inr 5480, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1)]

def sourceForm1053 : Integer.Sparse Master := [(Sum.inr 2669, 1), (Sum.inr 2670, 1), (Sum.inr 2673, 1), (Sum.inr 2682, 1), (Sum.inr 2763, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3529, 1), (Sum.inr 3540, 1), (Sum.inr 3542, 1), (Sum.inr 3544, 1), (Sum.inr 3578, 1), (Sum.inr 3606, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3859, 1), (Sum.inr 3873, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1)]

def sourceForm1054 : Integer.Sparse Master := [(Sum.inr 2621, 1), (Sum.inr 3115, 1), (Sum.inr 3790, 1), (Sum.inr 3825, 1), (Sum.inr 3876, 2), (Sum.inr 4091, -1)]

def sourceForm1055 : Integer.Sparse Master := [(Sum.inr 4826, 1), (Sum.inr 4827, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4866, 1), (Sum.inr 5070, 1), (Sum.inr 5080, 1), (Sum.inr 5095, 1), (Sum.inr 5291, 1), (Sum.inr 5349, 1), (Sum.inr 5355, 1), (Sum.inr 5363, 1), (Sum.inr 5364, 1), (Sum.inr 5370, 1), (Sum.inr 5380, 1), (Sum.inr 5388, 1), (Sum.inr 5397, 1), (Sum.inr 5401, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1), (Sum.inr 5481, 1), (Sum.inr 5484, 1), (Sum.inr 5490, 1), (Sum.inr 5492, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1056 : Integer.Sparse Master := [(Sum.inr 2077, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2107, 1), (Sum.inr 2216, 1), (Sum.inr 2477, 1), (Sum.inr 2488, 1), (Sum.inr 2505, 1), (Sum.inr 2765, 1), (Sum.inr 3687, 1), (Sum.inr 3693, 1), (Sum.inr 3702, 1), (Sum.inr 3721, 1), (Sum.inr 3737, 1), (Sum.inr 3751, 1), (Sum.inr 3771, 1), (Sum.inr 3787, 1), (Sum.inr 3796, 1), (Sum.inr 3850, 1), (Sum.inr 3875, 1), (Sum.inr 3876, 1), (Sum.inr 3887, 1), (Sum.inr 3888, 1), (Sum.inr 3906, 1), (Sum.inr 3907, 1), (Sum.inr 3979, 1), (Sum.inr 3982, 1), (Sum.inr 3983, 1), (Sum.inr 4013, 1), (Sum.inr 4017, 1)]

def sourceForm1057 : Integer.Sparse Master := [(Sum.inr 5160, 1), (Sum.inr 5163, 1), (Sum.inr 5164, 1), (Sum.inr 5173, 1), (Sum.inr 5263, 1), (Sum.inr 5264, 1), (Sum.inr 5267, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5382, 1), (Sum.inr 5384, 1), (Sum.inr 5385, 1), (Sum.inr 5400, 1), (Sum.inr 5409, 1), (Sum.inr 5414, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5428, 2), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1)]

def sourceForm1058 : Integer.Sparse Master := [(Sum.inr 2728, 1), (Sum.inr 2729, 1), (Sum.inr 2732, 1), (Sum.inr 2735, 1), (Sum.inr 2773, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3583, 1), (Sum.inr 3799, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3850, 1), (Sum.inr 3861, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3881, 1), (Sum.inr 3888, 1), (Sum.inr 3889, 1), (Sum.inr 3976, 1), (Sum.inr 3981, 1), (Sum.inr 3995, 1), (Sum.inr 4003, 1)]

def sourceForm1059 : Integer.Sparse Master := [(Sum.inr 5047, 1), (Sum.inr 5050, 2), (Sum.inr 5059, 2), (Sum.inr 5073, 2), (Sum.inr 5259, 2), (Sum.inr 5341, 1), (Sum.inr 5346, 2), (Sum.inr 5352, 2), (Sum.inr 5424, 2), (Sum.inr 5467, 1), (Sum.inr 5473, 2), (Sum.inr 5476, 1), (Sum.inr 5478, 2), (Sum.inr 5482, 2), (Sum.inr 5483, 2), (Sum.inr 5490, 2), (Sum.inr 5491, 1), (Sum.inr 5500, 1)]

def sourceForm1060 : Integer.Sparse Master := [(Sum.inr 2449, 1), (Sum.inr 2452, 2), (Sum.inr 2462, 2), (Sum.inr 2480, 2), (Sum.inr 2723, 2), (Sum.inr 3678, 1), (Sum.inr 3683, 2), (Sum.inr 3690, 2), (Sum.inr 3838, 2), (Sum.inr 3942, 1), (Sum.inr 3958, 2), (Sum.inr 3965, 1), (Sum.inr 3974, 2), (Sum.inr 3980, 2), (Sum.inr 3981, 2), (Sum.inr 4013, 2), (Sum.inr 4014, 1), (Sum.inr 4053, 1)]

def sourceForm1061 : Integer.Sparse Master := [(Sum.inr 5394, 1), (Sum.inr 5395, 2), (Sum.inr 5397, 2), (Sum.inr 5410, 2), (Sum.inr 5420, 1), (Sum.inr 5421, 2), (Sum.inr 5423, 1), (Sum.inr 5424, 4), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5434, 2), (Sum.inr 5445, 2), (Sum.inr 5468, 1), (Sum.inr 5473, 2), (Sum.inr 5477, 1), (Sum.inr 5483, 2), (Sum.inr 5487, 1)]

def sourceForm1062 : Integer.Sparse Master := [(Sum.inr 3793, 1), (Sum.inr 3794, 2), (Sum.inr 3796, 2), (Sum.inr 3808, 2), (Sum.inr 3838, 2), (Sum.inr 3870, 1), (Sum.inr 3872, 2), (Sum.inr 3873, 2), (Sum.inr 3880, 2), (Sum.inr 3950, 1), (Sum.inr 3958, 2), (Sum.inr 3972, 2), (Sum.inr 3981, 2), (Sum.inr 3982, 2), (Sum.inr 3986, 1), (Sum.inr 3989, 1), (Sum.inr 3990, 2), (Sum.inr 4032, 1)]

def sourceForm1063 : Integer.Sparse Master := [(Sum.inr 5128, 1), (Sum.inr 5129, 1), (Sum.inr 5130, 1), (Sum.inr 5137, 1), (Sum.inr 5138, 1), (Sum.inr 5145, 1), (Sum.inr 5149, 1), (Sum.inr 5251, 1), (Sum.inr 5259, 1), (Sum.inr 5377, 1), (Sum.inr 5379, 1), (Sum.inr 5380, 1), (Sum.inr 5393, 1), (Sum.inr 5396, 1), (Sum.inr 5410, 1), (Sum.inr 5419, 1), (Sum.inr 5421, 1), (Sum.inr 5424, 2), (Sum.inr 5427, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5431, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 1)]

def sourceForm1064 : Integer.Sparse Master := [(Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3519, 1), (Sum.inr 3520, 1), (Sum.inr 3521, 1), (Sum.inr 3539, 1), (Sum.inr 3544, 1), (Sum.inr 3562, 1), (Sum.inr 3605, 1), (Sum.inr 3797, 1), (Sum.inr 3798, 1), (Sum.inr 3816, 1), (Sum.inr 3832, 1), (Sum.inr 3835, 1), (Sum.inr 3836, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 2), (Sum.inr 3844, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3859, 1), (Sum.inr 3873, 1), (Sum.inr 3874, 1), (Sum.inr 3875, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3991, 1), (Sum.inr 3992, 1)]

def sourceForm1065 : Integer.Sparse Master := [(Sum.inr 4779, 1), (Sum.inr 4782, 1), (Sum.inr 4787, 1), (Sum.inr 4802, 1), (Sum.inr 4831, 1), (Sum.inr 5050, 1), (Sum.inr 5056, 1), (Sum.inr 5072, 1), (Sum.inr 5258, 1), (Sum.inr 5341, 1), (Sum.inr 5344, 1), (Sum.inr 5346, 2), (Sum.inr 5351, 1), (Sum.inr 5352, 1), (Sum.inr 5365, 1), (Sum.inr 5416, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 2), (Sum.inr 5428, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5477, 1), (Sum.inr 5478, 1), (Sum.inr 5482, 1), (Sum.inr 5490, 1), (Sum.inr 5500, 1)]

def sourceForm1066 : Integer.Sparse Master := [(Sum.inr 1987, 1), (Sum.inr 1990, 1), (Sum.inr 2000, 1), (Sum.inr 2020, 1), (Sum.inr 2191, 1), (Sum.inr 2452, 1), (Sum.inr 2459, 1), (Sum.inr 2479, 1), (Sum.inr 2722, 1), (Sum.inr 3678, 1), (Sum.inr 3681, 1), (Sum.inr 3683, 1), (Sum.inr 3689, 1), (Sum.inr 3690, 1), (Sum.inr 3746, 1), (Sum.inr 3758, 1), (Sum.inr 3821, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3843, 1), (Sum.inr 3845, 1), (Sum.inr 3851, 1), (Sum.inr 3852, 1), (Sum.inr 3901, 1), (Sum.inr 3902, 1), (Sum.inr 3971, 1), (Sum.inr 3974, 1), (Sum.inr 3980, 1), (Sum.inr 4013, 1), (Sum.inr 4053, 1)]

def sourceForm1067 : Integer.Sparse Master := [(Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5138, 1), (Sum.inr 5160, 1), (Sum.inr 5271, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5381, 1), (Sum.inr 5382, 1), (Sum.inr 5394, 1), (Sum.inr 5395, 1), (Sum.inr 5397, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 3), (Sum.inr 5426, 1), (Sum.inr 5428, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5442, 1), (Sum.inr 5445, 1), (Sum.inr 5477, 2), (Sum.inr 5483, 1)]

def sourceForm1068 : Integer.Sparse Master := [(Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 3517, 1), (Sum.inr 3534, 1), (Sum.inr 3558, 1), (Sum.inr 3793, 1), (Sum.inr 3794, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3807, 1), (Sum.inr 3808, 1), (Sum.inr 3832, 1), (Sum.inr 3834, 1), (Sum.inr 3837, 1), (Sum.inr 3839, 1), (Sum.inr 3840, 1), (Sum.inr 3841, 1), (Sum.inr 3845, 1), (Sum.inr 3852, 1), (Sum.inr 3853, 1), (Sum.inr 3861, 1), (Sum.inr 3866, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3880, 1), (Sum.inr 3971, 1), (Sum.inr 3981, 1), (Sum.inr 3989, 1), (Sum.inr 3990, 1)]

def sourceForm1069 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5169, 4), (Sum.inr 5171, 1), (Sum.inr 5177, 2), (Sum.inr 5293, 2), (Sum.inr 5465, 4), (Sum.inr 5466, 1), (Sum.inr 5476, 2), (Sum.inr 5483, 4), (Sum.inr 5486, 4), (Sum.inr 5487, 2), (Sum.inr 5491, 1), (Sum.inr 5493, 2)]

def sourceForm1070 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 1), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5294, 1), (Sum.inr 5309, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5416, 2), (Sum.inr 5418, 2), (Sum.inr 5434, 2), (Sum.inr 5440, 2), (Sum.inr 5442, 3), (Sum.inr 5451, 1), (Sum.inr 5455, 1), (Sum.inr 5485, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 1)]

def sourceForm1071 : Integer.Sparse Master := [(Sum.inr 5145, 1), (Sum.inr 5147, 1), (Sum.inr 5152, 1), (Sum.inr 5164, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5203, 1), (Sum.inr 5266, 1), (Sum.inr 5282, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5369, 1), (Sum.inr 5410, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 1), (Sum.inr 5459, 1), (Sum.inr 5463, 1), (Sum.inr 5469, 1), (Sum.inr 5470, 1), (Sum.inr 5471, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1), (Sum.inr 5478, 1), (Sum.inr 5484, 1), (Sum.inr 5485, 1), (Sum.inr 5486, 1)]

def sourceForm1072 : Integer.Sparse Master := [(Sum.inr 3529, 1), (Sum.inr 3530, 1), (Sum.inr 3535, 1), (Sum.inr 3542, 1), (Sum.inr 3562, 1), (Sum.inr 3565, 1), (Sum.inr 3580, 1), (Sum.inr 3612, 1), (Sum.inr 3621, 1), (Sum.inr 3764, 1), (Sum.inr 3773, 1), (Sum.inr 3774, 1), (Sum.inr 3816, 1), (Sum.inr 3951, 1), (Sum.inr 3952, 1), (Sum.inr 3955, 1), (Sum.inr 3956, 1), (Sum.inr 3957, 1), (Sum.inr 3959, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 2), (Sum.inr 3962, 1), (Sum.inr 3974, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3985, 1), (Sum.inr 4024, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 1)]

def sourceForm1073 : Integer.Sparse Master := [(Sum.inr 4998, 1), (Sum.inr 5000, 1), (Sum.inr 5003, 1), (Sum.inr 5013, 1), (Sum.inr 5014, 1), (Sum.inr 5015, 1), (Sum.inr 5018, 2), (Sum.inr 5059, 1), (Sum.inr 5102, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 1), (Sum.inr 5275, 1), (Sum.inr 5346, 1), (Sum.inr 5368, 1), (Sum.inr 5428, 1), (Sum.inr 5467, 1), (Sum.inr 5469, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5475, 1), (Sum.inr 5477, 1), (Sum.inr 5478, 1), (Sum.inr 5483, 1), (Sum.inr 5485, 1), (Sum.inr 5490, 2), (Sum.inr 5491, 1), (Sum.inr 5492, 1)]

def sourceForm1074 : Integer.Sparse Master := [(Sum.inr 2383, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2404, 1), (Sum.inr 2462, 1), (Sum.inr 2467, 1), (Sum.inr 2512, 1), (Sum.inr 2723, 1), (Sum.inr 2743, 1), (Sum.inr 3341, 1), (Sum.inr 3344, 1), (Sum.inr 3357, 1), (Sum.inr 3534, 1), (Sum.inr 3683, 1), (Sum.inr 3705, 1), (Sum.inr 3845, 1), (Sum.inr 3942, 1), (Sum.inr 3945, 1), (Sum.inr 3957, 1), (Sum.inr 3958, 1), (Sum.inr 3961, 1), (Sum.inr 3963, 1), (Sum.inr 3971, 1), (Sum.inr 3974, 1), (Sum.inr 3981, 1), (Sum.inr 3984, 1), (Sum.inr 4013, 1), (Sum.inr 4014, 1), (Sum.inr 4015, 1), (Sum.inr 4050, 1)]

def sourceForm1075 : Integer.Sparse Master := [(Sum.inr 5197, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5204, 1), (Sum.inr 5299, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5395, 1), (Sum.inr 5410, 1), (Sum.inr 5413, 1), (Sum.inr 5421, 1), (Sum.inr 5428, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5446, 2), (Sum.inr 5451, 1), (Sum.inr 5468, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5475, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5487, 1)]

def sourceForm1076 : Integer.Sparse Master := [(Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3624, 1), (Sum.inr 3758, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 3771, 1), (Sum.inr 3794, 1), (Sum.inr 3808, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3950, 1), (Sum.inr 3953, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1), (Sum.inr 3971, 1), (Sum.inr 3972, 1), (Sum.inr 3981, 1), (Sum.inr 3982, 1), (Sum.inr 3986, 1), (Sum.inr 3987, 1), (Sum.inr 3993, 1), (Sum.inr 4027, 1)]

def sourceForm1077 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 5073, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5104, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5170, 1), (Sum.inr 5259, 1), (Sum.inr 5284, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5369, 1), (Sum.inr 5393, 1), (Sum.inr 5396, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5405, 1), (Sum.inr 5408, 1), (Sum.inr 5410, 2), (Sum.inr 5424, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1), (Sum.inr 5484, 1), (Sum.inr 5485, 1), (Sum.inr 5486, 1)]

def sourceForm1078 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 5098, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1), (Sum.inr 5105, 1), (Sum.inr 5271, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5394, 1), (Sum.inr 5395, 1), (Sum.inr 5397, 1), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 2), (Sum.inr 5412, 1), (Sum.inr 5413, 1), (Sum.inr 5424, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 1), (Sum.inr 5442, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5487, 1)]

def sourceForm1079 : Integer.Sparse Master := [(Sum.inr 5135, 1), (Sum.inr 5139, 1), (Sum.inr 5141, 1), (Sum.inr 5164, 1), (Sum.inr 5187, 1), (Sum.inr 5188, 1), (Sum.inr 5204, 1), (Sum.inr 5267, 1), (Sum.inr 5275, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5367, 1), (Sum.inr 5379, 1), (Sum.inr 5385, 1), (Sum.inr 5395, 1), (Sum.inr 5409, 1), (Sum.inr 5413, 1), (Sum.inr 5414, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5428, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1)]

def sourceForm1080 : Integer.Sparse Master := [(Sum.inr 3515, 1), (Sum.inr 3522, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3548, 1), (Sum.inr 3565, 1), (Sum.inr 3624, 1), (Sum.inr 3757, 1), (Sum.inr 3766, 1), (Sum.inr 3770, 1), (Sum.inr 3794, 1), (Sum.inr 3807, 1), (Sum.inr 3817, 1), (Sum.inr 3832, 1), (Sum.inr 3838, 1), (Sum.inr 3839, 1), (Sum.inr 3845, 1), (Sum.inr 3861, 1), (Sum.inr 3862, 1), (Sum.inr 3868, 1), (Sum.inr 3869, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3953, 1), (Sum.inr 3958, 1), (Sum.inr 3981, 1), (Sum.inr 3993, 1)]

def sourceForm1081 : Integer.Sparse Master := [(Sum.inr 4787, 1), (Sum.inr 4788, 2), (Sum.inr 4835, 2), (Sum.inr 4996, 2), (Sum.inr 5003, 2), (Sum.inr 5015, 2), (Sum.inr 5258, 2), (Sum.inr 5346, 2), (Sum.inr 5368, 2), (Sum.inr 5395, 2), (Sum.inr 5424, 2), (Sum.inr 5434, 2), (Sum.inr 5439, 2), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5490, 2)]

def sourceForm1082 : Integer.Sparse Master := [(Sum.inr 5199, 4), (Sum.inr 5201, 1), (Sum.inr 5207, 2), (Sum.inr 5300, 2), (Sum.inr 5368, 4), (Sum.inr 5371, 1), (Sum.inr 5413, 2), (Sum.inr 5446, 4), (Sum.inr 5449, 1), (Sum.inr 5451, 2), (Sum.inr 5468, 2), (Sum.inr 5473, 4), (Sum.inr 5487, 1)]

def sourceForm1083 : Integer.Sparse Master := [(Sum.inr 3578, 4), (Sum.inr 3579, 1), (Sum.inr 3584, 2), (Sum.inr 3631, 2), (Sum.inr 3767, 4), (Sum.inr 3775, 1), (Sum.inr 3817, 2), (Sum.inr 3950, 2), (Sum.inr 3958, 4), (Sum.inr 3959, 4), (Sum.inr 3986, 1), (Sum.inr 3987, 2), (Sum.inr 4030, 1)]

def sourceForm1084 : Integer.Sparse Master := [(Sum.inr 5018, 8), (Sum.inr 5021, 2), (Sum.inr 5023, 2), (Sum.inr 5275, 4), (Sum.inr 5467, 2), (Sum.inr 5473, 8), (Sum.inr 5491, 2), (Sum.inr 5492, 2)]

def sourceForm1085 : Integer.Sparse Master := [(Sum.inr 5198, 4), (Sum.inr 5201, 1), (Sum.inr 5206, 2), (Sum.inr 5233, 4), (Sum.inr 5235, 1), (Sum.inr 5291, 2), (Sum.inr 5300, 2), (Sum.inr 5420, 2), (Sum.inr 5432, 4), (Sum.inr 5441, 1), (Sum.inr 5446, 4), (Sum.inr 5451, 2), (Sum.inr 5475, 1)]

def sourceForm1086 : Integer.Sparse Master := [(Sum.inr 2678, 4), (Sum.inr 2680, 1), (Sum.inr 2687, 2), (Sum.inr 2774, 2), (Sum.inr 3570, 4), (Sum.inr 3579, 1), (Sum.inr 3582, 2), (Sum.inr 3850, 4), (Sum.inr 3860, 1), (Sum.inr 3870, 2), (Sum.inr 3881, 4), (Sum.inr 3888, 2), (Sum.inr 4004, 1)]

def sourceForm1087 : Integer.Sparse Master := [(Sum.inr 4860, 4), (Sum.inr 4862, 1), (Sum.inr 4874, 4), (Sum.inr 5384, 8), (Sum.inr 5389, 2), (Sum.inr 5398, 2), (Sum.inr 5443, 4), (Sum.inr 5448, 4), (Sum.inr 5491, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1088 : Integer.Sparse Master := [(Sum.inr 5144, 1), (Sum.inr 5147, 1), (Sum.inr 5151, 1), (Sum.inr 5163, 1), (Sum.inr 5184, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5231, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5258, 1), (Sum.inr 5291, 1), (Sum.inr 5299, 1), (Sum.inr 5381, 1), (Sum.inr 5384, 1), (Sum.inr 5400, 1), (Sum.inr 5409, 1), (Sum.inr 5420, 1), (Sum.inr 5423, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5441, 1), (Sum.inr 5446, 1), (Sum.inr 5449, 1), (Sum.inr 5451, 1), (Sum.inr 5473, 1)]

def sourceForm1089 : Integer.Sparse Master := [(Sum.inr 2676, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2681, 1), (Sum.inr 2773, 1), (Sum.inr 3524, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3538, 1), (Sum.inr 3557, 1), (Sum.inr 3564, 1), (Sum.inr 3570, 1), (Sum.inr 3582, 1), (Sum.inr 3799, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3834, 1), (Sum.inr 3837, 1), (Sum.inr 3846, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3860, 1), (Sum.inr 3870, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3886, 1), (Sum.inr 3888, 1), (Sum.inr 3995, 1)]

def sourceForm1090 : Integer.Sparse Master := [(Sum.inr 4798, 2), (Sum.inr 4800, 1), (Sum.inr 4810, 2), (Sum.inr 4828, 2), (Sum.inr 4865, 2), (Sum.inr 5349, 2), (Sum.inr 5355, 2), (Sum.inr 5364, 1), (Sum.inr 5378, 2), (Sum.inr 5387, 2), (Sum.inr 5400, 2), (Sum.inr 5431, 2), (Sum.inr 5432, 1), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 2), (Sum.inr 5490, 1)]

def sourceForm1091 : Integer.Sparse Master := [(Sum.inr 5127, 1), (Sum.inr 5129, 2), (Sum.inr 5134, 2), (Sum.inr 5144, 2), (Sum.inr 5258, 2), (Sum.inr 5376, 1), (Sum.inr 5378, 2), (Sum.inr 5381, 2), (Sum.inr 5394, 1), (Sum.inr 5409, 2), (Sum.inr 5420, 1), (Sum.inr 5424, 2), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5432, 2), (Sum.inr 5434, 2), (Sum.inr 5441, 1), (Sum.inr 5477, 1)]

def sourceForm1092 : Integer.Sparse Master := [(Sum.inr 3513, 1), (Sum.inr 3514, 2), (Sum.inr 3516, 2), (Sum.inr 3533, 2), (Sum.inr 3557, 2), (Sum.inr 3793, 1), (Sum.inr 3795, 2), (Sum.inr 3807, 2), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3838, 2), (Sum.inr 3840, 2), (Sum.inr 3850, 2), (Sum.inr 3852, 2), (Sum.inr 3860, 1), (Sum.inr 3870, 1), (Sum.inr 3871, 2), (Sum.inr 3989, 1)]

def sourceForm1093 : Integer.Sparse Master := [(Sum.inr 4778, 1), (Sum.inr 4782, 4), (Sum.inr 4801, 4), (Sum.inr 5341, 2), (Sum.inr 5344, 2), (Sum.inr 5351, 4), (Sum.inr 5415, 2), (Sum.inr 5423, 2), (Sum.inr 5424, 4), (Sum.inr 5433, 4), (Sum.inr 5500, 1)]

def sourceForm1094 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 5168, 4), (Sum.inr 5171, 1), (Sum.inr 5176, 2), (Sum.inr 5308, 2), (Sum.inr 5387, 4), (Sum.inr 5389, 1), (Sum.inr 5415, 2), (Sum.inr 5439, 4), (Sum.inr 5441, 4), (Sum.inr 5443, 2), (Sum.inr 5455, 2), (Sum.inr 5491, 1)]

def sourceForm1095 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 5072, 1), (Sum.inr 5075, 1), (Sum.inr 5080, 1), (Sum.inr 5101, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5163, 1), (Sum.inr 5258, 1), (Sum.inr 5274, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5367, 1), (Sum.inr 5378, 1), (Sum.inr 5384, 1), (Sum.inr 5394, 1), (Sum.inr 5400, 1), (Sum.inr 5405, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1), (Sum.inr 5441, 1), (Sum.inr 5442, 1), (Sum.inr 5483, 1)]

def sourceForm1096 : Integer.Sparse Master := [(Sum.inr 4080, 4), (Sum.inr 4081, 1), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4088, 4), (Sum.inr 4089, 1), (Sum.inr 4090, 2), (Sum.inr 4091, 4), (Sum.inr 4092, 6), (Sum.inr 4093, 2), (Sum.inr 4094, 1), (Sum.inr 4096, 1)]

def sourceForm1097 : Integer.Sparse Master := [(Sum.inr 5166, 1), (Sum.inr 5168, 1), (Sum.inr 5170, 2), (Sum.inr 5306, 1), (Sum.inr 5383, 1), (Sum.inr 5384, 2), (Sum.inr 5387, 1), (Sum.inr 5403, 2), (Sum.inr 5412, 2), (Sum.inr 5415, 1), (Sum.inr 5437, 1), (Sum.inr 5439, 4), (Sum.inr 5441, 2), (Sum.inr 5443, 2), (Sum.inr 5448, 1), (Sum.inr 5453, 1), (Sum.inr 5455, 2), (Sum.inr 5488, 1), (Sum.inr 5491, 2)]

def sourceForm1098 : Integer.Sparse Master := [(Sum.inr 5148, 1), (Sum.inr 5149, 2), (Sum.inr 5167, 1), (Sum.inr 5292, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5397, 2), (Sum.inr 5406, 2), (Sum.inr 5422, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 2), (Sum.inr 5450, 1), (Sum.inr 5452, 1), (Sum.inr 5454, 2), (Sum.inr 5481, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2)]

def sourceForm1099 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4802, 2), (Sum.inr 4831, 1), (Sum.inr 4887, 1), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5365, 1), (Sum.inr 5415, 1), (Sum.inr 5416, 2), (Sum.inr 5423, 2), (Sum.inr 5424, 4), (Sum.inr 5433, 3), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1), (Sum.inr 5482, 1), (Sum.inr 5497, 1), (Sum.inr 5499, 1), (Sum.inr 5500, 2)]

def sourceForm1100 : Integer.Sparse Master := [(Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5257, 2), (Sum.inr 5281, 1), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5408, 2), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 2), (Sum.inr 5433, 2), (Sum.inr 5437, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 2), (Sum.inr 5445, 2), (Sum.inr 5447, 1), (Sum.inr 5450, 1), (Sum.inr 5478, 2), (Sum.inr 5479, 1), (Sum.inr 5482, 1), (Sum.inr 5486, 1)]

def sourceForm1101 : Integer.Sparse Master := [(Sum.inr 5155, 6), (Sum.inr 5166, 2), (Sum.inr 5301, 2), (Sum.inr 5374, 3), (Sum.inr 5383, 2), (Sum.inr 5412, 6), (Sum.inr 5439, 6), (Sum.inr 5453, 3)]

def sourceForm1102 : Integer.Sparse Master := [(Sum.inr 4815, 3), (Sum.inr 4830, 1), (Sum.inr 4885, 1), (Sum.inr 5251, 3), (Sum.inr 5277, 1), (Sum.inr 5359, 3), (Sum.inr 5406, 3), (Sum.inr 5422, 3), (Sum.inr 5425, 6), (Sum.inr 5433, 3), (Sum.inr 5447, 2), (Sum.inr 5479, 1)]

def sourceForm1103 : Integer.Sparse Master := [(Sum.inr 4864, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5400, 1), (Sum.inr 5401, 2), (Sum.inr 5406, 1), (Sum.inr 5431, 2), (Sum.inr 5432, 2), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5440, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 2), (Sum.inr 5453, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1)]

def sourceForm1104 : Integer.Sparse Master := [(Sum.inr 5265, 1), (Sum.inr 5266, 2), (Sum.inr 5270, 1), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5290, 2), (Sum.inr 5301, 1), (Sum.inr 5429, 1), (Sum.inr 5431, 2), (Sum.inr 5433, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 2), (Sum.inr 5445, 2), (Sum.inr 5446, 2), (Sum.inr 5447, 1), (Sum.inr 5448, 2), (Sum.inr 5450, 2), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1), (Sum.inr 5486, 1)]

def sourceForm1105 : Integer.Sparse Master := [(Sum.inr 5123, 3), (Sum.inr 5162, 1), (Sum.inr 5192, 3), (Sum.inr 5202, 1), (Sum.inr 5227, 1), (Sum.inr 5283, 1), (Sum.inr 5391, 3), (Sum.inr 5411, 6), (Sum.inr 5447, 1), (Sum.inr 5450, 3), (Sum.inr 5452, 3), (Sum.inr 5462, 1), (Sum.inr 5485, 3)]

def sourceForm1106 : Integer.Sparse Master := [(Sum.inr 2853, 3), (Sum.inr 2880, 1), (Sum.inr 3076, 1), (Sum.inr 3370, 3), (Sum.inr 3390, 1), (Sum.inr 3563, 1), (Sum.inr 3778, 3), (Sum.inr 3809, 6), (Sum.inr 4007, 1), (Sum.inr 4010, 3), (Sum.inr 4025, 1), (Sum.inr 4029, 3), (Sum.inr 4039, 3)]

def sourceForm1107 : Integer.Sparse Master := [(Sum.inr 4851, 3), (Sum.inr 4863, 1), (Sum.inr 4885, 1), (Sum.inr 5380, 3), (Sum.inr 5383, 1), (Sum.inr 5406, 3), (Sum.inr 5422, 3), (Sum.inr 5427, 1), (Sum.inr 5429, 3), (Sum.inr 5430, 6), (Sum.inr 5437, 1), (Sum.inr 5479, 1), (Sum.inr 5482, 3)]

def sourceForm1108 : Integer.Sparse Master := [(Sum.inr 5085, 3), (Sum.inr 5097, 1), (Sum.inr 5277, 1), (Sum.inr 5281, 3), (Sum.inr 5301, 1), (Sum.inr 5359, 3), (Sum.inr 5433, 3), (Sum.inr 5437, 1), (Sum.inr 5445, 6), (Sum.inr 5450, 3), (Sum.inr 5469, 3), (Sum.inr 5474, 1), (Sum.inr 5479, 1)]

def sourceForm1109 : Integer.Sparse Master := [(Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3074, 3), (Sum.inr 3461, 3), (Sum.inr 3619, 1), (Sum.inr 3759, 3), (Sum.inr 3899, 1), (Sum.inr 3952, 3), (Sum.inr 3962, 1), (Sum.inr 3975, 1), (Sum.inr 4024, 6), (Sum.inr 4029, 3), (Sum.inr 4033, 3)]

def sourceForm1110 : Integer.Sparse Master := [(Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 1), (Sum.inr 5290, 1), (Sum.inr 5401, 2), (Sum.inr 5404, 2), (Sum.inr 5411, 2), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5442, 2), (Sum.inr 5447, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 2), (Sum.inr 5452, 1), (Sum.inr 5462, 1), (Sum.inr 5481, 1), (Sum.inr 5485, 3), (Sum.inr 5489, 1), (Sum.inr 5492, 2), (Sum.inr 5493, 2)]

def sourceForm1111 : Integer.Sparse Master := [(Sum.inr 5098, 1), (Sum.inr 5099, 1), (Sum.inr 5102, 2), (Sum.inr 5247, 1), (Sum.inr 5248, 1), (Sum.inr 5271, 2), (Sum.inr 5306, 1), (Sum.inr 5365, 1), (Sum.inr 5368, 2), (Sum.inr 5439, 1), (Sum.inr 5469, 2), (Sum.inr 5473, 2), (Sum.inr 5478, 2), (Sum.inr 5482, 1), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5492, 2), (Sum.inr 5493, 1), (Sum.inr 5499, 1)]

def sourceForm1112 : Integer.Sparse Master := [(Sum.inr 5069, 1), (Sum.inr 5071, 1), (Sum.inr 5074, 1), (Sum.inr 5092, 1), (Sum.inr 5132, 1), (Sum.inr 5138, 1), (Sum.inr 5160, 1), (Sum.inr 5255, 1), (Sum.inr 5289, 1), (Sum.inr 5350, 1), (Sum.inr 5353, 1), (Sum.inr 5362, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5419, 1), (Sum.inr 5421, 1), (Sum.inr 5424, 1), (Sum.inr 5430, 2), (Sum.inr 5438, 1), (Sum.inr 5461, 1), (Sum.inr 5470, 1), (Sum.inr 5471, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1)]

def sourceForm1113 : Integer.Sparse Master := [(Sum.inr 2550, 1), (Sum.inr 2551, 1), (Sum.inr 2557, 1), (Sum.inr 2587, 1), (Sum.inr 2718, 1), (Sum.inr 3442, 1), (Sum.inr 3445, 1), (Sum.inr 3463, 1), (Sum.inr 3572, 1), (Sum.inr 3748, 1), (Sum.inr 3750, 1), (Sum.inr 3761, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3848, 1), (Sum.inr 3871, 1), (Sum.inr 3922, 1), (Sum.inr 3927, 1), (Sum.inr 3946, 1), (Sum.inr 3955, 1), (Sum.inr 3956, 1), (Sum.inr 3978, 1), (Sum.inr 3979, 1), (Sum.inr 3980, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1), (Sum.inr 3994, 1), (Sum.inr 3997, 1)]

def sourceForm1114 : Integer.Sparse Master := [(Sum.inr 2476, 1), (Sum.inr 2478, 1), (Sum.inr 2481, 1), (Sum.inr 2501, 1), (Sum.inr 2763, 1), (Sum.inr 3499, 1), (Sum.inr 3503, 1), (Sum.inr 3517, 1), (Sum.inr 3558, 1), (Sum.inr 3688, 1), (Sum.inr 3691, 1), (Sum.inr 3700, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3873, 1), (Sum.inr 3947, 1), (Sum.inr 3966, 1), (Sum.inr 3972, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 1), (Sum.inr 3976, 1), (Sum.inr 3977, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3991, 1), (Sum.inr 3992, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1)]

def sourceForm1116 : Integer.Sparse Master := [(Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5167, 1), (Sum.inr 5257, 1), (Sum.inr 5393, 2), (Sum.inr 5395, 2), (Sum.inr 5405, 2), (Sum.inr 5434, 2), (Sum.inr 5460, 1), (Sum.inr 5464, 1), (Sum.inr 5469, 1), (Sum.inr 5472, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 2), (Sum.inr 5486, 2), (Sum.inr 5489, 2), (Sum.inr 5490, 2), (Sum.inr 5498, 1), (Sum.inr 5499, 2)]

def sourceForm1117 : Integer.Sparse Master := [(Sum.inr 5072, 1), (Sum.inr 5073, 2), (Sum.inr 5098, 1), (Sum.inr 5292, 1), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5365, 1), (Sum.inr 5416, 1), (Sum.inr 5424, 2), (Sum.inr 5433, 1), (Sum.inr 5476, 2), (Sum.inr 5477, 2), (Sum.inr 5478, 2), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1), (Sum.inr 5497, 1), (Sum.inr 5499, 1), (Sum.inr 5500, 2)]

def sourceForm1118 : Integer.Sparse Master := [(Sum.inr 5070, 2), (Sum.inr 5076, 1), (Sum.inr 5093, 1), (Sum.inr 5290, 1), (Sum.inr 5349, 2), (Sum.inr 5354, 1), (Sum.inr 5363, 1), (Sum.inr 5397, 2), (Sum.inr 5401, 2), (Sum.inr 5416, 1), (Sum.inr 5422, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5492, 2)]

def sourceForm1119 : Integer.Sparse Master := [(Sum.inr 2477, 2), (Sum.inr 2483, 1), (Sum.inr 2503, 1), (Sum.inr 2764, 1), (Sum.inr 3687, 2), (Sum.inr 3692, 1), (Sum.inr 3701, 1), (Sum.inr 3787, 2), (Sum.inr 3796, 2), (Sum.inr 3849, 1), (Sum.inr 3876, 2), (Sum.inr 3900, 1), (Sum.inr 3901, 1), (Sum.inr 3910, 1), (Sum.inr 3967, 1), (Sum.inr 3982, 2), (Sum.inr 3983, 2), (Sum.inr 3998, 1), (Sum.inr 4011, 1), (Sum.inr 4013, 2), (Sum.inr 4017, 2)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1120 : Integer.Sparse Master := [(Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5255, 2), (Sum.inr 5281, 1), (Sum.inr 5401, 2), (Sum.inr 5403, 1), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5424, 2), (Sum.inr 5429, 1), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5439, 1), (Sum.inr 5470, 2), (Sum.inr 5472, 1), (Sum.inr 5478, 2), (Sum.inr 5480, 2), (Sum.inr 5482, 2), (Sum.inr 5484, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 1)]

def sourceForm1121 : Integer.Sparse Master := [(Sum.inr 2708, 1), (Sum.inr 2710, 1), (Sum.inr 2718, 2), (Sum.inr 2750, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 1), (Sum.inr 3810, 1), (Sum.inr 3849, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2), (Sum.inr 3954, 1), (Sum.inr 3955, 2), (Sum.inr 3957, 1), (Sum.inr 3978, 2), (Sum.inr 3980, 2), (Sum.inr 3983, 2), (Sum.inr 3985, 1), (Sum.inr 3990, 2), (Sum.inr 3994, 2), (Sum.inr 3998, 1), (Sum.inr 4012, 1)]

def sourceForm1122 : Integer.Sparse Master := [(Sum.inr 5160, 1), (Sum.inr 5161, 1), (Sum.inr 5164, 1), (Sum.inr 5170, 1), (Sum.inr 5255, 1), (Sum.inr 5260, 1), (Sum.inr 5269, 1), (Sum.inr 5289, 2), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 1), (Sum.inr 5430, 1), (Sum.inr 5438, 2), (Sum.inr 5439, 1), (Sum.inr 5446, 1), (Sum.inr 5461, 1), (Sum.inr 5463, 1), (Sum.inr 5470, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 2), (Sum.inr 5481, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 2), (Sum.inr 5486, 1)]

def sourceForm1123 : Integer.Sparse Master := [(Sum.inr 2718, 1), (Sum.inr 2719, 1), (Sum.inr 2724, 1), (Sum.inr 2736, 1), (Sum.inr 2763, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3572, 1), (Sum.inr 3606, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 1), (Sum.inr 3857, 1), (Sum.inr 3955, 1), (Sum.inr 3959, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 1), (Sum.inr 3972, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 2), (Sum.inr 3979, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3985, 1), (Sum.inr 3993, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1), (Sum.inr 4012, 1)]

def sourceForm1124 : Integer.Sparse Master := [(Sum.inr 5093, 2), (Sum.inr 5094, 1), (Sum.inr 5095, 2), (Sum.inr 5105, 2), (Sum.inr 5304, 2), (Sum.inr 5363, 2), (Sum.inr 5364, 1), (Sum.inr 5370, 2), (Sum.inr 5422, 2), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5451, 2), (Sum.inr 5481, 2), (Sum.inr 5484, 2), (Sum.inr 5490, 1), (Sum.inr 5492, 2), (Sum.inr 5494, 1)]

def sourceForm1125 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5292, 1), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5476, 2), (Sum.inr 5482, 3), (Sum.inr 5483, 2), (Sum.inr 5486, 2), (Sum.inr 5487, 2), (Sum.inr 5490, 2), (Sum.inr 5493, 1), (Sum.inr 5497, 1), (Sum.inr 5499, 2)]

def sourceForm1126 : Integer.Sparse Master := [(Sum.inr 5055, 1), (Sum.inr 5056, 2), (Sum.inr 5059, 2), (Sum.inr 5098, 2), (Sum.inr 5271, 2), (Sum.inr 5344, 1), (Sum.inr 5346, 2), (Sum.inr 5365, 2), (Sum.inr 5424, 2), (Sum.inr 5467, 1), (Sum.inr 5473, 2), (Sum.inr 5477, 2), (Sum.inr 5478, 1), (Sum.inr 5482, 2), (Sum.inr 5485, 2), (Sum.inr 5490, 2), (Sum.inr 5492, 1), (Sum.inr 5500, 1)]

def sourceForm1127 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 5396, 3), (Sum.inr 5422, 3), (Sum.inr 5427, 1), (Sum.inr 5433, 3), (Sum.inr 5437, 1), (Sum.inr 5447, 2), (Sum.inr 5469, 3), (Sum.inr 5474, 1), (Sum.inr 5478, 6), (Sum.inr 5482, 3), (Sum.inr 5486, 3)]

def sourceForm1128 : Integer.Sparse Master := [(Sum.inr 5184, 1), (Sum.inr 5185, 2), (Sum.inr 5202, 1), (Sum.inr 5265, 1), (Sum.inr 5352, 2), (Sum.inr 5354, 1), (Sum.inr 5366, 1), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5429, 3), (Sum.inr 5431, 2), (Sum.inr 5450, 1), (Sum.inr 5470, 2), (Sum.inr 5471, 2), (Sum.inr 5472, 2), (Sum.inr 5473, 2), (Sum.inr 5474, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 2), (Sum.inr 5486, 1)]

def sourceForm1129 : Integer.Sparse Master := [(Sum.inr 3524, 1), (Sum.inr 3526, 1), (Sum.inr 3529, 2), (Sum.inr 3617, 1), (Sum.inr 3764, 2), (Sum.inr 3765, 1), (Sum.inr 3769, 1), (Sum.inr 3806, 1), (Sum.inr 3869, 1), (Sum.inr 3874, 2), (Sum.inr 3954, 1), (Sum.inr 3955, 2), (Sum.inr 3956, 2), (Sum.inr 3957, 2), (Sum.inr 3961, 2), (Sum.inr 3962, 1), (Sum.inr 3979, 1), (Sum.inr 3980, 2), (Sum.inr 3985, 1), (Sum.inr 4026, 2), (Sum.inr 4029, 1)]

def sourceForm1130 : Integer.Sparse Master := [(Sum.inr 4996, 4), (Sum.inr 4998, 2), (Sum.inr 5013, 2), (Sum.inr 5257, 2), (Sum.inr 5395, 4), (Sum.inr 5428, 2), (Sum.inr 5469, 2), (Sum.inr 5473, 4), (Sum.inr 5482, 2), (Sum.inr 5489, 2), (Sum.inr 5490, 4)]

def sourceForm1131 : Integer.Sparse Master := [(Sum.inr 4859, 1), (Sum.inr 4860, 2), (Sum.inr 4869, 2), (Sum.inr 5383, 2), (Sum.inr 5384, 4), (Sum.inr 5387, 2), (Sum.inr 5398, 2), (Sum.inr 5403, 2), (Sum.inr 5439, 2), (Sum.inr 5443, 4), (Sum.inr 5448, 2), (Sum.inr 5449, 2), (Sum.inr 5488, 1), (Sum.inr 5491, 2)]

def sourceForm1132 : Integer.Sparse Master := [(Sum.inr 5185, 2), (Sum.inr 5187, 1), (Sum.inr 5197, 1), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5226, 2), (Sum.inr 5257, 1), (Sum.inr 5281, 1), (Sum.inr 5401, 2), (Sum.inr 5403, 1), (Sum.inr 5408, 1), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5433, 2), (Sum.inr 5438, 2), (Sum.inr 5440, 1), (Sum.inr 5445, 2), (Sum.inr 5448, 1), (Sum.inr 5478, 2), (Sum.inr 5481, 1), (Sum.inr 5485, 1)]

def sourceForm1133 : Integer.Sparse Master := [(Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2669, 2), (Sum.inr 2750, 1), (Sum.inr 3529, 2), (Sum.inr 3532, 1), (Sum.inr 3537, 1), (Sum.inr 3569, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 1), (Sum.inr 3810, 1), (Sum.inr 3840, 2), (Sum.inr 3848, 2), (Sum.inr 3851, 2), (Sum.inr 3857, 2), (Sum.inr 3859, 1), (Sum.inr 3880, 2), (Sum.inr 3885, 1), (Sum.inr 3979, 1), (Sum.inr 3994, 2), (Sum.inr 3998, 1)]

def sourceForm1134 : Integer.Sparse Master := [(Sum.inr 4798, 2), (Sum.inr 4805, 1), (Sum.inr 4826, 1), (Sum.inr 4864, 1), (Sum.inr 5349, 2), (Sum.inr 5354, 1), (Sum.inr 5363, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5400, 2), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 2), (Sum.inr 5433, 1), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 2), (Sum.inr 5481, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2)]

def sourceForm1135 : Integer.Sparse Master := [(Sum.inr 2075, 2), (Sum.inr 2077, 1), (Sum.inr 2105, 1), (Sum.inr 2214, 1), (Sum.inr 3719, 2), (Sum.inr 3721, 1), (Sum.inr 3735, 1), (Sum.inr 3749, 2), (Sum.inr 3751, 1), (Sum.inr 3769, 1), (Sum.inr 3799, 2), (Sum.inr 3850, 2), (Sum.inr 3875, 1), (Sum.inr 3876, 2), (Sum.inr 3887, 2), (Sum.inr 3897, 1), (Sum.inr 3906, 2), (Sum.inr 4008, 1), (Sum.inr 4009, 1), (Sum.inr 4013, 2), (Sum.inr 4033, 1)]

def sourceForm1136 : Integer.Sparse Master := [(Sum.inr 5145, 2), (Sum.inr 5150, 1), (Sum.inr 5162, 1), (Sum.inr 5243, 1), (Sum.inr 5244, 1), (Sum.inr 5265, 2), (Sum.inr 5290, 1), (Sum.inr 5379, 2), (Sum.inr 5383, 1), (Sum.inr 5421, 2), (Sum.inr 5424, 2), (Sum.inr 5427, 1), (Sum.inr 5429, 3), (Sum.inr 5431, 2), (Sum.inr 5440, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 2), (Sum.inr 5471, 1), (Sum.inr 5472, 2), (Sum.inr 5482, 1)]

def sourceForm1137 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 1), (Sum.inr 5307, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5416, 2), (Sum.inr 5417, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 2), (Sum.inr 5442, 2), (Sum.inr 5450, 1), (Sum.inr 5454, 2), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1)]

def sourceForm1138 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 5137, 3), (Sum.inr 5162, 1), (Sum.inr 5273, 1), (Sum.inr 5380, 3), (Sum.inr 5383, 1), (Sum.inr 5396, 3), (Sum.inr 5424, 6), (Sum.inr 5431, 3), (Sum.inr 5440, 3), (Sum.inr 5447, 1), (Sum.inr 5479, 1), (Sum.inr 5482, 3)]

def sourceForm1139 : Integer.Sparse Master := [(Sum.inr 4079, 1), (Sum.inr 4080, 3), (Sum.inr 4083, 1), (Sum.inr 4087, 1), (Sum.inr 4088, 3), (Sum.inr 4090, 3), (Sum.inr 4091, 5), (Sum.inr 4092, 6), (Sum.inr 4093, 3), (Sum.inr 4095, 1), (Sum.inr 4096, 3)]

def sourceForm1140 : Integer.Sparse Master := [(Sum.inr 5398, 4), (Sum.inr 5403, 8), (Sum.inr 5415, 2), (Sum.inr 5439, 8), (Sum.inr 5448, 4), (Sum.inr 5491, 4)]

def sourceForm1141 : Integer.Sparse Master := [(Sum.inr 4090, 9), (Sum.inr 4091, 12), (Sum.inr 4096, 9)]

def sourceForm1142 : Integer.Sparse Master := [(Sum.inr 617, 1), (Sum.inr 936, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

def sourceForm1143 : Integer.Sparse Master := [(Sum.inr 862, 1), (Sum.inr 1629, 3), (Sum.inr 1752, 1), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

def sourceForm1145 : Integer.Sparse Master := [(Sum.inr 1749, 3), (Sum.inr 1752, 2), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

def sourceForm1147 : Integer.Sparse Master := [(Sum.inr 587, 1), (Sum.inr 911, 2), (Sum.inr 951, 1), (Sum.inr 1027, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

def sourceForm1148 : Integer.Sparse Master := [(Sum.inr 849, 1), (Sum.inr 1615, 2), (Sum.inr 1749, 1), (Sum.inr 1752, 2), (Sum.inr 4072, -1)]

def sourceForm1150 : Integer.Sparse Master := [(Sum.inr 794, 2), (Sum.inr 797, 1), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 1716, 1), (Sum.inr 4069, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1152 : Integer.Sparse Master := [(Sum.inr 633, 1), (Sum.inr 1115, 2), (Sum.inr 1140, 1), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

def sourceForm1153 : Integer.Sparse Master := [(Sum.inr 1615, 2), (Sum.inr 1620, 1), (Sum.inr 1629, 1), (Sum.inr 1752, 1), (Sum.inr 3298, 1), (Sum.inr 4072, -1)]

def sourceForm1154 : Integer.Sparse Master := [(Sum.inr 1752, 2), (Sum.inr 3298, 3), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

def sourceForm1155 : Integer.Sparse Master := [(Sum.inr 989, 2), (Sum.inr 994, 1), (Sum.inr 1009, 1), (Sum.inr 1055, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def sourceForm1156 : Integer.Sparse Master := [(Sum.inr 994, 1), (Sum.inr 1179, 2), (Sum.inr 1190, 1), (Sum.inr 1258, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def sourceForm1157 : Integer.Sparse Master := [(Sum.inr 971, 1), (Sum.inr 975, 1), (Sum.inr 982, 2), (Sum.inr 1019, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def sourceForm1158 : Integer.Sparse Master := [(Sum.inr 975, 1), (Sum.inr 1194, 1), (Sum.inr 1202, 1), (Sum.inr 1211, 2), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def sourceForm1159 : Integer.Sparse Master := [(Sum.inr 4187, 8), (Sum.inr 4194, 1), (Sum.inr 4555, 12), (Sum.inr 4625, 8), (Sum.inr 5312, 1)]

def sourceForm1160 : Integer.Sparse Master := [(Sum.inr 615, 8), (Sum.inr 622, 1), (Sum.inr 1140, 12), (Sum.inr 1307, 8), (Sum.inr 3126, 1)]

def sourceForm1161 : Integer.Sparse Master := [(Sum.inr 4468, 16), (Sum.inr 4512, 2), (Sum.inr 4594, 12)]

def sourceForm1162 : Integer.Sparse Master := [(Sum.inr 1051, 8), (Sum.inr 1096, 1), (Sum.inr 1221, 12), (Sum.inr 1275, 8), (Sum.inr 1456, 1)]

def sourceForm1163 : Integer.Sparse Master := [(Sum.inr 1752, 4), (Sum.inr 1758, 1), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

def sourceForm1164 : Integer.Sparse Master := [(Sum.inr 4156, 3), (Sum.inr 4159, 3), (Sum.inr 4163, 1), (Sum.inr 4187, 1), (Sum.inr 4189, 1), (Sum.inr 4330, 6), (Sum.inr 4356, 3), (Sum.inr 4370, 3), (Sum.inr 4460, 3), (Sum.inr 4505, 1), (Sum.inr 4605, 3), (Sum.inr 4621, 1), (Sum.inr 4897, 1)]

def sourceForm1165 : Integer.Sparse Master := [(Sum.inr 587, 3), (Sum.inr 591, 1), (Sum.inr 617, 1), (Sum.inr 633, 3), (Sum.inr 650, 1), (Sum.inr 1118, 6), (Sum.inr 1142, 3), (Sum.inr 1173, 3), (Sum.inr 1271, 3), (Sum.inr 1308, 1), (Sum.inr 1416, 3), (Sum.inr 1450, 1), (Sum.inr 3114, 1)]

def sourceForm1166 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1532, 3), (Sum.inr 1534, 1), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 1672, 6), (Sum.inr 1692, 3), (Sum.inr 1722, 3), (Sum.inr 1725, 3), (Sum.inr 1754, 1), (Sum.inr 2226, 3), (Sum.inr 2289, 1), (Sum.inr 2292, 1)]

def sourceForm1167 : Integer.Sparse Master := [(Sum.inr 591, 1), (Sum.inr 628, 3), (Sum.inr 643, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

def sourceForm1168 : Integer.Sparse Master := [(Sum.inr 628, 1), (Sum.inr 908, 2), (Sum.inr 934, 1), (Sum.inr 1051, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

def sourceForm1169 : Integer.Sparse Master := [(Sum.inr 584, 1), (Sum.inr 908, 2), (Sum.inr 948, 1), (Sum.inr 1043, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

def sourceForm1170 : Integer.Sparse Master := [(Sum.inr 643, 1), (Sum.inr 948, 3), (Sum.inr 1051, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def sourceForm1171 : Integer.Sparse Master := [(Sum.inr 615, 1), (Sum.inr 934, 3), (Sum.inr 1051, 1), (Sum.inr 1089, 1), (Sum.inr 4084, -1)]

def sourceForm1172 : Integer.Sparse Master := [(Sum.inr 4108, 3), (Sum.inr 4112, 1), (Sum.inr 4134, 1), (Sum.inr 4146, 3), (Sum.inr 4181, 1), (Sum.inr 4293, 6), (Sum.inr 4315, 3), (Sum.inr 4356, 3), (Sum.inr 4463, 3), (Sum.inr 4507, 1), (Sum.inr 4608, 3), (Sum.inr 4625, 1), (Sum.inr 5296, 1)]

def sourceForm1173 : Integer.Sparse Master := [(Sum.inr 545, 3), (Sum.inr 549, 1), (Sum.inr 564, 1), (Sum.inr 574, 3), (Sum.inr 609, 1), (Sum.inr 871, 6), (Sum.inr 893, 3), (Sum.inr 934, 3), (Sum.inr 1046, 3), (Sum.inr 1091, 1), (Sum.inr 1242, 3), (Sum.inr 1304, 1), (Sum.inr 2770, 1)]

def sourceForm1177 : Integer.Sparse Master := [(Sum.inr 855, 1), (Sum.inr 1620, 3), (Sum.inr 1752, 1), (Sum.inr 1758, 1), (Sum.inr 4072, -1)]

def sourceForm1178 : Integer.Sparse Master := [(Sum.inr 826, 3), (Sum.inr 832, 1), (Sum.inr 859, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

def sourceForm1179 : Integer.Sparse Master := [(Sum.inr 564, 1), (Sum.inr 726, 3), (Sum.inr 832, 1), (Sum.inr 859, 1), (Sum.inr 4071, -1)]

def sourceForm1180 : Integer.Sparse Master := [(Sum.inr 832, 1), (Sum.inr 1186, 3), (Sum.inr 1289, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

def sourceForm1182 : Integer.Sparse Master := [(Sum.inr 785, 2), (Sum.inr 791, 1), (Sum.inr 812, 2), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def sourceForm1183 : Integer.Sparse Master := [(Sum.inr 545, 1), (Sum.inr 705, 2), (Sum.inr 740, 1), (Sum.inr 791, 1), (Sum.inr 812, 1), (Sum.inr 4069, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1184 : Integer.Sparse Master := [(Sum.inr 791, 1), (Sum.inr 1199, 2), (Sum.inr 1231, 2), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def sourceForm1186 : Integer.Sparse Master := [(Sum.inr 979, 2), (Sum.inr 986, 1), (Sum.inr 1007, 1), (Sum.inr 1037, 1), (Sum.inr 2208, 1), (Sum.inr 4081, -1)]

def sourceForm1189 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4181, 8), (Sum.inr 4194, 1), (Sum.inr 4350, 12), (Sum.inr 4501, 8)]

def sourceForm1190 : Integer.Sparse Master := [(Sum.inr 1521, 8), (Sum.inr 1541, 1), (Sum.inr 1677, 12), (Sum.inr 1730, 8), (Sum.inr 4085, 1)]

def sourceForm1191 : Integer.Sparse Master := [(Sum.inr 609, 4), (Sum.inr 622, 1), (Sum.inr 1096, 1), (Sum.inr 4085, -1)]

def sourceForm1192 : Integer.Sparse Master := [(Sum.inr 4072, 1), (Sum.inr 4274, 8), (Sum.inr 4405, 12), (Sum.inr 4468, 8), (Sum.inr 4629, 1)]

def sourceForm1193 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4103, 3), (Sum.inr 4112, 1), (Sum.inr 4131, 1), (Sum.inr 4142, 3), (Sum.inr 4168, 1), (Sum.inr 4198, 6), (Sum.inr 4222, 3), (Sum.inr 4235, 3), (Sum.inr 4266, 3), (Sum.inr 4421, 3), (Sum.inr 4493, 1), (Sum.inr 4501, 1)]

def sourceForm1194 : Integer.Sparse Master := [(Sum.inr 665, 3), (Sum.inr 686, 1), (Sum.inr 691, 1), (Sum.inr 750, 6), (Sum.inr 765, 3), (Sum.inr 770, 3), (Sum.inr 801, 3), (Sum.inr 809, 3), (Sum.inr 845, 1), (Sum.inr 1002, 3), (Sum.inr 1077, 1), (Sum.inr 1085, 1), (Sum.inr 4070, 1)]

def sourceForm1195 : Integer.Sparse Master := [(Sum.inr 549, 1), (Sum.inr 570, 3), (Sum.inr 596, 1), (Sum.inr 817, 1), (Sum.inr 4070, -1)]

def sourceForm1197 : Integer.Sparse Master := [(Sum.inr 540, 1), (Sum.inr 701, 2), (Sum.inr 735, 1), (Sum.inr 809, 1), (Sum.inr 817, 1), (Sum.inr 4070, -1)]

def sourceForm1198 : Integer.Sparse Master := [(Sum.inr 596, 1), (Sum.inr 735, 3), (Sum.inr 817, 1), (Sum.inr 1077, 1), (Sum.inr 4070, -1)]

def sourceForm1200 : Integer.Sparse Master := [(Sum.inr 4060, 8), (Sum.inr 4062, 1), (Sum.inr 4066, 12), (Sum.inr 4070, 8), (Sum.inr 4085, 1)]

def sourceForm1201 : Integer.Sparse Master := [(Sum.inr 621, 1), (Sum.inr 940, 3), (Sum.inr 1092, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

def sourceForm1202 : Integer.Sparse Master := [(Sum.inr 1093, 1), (Sum.inr 1747, 1), (Sum.inr 2064, 3), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def sourceForm1203 : Integer.Sparse Master := [(Sum.inr 1745, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def sourceForm1204 : Integer.Sparse Master := [(Sum.inr 860, 1), (Sum.inr 1628, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

def sourceForm1205 : Integer.Sparse Master := [(Sum.inr 612, 1), (Sum.inr 931, 2), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def sourceForm1206 : Integer.Sparse Master := [(Sum.inr 590, 1), (Sum.inr 914, 2), (Sum.inr 954, 1), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

def sourceForm1207 : Integer.Sparse Master := [(Sum.inr 951, 1), (Sum.inr 1336, 2), (Sum.inr 1348, 1), (Sum.inr 1408, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

def sourceForm1208 : Integer.Sparse Master := [(Sum.inr 1072, 1), (Sum.inr 1745, 1), (Sum.inr 2045, 2), (Sum.inr 2226, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def sourceForm1210 : Integer.Sparse Master := [(Sum.inr 1744, 2), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

def sourceForm1211 : Integer.Sparse Master := [(Sum.inr 853, 1), (Sum.inr 1619, 2), (Sum.inr 1745, 1), (Sum.inr 1750, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

def sourceForm1212 : Integer.Sparse Master := [(Sum.inr 606, 1), (Sum.inr 925, 2), (Sum.inr 1059, 1), (Sum.inr 1083, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

def sourceForm1213 : Integer.Sparse Master := [(Sum.inr 1142, 1), (Sum.inr 1317, 2), (Sum.inr 1324, 1), (Sum.inr 1372, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

def sourceForm1214 : Integer.Sparse Master := [(Sum.inr 1729, 1), (Sum.inr 1952, 1), (Sum.inr 3242, 2), (Sum.inr 3247, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def sourceForm1215 : Integer.Sparse Master := [(Sum.inr 808, 2), (Sum.inr 814, 1), (Sum.inr 815, 1), (Sum.inr 857, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1216 : Integer.Sparse Master := [(Sum.inr 1723, 2), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 1750, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def sourceForm1217 : Integer.Sparse Master := [(Sum.inr 857, 1), (Sum.inr 1624, 2), (Sum.inr 1729, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

def sourceForm1218 : Integer.Sparse Master := [(Sum.inr 815, 1), (Sum.inr 1604, 2), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

def sourceForm1220 : Integer.Sparse Master := [(Sum.inr 936, 1), (Sum.inr 1315, 2), (Sum.inr 1323, 1), (Sum.inr 1369, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def sourceForm1221 : Integer.Sparse Master := [(Sum.inr 1011, 1), (Sum.inr 1746, 1), (Sum.inr 1952, 1), (Sum.inr 2005, 2), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

def sourceForm1224 : Integer.Sparse Master := [(Sum.inr 581, 1), (Sum.inr 905, 1), (Sum.inr 945, 1), (Sum.inr 1022, 1), (Sum.inr 1041, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

def sourceForm1225 : Integer.Sparse Master := [(Sum.inr 1118, 1), (Sum.inr 1327, 1), (Sum.inr 1333, 1), (Sum.inr 1337, 1), (Sum.inr 1388, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

def sourceForm1226 : Integer.Sparse Master := [(Sum.inr 1723, 1), (Sum.inr 1942, 1), (Sum.inr 3279, 1), (Sum.inr 3283, 1), (Sum.inr 3300, 2), (Sum.inr 4070, -1)]

def sourceForm1228 : Integer.Sparse Master := [(Sum.inr 847, 1), (Sum.inr 1613, 1), (Sum.inr 1723, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 2), (Sum.inr 4070, -1)]

def sourceForm1229 : Integer.Sparse Master := [(Sum.inr 804, 1), (Sum.inr 1596, 1), (Sum.inr 1643, 1), (Sum.inr 1723, 1), (Sum.inr 1725, 2), (Sum.inr 4070, -1)]

def sourceForm1231 : Integer.Sparse Master := [(Sum.inr 585, 1), (Sum.inr 909, 1), (Sum.inr 949, 1), (Sum.inr 1024, 2), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

def sourceForm1232 : Integer.Sparse Master := [(Sum.inr 911, 1), (Sum.inr 1326, 1), (Sum.inr 1332, 1), (Sum.inr 1336, 1), (Sum.inr 1385, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

def sourceForm1233 : Integer.Sparse Master := [(Sum.inr 997, 1), (Sum.inr 1744, 1), (Sum.inr 1942, 1), (Sum.inr 1995, 1), (Sum.inr 2226, 2), (Sum.inr 4070, -1)]

def sourceForm1235 : Integer.Sparse Master := [(Sum.inr 1355, 1), (Sum.inr 1902, 1), (Sum.inr 1915, 1), (Sum.inr 1926, 1), (Sum.inr 2197, 1), (Sum.inr 3024, 1), (Sum.inr 4080, -1)]

def sourceForm1237 : Integer.Sparse Master := [(Sum.inr 1132, 2), (Sum.inr 1142, 1), (Sum.inr 1145, 1), (Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

def sourceForm1238 : Integer.Sparse Master := [(Sum.inr 636, 1), (Sum.inr 1145, 1), (Sum.inr 1155, 2), (Sum.inr 1243, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

def sourceForm1239 : Integer.Sparse Master := [(Sum.inr 641, 1), (Sum.inr 1159, 2), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

def sourceForm1240 : Integer.Sparse Master := [(Sum.inr 1643, 2), (Sum.inr 1647, 1), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

def sourceForm1241 : Integer.Sparse Master := [(Sum.inr 1619, 2), (Sum.inr 1628, 1), (Sum.inr 1630, 1), (Sum.inr 1756, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

def sourceForm1242 : Integer.Sparse Master := [(Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 3302, 3), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def sourceForm1243 : Integer.Sparse Master := [(Sum.inr 1725, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def sourceForm1244 : Integer.Sparse Master := [(Sum.inr 1630, 1), (Sum.inr 3247, 1), (Sum.inr 3283, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

def sourceForm1246 : Integer.Sparse Master := [(Sum.inr 1258, 1), (Sum.inr 2119, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2761, 1), (Sum.inr 4082, -1)]

def sourceForm1247 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1115, 1), (Sum.inr 1119, 1), (Sum.inr 1131, 1), (Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1248 : Integer.Sparse Master := [(Sum.inr 626, 1), (Sum.inr 1131, 1), (Sum.inr 1148, 1), (Sum.inr 1215, 1), (Sum.inr 1236, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

def sourceForm1249 : Integer.Sparse Master := [(Sum.inr 630, 1), (Sum.inr 1136, 1), (Sum.inr 1150, 1), (Sum.inr 1217, 2), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

def sourceForm1250 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1118, 1), (Sum.inr 1120, 1), (Sum.inr 1136, 1), (Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

def sourceForm1251 : Integer.Sparse Master := [(Sum.inr 1613, 1), (Sum.inr 1617, 1), (Sum.inr 1619, 1), (Sum.inr 1624, 1), (Sum.inr 1750, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

def sourceForm1252 : Integer.Sparse Master := [(Sum.inr 1596, 1), (Sum.inr 1599, 1), (Sum.inr 1604, 1), (Sum.inr 1617, 1), (Sum.inr 1725, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

def sourceForm1253 : Integer.Sparse Master := [(Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def sourceForm1254 : Integer.Sparse Master := [(Sum.inr 1617, 1), (Sum.inr 3242, 1), (Sum.inr 3279, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def sourceForm1255 : Integer.Sparse Master := [(Sum.inr 1599, 1), (Sum.inr 1995, 1), (Sum.inr 2005, 1), (Sum.inr 2045, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

def sourceForm1256 : Integer.Sparse Master := [(Sum.inr 1211, 1), (Sum.inr 2070, 1), (Sum.inr 2079, 1), (Sum.inr 2087, 1), (Sum.inr 2193, 1), (Sum.inr 2719, 1), (Sum.inr 4080, -1)]

def sourceForm1257 : Integer.Sparse Master := [(Sum.inr 1181, 1), (Sum.inr 2385, 1), (Sum.inr 2453, 1), (Sum.inr 2492, 1), (Sum.inr 2664, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

def sourceForm1258 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 1181, 1), (Sum.inr 1182, 1), (Sum.inr 1188, 1), (Sum.inr 1257, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

def sourceForm1259 : Integer.Sparse Master := [(Sum.inr 1179, 1), (Sum.inr 1991, 1), (Sum.inr 2003, 1), (Sum.inr 2032, 1), (Sum.inr 2218, 1), (Sum.inr 2670, 1), (Sum.inr 4082, -1)]

def sourceForm1260 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 2449, 2), (Sum.inr 2469, 1), (Sum.inr 2691, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

def sourceForm1261 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 1196, 1), (Sum.inr 1200, 1), (Sum.inr 1210, 2), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

def sourceForm1262 : Integer.Sparse Master := [(Sum.inr 1194, 1), (Sum.inr 1987, 2), (Sum.inr 2008, 1), (Sum.inr 2193, 1), (Sum.inr 2693, 1), (Sum.inr 4080, -1)]

def sourceForm1263 : Integer.Sparse Master := [(Sum.inr 4183, 3), (Sum.inr 4187, 1), (Sum.inr 4192, 1), (Sum.inr 4551, 6), (Sum.inr 4555, 3), (Sum.inr 4559, 3), (Sum.inr 4623, 3), (Sum.inr 4625, 3), (Sum.inr 4627, 1), (Sum.inr 4629, 1), (Sum.inr 5171, 3), (Sum.inr 5308, 1), (Sum.inr 5312, 1)]

def sourceForm1264 : Integer.Sparse Master := [(Sum.inr 611, 3), (Sum.inr 615, 1), (Sum.inr 620, 1), (Sum.inr 1136, 6), (Sum.inr 1140, 3), (Sum.inr 1145, 3), (Sum.inr 1305, 3), (Sum.inr 1307, 3), (Sum.inr 1311, 1), (Sum.inr 1313, 1), (Sum.inr 2965, 3), (Sum.inr 3124, 1), (Sum.inr 3126, 1)]

def sourceForm1265 : Integer.Sparse Master := [(Sum.inr 4177, 3), (Sum.inr 4181, 1), (Sum.inr 4191, 1), (Sum.inr 4356, 3), (Sum.inr 4468, 1), (Sum.inr 4546, 6), (Sum.inr 4558, 3), (Sum.inr 4608, 3), (Sum.inr 4624, 3), (Sum.inr 4628, 1), (Sum.inr 5174, 3), (Sum.inr 5296, 1), (Sum.inr 5309, 1)]

def sourceForm1266 : Integer.Sparse Master := [(Sum.inr 605, 3), (Sum.inr 609, 1), (Sum.inr 619, 1), (Sum.inr 934, 3), (Sum.inr 1051, 1), (Sum.inr 1131, 6), (Sum.inr 1144, 3), (Sum.inr 1242, 3), (Sum.inr 1301, 3), (Sum.inr 1312, 1), (Sum.inr 2601, 3), (Sum.inr 2770, 1), (Sum.inr 3123, 1)]

def sourceForm1267 : Integer.Sparse Master := [(Sum.inr 4460, 3), (Sum.inr 4463, 3), (Sum.inr 4501, 1), (Sum.inr 4505, 2), (Sum.inr 4507, 1), (Sum.inr 4591, 6), (Sum.inr 4605, 3), (Sum.inr 4608, 6), (Sum.inr 4609, 3), (Sum.inr 4621, 1), (Sum.inr 4625, 1)]

def sourceForm1268 : Integer.Sparse Master := [(Sum.inr 1046, 3), (Sum.inr 1089, 1), (Sum.inr 1091, 1), (Sum.inr 1217, 6), (Sum.inr 1242, 3), (Sum.inr 1243, 3), (Sum.inr 1269, 3), (Sum.inr 1271, 3), (Sum.inr 1304, 1), (Sum.inr 1308, 1), (Sum.inr 1416, 3), (Sum.inr 1450, 1), (Sum.inr 1452, 1)]

def sourceForm1269 : Integer.Sparse Master := [(Sum.inr 1750, 3), (Sum.inr 1754, 1), (Sum.inr 1756, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def sourceForm1270 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 1730, 1), (Sum.inr 1754, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def sourceForm1271 : Integer.Sparse Master := [(Sum.inr 1754, 1), (Sum.inr 3300, 3), (Sum.inr 3310, 2), (Sum.inr 4070, -1)]

def sourceForm1272 : Integer.Sparse Master := [(Sum.inr 4184, 3), (Sum.inr 4189, 1), (Sum.inr 4193, 1), (Sum.inr 4370, 3), (Sum.inr 4468, 1), (Sum.inr 4552, 6), (Sum.inr 4560, 3), (Sum.inr 4605, 3), (Sum.inr 4617, 3), (Sum.inr 4626, 1), (Sum.inr 4868, 3), (Sum.inr 4897, 1), (Sum.inr 5305, 1)]

def sourceForm1273 : Integer.Sparse Master := [(Sum.inr 612, 3), (Sum.inr 617, 1), (Sum.inr 621, 1), (Sum.inr 1137, 6), (Sum.inr 1142, 3), (Sum.inr 1146, 3), (Sum.inr 1271, 3), (Sum.inr 1275, 1), (Sum.inr 1306, 3), (Sum.inr 1310, 1), (Sum.inr 2966, 3), (Sum.inr 3114, 1), (Sum.inr 3125, 1)]

def sourceForm1274 : Integer.Sparse Master := [(Sum.inr 1530, 3), (Sum.inr 1531, 1), (Sum.inr 1540, 1), (Sum.inr 1722, 3), (Sum.inr 1752, 1), (Sum.inr 2200, 6), (Sum.inr 2226, 3), (Sum.inr 2258, 3), (Sum.inr 2261, 3), (Sum.inr 2292, 1), (Sum.inr 2737, 3), (Sum.inr 2780, 1), (Sum.inr 2783, 1)]

def sourceForm1275 : Integer.Sparse Master := [(Sum.inr 639, 3), (Sum.inr 643, 1), (Sum.inr 654, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def sourceForm1276 : Integer.Sparse Master := [(Sum.inr 639, 1), (Sum.inr 1157, 2), (Sum.inr 1239, 1), (Sum.inr 1292, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def sourceForm1277 : Integer.Sparse Master := [(Sum.inr 948, 1), (Sum.inr 1157, 2), (Sum.inr 1174, 1), (Sum.inr 1297, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

def sourceForm1278 : Integer.Sparse Master := [(Sum.inr 4166, 3), (Sum.inr 4168, 1), (Sum.inr 4190, 1), (Sum.inr 4240, 3), (Sum.inr 4280, 1), (Sum.inr 4538, 6), (Sum.inr 4557, 3), (Sum.inr 4572, 3), (Sum.inr 4619, 3), (Sum.inr 4627, 1), (Sum.inr 4871, 3), (Sum.inr 4899, 1), (Sum.inr 5310, 1)]

def sourceForm1279 : Integer.Sparse Master := [(Sum.inr 594, 3), (Sum.inr 596, 1), (Sum.inr 618, 1), (Sum.inr 740, 3), (Sum.inr 832, 1), (Sum.inr 1123, 6), (Sum.inr 1143, 3), (Sum.inr 1190, 3), (Sum.inr 1294, 3), (Sum.inr 1311, 1), (Sum.inr 2112, 3), (Sum.inr 2281, 1), (Sum.inr 3121, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm128 : Integer.Sparse Master := [(Sum.inr 1059, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def sourceForm129 : Integer.Sparse Master := [(Sum.inr 4500, 3), (Sum.inr 4508, 1), (Sum.inr 4510, 1), (Sum.inr 4836, 6), (Sum.inr 4844, 3), (Sum.inr 4845, 3), (Sum.inr 4890, 3), (Sum.inr 4892, 3), (Sum.inr 4897, 1), (Sum.inr 4899, 1), (Sum.inr 4900, 1), (Sum.inr 5268, 3), (Sum.inr 5296, 1)]

def sourceForm130 : Integer.Sparse Master := [(Sum.inr 1436, 3), (Sum.inr 1438, 1), (Sum.inr 1454, 1), (Sum.inr 2136, 3), (Sum.inr 2255, 3), (Sum.inr 2281, 1), (Sum.inr 2285, 1), (Sum.inr 2716, 6), (Sum.inr 2734, 3), (Sum.inr 2755, 3), (Sum.inr 2770, 1), (Sum.inr 3095, 3), (Sum.inr 3114, 1)]

def sourceForm131 : Integer.Sparse Master := [(Sum.inr 1716, 3), (Sum.inr 1741, 1), (Sum.inr 1747, 1), (Sum.inr 2197, 6), (Sum.inr 2218, 3), (Sum.inr 2222, 3), (Sum.inr 2247, 3), (Sum.inr 2255, 3), (Sum.inr 2268, 1), (Sum.inr 2285, 1), (Sum.inr 2734, 3), (Sum.inr 2770, 1), (Sum.inr 2778, 1)]

def sourceForm132 : Integer.Sparse Master := [(Sum.inr 1094, 1), (Sum.inr 2065, 3), (Sum.inr 2292, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

def sourceForm133 : Integer.Sparse Master := [(Sum.inr 4253, 2), (Sum.inr 4257, 1), (Sum.inr 4270, 2), (Sum.inr 4583, 2), (Sum.inr 4605, 2), (Sum.inr 4729, 2), (Sum.inr 4742, 4), (Sum.inr 4807, 4), (Sum.inr 4843, 2), (Sum.inr 4889, 2), (Sum.inr 4896, 2), (Sum.inr 5284, 2), (Sum.inr 5294, 2), (Sum.inr 5453, 1)]

def sourceForm134 : Integer.Sparse Master := [(Sum.inr 787, 2), (Sum.inr 791, 1), (Sum.inr 813, 2), (Sum.inr 1202, 2), (Sum.inr 1239, 2), (Sum.inr 1898, 2), (Sum.inr 1915, 4), (Sum.inr 2025, 4), (Sum.inr 2062, 2), (Sum.inr 2245, 2), (Sum.inr 2266, 2), (Sum.inr 3077, 2), (Sum.inr 3101, 2), (Sum.inr 3912, 1)]

def sourceForm135 : Integer.Sparse Master := [(Sum.inr 4440, 2), (Sum.inr 4442, 2), (Sum.inr 4445, 1), (Sum.inr 4463, 2), (Sum.inr 4464, 2), (Sum.inr 4792, 2), (Sum.inr 4807, 4), (Sum.inr 4853, 4), (Sum.inr 4871, 2), (Sum.inr 4888, 2), (Sum.inr 4895, 2), (Sum.inr 5270, 2), (Sum.inr 5295, 2), (Sum.inr 5306, 1)]

def sourceForm136 : Integer.Sparse Master := [(Sum.inr 1024, 2), (Sum.inr 1027, 1), (Sum.inr 1047, 2), (Sum.inr 1388, 2), (Sum.inr 1413, 2), (Sum.inr 2471, 2), (Sum.inr 2486, 4), (Sum.inr 2574, 4), (Sum.inr 2602, 2), (Sum.inr 2754, 2), (Sum.inr 2769, 2), (Sum.inr 3120, 1), (Sum.inr 3227, 2), (Sum.inr 3229, 2)]

def sourceForm137 : Integer.Sparse Master := [(Sum.inr 1723, 2), (Sum.inr 1744, 2), (Sum.inr 1745, 2), (Sum.inr 1749, 1), (Sum.inr 1750, 2), (Sum.inr 2201, 2), (Sum.inr 2224, 4), (Sum.inr 2259, 4), (Sum.inr 2262, 2), (Sum.inr 2287, 2), (Sum.inr 2291, 2), (Sum.inr 2738, 2), (Sum.inr 2781, 2), (Sum.inr 2784, 1)]

def sourceForm138 : Integer.Sparse Master := [(Sum.inr 2244, 2), (Sum.inr 2247, 1), (Sum.inr 2265, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def sourceForm139 : Integer.Sparse Master := [(Sum.inr 1027, 1), (Sum.inr 1385, 2), (Sum.inr 1408, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def sourceForm140 : Integer.Sparse Master := [(Sum.inr 1385, 1), (Sum.inr 2009, 1), (Sum.inr 2025, 2), (Sum.inr 2247, 1), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

def sourceForm141 : Integer.Sparse Master := [(Sum.inr 1022, 1), (Sum.inr 2009, 1), (Sum.inr 2090, 2), (Sum.inr 2244, 1), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def sourceForm142 : Integer.Sparse Master := [(Sum.inr 1408, 1), (Sum.inr 2090, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def sourceForm143 : Integer.Sparse Master := [(Sum.inr 1046, 1), (Sum.inr 2025, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 2265, 1), (Sum.inr 4083, -1)]

def sourceForm144 : Integer.Sparse Master := [(Sum.inr 1022, 2), (Sum.inr 1027, 1), (Sum.inr 1046, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def sourceForm145 : Integer.Sparse Master := [(Sum.inr 4494, 2), (Sum.inr 4496, 1), (Sum.inr 4500, 2), (Sum.inr 4830, 2), (Sum.inr 4832, 2), (Sum.inr 4836, 4), (Sum.inr 4886, 2), (Sum.inr 4890, 5), (Sum.inr 4892, 2), (Sum.inr 4897, 2), (Sum.inr 4899, 2), (Sum.inr 5252, 2), (Sum.inr 5296, 2)]

def sourceForm146 : Integer.Sparse Master := [(Sum.inr 1435, 2), (Sum.inr 1436, 2), (Sum.inr 1451, 1), (Sum.inr 2235, 2), (Sum.inr 2247, 1), (Sum.inr 2255, 2), (Sum.inr 2707, 2), (Sum.inr 2712, 2), (Sum.inr 2716, 4), (Sum.inr 2755, 4), (Sum.inr 2770, 2), (Sum.inr 2778, 2), (Sum.inr 3082, 2), (Sum.inr 3114, 2)]

def sourceForm147 : Integer.Sparse Master := [(Sum.inr 1700, 2), (Sum.inr 1710, 1), (Sum.inr 1716, 2), (Sum.inr 2187, 2), (Sum.inr 2193, 2), (Sum.inr 2197, 4), (Sum.inr 2235, 2), (Sum.inr 2247, 4), (Sum.inr 2255, 2), (Sum.inr 2268, 2), (Sum.inr 2281, 2), (Sum.inr 2712, 2), (Sum.inr 2755, 1), (Sum.inr 2770, 2)]

def sourceForm148 : Integer.Sparse Master := [(Sum.inr 1080, 1), (Sum.inr 2052, 2), (Sum.inr 2290, 1), (Sum.inr 2292, 2), (Sum.inr 4085, -1)]

def sourceForm149 : Integer.Sparse Master := [(Sum.inr 4591, 4), (Sum.inr 4594, 1), (Sum.inr 4608, 2), (Sum.inr 4609, 2), (Sum.inr 5075, 4), (Sum.inr 5107, 1), (Sum.inr 5127, 2), (Sum.inr 5147, 4), (Sum.inr 5201, 1), (Sum.inr 5258, 4), (Sum.inr 5274, 2), (Sum.inr 5291, 2), (Sum.inr 5441, 1)]

def sourceForm150 : Integer.Sparse Master := [(Sum.inr 1217, 4), (Sum.inr 1221, 1), (Sum.inr 1243, 2), (Sum.inr 1269, 2), (Sum.inr 2865, 4), (Sum.inr 2886, 1), (Sum.inr 2914, 2), (Sum.inr 2939, 4), (Sum.inr 3002, 1), (Sum.inr 3089, 4), (Sum.inr 3103, 2), (Sum.inr 3112, 2), (Sum.inr 4037, 1)]

def sourceForm151 : Integer.Sparse Master := [(Sum.inr 3291, 4), (Sum.inr 3298, 1), (Sum.inr 3300, 2), (Sum.inr 3302, 2), (Sum.inr 3468, 4), (Sum.inr 3484, 1), (Sum.inr 3513, 2), (Sum.inr 3530, 4), (Sum.inr 3533, 4), (Sum.inr 3547, 2), (Sum.inr 3579, 1), (Sum.inr 3582, 2), (Sum.inr 3860, 1)]

def sourceForm152 : Integer.Sparse Master := [(Sum.inr 2722, 2), (Sum.inr 2726, 1), (Sum.inr 2742, 1), (Sum.inr 2765, 1), (Sum.inr 3905, 1), (Sum.inr 4092, -1)]

def sourceForm153 : Integer.Sparse Master := [(Sum.inr 1215, 2), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

def sourceForm154 : Integer.Sparse Master := [(Sum.inr 1242, 1), (Sum.inr 2482, 2), (Sum.inr 2517, 1), (Sum.inr 2726, 1), (Sum.inr 2742, 1), (Sum.inr 4092, -1)]

def sourceForm155 : Integer.Sparse Master := [(Sum.inr 1264, 1), (Sum.inr 2569, 2), (Sum.inr 2635, 1), (Sum.inr 2726, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def sourceForm156 : Integer.Sparse Master := [(Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 2542, 1), (Sum.inr 2569, 1), (Sum.inr 2722, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

def sourceForm157 : Integer.Sparse Master := [(Sum.inr 4401, 4), (Sum.inr 4405, 1), (Sum.inr 4428, 2), (Sum.inr 4460, 2), (Sum.inr 5000, 4), (Sum.inr 5021, 1), (Sum.inr 5047, 2), (Sum.inr 5075, 4), (Sum.inr 5171, 1), (Sum.inr 5259, 4), (Sum.inr 5275, 2), (Sum.inr 5293, 2), (Sum.inr 5491, 1)]

def sourceForm158 : Integer.Sparse Master := [(Sum.inr 982, 4), (Sum.inr 986, 1), (Sum.inr 1009, 2), (Sum.inr 1043, 2), (Sum.inr 2385, 4), (Sum.inr 2407, 1), (Sum.inr 2449, 2), (Sum.inr 2482, 4), (Sum.inr 2598, 1), (Sum.inr 2723, 4), (Sum.inr 2743, 2), (Sum.inr 2767, 2), (Sum.inr 4014, 1)]

def sourceForm159 : Integer.Sparse Master := [(Sum.inr 4832, 4), (Sum.inr 4837, 1), (Sum.inr 4845, 2), (Sum.inr 4897, 2), (Sum.inr 5222, 4), (Sum.inr 5235, 1), (Sum.inr 5239, 2), (Sum.inr 5252, 4), (Sum.inr 5261, 5), (Sum.inr 5268, 2), (Sum.inr 5296, 2), (Sum.inr 5312, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1281 : Integer.Sparse Master := [(Sum.inr 1037, 3), (Sum.inr 1077, 1), (Sum.inr 1085, 1), (Sum.inr 1211, 6), (Sum.inr 1231, 3), (Sum.inr 1239, 3), (Sum.inr 1258, 3), (Sum.inr 1264, 3), (Sum.inr 1289, 1), (Sum.inr 1304, 1), (Sum.inr 1408, 3), (Sum.inr 1438, 1), (Sum.inr 1445, 1)]

def sourceForm1282 : Integer.Sparse Master := [(Sum.inr 1047, 3), (Sum.inr 1091, 1), (Sum.inr 1092, 1), (Sum.inr 1218, 6), (Sum.inr 1243, 3), (Sum.inr 1244, 3), (Sum.inr 1271, 3), (Sum.inr 1272, 3), (Sum.inr 1307, 1), (Sum.inr 1309, 1), (Sum.inr 1417, 3), (Sum.inr 1452, 1), (Sum.inr 1453, 1)]

def sourceForm1283 : Integer.Sparse Master := [(Sum.inr 1077, 1), (Sum.inr 1647, 3), (Sum.inr 1730, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def sourceForm1284 : Integer.Sparse Master := [(Sum.inr 1289, 1), (Sum.inr 1657, 3), (Sum.inr 1741, 1), (Sum.inr 2780, 1), (Sum.inr 4071, -1)]

def sourceForm1285 : Integer.Sparse Master := [(Sum.inr 4153, 2), (Sum.inr 4156, 1), (Sum.inr 4161, 1), (Sum.inr 4178, 1), (Sum.inr 4528, 2), (Sum.inr 4531, 2), (Sum.inr 4535, 2), (Sum.inr 4546, 2), (Sum.inr 4547, 2), (Sum.inr 4555, 1), (Sum.inr 4558, 1), (Sum.inr 4591, 2), (Sum.inr 4594, 1), (Sum.inr 4602, 2), (Sum.inr 4609, 1), (Sum.inr 4612, 1), (Sum.inr 4619, 1), (Sum.inr 5075, 2), (Sum.inr 5107, 1), (Sum.inr 5261, 1), (Sum.inr 5274, 1)]

def sourceForm1286 : Integer.Sparse Master := [(Sum.inr 581, 2), (Sum.inr 584, 1), (Sum.inr 589, 1), (Sum.inr 606, 1), (Sum.inr 1112, 2), (Sum.inr 1115, 2), (Sum.inr 1120, 2), (Sum.inr 1132, 2), (Sum.inr 1165, 2), (Sum.inr 1168, 1), (Sum.inr 1176, 1), (Sum.inr 1217, 2), (Sum.inr 1221, 1), (Sum.inr 1243, 1), (Sum.inr 1267, 2), (Sum.inr 1274, 1), (Sum.inr 1302, 1), (Sum.inr 2939, 2), (Sum.inr 3002, 1), (Sum.inr 3090, 1), (Sum.inr 3112, 1)]

def sourceForm1287 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1516, 1), (Sum.inr 1520, 1), (Sum.inr 1533, 1), (Sum.inr 3260, 2), (Sum.inr 3262, 2), (Sum.inr 3264, 2), (Sum.inr 3266, 2), (Sum.inr 3272, 2), (Sum.inr 3275, 1), (Sum.inr 3276, 1), (Sum.inr 3291, 2), (Sum.inr 3293, 2), (Sum.inr 3298, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3468, 2), (Sum.inr 3484, 1), (Sum.inr 3545, 1), (Sum.inr 3547, 1)]

def sourceForm1288 : Integer.Sparse Master := [(Sum.inr 626, 2), (Sum.inr 633, 1), (Sum.inr 635, 1), (Sum.inr 641, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

def sourceForm1289 : Integer.Sparse Master := [(Sum.inr 1115, 1), (Sum.inr 1148, 1), (Sum.inr 1154, 1), (Sum.inr 1159, 1), (Sum.inr 1242, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

def sourceForm1290 : Integer.Sparse Master := [(Sum.inr 1131, 2), (Sum.inr 1140, 1), (Sum.inr 1144, 1), (Sum.inr 1242, 1), (Sum.inr 2517, 1), (Sum.inr 4092, -1)]

def sourceForm1291 : Integer.Sparse Master := [(Sum.inr 4144, 2), (Sum.inr 4146, 1), (Sum.inr 4148, 1), (Sum.inr 4177, 1), (Sum.inr 4293, 2), (Sum.inr 4315, 1), (Sum.inr 4468, 1), (Sum.inr 4517, 2), (Sum.inr 4520, 1), (Sum.inr 4523, 2), (Sum.inr 4526, 2), (Sum.inr 4546, 2), (Sum.inr 4606, 2), (Sum.inr 4608, 2), (Sum.inr 4612, 1), (Sum.inr 4624, 1), (Sum.inr 4625, 1), (Sum.inr 5078, 2), (Sum.inr 5109, 1), (Sum.inr 5293, 1), (Sum.inr 5296, 1)]

def sourceForm1292 : Integer.Sparse Master := [(Sum.inr 572, 2), (Sum.inr 574, 1), (Sum.inr 576, 1), (Sum.inr 605, 1), (Sum.inr 871, 2), (Sum.inr 893, 1), (Sum.inr 1051, 1), (Sum.inr 1101, 2), (Sum.inr 1104, 1), (Sum.inr 1107, 2), (Sum.inr 1110, 2), (Sum.inr 1131, 2), (Sum.inr 1240, 2), (Sum.inr 1242, 2), (Sum.inr 1246, 1), (Sum.inr 1301, 1), (Sum.inr 1304, 1), (Sum.inr 2485, 2), (Sum.inr 2519, 1), (Sum.inr 2770, 1), (Sum.inr 3102, 1)]

def sourceForm1295 : Integer.Sparse Master := [(Sum.inr 1617, 2), (Sum.inr 1625, 1), (Sum.inr 1630, 1), (Sum.inr 1754, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def sourceForm1296 : Integer.Sparse Master := [(Sum.inr 4157, 2), (Sum.inr 4159, 1), (Sum.inr 4162, 1), (Sum.inr 4184, 1), (Sum.inr 4330, 2), (Sum.inr 4356, 1), (Sum.inr 4468, 1), (Sum.inr 4532, 2), (Sum.inr 4536, 2), (Sum.inr 4543, 2), (Sum.inr 4552, 2), (Sum.inr 4557, 1), (Sum.inr 4600, 2), (Sum.inr 4605, 2), (Sum.inr 4611, 1), (Sum.inr 4617, 1), (Sum.inr 4621, 1), (Sum.inr 4804, 2), (Sum.inr 4841, 1), (Sum.inr 4897, 1), (Sum.inr 5272, 1)]

def sourceForm1297 : Integer.Sparse Master := [(Sum.inr 585, 2), (Sum.inr 587, 1), (Sum.inr 590, 1), (Sum.inr 612, 1), (Sum.inr 1116, 2), (Sum.inr 1118, 2), (Sum.inr 1121, 2), (Sum.inr 1137, 2), (Sum.inr 1170, 2), (Sum.inr 1173, 1), (Sum.inr 1177, 1), (Sum.inr 1270, 2), (Sum.inr 1271, 2), (Sum.inr 1273, 1), (Sum.inr 1275, 1), (Sum.inr 1306, 1), (Sum.inr 1308, 1), (Sum.inr 2941, 2), (Sum.inr 3004, 1), (Sum.inr 3113, 1), (Sum.inr 3114, 1)]

def sourceForm1298 : Integer.Sparse Master := [(Sum.inr 1528, 2), (Sum.inr 1529, 1), (Sum.inr 1530, 1), (Sum.inr 1532, 1), (Sum.inr 1672, 2), (Sum.inr 1692, 1), (Sum.inr 1752, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2172, 2), (Sum.inr 2184, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2226, 2), (Sum.inr 2228, 1), (Sum.inr 2289, 1), (Sum.inr 2292, 1), (Sum.inr 2683, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 1)]

def sourceForm1299 : Integer.Sparse Master := [(Sum.inr 624, 2), (Sum.inr 628, 1), (Sum.inr 634, 1), (Sum.inr 639, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

def sourceForm1300 : Integer.Sparse Master := [(Sum.inr 624, 1), (Sum.inr 1128, 1), (Sum.inr 1147, 1), (Sum.inr 1234, 1), (Sum.inr 1239, 2), (Sum.inr 4084, -1)]

def sourceForm1301 : Integer.Sparse Master := [(Sum.inr 908, 1), (Sum.inr 1147, 1), (Sum.inr 1153, 1), (Sum.inr 1157, 1), (Sum.inr 1239, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

def sourceForm1302 : Integer.Sparse Master := [(Sum.inr 934, 1), (Sum.inr 1128, 2), (Sum.inr 1143, 1), (Sum.inr 1239, 1), (Sum.inr 2060, 1), (Sum.inr 4084, -1)]

def sourceForm1303 : Integer.Sparse Master := [(Sum.inr 4140, 2), (Sum.inr 4142, 1), (Sum.inr 4147, 1), (Sum.inr 4174, 1), (Sum.inr 4202, 2), (Sum.inr 4225, 1), (Sum.inr 4257, 1), (Sum.inr 4514, 2), (Sum.inr 4519, 1), (Sum.inr 4521, 2), (Sum.inr 4525, 2), (Sum.inr 4543, 2), (Sum.inr 4583, 2), (Sum.inr 4602, 2), (Sum.inr 4605, 1), (Sum.inr 4612, 1), (Sum.inr 4623, 1), (Sum.inr 4807, 2), (Sum.inr 4843, 1), (Sum.inr 4890, 1), (Sum.inr 5294, 1)]

def sourceForm1304 : Integer.Sparse Master := [(Sum.inr 568, 2), (Sum.inr 570, 1), (Sum.inr 575, 1), (Sum.inr 602, 1), (Sum.inr 705, 2), (Sum.inr 726, 1), (Sum.inr 791, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1105, 2), (Sum.inr 1109, 2), (Sum.inr 1128, 2), (Sum.inr 1202, 2), (Sum.inr 1236, 2), (Sum.inr 1239, 1), (Sum.inr 1246, 1), (Sum.inr 1300, 1), (Sum.inr 2025, 2), (Sum.inr 2062, 1), (Sum.inr 2247, 1), (Sum.inr 3101, 1)]

def sourceForm1307 : Integer.Sparse Master := [(Sum.inr 1002, 1), (Sum.inr 1599, 2), (Sum.inr 1625, 1), (Sum.inr 1730, 1), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

def sourceForm1308 : Integer.Sparse Master := [(Sum.inr 1231, 1), (Sum.inr 1637, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

def sourceForm1309 : Integer.Sparse Master := [(Sum.inr 1191, 1), (Sum.inr 2391, 2), (Sum.inr 2407, 1), (Sum.inr 2680, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

def sourceForm1310 : Integer.Sparse Master := [(Sum.inr 1185, 2), (Sum.inr 1191, 1), (Sum.inr 1193, 1), (Sum.inr 1288, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

def sourceForm1311 : Integer.Sparse Master := [(Sum.inr 1190, 1), (Sum.inr 1924, 2), (Sum.inr 1950, 1), (Sum.inr 2218, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1312 : Integer.Sparse Master := [(Sum.inr 893, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1190, 1), (Sum.inr 1950, 1), (Sum.inr 4082, -1)]

def sourceForm1313 : Integer.Sparse Master := [(Sum.inr 1184, 2), (Sum.inr 1190, 1), (Sum.inr 1192, 1), (Sum.inr 1287, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

def sourceForm1315 : Integer.Sparse Master := [(Sum.inr 1186, 1), (Sum.inr 1608, 2), (Sum.inr 1627, 1), (Sum.inr 1741, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

def sourceForm1316 : Integer.Sparse Master := [(Sum.inr 1203, 1), (Sum.inr 2377, 1), (Sum.inr 2385, 2), (Sum.inr 2664, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def sourceForm1317 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 1203, 1), (Sum.inr 1205, 1), (Sum.inr 1230, 2), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def sourceForm1318 : Integer.Sparse Master := [(Sum.inr 1202, 1), (Sum.inr 1897, 1), (Sum.inr 1914, 2), (Sum.inr 2193, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

def sourceForm1319 : Integer.Sparse Master := [(Sum.inr 871, 1), (Sum.inr 1105, 1), (Sum.inr 1109, 1), (Sum.inr 1123, 1), (Sum.inr 1202, 1), (Sum.inr 1914, 1), (Sum.inr 4080, -1)]

def sourceForm1320 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 1202, 1), (Sum.inr 1204, 1), (Sum.inr 1229, 2), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

def sourceForm1322 : Integer.Sparse Master := [(Sum.inr 1199, 1), (Sum.inr 1592, 1), (Sum.inr 1602, 2), (Sum.inr 1710, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

def sourceForm1323 : Integer.Sparse Master := [(Sum.inr 1055, 1), (Sum.inr 2032, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

def sourceForm1324 : Integer.Sparse Master := [(Sum.inr 1053, 2), (Sum.inr 1055, 1), (Sum.inr 1062, 1), (Sum.inr 1075, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

def sourceForm1325 : Integer.Sparse Master := [(Sum.inr 991, 1), (Sum.inr 1926, 1), (Sum.inr 1992, 1), (Sum.inr 2121, 1), (Sum.inr 2197, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def sourceForm1326 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 991, 1), (Sum.inr 993, 1), (Sum.inr 1005, 1), (Sum.inr 1054, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def sourceForm1327 : Integer.Sparse Master := [(Sum.inr 989, 1), (Sum.inr 1924, 1), (Sum.inr 1991, 1), (Sum.inr 2119, 1), (Sum.inr 2215, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def sourceForm1328 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 989, 1), (Sum.inr 992, 1), (Sum.inr 1000, 1), (Sum.inr 1053, 1), (Sum.inr 2215, 1), (Sum.inr 4082, -1)]

def sourceForm1329 : Integer.Sparse Master := [(Sum.inr 1019, 1), (Sum.inr 2008, 1), (Sum.inr 2087, 2), (Sum.inr 2193, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

def sourceForm1330 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 1019, 1), (Sum.inr 1025, 1), (Sum.inr 1035, 2), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

def sourceForm1331 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 1898, 1), (Sum.inr 2071, 2), (Sum.inr 2187, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

def sourceForm1332 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 974, 1), (Sum.inr 980, 2), (Sum.inr 1018, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

def sourceForm1333 : Integer.Sparse Master := [(Sum.inr 971, 1), (Sum.inr 1897, 1), (Sum.inr 2070, 2), (Sum.inr 2190, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def sourceForm1334 : Integer.Sparse Master := [(Sum.inr 971, 1), (Sum.inr 973, 1), (Sum.inr 977, 2), (Sum.inr 1017, 1), (Sum.inr 2190, 1), (Sum.inr 4080, -1)]

def sourceForm1335 : Integer.Sparse Master := [(Sum.inr 4153, 2), (Sum.inr 4159, 1), (Sum.inr 4161, 1), (Sum.inr 4183, 1), (Sum.inr 4327, 2), (Sum.inr 4333, 2), (Sum.inr 4335, 2), (Sum.inr 4352, 2), (Sum.inr 4358, 1), (Sum.inr 4367, 2), (Sum.inr 4374, 1), (Sum.inr 4440, 2), (Sum.inr 4445, 1), (Sum.inr 4458, 2), (Sum.inr 4463, 1), (Sum.inr 4467, 1), (Sum.inr 4502, 1), (Sum.inr 4807, 2), (Sum.inr 4871, 1), (Sum.inr 4890, 1), (Sum.inr 4895, 1)]

def sourceForm1336 : Integer.Sparse Master := [(Sum.inr 626, 2), (Sum.inr 628, 1), (Sum.inr 635, 1), (Sum.inr 645, 1), (Sum.inr 911, 2), (Sum.inr 936, 1), (Sum.inr 1027, 1), (Sum.inr 1317, 2), (Sum.inr 1324, 1), (Sum.inr 1327, 2), (Sum.inr 1333, 2), (Sum.inr 1340, 2), (Sum.inr 1388, 2), (Sum.inr 1411, 2), (Sum.inr 1413, 1), (Sum.inr 1420, 1), (Sum.inr 1447, 1), (Sum.inr 2574, 2), (Sum.inr 2602, 1), (Sum.inr 2755, 1), (Sum.inr 3229, 1)]

def sourceForm1337 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1532, 1), (Sum.inr 1533, 1), (Sum.inr 1535, 1), (Sum.inr 1670, 2), (Sum.inr 1688, 2), (Sum.inr 1689, 2), (Sum.inr 1690, 2), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1723, 2), (Sum.inr 1724, 2), (Sum.inr 1748, 1), (Sum.inr 1749, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 1753, 1), (Sum.inr 2224, 2), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 1)]

def sourceForm1338 : Integer.Sparse Master := [(Sum.inr 581, 2), (Sum.inr 587, 1), (Sum.inr 589, 1), (Sum.inr 611, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

def sourceForm1339 : Integer.Sparse Master := [(Sum.inr 611, 1), (Sum.inr 930, 2), (Sum.inr 1046, 2), (Sum.inr 1086, 1), (Sum.inr 4083, -1)]

def sourceForm1340 : Integer.Sparse Master := [(Sum.inr 945, 2), (Sum.inr 951, 1), (Sum.inr 953, 1), (Sum.inr 1046, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

def sourceForm1341 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 911, 1), (Sum.inr 913, 1), (Sum.inr 930, 1), (Sum.inr 1046, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

def sourceForm1342 : Integer.Sparse Master := [(Sum.inr 4105, 2), (Sum.inr 4108, 1), (Sum.inr 4111, 1), (Sum.inr 4128, 1), (Sum.inr 4290, 2), (Sum.inr 4293, 2), (Sum.inr 4296, 2), (Sum.inr 4309, 2), (Sum.inr 4352, 2), (Sum.inr 4356, 1), (Sum.inr 4361, 1), (Sum.inr 4461, 2), (Sum.inr 4463, 2), (Sum.inr 4466, 1), (Sum.inr 4468, 1), (Sum.inr 4503, 1), (Sum.inr 4507, 1), (Sum.inr 5078, 2), (Sum.inr 5174, 1), (Sum.inr 5294, 1), (Sum.inr 5296, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1344 : Integer.Sparse Master := [(Sum.inr 4253, 2), (Sum.inr 4269, 1), (Sum.inr 4270, 1), (Sum.inr 4276, 1), (Sum.inr 4391, 2), (Sum.inr 4401, 2), (Sum.inr 4402, 2), (Sum.inr 4410, 2), (Sum.inr 4440, 2), (Sum.inr 4442, 2), (Sum.inr 4460, 1), (Sum.inr 4463, 2), (Sum.inr 4464, 1), (Sum.inr 4476, 1), (Sum.inr 4478, 1), (Sum.inr 4505, 1), (Sum.inr 4507, 1), (Sum.inr 4591, 2), (Sum.inr 4605, 1), (Sum.inr 4608, 1), (Sum.inr 4625, 1)]

def sourceForm1345 : Integer.Sparse Master := [(Sum.inr 787, 2), (Sum.inr 812, 1), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 972, 2), (Sum.inr 982, 2), (Sum.inr 983, 2), (Sum.inr 991, 2), (Sum.inr 1022, 2), (Sum.inr 1024, 2), (Sum.inr 1043, 1), (Sum.inr 1046, 2), (Sum.inr 1047, 1), (Sum.inr 1059, 1), (Sum.inr 1061, 1), (Sum.inr 1089, 1), (Sum.inr 1091, 1), (Sum.inr 1217, 2), (Sum.inr 1269, 1), (Sum.inr 1271, 1), (Sum.inr 1307, 1)]

def sourceForm1347 : Integer.Sparse Master := [(Sum.inr 847, 2), (Sum.inr 851, 1), (Sum.inr 853, 1), (Sum.inr 857, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

def sourceForm1348 : Integer.Sparse Master := [(Sum.inr 4151, 2), (Sum.inr 4156, 1), (Sum.inr 4160, 1), (Sum.inr 4177, 1), (Sum.inr 4326, 2), (Sum.inr 4330, 2), (Sum.inr 4334, 2), (Sum.inr 4346, 2), (Sum.inr 4365, 2), (Sum.inr 4370, 1), (Sum.inr 4373, 1), (Sum.inr 4457, 2), (Sum.inr 4460, 2), (Sum.inr 4466, 1), (Sum.inr 4468, 1), (Sum.inr 4498, 1), (Sum.inr 4505, 1), (Sum.inr 4804, 2), (Sum.inr 4868, 1), (Sum.inr 4894, 1), (Sum.inr 4897, 1)]

def sourceForm1349 : Integer.Sparse Master := [(Sum.inr 630, 2), (Sum.inr 633, 1), (Sum.inr 636, 1), (Sum.inr 647, 1), (Sum.inr 1118, 2), (Sum.inr 1142, 1), (Sum.inr 1275, 1), (Sum.inr 1320, 2), (Sum.inr 1325, 1), (Sum.inr 1329, 2), (Sum.inr 1334, 2), (Sum.inr 1342, 2), (Sum.inr 1414, 2), (Sum.inr 1416, 2), (Sum.inr 1419, 1), (Sum.inr 1448, 1), (Sum.inr 1450, 1), (Sum.inr 2941, 2), (Sum.inr 2966, 1), (Sum.inr 3114, 1), (Sum.inr 3230, 1)]

def sourceForm1350 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1516, 1), (Sum.inr 1518, 1), (Sum.inr 1523, 1), (Sum.inr 1663, 2), (Sum.inr 1672, 2), (Sum.inr 1674, 2), (Sum.inr 1679, 2), (Sum.inr 1704, 2), (Sum.inr 1707, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 2), (Sum.inr 1727, 1), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1752, 1), (Sum.inr 1754, 1), (Sum.inr 2203, 2), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2292, 1)]

def sourceForm1351 : Integer.Sparse Master := [(Sum.inr 579, 2), (Sum.inr 584, 1), (Sum.inr 588, 1), (Sum.inr 605, 1), (Sum.inr 1043, 1), (Sum.inr 4084, -1)]

def sourceForm1352 : Integer.Sparse Master := [(Sum.inr 605, 1), (Sum.inr 924, 2), (Sum.inr 1043, 1), (Sum.inr 1082, 1), (Sum.inr 1089, 1), (Sum.inr 4084, -1)]

def sourceForm1353 : Integer.Sparse Master := [(Sum.inr 943, 2), (Sum.inr 948, 1), (Sum.inr 952, 1), (Sum.inr 1043, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

def sourceForm1354 : Integer.Sparse Master := [(Sum.inr 579, 1), (Sum.inr 904, 1), (Sum.inr 943, 1), (Sum.inr 1040, 1), (Sum.inr 1043, 2), (Sum.inr 4084, -1)]

def sourceForm1355 : Integer.Sparse Master := [(Sum.inr 904, 1), (Sum.inr 908, 1), (Sum.inr 912, 1), (Sum.inr 924, 1), (Sum.inr 1043, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

def sourceForm1356 : Integer.Sparse Master := [(Sum.inr 4101, 2), (Sum.inr 4103, 1), (Sum.inr 4110, 1), (Sum.inr 4121, 1), (Sum.inr 4287, 2), (Sum.inr 4289, 2), (Sum.inr 4295, 2), (Sum.inr 4303, 2), (Sum.inr 4346, 2), (Sum.inr 4350, 1), (Sum.inr 4360, 1), (Sum.inr 4401, 2), (Sum.inr 4405, 1), (Sum.inr 4428, 1), (Sum.inr 4458, 2), (Sum.inr 4467, 1), (Sum.inr 4499, 1), (Sum.inr 5075, 2), (Sum.inr 5171, 1), (Sum.inr 5261, 1), (Sum.inr 5293, 1)]

def sourceForm1357 : Integer.Sparse Master := [(Sum.inr 538, 2), (Sum.inr 540, 1), (Sum.inr 547, 1), (Sum.inr 555, 1), (Sum.inr 865, 2), (Sum.inr 867, 2), (Sum.inr 873, 2), (Sum.inr 881, 2), (Sum.inr 924, 2), (Sum.inr 928, 1), (Sum.inr 938, 1), (Sum.inr 982, 2), (Sum.inr 986, 1), (Sum.inr 1009, 1), (Sum.inr 1041, 2), (Sum.inr 1050, 1), (Sum.inr 1083, 1), (Sum.inr 2482, 2), (Sum.inr 2598, 1), (Sum.inr 2726, 1), (Sum.inr 2767, 1)]

def sourceForm1360 : Integer.Sparse Master := [(Sum.inr 1217, 2), (Sum.inr 1242, 1), (Sum.inr 1243, 1), (Sum.inr 1307, 1), (Sum.inr 1361, 2), (Sum.inr 1372, 1), (Sum.inr 1373, 1), (Sum.inr 1379, 2), (Sum.inr 1388, 2), (Sum.inr 1389, 2), (Sum.inr 1397, 2), (Sum.inr 1399, 2), (Sum.inr 1413, 1), (Sum.inr 1416, 2), (Sum.inr 1417, 1), (Sum.inr 1450, 1), (Sum.inr 1452, 1), (Sum.inr 1471, 1), (Sum.inr 1478, 2), (Sum.inr 1484, 1), (Sum.inr 1485, 1)]

def sourceForm1361 : Integer.Sparse Master := [(Sum.inr 1037, 1), (Sum.inr 2018, 2), (Sum.inr 2103, 1), (Sum.inr 2208, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

def sourceForm1362 : Integer.Sparse Master := [(Sum.inr 594, 1), (Sum.inr 916, 2), (Sum.inr 1007, 1), (Sum.inr 1037, 1), (Sum.inr 1074, 1), (Sum.inr 4081, -1)]

def sourceForm1363 : Integer.Sparse Master := [(Sum.inr 1033, 2), (Sum.inr 1037, 1), (Sum.inr 1048, 1), (Sum.inr 1074, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

def sourceForm1364 : Integer.Sparse Master := [(Sum.inr 731, 2), (Sum.inr 735, 1), (Sum.inr 741, 1), (Sum.inr 809, 1), (Sum.inr 1647, 1), (Sum.inr 4070, -1)]

def sourceForm1366 : Integer.Sparse Master := [(Sum.inr 978, 1), (Sum.inr 983, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1036, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

def sourceForm1367 : Integer.Sparse Master := [(Sum.inr 982, 1), (Sum.inr 1914, 1), (Sum.inr 1987, 1), (Sum.inr 2079, 1), (Sum.inr 2193, 1), (Sum.inr 2205, 1), (Sum.inr 4080, -1)]

def sourceForm1370 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1004, 1), (Sum.inr 1035, 1), (Sum.inr 2205, 1), (Sum.inr 4080, -1)]

def sourceForm1373 : Integer.Sparse Master := [(Sum.inr 979, 1), (Sum.inr 1911, 1), (Sum.inr 1986, 1), (Sum.inr 2018, 1), (Sum.inr 2203, 1), (Sum.inr 2208, 1), (Sum.inr 4081, -1)]

def sourceForm1375 : Integer.Sparse Master := [(Sum.inr 864, 1), (Sum.inr 867, 1), (Sum.inr 872, 1), (Sum.inr 880, 1), (Sum.inr 979, 1), (Sum.inr 1911, 1), (Sum.inr 4081, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1376 : Integer.Sparse Master := [(Sum.inr 976, 1), (Sum.inr 979, 1), (Sum.inr 984, 1), (Sum.inr 999, 1), (Sum.inr 1033, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

def sourceForm1377 : Integer.Sparse Master := [(Sum.inr 698, 1), (Sum.inr 701, 1), (Sum.inr 706, 1), (Sum.inr 714, 1), (Sum.inr 809, 1), (Sum.inr 1599, 1), (Sum.inr 4070, -1)]

def sourceForm1378 : Integer.Sparse Master := [(Sum.inr 4178, 3), (Sum.inr 4189, 1), (Sum.inr 4192, 1), (Sum.inr 4347, 6), (Sum.inr 4358, 3), (Sum.inr 4361, 3), (Sum.inr 4476, 3), (Sum.inr 4481, 1), (Sum.inr 4499, 3), (Sum.inr 4511, 1), (Sum.inr 4843, 3), (Sum.inr 4899, 1), (Sum.inr 4901, 1)]

def sourceForm1379 : Integer.Sparse Master := [(Sum.inr 1520, 3), (Sum.inr 1539, 1), (Sum.inr 1540, 1), (Sum.inr 1676, 6), (Sum.inr 1694, 3), (Sum.inr 1695, 3), (Sum.inr 1728, 3), (Sum.inr 1729, 3), (Sum.inr 1755, 1), (Sum.inr 1757, 1), (Sum.inr 2230, 3), (Sum.inr 2293, 1), (Sum.inr 2294, 1)]

def sourceForm1380 : Integer.Sparse Master := [(Sum.inr 925, 2), (Sum.inr 936, 1), (Sum.inr 939, 1), (Sum.inr 1091, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def sourceForm1381 : Integer.Sparse Master := [(Sum.inr 4128, 3), (Sum.inr 4134, 1), (Sum.inr 4138, 1), (Sum.inr 4309, 6), (Sum.inr 4315, 3), (Sum.inr 4319, 3), (Sum.inr 4463, 3), (Sum.inr 4468, 1), (Sum.inr 4503, 3), (Sum.inr 4510, 1), (Sum.inr 5109, 3), (Sum.inr 5296, 1), (Sum.inr 5310, 1)]

def sourceForm1385 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4177, 3), (Sum.inr 4187, 1), (Sum.inr 4191, 1), (Sum.inr 4346, 6), (Sum.inr 4356, 3), (Sum.inr 4360, 3), (Sum.inr 4460, 3), (Sum.inr 4468, 1), (Sum.inr 4498, 3), (Sum.inr 4511, 1), (Sum.inr 4841, 3), (Sum.inr 4897, 1)]

def sourceForm1386 : Integer.Sparse Master := [(Sum.inr 1518, 3), (Sum.inr 1537, 1), (Sum.inr 1538, 1), (Sum.inr 1674, 6), (Sum.inr 1692, 3), (Sum.inr 1693, 3), (Sum.inr 1725, 3), (Sum.inr 1727, 3), (Sum.inr 1752, 1), (Sum.inr 1755, 1), (Sum.inr 2228, 3), (Sum.inr 2292, 1), (Sum.inr 4084, 1)]

def sourceForm1387 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4174, 3), (Sum.inr 4181, 1), (Sum.inr 4190, 1), (Sum.inr 4343, 6), (Sum.inr 4350, 3), (Sum.inr 4359, 3), (Sum.inr 4496, 3), (Sum.inr 4501, 3), (Sum.inr 4510, 1), (Sum.inr 4512, 1), (Sum.inr 4837, 3), (Sum.inr 4897, 1)]

def sourceForm1388 : Integer.Sparse Master := [(Sum.inr 1509, 3), (Sum.inr 1521, 1), (Sum.inr 1527, 1), (Sum.inr 1666, 6), (Sum.inr 1677, 3), (Sum.inr 1683, 3), (Sum.inr 1710, 3), (Sum.inr 1730, 3), (Sum.inr 1741, 1), (Sum.inr 1758, 1), (Sum.inr 2208, 3), (Sum.inr 2268, 1), (Sum.inr 4085, 1)]

def sourceForm1389 : Integer.Sparse Master := [(Sum.inr 602, 3), (Sum.inr 609, 1), (Sum.inr 618, 1), (Sum.inr 1085, 1), (Sum.inr 4085, -1)]

def sourceForm1390 : Integer.Sparse Master := [(Sum.inr 602, 1), (Sum.inr 921, 2), (Sum.inr 1080, 1), (Sum.inr 1085, 2), (Sum.inr 4085, -1)]

def sourceForm1391 : Integer.Sparse Master := [(Sum.inr 1010, 1), (Sum.inr 1951, 1), (Sum.inr 2004, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def sourceForm1392 : Integer.Sparse Master := [(Sum.inr 1001, 2), (Sum.inr 1010, 1), (Sum.inr 1012, 1), (Sum.inr 1076, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def sourceForm1393 : Integer.Sparse Master := [(Sum.inr 1009, 1), (Sum.inr 1950, 1), (Sum.inr 2003, 2), (Sum.inr 2218, 1), (Sum.inr 2229, 1), (Sum.inr 4082, -1)]

def sourceForm1396 : Integer.Sparse Master := [(Sum.inr 1000, 2), (Sum.inr 1009, 1), (Sum.inr 1013, 1), (Sum.inr 1075, 1), (Sum.inr 2229, 1), (Sum.inr 4082, -1)]

def sourceForm1399 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4140, 2), (Sum.inr 4146, 1), (Sum.inr 4147, 1), (Sum.inr 4166, 1), (Sum.inr 4289, 2), (Sum.inr 4302, 2), (Sum.inr 4312, 1), (Sum.inr 4317, 1), (Sum.inr 4320, 2), (Sum.inr 4324, 2), (Sum.inr 4338, 2), (Sum.inr 4398, 2), (Sum.inr 4405, 1), (Sum.inr 4418, 2), (Sum.inr 4431, 1), (Sum.inr 4454, 1), (Sum.inr 4490, 1), (Sum.inr 4738, 2), (Sum.inr 4837, 1), (Sum.inr 4841, 1)]

def sourceForm1400 : Integer.Sparse Master := [(Sum.inr 1489, 2), (Sum.inr 1494, 1), (Sum.inr 1495, 1), (Sum.inr 1499, 1), (Sum.inr 1555, 2), (Sum.inr 1557, 2), (Sum.inr 1574, 1), (Sum.inr 1576, 1), (Sum.inr 1586, 2), (Sum.inr 1590, 2), (Sum.inr 1599, 2), (Sum.inr 1602, 2), (Sum.inr 1620, 1), (Sum.inr 1627, 1), (Sum.inr 1633, 2), (Sum.inr 1647, 1), (Sum.inr 1650, 1), (Sum.inr 1911, 2), (Sum.inr 2056, 1), (Sum.inr 2060, 1), (Sum.inr 4081, 1)]

def sourceForm1401 : Integer.Sparse Master := [(Sum.inr 867, 1), (Sum.inr 898, 1), (Sum.inr 902, 1), (Sum.inr 916, 1), (Sum.inr 1007, 1), (Sum.inr 1911, 1), (Sum.inr 4081, -1)]

def sourceForm1403 : Integer.Sparse Master := [(Sum.inr 793, 1), (Sum.inr 795, 1), (Sum.inr 796, 1), (Sum.inr 811, 1), (Sum.inr 827, 1), (Sum.inr 1715, 1), (Sum.inr 4069, -1)]

def sourceForm1405 : Integer.Sparse Master := [(Sum.inr 825, 2), (Sum.inr 829, 1), (Sum.inr 830, 1), (Sum.inr 858, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

def sourceForm1406 : Integer.Sparse Master := [(Sum.inr 828, 1), (Sum.inr 1610, 2), (Sum.inr 1659, 1), (Sum.inr 1716, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1408 : Integer.Sparse Master := [(Sum.inr 824, 2), (Sum.inr 828, 1), (Sum.inr 831, 1), (Sum.inr 856, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

def sourceForm1410 : Integer.Sparse Master := [(Sum.inr 826, 1), (Sum.inr 1608, 2), (Sum.inr 1657, 1), (Sum.inr 1738, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

def sourceForm1411 : Integer.Sparse Master := [(Sum.inr 555, 1), (Sum.inr 715, 2), (Sum.inr 826, 1), (Sum.inr 852, 1), (Sum.inr 859, 1), (Sum.inr 4071, -1)]

def sourceForm1412 : Integer.Sparse Master := [(Sum.inr 823, 2), (Sum.inr 826, 1), (Sum.inr 830, 1), (Sum.inr 852, 1), (Sum.inr 1738, 1), (Sum.inr 4071, -1)]

def sourceForm1413 : Integer.Sparse Master := [(Sum.inr 546, 1), (Sum.inr 706, 2), (Sum.inr 741, 1), (Sum.inr 809, 1), (Sum.inr 815, 1), (Sum.inr 4070, -1)]

def sourceForm1415 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 778, 1), (Sum.inr 783, 3), (Sum.inr 1698, 1), (Sum.inr 4068, -1)]

def sourceForm1417 : Integer.Sparse Master := [(Sum.inr 787, 1), (Sum.inr 1593, 1), (Sum.inr 1639, 2), (Sum.inr 1700, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

def sourceForm1418 : Integer.Sparse Master := [(Sum.inr 542, 1), (Sum.inr 702, 1), (Sum.inr 737, 1), (Sum.inr 787, 2), (Sum.inr 810, 1), (Sum.inr 4068, -1)]

def sourceForm1419 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 787, 1), (Sum.inr 790, 1), (Sum.inr 810, 2), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

def sourceForm1421 : Integer.Sparse Master := [(Sum.inr 785, 1), (Sum.inr 1592, 1), (Sum.inr 1637, 2), (Sum.inr 1707, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def sourceForm1422 : Integer.Sparse Master := [(Sum.inr 538, 1), (Sum.inr 699, 1), (Sum.inr 733, 1), (Sum.inr 785, 1), (Sum.inr 806, 1), (Sum.inr 812, 1), (Sum.inr 4069, -1)]

def sourceForm1423 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 785, 1), (Sum.inr 789, 1), (Sum.inr 806, 2), (Sum.inr 1707, 1), (Sum.inr 4069, -1)]

def sourceForm1424 : Integer.Sparse Master := [(Sum.inr 536, 1), (Sum.inr 698, 1), (Sum.inr 731, 1), (Sum.inr 804, 1), (Sum.inr 809, 2), (Sum.inr 4070, -1)]

def sourceForm1425 : Integer.Sparse Master := [(Sum.inr 813, 1), (Sum.inr 1603, 2), (Sum.inr 1651, 1), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def sourceForm1426 : Integer.Sparse Master := [(Sum.inr 548, 1), (Sum.inr 708, 2), (Sum.inr 743, 1), (Sum.inr 813, 1), (Sum.inr 816, 1), (Sum.inr 4069, -1)]

def sourceForm1427 : Integer.Sparse Master := [(Sum.inr 807, 2), (Sum.inr 813, 1), (Sum.inr 816, 1), (Sum.inr 856, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def sourceForm1429 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4101, 2), (Sum.inr 4108, 1), (Sum.inr 4110, 1), (Sum.inr 4127, 1), (Sum.inr 4196, 2), (Sum.inr 4202, 2), (Sum.inr 4204, 2), (Sum.inr 4218, 2), (Sum.inr 4233, 2), (Sum.inr 4240, 1), (Sum.inr 4242, 1), (Sum.inr 4251, 2), (Sum.inr 4257, 1), (Sum.inr 4264, 2), (Sum.inr 4269, 1), (Sum.inr 4273, 1), (Sum.inr 4418, 2), (Sum.inr 4490, 1), (Sum.inr 4496, 1), (Sum.inr 4498, 1)]

def sourceForm1430 : Integer.Sparse Master := [(Sum.inr 663, 2), (Sum.inr 683, 1), (Sum.inr 684, 1), (Sum.inr 688, 1), (Sum.inr 748, 2), (Sum.inr 762, 2), (Sum.inr 763, 2), (Sum.inr 767, 2), (Sum.inr 799, 2), (Sum.inr 804, 2), (Sum.inr 806, 2), (Sum.inr 842, 1), (Sum.inr 843, 1), (Sum.inr 849, 1), (Sum.inr 851, 1), (Sum.inr 852, 1), (Sum.inr 999, 2), (Sum.inr 1074, 1), (Sum.inr 1080, 1), (Sum.inr 1082, 1), (Sum.inr 4069, 1)]

def sourceForm1431 : Integer.Sparse Master := [(Sum.inr 812, 1), (Sum.inr 1602, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 1727, 1), (Sum.inr 4069, -1)]

def sourceForm1433 : Integer.Sparse Master := [(Sum.inr 733, 2), (Sum.inr 740, 1), (Sum.inr 742, 1), (Sum.inr 812, 1), (Sum.inr 1650, 1), (Sum.inr 4069, -1)]

def sourceForm1435 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4099, 2), (Sum.inr 4103, 1), (Sum.inr 4109, 1), (Sum.inr 4120, 1), (Sum.inr 4195, 2), (Sum.inr 4198, 2), (Sum.inr 4203, 2), (Sum.inr 4211, 2), (Sum.inr 4231, 2), (Sum.inr 4235, 1), (Sum.inr 4241, 1), (Sum.inr 4251, 2), (Sum.inr 4266, 2), (Sum.inr 4269, 1), (Sum.inr 4272, 1), (Sum.inr 4274, 1), (Sum.inr 4398, 2), (Sum.inr 4454, 1), (Sum.inr 4460, 1), (Sum.inr 4501, 1)]

def sourceForm1437 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4121, 3), (Sum.inr 4134, 1), (Sum.inr 4137, 1), (Sum.inr 4212, 6), (Sum.inr 4225, 3), (Sum.inr 4228, 3), (Sum.inr 4272, 3), (Sum.inr 4273, 3), (Sum.inr 4280, 1), (Sum.inr 4431, 3), (Sum.inr 4510, 1), (Sum.inr 4511, 1)]

def sourceForm1438 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4122, 3), (Sum.inr 4136, 1), (Sum.inr 4138, 1), (Sum.inr 4213, 6), (Sum.inr 4227, 3), (Sum.inr 4229, 3), (Sum.inr 4269, 3), (Sum.inr 4270, 3), (Sum.inr 4285, 1), (Sum.inr 4428, 3), (Sum.inr 4505, 1), (Sum.inr 4507, 1)]

def sourceForm1439 : Integer.Sparse Master := [(Sum.inr 4058, 3), (Sum.inr 4060, 1), (Sum.inr 4061, 1), (Sum.inr 4064, 6), (Sum.inr 4066, 3), (Sum.inr 4067, 3), (Sum.inr 4069, 3), (Sum.inr 4070, 3), (Sum.inr 4071, 1), (Sum.inr 4072, 1), (Sum.inr 4081, 3), (Sum.inr 4084, 1), (Sum.inr 4085, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1440 : Integer.Sparse Master := [(Sum.inr 616, 1), (Sum.inr 935, 2), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def sourceForm1441 : Integer.Sparse Master := [(Sum.inr 1318, 2), (Sum.inr 1324, 1), (Sum.inr 1325, 1), (Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

def sourceForm1443 : Integer.Sparse Master := [(Sum.inr 1736, 2), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1751, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

def sourceForm1444 : Integer.Sparse Master := [(Sum.inr 858, 1), (Sum.inr 1626, 2), (Sum.inr 1740, 2), (Sum.inr 1751, 1), (Sum.inr 4071, -1)]

def sourceForm1445 : Integer.Sparse Master := [(Sum.inr 830, 1), (Sum.inr 1611, 2), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

def sourceForm1448 : Integer.Sparse Master := [(Sum.inr 586, 1), (Sum.inr 910, 1), (Sum.inr 950, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

def sourceForm1449 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 1333, 1), (Sum.inr 1334, 1), (Sum.inr 1338, 1), (Sum.inr 1391, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

def sourceForm1450 : Integer.Sparse Master := [(Sum.inr 1736, 1), (Sum.inr 2397, 1), (Sum.inr 3280, 1), (Sum.inr 3284, 1), (Sum.inr 3301, 2), (Sum.inr 4071, -1)]

def sourceForm1452 : Integer.Sparse Master := [(Sum.inr 848, 1), (Sum.inr 1614, 1), (Sum.inr 1736, 2), (Sum.inr 1751, 2), (Sum.inr 4071, -1)]

def sourceForm1453 : Integer.Sparse Master := [(Sum.inr 823, 1), (Sum.inr 1606, 1), (Sum.inr 1655, 1), (Sum.inr 1736, 1), (Sum.inr 1738, 2), (Sum.inr 4071, -1)]

def sourceForm1455 : Integer.Sparse Master := [(Sum.inr 1356, 1), (Sum.inr 2856, 1), (Sum.inr 2911, 1), (Sum.inr 2970, 1), (Sum.inr 3025, 2), (Sum.inr 4088, -1)]

def sourceForm1457 : Integer.Sparse Master := [(Sum.inr 1133, 2), (Sum.inr 1143, 1), (Sum.inr 1146, 1), (Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

def sourceForm1458 : Integer.Sparse Master := [(Sum.inr 653, 1), (Sum.inr 1171, 2), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 1306, 1), (Sum.inr 4092, -1)]

def sourceForm1459 : Integer.Sparse Master := [(Sum.inr 1655, 2), (Sum.inr 1657, 1), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

def sourceForm1460 : Integer.Sparse Master := [(Sum.inr 1741, 1), (Sum.inr 2683, 3), (Sum.inr 2780, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

def sourceForm1461 : Integer.Sparse Master := [(Sum.inr 1627, 1), (Sum.inr 2397, 2), (Sum.inr 2409, 1), (Sum.inr 2683, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

def sourceForm1462 : Integer.Sparse Master := [(Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 3295, 2), (Sum.inr 3301, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

def sourceForm1463 : Integer.Sparse Master := [(Sum.inr 1113, 1), (Sum.inr 1119, 1), (Sum.inr 1121, 1), (Sum.inr 1138, 1), (Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

def sourceForm1464 : Integer.Sparse Master := [(Sum.inr 631, 1), (Sum.inr 1138, 1), (Sum.inr 1151, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1241, 1), (Sum.inr 4092, -1)]

def sourceForm1465 : Integer.Sparse Master := [(Sum.inr 1606, 1), (Sum.inr 1608, 1), (Sum.inr 1611, 1), (Sum.inr 1618, 1), (Sum.inr 1738, 1), (Sum.inr 3295, 1), (Sum.inr 4071, -1)]

def sourceForm1467 : Integer.Sparse Master := [(Sum.inr 1114, 1), (Sum.inr 1120, 2), (Sum.inr 1139, 1), (Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 4091, -1)]

def sourceForm1468 : Integer.Sparse Master := [(Sum.inr 632, 1), (Sum.inr 1139, 1), (Sum.inr 1152, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 2), (Sum.inr 4091, -1)]

def sourceForm1469 : Integer.Sparse Master := [(Sum.inr 1614, 1), (Sum.inr 1618, 2), (Sum.inr 1626, 1), (Sum.inr 1751, 1), (Sum.inr 3297, 1), (Sum.inr 4071, -1)]

def sourceForm1470 : Integer.Sparse Master := [(Sum.inr 1751, 1), (Sum.inr 3297, 2), (Sum.inr 3301, 2), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

def sourceForm1471 : Integer.Sparse Master := [(Sum.inr 1182, 1), (Sum.inr 2388, 1), (Sum.inr 2533, 1), (Sum.inr 2608, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 4088, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1472 : Integer.Sparse Master := [(Sum.inr 1196, 1), (Sum.inr 2452, 2), (Sum.inr 2609, 1), (Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 4090, -1)]

def sourceForm1473 : Integer.Sparse Master := [(Sum.inr 4185, 3), (Sum.inr 4190, 1), (Sum.inr 4192, 1), (Sum.inr 4553, 6), (Sum.inr 4557, 3), (Sum.inr 4559, 3), (Sum.inr 4619, 3), (Sum.inr 4621, 1), (Sum.inr 4623, 3), (Sum.inr 4625, 1), (Sum.inr 5176, 3), (Sum.inr 5308, 1), (Sum.inr 5310, 1)]

def sourceForm1474 : Integer.Sparse Master := [(Sum.inr 613, 3), (Sum.inr 618, 1), (Sum.inr 620, 1), (Sum.inr 1138, 6), (Sum.inr 1143, 3), (Sum.inr 1145, 3), (Sum.inr 1294, 3), (Sum.inr 1297, 1), (Sum.inr 1305, 3), (Sum.inr 1307, 1), (Sum.inr 2968, 3), (Sum.inr 3121, 1), (Sum.inr 3124, 1)]

def sourceForm1475 : Integer.Sparse Master := [(Sum.inr 4466, 6), (Sum.inr 4510, 2), (Sum.inr 4511, 2), (Sum.inr 4592, 6), (Sum.inr 4611, 6), (Sum.inr 4612, 6), (Sum.inr 4626, 1), (Sum.inr 4628, 1)]

def sourceForm1476 : Integer.Sparse Master := [(Sum.inr 1049, 3), (Sum.inr 1094, 1), (Sum.inr 1095, 1), (Sum.inr 1219, 6), (Sum.inr 1245, 3), (Sum.inr 1246, 3), (Sum.inr 1273, 3), (Sum.inr 1274, 3), (Sum.inr 1310, 1), (Sum.inr 1312, 1), (Sum.inr 1419, 3), (Sum.inr 1454, 1), (Sum.inr 1455, 1)]

def sourceForm1477 : Integer.Sparse Master := [(Sum.inr 1755, 1), (Sum.inr 3301, 3), (Sum.inr 3311, 1), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

def sourceForm1478 : Integer.Sparse Master := [(Sum.inr 4186, 3), (Sum.inr 4191, 2), (Sum.inr 4554, 6), (Sum.inr 4558, 6), (Sum.inr 4624, 6), (Sum.inr 4625, 2), (Sum.inr 5177, 3), (Sum.inr 5309, 2)]

def sourceForm1479 : Integer.Sparse Master := [(Sum.inr 614, 3), (Sum.inr 619, 2), (Sum.inr 1139, 6), (Sum.inr 1144, 6), (Sum.inr 1301, 6), (Sum.inr 1304, 2), (Sum.inr 2969, 3), (Sum.inr 3123, 2)]

def sourceForm1480 : Integer.Sparse Master := [(Sum.inr 4467, 6), (Sum.inr 4511, 4), (Sum.inr 4593, 6), (Sum.inr 4612, 12), (Sum.inr 4627, 2)]

def sourceForm1481 : Integer.Sparse Master := [(Sum.inr 1050, 3), (Sum.inr 1095, 2), (Sum.inr 1220, 6), (Sum.inr 1246, 6), (Sum.inr 1274, 6), (Sum.inr 1311, 2), (Sum.inr 1420, 3), (Sum.inr 1455, 2)]

def sourceForm1482 : Integer.Sparse Master := [(Sum.inr 1751, 3), (Sum.inr 1755, 2), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

def sourceForm1483 : Integer.Sparse Master := [(Sum.inr 4158, 2), (Sum.inr 4160, 1), (Sum.inr 4161, 1), (Sum.inr 4188, 1), (Sum.inr 4533, 2), (Sum.inr 4534, 2), (Sum.inr 4535, 2), (Sum.inr 4549, 2), (Sum.inr 4556, 2), (Sum.inr 4558, 1), (Sum.inr 4559, 1), (Sum.inr 4602, 2), (Sum.inr 4603, 2), (Sum.inr 4608, 1), (Sum.inr 4609, 1), (Sum.inr 4619, 1), (Sum.inr 4620, 1), (Sum.inr 5111, 1), (Sum.inr 5141, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1)]

def sourceForm1484 : Integer.Sparse Master := [(Sum.inr 586, 2), (Sum.inr 588, 1), (Sum.inr 589, 1), (Sum.inr 616, 1), (Sum.inr 1117, 2), (Sum.inr 1119, 2), (Sum.inr 1120, 2), (Sum.inr 1141, 2), (Sum.inr 1172, 2), (Sum.inr 1175, 1), (Sum.inr 1176, 1), (Sum.inr 1262, 2), (Sum.inr 1264, 1), (Sum.inr 1267, 2), (Sum.inr 1269, 1), (Sum.inr 1295, 1), (Sum.inr 1302, 1), (Sum.inr 2943, 2), (Sum.inr 3006, 1), (Sum.inr 3110, 1), (Sum.inr 3112, 1)]

def sourceForm1485 : Integer.Sparse Master := [(Sum.inr 1522, 2), (Sum.inr 1523, 1), (Sum.inr 1526, 1), (Sum.inr 1533, 1), (Sum.inr 3265, 2), (Sum.inr 3267, 2), (Sum.inr 3268, 2), (Sum.inr 3271, 2), (Sum.inr 3272, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3293, 2), (Sum.inr 3294, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3485, 1), (Sum.inr 3522, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1)]

def sourceForm1486 : Integer.Sparse Master := [(Sum.inr 627, 2), (Sum.inr 635, 1), (Sum.inr 636, 1), (Sum.inr 642, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

def sourceForm1487 : Integer.Sparse Master := [(Sum.inr 627, 1), (Sum.inr 1134, 1), (Sum.inr 1149, 1), (Sum.inr 1236, 1), (Sum.inr 1237, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

def sourceForm1488 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 1154, 1), (Sum.inr 1155, 1), (Sum.inr 1160, 1), (Sum.inr 1246, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

def sourceForm1489 : Integer.Sparse Master := [(Sum.inr 642, 1), (Sum.inr 1160, 2), (Sum.inr 1246, 1), (Sum.inr 1294, 1), (Sum.inr 1295, 1), (Sum.inr 4092, -1)]

def sourceForm1490 : Integer.Sparse Master := [(Sum.inr 4145, 2), (Sum.inr 4147, 1), (Sum.inr 4148, 1), (Sum.inr 4180, 1), (Sum.inr 4518, 2), (Sum.inr 4519, 1), (Sum.inr 4520, 1), (Sum.inr 4524, 2), (Sum.inr 4525, 2), (Sum.inr 4526, 2), (Sum.inr 4549, 2), (Sum.inr 4602, 2), (Sum.inr 4605, 1), (Sum.inr 4606, 2), (Sum.inr 4608, 1), (Sum.inr 4623, 1), (Sum.inr 4624, 1), (Sum.inr 5152, 2), (Sum.inr 5207, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1)]

def sourceForm1491 : Integer.Sparse Master := [(Sum.inr 573, 2), (Sum.inr 575, 1), (Sum.inr 576, 1), (Sum.inr 608, 1), (Sum.inr 1102, 2), (Sum.inr 1103, 1), (Sum.inr 1104, 1), (Sum.inr 1108, 2), (Sum.inr 1109, 2), (Sum.inr 1110, 2), (Sum.inr 1134, 2), (Sum.inr 1236, 2), (Sum.inr 1239, 1), (Sum.inr 1240, 2), (Sum.inr 1242, 1), (Sum.inr 1300, 1), (Sum.inr 1301, 1), (Sum.inr 2889, 1), (Sum.inr 2931, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1)]

def sourceForm1495 : Integer.Sparse Master := [(Sum.inr 1192, 1), (Sum.inr 2410, 1), (Sum.inr 2538, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

def sourceForm1496 : Integer.Sparse Master := [(Sum.inr 1193, 1), (Sum.inr 2411, 1), (Sum.inr 2539, 2), (Sum.inr 2686, 2), (Sum.inr 4089, -1)]

def sourceForm1497 : Integer.Sparse Master := [(Sum.inr 1099, 2), (Sum.inr 1104, 2), (Sum.inr 1193, 1), (Sum.inr 2411, 1), (Sum.inr 4089, -1)]

def sourceForm1499 : Integer.Sparse Master := [(Sum.inr 1204, 1), (Sum.inr 2467, 2), (Sum.inr 2540, 1), (Sum.inr 2704, 1), (Sum.inr 2706, 1), (Sum.inr 4080, -1)]

def sourceForm1500 : Integer.Sparse Master := [(Sum.inr 1205, 1), (Sum.inr 2468, 2), (Sum.inr 2541, 1), (Sum.inr 2705, 2), (Sum.inr 4088, -1)]

def sourceForm1501 : Integer.Sparse Master := [(Sum.inr 1106, 1), (Sum.inr 1110, 2), (Sum.inr 1124, 1), (Sum.inr 1205, 1), (Sum.inr 2468, 1), (Sum.inr 4088, -1)]

def sourceForm1503 : Integer.Sparse Master := [(Sum.inr 1062, 1), (Sum.inr 2038, 2), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 4082, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1504 : Integer.Sparse Master := [(Sum.inr 992, 1), (Sum.inr 1928, 1), (Sum.inr 1993, 1), (Sum.inr 2122, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 4082, -1)]

def sourceForm1505 : Integer.Sparse Master := [(Sum.inr 993, 1), (Sum.inr 1929, 1), (Sum.inr 1994, 1), (Sum.inr 2123, 1), (Sum.inr 2216, 2), (Sum.inr 4080, -1)]

def sourceForm1506 : Integer.Sparse Master := [(Sum.inr 1025, 1), (Sum.inr 2011, 1), (Sum.inr 2093, 2), (Sum.inr 2242, 1), (Sum.inr 2246, 1), (Sum.inr 4080, -1)]

def sourceForm1507 : Integer.Sparse Master := [(Sum.inr 973, 1), (Sum.inr 1900, 1), (Sum.inr 2072, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 4080, -1)]

def sourceForm1508 : Integer.Sparse Master := [(Sum.inr 974, 1), (Sum.inr 1901, 1), (Sum.inr 2073, 2), (Sum.inr 2191, 2), (Sum.inr 4079, -1)]

def sourceForm1509 : Integer.Sparse Master := [(Sum.inr 1048, 1), (Sum.inr 2027, 2), (Sum.inr 2114, 1), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 4081, -1)]

def sourceForm1510 : Integer.Sparse Master := [(Sum.inr 4154, 2), (Sum.inr 4160, 1), (Sum.inr 4162, 1), (Sum.inr 4185, 1), (Sum.inr 4328, 2), (Sum.inr 4334, 2), (Sum.inr 4336, 2), (Sum.inr 4354, 2), (Sum.inr 4368, 2), (Sum.inr 4373, 1), (Sum.inr 4375, 1), (Sum.inr 4457, 2), (Sum.inr 4459, 2), (Sum.inr 4460, 1), (Sum.inr 4464, 1), (Sum.inr 4498, 1), (Sum.inr 4503, 1), (Sum.inr 4810, 2), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 4896, 1)]

def sourceForm1511 : Integer.Sparse Master := [(Sum.inr 631, 2), (Sum.inr 634, 1), (Sum.inr 636, 1), (Sum.inr 648, 1), (Sum.inr 1321, 2), (Sum.inr 1323, 1), (Sum.inr 1325, 1), (Sum.inr 1330, 2), (Sum.inr 1332, 2), (Sum.inr 1334, 2), (Sum.inr 1343, 2), (Sum.inr 1406, 2), (Sum.inr 1408, 1), (Sum.inr 1414, 2), (Sum.inr 1416, 1), (Sum.inr 1442, 1), (Sum.inr 1448, 1), (Sum.inr 3187, 1), (Sum.inr 3206, 2), (Sum.inr 3225, 1), (Sum.inr 3230, 1)]

def sourceForm1512 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1523, 1), (Sum.inr 1525, 1), (Sum.inr 1529, 1), (Sum.inr 1667, 2), (Sum.inr 1679, 2), (Sum.inr 1681, 2), (Sum.inr 1685, 2), (Sum.inr 1707, 2), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 1), (Sum.inr 1727, 1), (Sum.inr 1735, 1), (Sum.inr 1739, 1), (Sum.inr 1743, 1), (Sum.inr 1745, 1), (Sum.inr 2215, 2), (Sum.inr 2264, 1), (Sum.inr 2276, 1), (Sum.inr 2278, 1)]

def sourceForm1513 : Integer.Sparse Master := [(Sum.inr 582, 2), (Sum.inr 588, 1), (Sum.inr 590, 1), (Sum.inr 613, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

def sourceForm1514 : Integer.Sparse Master := [(Sum.inr 613, 1), (Sum.inr 932, 2), (Sum.inr 1049, 1), (Sum.inr 1082, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def sourceForm1515 : Integer.Sparse Master := [(Sum.inr 946, 2), (Sum.inr 952, 1), (Sum.inr 954, 1), (Sum.inr 1049, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def sourceForm1516 : Integer.Sparse Master := [(Sum.inr 582, 1), (Sum.inr 906, 1), (Sum.inr 946, 1), (Sum.inr 1040, 1), (Sum.inr 1042, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

def sourceForm1517 : Integer.Sparse Master := [(Sum.inr 4106, 2), (Sum.inr 4109, 1), (Sum.inr 4111, 1), (Sum.inr 4132, 1), (Sum.inr 4291, 2), (Sum.inr 4294, 2), (Sum.inr 4296, 2), (Sum.inr 4313, 2), (Sum.inr 4354, 2), (Sum.inr 4359, 1), (Sum.inr 4361, 1), (Sum.inr 4452, 2), (Sum.inr 4454, 1), (Sum.inr 4461, 2), (Sum.inr 4463, 1), (Sum.inr 4491, 1), (Sum.inr 4503, 1), (Sum.inr 5080, 2), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1)]

def sourceForm1518 : Integer.Sparse Master := [(Sum.inr 543, 2), (Sum.inr 546, 1), (Sum.inr 548, 1), (Sum.inr 562, 1), (Sum.inr 869, 2), (Sum.inr 872, 2), (Sum.inr 874, 2), (Sum.inr 891, 2), (Sum.inr 932, 2), (Sum.inr 937, 1), (Sum.inr 939, 1), (Sum.inr 1035, 2), (Sum.inr 1037, 1), (Sum.inr 1044, 2), (Sum.inr 1046, 1), (Sum.inr 1075, 1), (Sum.inr 1087, 1), (Sum.inr 2488, 2), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 2768, 1)]

def sourceForm1522 : Integer.Sparse Master := [(Sum.inr 4155, 2), (Sum.inr 4161, 2), (Sum.inr 4186, 1), (Sum.inr 4329, 2), (Sum.inr 4335, 4), (Sum.inr 4355, 2), (Sum.inr 4369, 2), (Sum.inr 4374, 2), (Sum.inr 4458, 4), (Sum.inr 4463, 2), (Sum.inr 4502, 2), (Sum.inr 4811, 2), (Sum.inr 4875, 1), (Sum.inr 4895, 2)]

def sourceForm1523 : Integer.Sparse Master := [(Sum.inr 632, 2), (Sum.inr 635, 2), (Sum.inr 649, 1), (Sum.inr 1322, 2), (Sum.inr 1324, 2), (Sum.inr 1331, 2), (Sum.inr 1333, 4), (Sum.inr 1344, 2), (Sum.inr 1411, 4), (Sum.inr 1413, 2), (Sum.inr 1447, 2), (Sum.inr 3188, 1), (Sum.inr 3207, 2), (Sum.inr 3229, 2)]

def sourceForm1524 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1533, 2), (Sum.inr 1536, 1), (Sum.inr 1671, 2), (Sum.inr 1689, 4), (Sum.inr 1691, 2), (Sum.inr 1721, 2), (Sum.inr 1724, 4), (Sum.inr 1748, 2), (Sum.inr 1750, 2), (Sum.inr 1753, 2), (Sum.inr 2225, 2), (Sum.inr 2288, 1), (Sum.inr 2291, 2)]

def sourceForm1525 : Integer.Sparse Master := [(Sum.inr 583, 2), (Sum.inr 589, 2), (Sum.inr 614, 1), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

def sourceForm1526 : Integer.Sparse Master := [(Sum.inr 614, 1), (Sum.inr 933, 2), (Sum.inr 1050, 1), (Sum.inr 1086, 2), (Sum.inr 4083, -1)]

def sourceForm1527 : Integer.Sparse Master := [(Sum.inr 947, 2), (Sum.inr 953, 2), (Sum.inr 1050, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

def sourceForm1528 : Integer.Sparse Master := [(Sum.inr 583, 1), (Sum.inr 907, 1), (Sum.inr 947, 1), (Sum.inr 1041, 2), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

def sourceForm1529 : Integer.Sparse Master := [(Sum.inr 4107, 2), (Sum.inr 4110, 2), (Sum.inr 4133, 1), (Sum.inr 4292, 2), (Sum.inr 4295, 4), (Sum.inr 4314, 2), (Sum.inr 4355, 2), (Sum.inr 4360, 2), (Sum.inr 4458, 4), (Sum.inr 4460, 2), (Sum.inr 4499, 2), (Sum.inr 5081, 2), (Sum.inr 5177, 1), (Sum.inr 5293, 2)]

def sourceForm1531 : Integer.Sparse Master := [(Sum.inr 4256, 2), (Sum.inr 4273, 2), (Sum.inr 4279, 1), (Sum.inr 4393, 2), (Sum.inr 4404, 4), (Sum.inr 4412, 2), (Sum.inr 4444, 4), (Sum.inr 4466, 2), (Sum.inr 4467, 2), (Sum.inr 4480, 2), (Sum.inr 4511, 2), (Sum.inr 4593, 2), (Sum.inr 4612, 2), (Sum.inr 4628, 1)]

def sourceForm1532 : Integer.Sparse Master := [(Sum.inr 790, 2), (Sum.inr 816, 2), (Sum.inr 831, 1), (Sum.inr 974, 2), (Sum.inr 985, 4), (Sum.inr 993, 2), (Sum.inr 1026, 4), (Sum.inr 1049, 2), (Sum.inr 1050, 2), (Sum.inr 1063, 2), (Sum.inr 1095, 2), (Sum.inr 1220, 2), (Sum.inr 1274, 2), (Sum.inr 1312, 1)]

def sourceForm1533 : Integer.Sparse Master := [(Sum.inr 1220, 2), (Sum.inr 1246, 2), (Sum.inr 1312, 1), (Sum.inr 1363, 2), (Sum.inr 1375, 2), (Sum.inr 1381, 2), (Sum.inr 1391, 4), (Sum.inr 1401, 4), (Sum.inr 1419, 2), (Sum.inr 1420, 2), (Sum.inr 1455, 2), (Sum.inr 1473, 1), (Sum.inr 1479, 2), (Sum.inr 1486, 2)]

def sourceForm1534 : Integer.Sparse Master := [(Sum.inr 984, 1), (Sum.inr 1917, 1), (Sum.inr 1989, 1), (Sum.inr 2081, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 4081, -1)]

def sourceForm1535 : Integer.Sparse Master := [(Sum.inr 985, 1), (Sum.inr 1918, 1), (Sum.inr 1990, 1), (Sum.inr 2082, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1537 : Integer.Sparse Master := [(Sum.inr 866, 1), (Sum.inr 873, 1), (Sum.inr 874, 1), (Sum.inr 889, 1), (Sum.inr 985, 1), (Sum.inr 1918, 1), (Sum.inr 4080, -1)]

def sourceForm1538 : Integer.Sparse Master := [(Sum.inr 710, 1), (Sum.inr 715, 1), (Sum.inr 717, 1), (Sum.inr 724, 1), (Sum.inr 852, 1), (Sum.inr 1618, 1), (Sum.inr 4071, -1)]

def sourceForm1540 : Integer.Sparse Master := [(Sum.inr 4179, 3), (Sum.inr 4190, 1), (Sum.inr 4193, 1), (Sum.inr 4348, 6), (Sum.inr 4359, 3), (Sum.inr 4362, 3), (Sum.inr 4496, 3), (Sum.inr 4500, 3), (Sum.inr 4501, 1), (Sum.inr 4508, 1), (Sum.inr 4845, 3), (Sum.inr 4897, 1), (Sum.inr 4899, 1)]

def sourceForm1541 : Integer.Sparse Master := [(Sum.inr 653, 3), (Sum.inr 654, 1), (Sum.inr 655, 1), (Sum.inr 1347, 6), (Sum.inr 1348, 3), (Sum.inr 1349, 3), (Sum.inr 1436, 3), (Sum.inr 1438, 1), (Sum.inr 1451, 3), (Sum.inr 1452, 1), (Sum.inr 2778, 1), (Sum.inr 3095, 3), (Sum.inr 3114, 1)]

def sourceForm1542 : Integer.Sparse Master := [(Sum.inr 1513, 3), (Sum.inr 1527, 1), (Sum.inr 1531, 1), (Sum.inr 1669, 6), (Sum.inr 1683, 3), (Sum.inr 1687, 3), (Sum.inr 1710, 3), (Sum.inr 1716, 3), (Sum.inr 1730, 1), (Sum.inr 1747, 1), (Sum.inr 2218, 3), (Sum.inr 2268, 1), (Sum.inr 2281, 1)]

def sourceForm1543 : Integer.Sparse Master := [(Sum.inr 607, 3), (Sum.inr 618, 1), (Sum.inr 621, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

def sourceForm1550 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4180, 3), (Sum.inr 4191, 1), (Sum.inr 4192, 1), (Sum.inr 4349, 6), (Sum.inr 4360, 3), (Sum.inr 4361, 3), (Sum.inr 4498, 3), (Sum.inr 4499, 3), (Sum.inr 4505, 1), (Sum.inr 4507, 1), (Sum.inr 4846, 3), (Sum.inr 4901, 1)]

def sourceForm1551 : Integer.Sparse Master := [(Sum.inr 1519, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 1675, 6), (Sum.inr 1693, 3), (Sum.inr 1694, 3), (Sum.inr 1727, 3), (Sum.inr 1728, 3), (Sum.inr 1754, 1), (Sum.inr 1756, 1), (Sum.inr 2229, 3), (Sum.inr 2293, 1), (Sum.inr 4084, 1)]

def sourceForm1552 : Integer.Sparse Master := [(Sum.inr 608, 3), (Sum.inr 619, 1), (Sum.inr 620, 1), (Sum.inr 1095, 1), (Sum.inr 4084, -1)]

def sourceForm1553 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4273, 3), (Sum.inr 4284, 1), (Sum.inr 4404, 6), (Sum.inr 4431, 3), (Sum.inr 4432, 3), (Sum.inr 4466, 3), (Sum.inr 4467, 3), (Sum.inr 4510, 1), (Sum.inr 4511, 1), (Sum.inr 4612, 3), (Sum.inr 4627, 1), (Sum.inr 4628, 1)]

def sourceForm1554 : Integer.Sparse Master := [(Sum.inr 1012, 1), (Sum.inr 1953, 1), (Sum.inr 2006, 2), (Sum.inr 2228, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def sourceForm1556 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4141, 2), (Sum.inr 4148, 2), (Sum.inr 4167, 1), (Sum.inr 4305, 2), (Sum.inr 4318, 2), (Sum.inr 4321, 2), (Sum.inr 4325, 4), (Sum.inr 4339, 2), (Sum.inr 4419, 4), (Sum.inr 4428, 2), (Sum.inr 4491, 2), (Sum.inr 4790, 2), (Sum.inr 4846, 2)]

def sourceForm1558 : Integer.Sparse Master := [(Sum.inr 569, 2), (Sum.inr 576, 2), (Sum.inr 595, 1), (Sum.inr 1013, 1), (Sum.inr 4082, -1)]

def sourceForm1561 : Integer.Sparse Master := [(Sum.inr 562, 1), (Sum.inr 724, 2), (Sum.inr 830, 1), (Sum.inr 852, 1), (Sum.inr 858, 1), (Sum.inr 4071, -1)]

def sourceForm1562 : Integer.Sparse Master := [(Sum.inr 831, 1), (Sum.inr 1612, 2), (Sum.inr 1661, 1), (Sum.inr 1739, 2), (Sum.inr 4069, -1)]

def sourceForm1564 : Integer.Sparse Master := [(Sum.inr 789, 1), (Sum.inr 1594, 1), (Sum.inr 1640, 2), (Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 4069, -1)]

def sourceForm1565 : Integer.Sparse Master := [(Sum.inr 543, 1), (Sum.inr 703, 1), (Sum.inr 738, 1), (Sum.inr 789, 1), (Sum.inr 806, 1), (Sum.inr 811, 1), (Sum.inr 4069, -1)]

def sourceForm1566 : Integer.Sparse Master := [(Sum.inr 552, 1), (Sum.inr 710, 1), (Sum.inr 823, 1), (Sum.inr 848, 1), (Sum.inr 852, 2), (Sum.inr 4071, -1)]

def sourceForm1567 : Integer.Sparse Master := [(Sum.inr 790, 1), (Sum.inr 1595, 1), (Sum.inr 1641, 2), (Sum.inr 1708, 2), (Sum.inr 4068, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1568 : Integer.Sparse Master := [(Sum.inr 544, 1), (Sum.inr 704, 1), (Sum.inr 739, 1), (Sum.inr 790, 1), (Sum.inr 810, 2), (Sum.inr 4068, -1)]

def sourceForm1569 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4102, 2), (Sum.inr 4110, 1), (Sum.inr 4111, 1), (Sum.inr 4130, 1), (Sum.inr 4197, 2), (Sum.inr 4204, 2), (Sum.inr 4205, 2), (Sum.inr 4221, 2), (Sum.inr 4234, 2), (Sum.inr 4242, 1), (Sum.inr 4243, 1), (Sum.inr 4264, 2), (Sum.inr 4265, 2), (Sum.inr 4269, 1), (Sum.inr 4270, 1), (Sum.inr 4283, 1), (Sum.inr 4419, 2), (Sum.inr 4491, 1), (Sum.inr 4498, 1), (Sum.inr 4499, 1)]

def sourceForm1570 : Integer.Sparse Master := [(Sum.inr 664, 2), (Sum.inr 684, 1), (Sum.inr 685, 1), (Sum.inr 689, 1), (Sum.inr 749, 2), (Sum.inr 763, 2), (Sum.inr 764, 2), (Sum.inr 768, 2), (Sum.inr 800, 2), (Sum.inr 806, 2), (Sum.inr 807, 2), (Sum.inr 843, 1), (Sum.inr 844, 1), (Sum.inr 851, 1), (Sum.inr 853, 1), (Sum.inr 856, 1), (Sum.inr 1000, 2), (Sum.inr 1075, 1), (Sum.inr 1082, 1), (Sum.inr 1083, 1), (Sum.inr 4069, 1)]

def sourceForm1571 : Integer.Sparse Master := [(Sum.inr 816, 1), (Sum.inr 1605, 2), (Sum.inr 1653, 1), (Sum.inr 1727, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def sourceForm1572 : Integer.Sparse Master := [(Sum.inr 539, 2), (Sum.inr 547, 1), (Sum.inr 548, 1), (Sum.inr 561, 1), (Sum.inr 816, 1), (Sum.inr 4069, -1)]

def sourceForm1573 : Integer.Sparse Master := [(Sum.inr 734, 2), (Sum.inr 742, 1), (Sum.inr 743, 1), (Sum.inr 816, 1), (Sum.inr 1653, 1), (Sum.inr 4069, -1)]

def sourceForm1574 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4115, 2), (Sum.inr 4121, 1), (Sum.inr 4123, 1), (Sum.inr 4132, 1), (Sum.inr 4207, 2), (Sum.inr 4212, 2), (Sum.inr 4214, 2), (Sum.inr 4223, 2), (Sum.inr 4255, 2), (Sum.inr 4256, 2), (Sum.inr 4272, 1), (Sum.inr 4273, 3), (Sum.inr 4278, 1), (Sum.inr 4279, 1), (Sum.inr 4284, 1), (Sum.inr 4404, 2), (Sum.inr 4466, 1), (Sum.inr 4467, 1), (Sum.inr 4511, 1)]

def sourceForm1575 : Integer.Sparse Master := [(Sum.inr 4059, 3), (Sum.inr 4061, 2), (Sum.inr 4065, 6), (Sum.inr 4067, 6), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4082, 3), (Sum.inr 4084, 2)]

def sourceForm1576 : Integer.Sparse Master := [(Sum.inr 1716, 1), (Sum.inr 2521, 1), (Sum.inr 3022, 2), (Sum.inr 3049, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def sourceForm1577 : Integer.Sparse Master := [(Sum.inr 1714, 2), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 1739, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def sourceForm1578 : Integer.Sparse Master := [(Sum.inr 604, 1), (Sum.inr 923, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 1079, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def sourceForm1579 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 1337, 1), (Sum.inr 1338, 1), (Sum.inr 1347, 1), (Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

def sourceForm1580 : Integer.Sparse Master := [(Sum.inr 1714, 1), (Sum.inr 2502, 1), (Sum.inr 3285, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def sourceForm1581 : Integer.Sparse Master := [(Sum.inr 824, 1), (Sum.inr 1607, 1), (Sum.inr 1656, 1), (Sum.inr 1714, 1), (Sum.inr 1737, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

def sourceForm1582 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1714, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 1737, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def sourceForm1583 : Integer.Sparse Master := [(Sum.inr 807, 1), (Sum.inr 1598, 1), (Sum.inr 1646, 1), (Sum.inr 1714, 1), (Sum.inr 1724, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def sourceForm1584 : Integer.Sparse Master := [(Sum.inr 601, 1), (Sum.inr 920, 1), (Sum.inr 1057, 1), (Sum.inr 1079, 1), (Sum.inr 1083, 2), (Sum.inr 4084, -1)]

def sourceForm1585 : Integer.Sparse Master := [(Sum.inr 1316, 1), (Sum.inr 1320, 1), (Sum.inr 1322, 2), (Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

def sourceForm1586 : Integer.Sparse Master := [(Sum.inr 1709, 1), (Sum.inr 3241, 1), (Sum.inr 3245, 1), (Sum.inr 3246, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def sourceForm1587 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 1724, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def sourceForm1588 : Integer.Sparse Master := [(Sum.inr 811, 1), (Sum.inr 1601, 1), (Sum.inr 1649, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 4069, -1)]

def sourceForm1590 : Integer.Sparse Master := [(Sum.inr 1314, 1), (Sum.inr 1317, 1), (Sum.inr 1318, 1), (Sum.inr 1321, 1), (Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

def sourceForm1591 : Integer.Sparse Master := [(Sum.inr 1715, 1), (Sum.inr 2466, 1), (Sum.inr 3238, 1), (Sum.inr 3240, 1), (Sum.inr 3245, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def sourceForm1592 : Integer.Sparse Master := [(Sum.inr 827, 1), (Sum.inr 1609, 1), (Sum.inr 1658, 1), (Sum.inr 1715, 2), (Sum.inr 1737, 1), (Sum.inr 4069, -1)]

def sourceForm1594 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 942, 1), (Sum.inr 1020, 1), (Sum.inr 1039, 1), (Sum.inr 1041, 2), (Sum.inr 4083, -1)]

def sourceForm1595 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 3281, 1), (Sum.inr 3282, 2), (Sum.inr 3299, 2), (Sum.inr 4069, -1)]

def sourceForm1596 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 784, 2), (Sum.inr 803, 2), (Sum.inr 1705, 1), (Sum.inr 4069, -1)]

def sourceForm1597 : Integer.Sparse Master := [(Sum.inr 803, 1), (Sum.inr 1642, 1), (Sum.inr 1705, 1), (Sum.inr 1713, 1), (Sum.inr 1724, 2), (Sum.inr 4069, -1)]

def sourceForm1598 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 1635, 2), (Sum.inr 1705, 1), (Sum.inr 1707, 2), (Sum.inr 4069, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm160 : Integer.Sparse Master := [(Sum.inr 2193, 4), (Sum.inr 2208, 1), (Sum.inr 2218, 2), (Sum.inr 2268, 2), (Sum.inr 2664, 4), (Sum.inr 2680, 1), (Sum.inr 2691, 2), (Sum.inr 2712, 4), (Sum.inr 2726, 4), (Sum.inr 2734, 2), (Sum.inr 2770, 2), (Sum.inr 2790, 1), (Sum.inr 3090, 1)]

def sourceForm161 : Integer.Sparse Master := [(Sum.inr 2712, 4), (Sum.inr 2726, 1), (Sum.inr 2734, 2), (Sum.inr 2770, 2), (Sum.inr 3031, 4), (Sum.inr 3046, 1), (Sum.inr 3061, 2), (Sum.inr 3082, 4), (Sum.inr 3090, 4), (Sum.inr 3095, 2), (Sum.inr 3114, 2), (Sum.inr 3126, 1), (Sum.inr 3215, 1)]

def sourceForm162 : Integer.Sparse Master := [(Sum.inr 2052, 2), (Sum.inr 2056, 1), (Sum.inr 2065, 1), (Sum.inr 2292, 1), (Sum.inr 3545, 1), (Sum.inr 4085, -1)]

def sourceForm163 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 4625, 8), (Sum.inr 4629, 1), (Sum.inr 5171, 12), (Sum.inr 5308, 8)]

def sourceForm164 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4897, 8), (Sum.inr 5261, 12), (Sum.inr 5296, 8), (Sum.inr 5312, 1)]

def sourceForm165 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4460, 3), (Sum.inr 4468, 1), (Sum.inr 4505, 1), (Sum.inr 4605, 3), (Sum.inr 4621, 1), (Sum.inr 4804, 6), (Sum.inr 4841, 3), (Sum.inr 4868, 3), (Sum.inr 4894, 3), (Sum.inr 5272, 3), (Sum.inr 5305, 1), (Sum.inr 5308, 1)]

def sourceForm166 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 1752, 1), (Sum.inr 1754, 1), (Sum.inr 2203, 6), (Sum.inr 2226, 3), (Sum.inr 2228, 3), (Sum.inr 2261, 3), (Sum.inr 2264, 3), (Sum.inr 2289, 1), (Sum.inr 2740, 3), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 4084, 1)]

def sourceForm167 : Integer.Sparse Master := [(Sum.inr 1051, 1), (Sum.inr 1239, 3), (Sum.inr 1297, 1), (Sum.inr 2268, 1), (Sum.inr 4084, -1)]

def sourceForm168 : Integer.Sparse Master := [(Sum.inr 1239, 1), (Sum.inr 2022, 2), (Sum.inr 2060, 1), (Sum.inr 2268, 1), (Sum.inr 2740, 1), (Sum.inr 4084, -1)]

def sourceForm169 : Integer.Sparse Master := [(Sum.inr 1043, 1), (Sum.inr 2022, 2), (Sum.inr 2109, 1), (Sum.inr 2264, 1), (Sum.inr 2268, 1), (Sum.inr 4084, -1)]

def sourceForm170 : Integer.Sparse Master := [(Sum.inr 1297, 1), (Sum.inr 2109, 3), (Sum.inr 2268, 1), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

def sourceForm171 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4496, 3), (Sum.inr 4501, 1), (Sum.inr 4510, 1), (Sum.inr 4832, 6), (Sum.inr 4837, 3), (Sum.inr 4845, 3), (Sum.inr 4890, 3), (Sum.inr 4897, 3), (Sum.inr 4899, 1), (Sum.inr 5261, 3), (Sum.inr 5296, 1), (Sum.inr 5312, 1)]

def sourceForm172 : Integer.Sparse Master := [(Sum.inr 4070, 8), (Sum.inr 4072, 1), (Sum.inr 4081, 12), (Sum.inr 4084, 8), (Sum.inr 4094, 1)]

def sourceForm174 : Integer.Sparse Master := [(Sum.inr 1354, 1), (Sum.inr 1355, 1), (Sum.inr 1356, 1), (Sum.inr 1367, 1), (Sum.inr 1406, 1), (Sum.inr 1903, 1), (Sum.inr 1916, 1), (Sum.inr 1927, 1), (Sum.inr 2255, 1), (Sum.inr 3016, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3054, 1), (Sum.inr 3077, 1), (Sum.inr 3146, 1), (Sum.inr 3147, 1), (Sum.inr 3156, 1), (Sum.inr 3165, 1), (Sum.inr 3166, 1), (Sum.inr 3180, 1), (Sum.inr 3193, 1), (Sum.inr 3196, 1), (Sum.inr 3202, 1), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 1), (Sum.inr 3224, 1), (Sum.inr 3225, 1), (Sum.inr 3227, 1)]

def sourceForm176 : Integer.Sparse Master := [(Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 3528, 1), (Sum.inr 3577, 1), (Sum.inr 3625, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

def sourceForm177 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 1029, 1), (Sum.inr 1030, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 2253, 1), (Sum.inr 4084, -1)]

def sourceForm178 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 2095, 1), (Sum.inr 2124, 1), (Sum.inr 2252, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

def sourceForm179 : Integer.Sparse Master := [(Sum.inr 2013, 1), (Sum.inr 2014, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2253, 1), (Sum.inr 3528, 1), (Sum.inr 4084, -1)]

def sourceForm180 : Integer.Sparse Master := [(Sum.inr 1058, 1), (Sum.inr 2034, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2277, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

def sourceForm181 : Integer.Sparse Master := [(Sum.inr 2095, 1), (Sum.inr 2096, 1), (Sum.inr 2097, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 3577, 1), (Sum.inr 4084, -1)]

def sourceForm182 : Integer.Sparse Master := [(Sum.inr 1042, 1), (Sum.inr 2021, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 2262, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

def sourceForm183 : Integer.Sparse Master := [(Sum.inr 2124, 1), (Sum.inr 2125, 1), (Sum.inr 2126, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 4084, -1)]

def sourceForm184 : Integer.Sparse Master := [(Sum.inr 1030, 1), (Sum.inr 2014, 1), (Sum.inr 2097, 1), (Sum.inr 2126, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

def sourceForm186 : Integer.Sparse Master := [(Sum.inr 793, 1), (Sum.inr 794, 1), (Sum.inr 796, 1), (Sum.inr 808, 1), (Sum.inr 825, 1), (Sum.inr 1902, 1), (Sum.inr 1904, 1), (Sum.inr 1910, 1), (Sum.inr 1923, 1), (Sum.inr 2034, 1), (Sum.inr 2035, 1), (Sum.inr 2039, 1), (Sum.inr 2055, 1), (Sum.inr 2089, 1), (Sum.inr 2090, 1), (Sum.inr 2094, 1), (Sum.inr 2108, 1), (Sum.inr 2196, 1), (Sum.inr 2197, 1), (Sum.inr 2207, 1), (Sum.inr 2217, 1), (Sum.inr 2250, 1), (Sum.inr 2251, 1), (Sum.inr 2259, 1), (Sum.inr 2274, 1), (Sum.inr 3803, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3856, 1), (Sum.inr 3883, 1)]

def sourceForm187 : Integer.Sparse Master := [(Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 3809, 2), (Sum.inr 3814, 2), (Sum.inr 4092, -1)]

def sourceForm188 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 1465, 2), (Sum.inr 1466, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def sourceForm189 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 3170, 2), (Sum.inr 3196, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def sourceForm190 : Integer.Sparse Master := [(Sum.inr 2474, 2), (Sum.inr 3217, 2), (Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

def sourceForm191 : Integer.Sparse Master := [(Sum.inr 1466, 1), (Sum.inr 3174, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3217, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1600 : Integer.Sparse Master := [(Sum.inr 580, 1), (Sum.inr 944, 1), (Sum.inr 1021, 2), (Sum.inr 1039, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

def sourceForm1601 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1330, 1), (Sum.inr 1335, 1), (Sum.inr 1383, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

def sourceForm1602 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 2457, 1), (Sum.inr 3278, 1), (Sum.inr 3281, 1), (Sum.inr 3293, 2), (Sum.inr 4069, -1)]

def sourceForm1604 : Integer.Sparse Master := [(Sum.inr 822, 1), (Sum.inr 1654, 1), (Sum.inr 1713, 2), (Sum.inr 1737, 2), (Sum.inr 4069, -1)]

def sourceForm1606 : Integer.Sparse Master := [(Sum.inr 1125, 1), (Sum.inr 1128, 1), (Sum.inr 1133, 2), (Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 4084, -1)]

def sourceForm1607 : Integer.Sparse Master := [(Sum.inr 651, 1), (Sum.inr 1169, 1), (Sum.inr 1270, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def sourceForm1608 : Integer.Sparse Master := [(Sum.inr 1654, 1), (Sum.inr 1656, 2), (Sum.inr 1658, 1), (Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

def sourceForm1609 : Integer.Sparse Master := [(Sum.inr 1710, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def sourceForm1610 : Integer.Sparse Master := [(Sum.inr 1602, 1), (Sum.inr 2457, 1), (Sum.inr 2466, 1), (Sum.inr 2502, 1), (Sum.inr 2702, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def sourceForm1611 : Integer.Sparse Master := [(Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 3288, 1), (Sum.inr 3293, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def sourceForm1612 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 1132, 1), (Sum.inr 1134, 1), (Sum.inr 1141, 1), (Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 4092, -1)]

def sourceForm1613 : Integer.Sparse Master := [(Sum.inr 640, 1), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 2), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def sourceForm1614 : Integer.Sparse Master := [(Sum.inr 1642, 1), (Sum.inr 1645, 1), (Sum.inr 1646, 1), (Sum.inr 1649, 1), (Sum.inr 1724, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

def sourceForm1615 : Integer.Sparse Master := [(Sum.inr 1598, 1), (Sum.inr 1603, 1), (Sum.inr 1605, 1), (Sum.inr 1623, 1), (Sum.inr 1728, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

def sourceForm1616 : Integer.Sparse Master := [(Sum.inr 1728, 1), (Sum.inr 3294, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

def sourceForm1617 : Integer.Sparse Master := [(Sum.inr 1623, 1), (Sum.inr 3246, 1), (Sum.inr 3282, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def sourceForm1618 : Integer.Sparse Master := [(Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3299, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

def sourceForm1619 : Integer.Sparse Master := [(Sum.inr 1605, 1), (Sum.inr 3240, 1), (Sum.inr 3278, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

def sourceForm1620 : Integer.Sparse Master := [(Sum.inr 1645, 1), (Sum.inr 3022, 1), (Sum.inr 3285, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def sourceForm1621 : Integer.Sparse Master := [(Sum.inr 1257, 1), (Sum.inr 2565, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 2748, 1), (Sum.inr 2760, 1), (Sum.inr 4088, -1)]

def sourceForm1622 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 1137, 1), (Sum.inr 1138, 1), (Sum.inr 1141, 1), (Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def sourceForm1623 : Integer.Sparse Master := [(Sum.inr 638, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 1291, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

def sourceForm1624 : Integer.Sparse Master := [(Sum.inr 1635, 1), (Sum.inr 1637, 1), (Sum.inr 1640, 1), (Sum.inr 1645, 1), (Sum.inr 1707, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

def sourceForm1625 : Integer.Sparse Master := [(Sum.inr 1607, 1), (Sum.inr 1610, 1), (Sum.inr 1612, 1), (Sum.inr 1623, 1), (Sum.inr 1739, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

def sourceForm1626 : Integer.Sparse Master := [(Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 3296, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def sourceForm1627 : Integer.Sparse Master := [(Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 3296, 2), (Sum.inr 3299, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def sourceForm1628 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1113, 2), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 4092, -1)]

def sourceForm1629 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 1233, 1), (Sum.inr 1236, 2), (Sum.inr 4092, -1)]

def sourceForm1630 : Integer.Sparse Master := [(Sum.inr 629, 1), (Sum.inr 1135, 1), (Sum.inr 1216, 3), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

def sourceForm1631 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 1117, 2), (Sum.inr 1135, 1), (Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1632 : Integer.Sparse Master := [(Sum.inr 1607, 2), (Sum.inr 1609, 1), (Sum.inr 1616, 1), (Sum.inr 1737, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

def sourceForm1633 : Integer.Sparse Master := [(Sum.inr 1592, 1), (Sum.inr 1594, 1), (Sum.inr 1597, 2), (Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

def sourceForm1634 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 3238, 1), (Sum.inr 3285, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def sourceForm1635 : Integer.Sparse Master := [(Sum.inr 1616, 1), (Sum.inr 3241, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def sourceForm1636 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1114, 1), (Sum.inr 1117, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 4091, -1)]

def sourceForm1637 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 2), (Sum.inr 1235, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

def sourceForm1638 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 1598, 1), (Sum.inr 1601, 1), (Sum.inr 1616, 1), (Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 4069, -1)]

def sourceForm1639 : Integer.Sparse Master := [(Sum.inr 1210, 1), (Sum.inr 2477, 1), (Sum.inr 2613, 1), (Sum.inr 2694, 1), (Sum.inr 2708, 1), (Sum.inr 2718, 1), (Sum.inr 4090, -1)]

def sourceForm1640 : Integer.Sparse Master := [(Sum.inr 1180, 1), (Sum.inr 2383, 1), (Sum.inr 2607, 1), (Sum.inr 2662, 2), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

def sourceForm1641 : Integer.Sparse Master := [(Sum.inr 1180, 3), (Sum.inr 1187, 1), (Sum.inr 1256, 1), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

def sourceForm1642 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 2382, 1), (Sum.inr 2606, 1), (Sum.inr 2661, 1), (Sum.inr 2669, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

def sourceForm1643 : Integer.Sparse Master := [(Sum.inr 1656, 2), (Sum.inr 1659, 1), (Sum.inr 1661, 1), (Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

def sourceForm1644 : Integer.Sparse Master := [(Sum.inr 1650, 1), (Sum.inr 2502, 2), (Sum.inr 2521, 1), (Sum.inr 2737, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def sourceForm1645 : Integer.Sparse Master := [(Sum.inr 1646, 2), (Sum.inr 1651, 1), (Sum.inr 1653, 1), (Sum.inr 1728, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

def sourceForm1646 : Integer.Sparse Master := [(Sum.inr 1653, 1), (Sum.inr 3049, 1), (Sum.inr 3287, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

def sourceForm1647 : Integer.Sparse Master := [(Sum.inr 1288, 1), (Sum.inr 2585, 2), (Sum.inr 2686, 1), (Sum.inr 2771, 1), (Sum.inr 2779, 1), (Sum.inr 4089, -1)]

def sourceForm1648 : Integer.Sparse Master := [(Sum.inr 4182, 2), (Sum.inr 4183, 1), (Sum.inr 4185, 2), (Sum.inr 4550, 2), (Sum.inr 4551, 2), (Sum.inr 4553, 4), (Sum.inr 4618, 2), (Sum.inr 4619, 2), (Sum.inr 4623, 4), (Sum.inr 4625, 2), (Sum.inr 4627, 2), (Sum.inr 5168, 2), (Sum.inr 5306, 1), (Sum.inr 5308, 2)]

def sourceForm1649 : Integer.Sparse Master := [(Sum.inr 610, 2), (Sum.inr 611, 1), (Sum.inr 613, 2), (Sum.inr 1135, 2), (Sum.inr 1136, 2), (Sum.inr 1138, 4), (Sum.inr 1293, 2), (Sum.inr 1294, 2), (Sum.inr 1305, 4), (Sum.inr 1307, 2), (Sum.inr 1311, 2), (Sum.inr 2963, 2), (Sum.inr 3120, 1), (Sum.inr 3124, 2)]

def sourceForm1650 : Integer.Sparse Master := [(Sum.inr 4172, 2), (Sum.inr 4174, 1), (Sum.inr 4180, 2), (Sum.inr 4541, 2), (Sum.inr 4543, 2), (Sum.inr 4549, 4), (Sum.inr 4602, 4), (Sum.inr 4605, 2), (Sum.inr 4612, 2), (Sum.inr 4622, 2), (Sum.inr 4624, 2), (Sum.inr 5172, 2), (Sum.inr 5294, 2), (Sum.inr 5307, 1)]

def sourceForm1651 : Integer.Sparse Master := [(Sum.inr 600, 2), (Sum.inr 602, 1), (Sum.inr 608, 2), (Sum.inr 1126, 2), (Sum.inr 1128, 2), (Sum.inr 1134, 4), (Sum.inr 1236, 4), (Sum.inr 1239, 2), (Sum.inr 1246, 2), (Sum.inr 1299, 2), (Sum.inr 1301, 2), (Sum.inr 2959, 2), (Sum.inr 3101, 2), (Sum.inr 3122, 1)]

def sourceForm1652 : Integer.Sparse Master := [(Sum.inr 4457, 2), (Sum.inr 4461, 2), (Sum.inr 4496, 1), (Sum.inr 4498, 2), (Sum.inr 4502, 1), (Sum.inr 4503, 2), (Sum.inr 4589, 2), (Sum.inr 4600, 2), (Sum.inr 4602, 4), (Sum.inr 4606, 2), (Sum.inr 4607, 4), (Sum.inr 4617, 2), (Sum.inr 4619, 2), (Sum.inr 4624, 2)]

def sourceForm1653 : Integer.Sparse Master := [(Sum.inr 1044, 2), (Sum.inr 1086, 1), (Sum.inr 1087, 2), (Sum.inr 1216, 2), (Sum.inr 1240, 2), (Sum.inr 1241, 4), (Sum.inr 1267, 4), (Sum.inr 1270, 2), (Sum.inr 1301, 2), (Sum.inr 1302, 2), (Sum.inr 1306, 2), (Sum.inr 1414, 2), (Sum.inr 1448, 2), (Sum.inr 1451, 1)]

def sourceForm1654 : Integer.Sparse Master := [(Sum.inr 1737, 2), (Sum.inr 1739, 2), (Sum.inr 1753, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def sourceForm1655 : Integer.Sparse Master := [(Sum.inr 1727, 1), (Sum.inr 3293, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

def sourceForm1656 : Integer.Sparse Master := [(Sum.inr 4175, 2), (Sum.inr 4177, 1), (Sum.inr 4180, 1), (Sum.inr 4186, 1), (Sum.inr 4544, 2), (Sum.inr 4546, 2), (Sum.inr 4549, 2), (Sum.inr 4554, 2), (Sum.inr 4606, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4622, 2), (Sum.inr 4623, 1), (Sum.inr 4624, 3), (Sum.inr 4625, 1), (Sum.inr 4628, 1), (Sum.inr 5169, 2), (Sum.inr 5293, 1), (Sum.inr 5307, 1), (Sum.inr 5309, 1)]

def sourceForm1657 : Integer.Sparse Master := [(Sum.inr 603, 2), (Sum.inr 605, 1), (Sum.inr 608, 1), (Sum.inr 614, 1), (Sum.inr 1129, 2), (Sum.inr 1131, 2), (Sum.inr 1134, 2), (Sum.inr 1139, 2), (Sum.inr 1240, 2), (Sum.inr 1242, 1), (Sum.inr 1246, 1), (Sum.inr 1299, 2), (Sum.inr 1300, 1), (Sum.inr 1301, 3), (Sum.inr 1304, 1), (Sum.inr 1312, 1), (Sum.inr 2960, 2), (Sum.inr 3102, 1), (Sum.inr 3122, 1), (Sum.inr 3123, 1)]

def sourceForm1658 : Integer.Sparse Master := [(Sum.inr 4458, 4), (Sum.inr 4498, 2), (Sum.inr 4499, 2), (Sum.inr 4502, 2), (Sum.inr 4590, 2), (Sum.inr 4602, 4), (Sum.inr 4603, 4), (Sum.inr 4606, 4), (Sum.inr 4619, 2), (Sum.inr 4620, 1), (Sum.inr 4623, 2), (Sum.inr 4624, 1)]

def sourceForm1659 : Integer.Sparse Master := [(Sum.inr 4165, 2), (Sum.inr 4166, 1), (Sum.inr 4167, 1), (Sum.inr 4185, 1), (Sum.inr 4537, 2), (Sum.inr 4538, 2), (Sum.inr 4539, 2), (Sum.inr 4553, 2), (Sum.inr 4570, 2), (Sum.inr 4572, 1), (Sum.inr 4575, 1), (Sum.inr 4618, 2), (Sum.inr 4619, 3), (Sum.inr 4621, 1), (Sum.inr 4623, 1), (Sum.inr 4627, 1), (Sum.inr 5170, 2), (Sum.inr 5302, 1), (Sum.inr 5306, 1), (Sum.inr 5310, 1)]

def sourceForm1660 : Integer.Sparse Master := [(Sum.inr 593, 2), (Sum.inr 594, 1), (Sum.inr 595, 1), (Sum.inr 613, 1), (Sum.inr 1122, 2), (Sum.inr 1123, 2), (Sum.inr 1124, 2), (Sum.inr 1138, 2), (Sum.inr 1188, 2), (Sum.inr 1190, 1), (Sum.inr 1193, 1), (Sum.inr 1293, 2), (Sum.inr 1294, 3), (Sum.inr 1297, 1), (Sum.inr 1305, 1), (Sum.inr 1311, 1), (Sum.inr 2954, 2), (Sum.inr 3054, 1), (Sum.inr 3120, 1), (Sum.inr 3121, 1)]

def sourceForm1661 : Integer.Sparse Master := [(Sum.inr 4176, 2), (Sum.inr 4178, 1), (Sum.inr 4179, 1), (Sum.inr 4188, 1), (Sum.inr 4545, 2), (Sum.inr 4547, 2), (Sum.inr 4548, 2), (Sum.inr 4556, 2), (Sum.inr 4602, 2), (Sum.inr 4607, 2), (Sum.inr 4608, 1), (Sum.inr 4609, 1), (Sum.inr 4611, 1), (Sum.inr 4612, 1), (Sum.inr 4616, 2), (Sum.inr 4617, 1), (Sum.inr 4620, 1), (Sum.inr 5163, 2), (Sum.inr 5274, 1), (Sum.inr 5291, 1), (Sum.inr 5304, 1)]

def sourceForm1662 : Integer.Sparse Master := [(Sum.inr 604, 2), (Sum.inr 606, 1), (Sum.inr 607, 1), (Sum.inr 616, 1), (Sum.inr 1130, 2), (Sum.inr 1132, 2), (Sum.inr 1133, 2), (Sum.inr 1141, 2), (Sum.inr 1241, 2), (Sum.inr 1243, 1), (Sum.inr 1245, 1), (Sum.inr 1267, 2), (Sum.inr 1269, 1), (Sum.inr 1274, 1), (Sum.inr 1291, 2), (Sum.inr 1292, 1), (Sum.inr 1295, 1), (Sum.inr 2961, 2), (Sum.inr 3103, 1), (Sum.inr 3112, 1), (Sum.inr 3119, 1)]

def sourceForm1663 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1513, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 2657, 2), (Sum.inr 2683, 1), (Sum.inr 2737, 1), (Sum.inr 3259, 2), (Sum.inr 3266, 2), (Sum.inr 3271, 2), (Sum.inr 3293, 2), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3303, 2), (Sum.inr 3306, 1), (Sum.inr 3547, 1), (Sum.inr 3564, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1664 : Integer.Sparse Master := [(Sum.inr 638, 2), (Sum.inr 641, 1), (Sum.inr 642, 1), (Sum.inr 653, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

def sourceForm1667 : Integer.Sparse Master := [(Sum.inr 1287, 1), (Sum.inr 2584, 2), (Sum.inr 2685, 1), (Sum.inr 2761, 2), (Sum.inr 4082, -1)]

def sourceForm1668 : Integer.Sparse Master := [(Sum.inr 1230, 1), (Sum.inr 2505, 1), (Sum.inr 2551, 1), (Sum.inr 2705, 1), (Sum.inr 2729, 1), (Sum.inr 2736, 1), (Sum.inr 4088, -1)]

def sourceForm1669 : Integer.Sparse Master := [(Sum.inr 4150, 1), (Sum.inr 4151, 1), (Sum.inr 4155, 2), (Sum.inr 4173, 1), (Sum.inr 4527, 1), (Sum.inr 4530, 2), (Sum.inr 4542, 1), (Sum.inr 4544, 1), (Sum.inr 4551, 1), (Sum.inr 4554, 2), (Sum.inr 4590, 2), (Sum.inr 4591, 2), (Sum.inr 4593, 2), (Sum.inr 4601, 1), (Sum.inr 4603, 2), (Sum.inr 4606, 2), (Sum.inr 4618, 1), (Sum.inr 5104, 1), (Sum.inr 5137, 1), (Sum.inr 5259, 2), (Sum.inr 5273, 1)]

def sourceForm1670 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 579, 1), (Sum.inr 583, 2), (Sum.inr 601, 1), (Sum.inr 1111, 1), (Sum.inr 1114, 2), (Sum.inr 1127, 1), (Sum.inr 1162, 1), (Sum.inr 1163, 1), (Sum.inr 1167, 2), (Sum.inr 1213, 2), (Sum.inr 1215, 2), (Sum.inr 1220, 2), (Sum.inr 1237, 2), (Sum.inr 1265, 1), (Sum.inr 1266, 2), (Sum.inr 1298, 1), (Sum.inr 2936, 1), (Sum.inr 3000, 1), (Sum.inr 3088, 2), (Sum.inr 3111, 1)]

def sourceForm1671 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1505, 1), (Sum.inr 1508, 1), (Sum.inr 1515, 2), (Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3263, 1), (Sum.inr 3273, 1), (Sum.inr 3274, 2), (Sum.inr 3290, 2), (Sum.inr 3291, 2), (Sum.inr 3292, 1), (Sum.inr 3294, 2), (Sum.inr 3297, 2), (Sum.inr 3299, 2), (Sum.inr 3304, 1), (Sum.inr 3483, 1), (Sum.inr 3521, 1), (Sum.inr 3544, 2), (Sum.inr 3546, 1)]

def sourceForm1672 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 630, 1), (Sum.inr 632, 2), (Sum.inr 640, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

def sourceForm1673 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 1152, 2), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

def sourceForm1674 : Integer.Sparse Master := [(Sum.inr 4143, 1), (Sum.inr 4144, 1), (Sum.inr 4145, 2), (Sum.inr 4175, 1), (Sum.inr 4516, 1), (Sum.inr 4517, 1), (Sum.inr 4518, 2), (Sum.inr 4523, 1), (Sum.inr 4524, 2), (Sum.inr 4544, 1), (Sum.inr 4601, 1), (Sum.inr 4602, 2), (Sum.inr 4606, 2), (Sum.inr 4608, 2), (Sum.inr 4612, 2), (Sum.inr 4622, 1), (Sum.inr 4624, 2), (Sum.inr 5148, 1), (Sum.inr 5203, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 2)]

def sourceForm1675 : Integer.Sparse Master := [(Sum.inr 571, 1), (Sum.inr 572, 1), (Sum.inr 573, 2), (Sum.inr 603, 1), (Sum.inr 1100, 1), (Sum.inr 1101, 1), (Sum.inr 1102, 2), (Sum.inr 1107, 1), (Sum.inr 1108, 2), (Sum.inr 1129, 1), (Sum.inr 1235, 1), (Sum.inr 1236, 2), (Sum.inr 1240, 2), (Sum.inr 1242, 2), (Sum.inr 1246, 2), (Sum.inr 1299, 1), (Sum.inr 1301, 2), (Sum.inr 2884, 1), (Sum.inr 2927, 1), (Sum.inr 3100, 1), (Sum.inr 3102, 2)]

def sourceForm1677 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 1004, 1), (Sum.inr 1005, 2), (Sum.inr 1086, 1), (Sum.inr 1180, 1), (Sum.inr 1188, 1), (Sum.inr 1189, 2), (Sum.inr 1200, 1), (Sum.inr 1201, 2), (Sum.inr 1213, 2), (Sum.inr 1216, 1), (Sum.inr 1236, 2), (Sum.inr 1237, 2), (Sum.inr 1240, 1), (Sum.inr 1241, 2), (Sum.inr 1301, 2), (Sum.inr 1305, 1), (Sum.inr 1370, 1), (Sum.inr 1386, 1), (Sum.inr 1411, 2), (Sum.inr 1414, 1)]

def sourceForm1678 : Integer.Sparse Master := [(Sum.inr 4152, 1), (Sum.inr 4153, 1), (Sum.inr 4154, 1), (Sum.inr 4158, 1), (Sum.inr 4176, 1), (Sum.inr 4528, 1), (Sum.inr 4529, 1), (Sum.inr 4533, 1), (Sum.inr 4541, 1), (Sum.inr 4545, 1), (Sum.inr 4546, 1), (Sum.inr 4549, 1), (Sum.inr 4553, 1), (Sum.inr 4589, 1), (Sum.inr 4591, 1), (Sum.inr 4592, 1), (Sum.inr 4599, 1), (Sum.inr 4602, 1), (Sum.inr 4603, 1), (Sum.inr 4607, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4616, 1), (Sum.inr 4619, 1), (Sum.inr 5101, 1), (Sum.inr 5134, 1), (Sum.inr 5258, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1)]

def sourceForm1679 : Integer.Sparse Master := [(Sum.inr 580, 1), (Sum.inr 581, 1), (Sum.inr 582, 1), (Sum.inr 586, 1), (Sum.inr 604, 1), (Sum.inr 1112, 1), (Sum.inr 1113, 1), (Sum.inr 1117, 1), (Sum.inr 1130, 1), (Sum.inr 1164, 1), (Sum.inr 1165, 1), (Sum.inr 1166, 1), (Sum.inr 1172, 1), (Sum.inr 1216, 1), (Sum.inr 1217, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1260, 1), (Sum.inr 1261, 1), (Sum.inr 1262, 1), (Sum.inr 1267, 1), (Sum.inr 1269, 1), (Sum.inr 1274, 1), (Sum.inr 1291, 1), (Sum.inr 1302, 1), (Sum.inr 2937, 1), (Sum.inr 3001, 1), (Sum.inr 3089, 1), (Sum.inr 3109, 1), (Sum.inr 3112, 1)]

def sourceForm1680 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1511, 1), (Sum.inr 1512, 1), (Sum.inr 1514, 1), (Sum.inr 1522, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3264, 1), (Sum.inr 3265, 1), (Sum.inr 3267, 1), (Sum.inr 3270, 1), (Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3291, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3303, 1), (Sum.inr 3305, 1), (Sum.inr 3470, 1), (Sum.inr 3514, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3547, 1)]

def sourceForm1681 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 626, 1), (Sum.inr 627, 1), (Sum.inr 631, 1), (Sum.inr 638, 1), (Sum.inr 1236, 1), (Sum.inr 4092, -1)]

def sourceForm1682 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 1149, 1), (Sum.inr 1151, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

def sourceForm1683 : Integer.Sparse Master := [(Sum.inr 4139, 1), (Sum.inr 4140, 1), (Sum.inr 4141, 1), (Sum.inr 4145, 1), (Sum.inr 4172, 1), (Sum.inr 4513, 1), (Sum.inr 4514, 1), (Sum.inr 4515, 1), (Sum.inr 4518, 1), (Sum.inr 4521, 1), (Sum.inr 4522, 1), (Sum.inr 4524, 1), (Sum.inr 4541, 1), (Sum.inr 4581, 1), (Sum.inr 4583, 1), (Sum.inr 4586, 1), (Sum.inr 4601, 1), (Sum.inr 4602, 3), (Sum.inr 4605, 1), (Sum.inr 4606, 1), (Sum.inr 4612, 1), (Sum.inr 4622, 1), (Sum.inr 4623, 1), (Sum.inr 5149, 1), (Sum.inr 5204, 1), (Sum.inr 5284, 1), (Sum.inr 5292, 1), (Sum.inr 5294, 1)]

def sourceForm1684 : Integer.Sparse Master := [(Sum.inr 567, 1), (Sum.inr 568, 1), (Sum.inr 569, 1), (Sum.inr 573, 1), (Sum.inr 600, 1), (Sum.inr 1097, 1), (Sum.inr 1098, 1), (Sum.inr 1099, 1), (Sum.inr 1102, 1), (Sum.inr 1105, 1), (Sum.inr 1106, 1), (Sum.inr 1108, 1), (Sum.inr 1126, 1), (Sum.inr 1200, 1), (Sum.inr 1202, 1), (Sum.inr 1205, 1), (Sum.inr 1235, 1), (Sum.inr 1236, 3), (Sum.inr 1239, 1), (Sum.inr 1240, 1), (Sum.inr 1246, 1), (Sum.inr 1299, 1), (Sum.inr 1300, 1), (Sum.inr 2881, 1), (Sum.inr 2924, 1), (Sum.inr 3077, 1), (Sum.inr 3100, 1), (Sum.inr 3101, 1)]

def sourceForm1686 : Integer.Sparse Master := [(Sum.inr 1229, 1), (Sum.inr 2504, 1), (Sum.inr 2550, 1), (Sum.inr 2704, 1), (Sum.inr 2719, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

def sourceForm1688 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 1188, 1), (Sum.inr 1189, 2), (Sum.inr 1286, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

def sourceForm1689 : Integer.Sparse Master := [(Sum.inr 1185, 1), (Sum.inr 2400, 1), (Sum.inr 2535, 1), (Sum.inr 2677, 1), (Sum.inr 2682, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

def sourceForm1690 : Integer.Sparse Master := [(Sum.inr 1188, 1), (Sum.inr 2403, 1), (Sum.inr 2536, 1), (Sum.inr 2672, 2), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

def sourceForm1693 : Integer.Sparse Master := [(Sum.inr 1184, 1), (Sum.inr 2399, 1), (Sum.inr 2534, 1), (Sum.inr 2670, 1), (Sum.inr 2681, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

def sourceForm1695 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 1201, 2), (Sum.inr 1228, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1696 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 2459, 2), (Sum.inr 2697, 1), (Sum.inr 2701, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def sourceForm1697 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 2461, 2), (Sum.inr 2694, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

def sourceForm1700 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 2458, 2), (Sum.inr 2693, 1), (Sum.inr 2700, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

def sourceForm1702 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 1054, 2), (Sum.inr 1060, 1), (Sum.inr 1073, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def sourceForm1703 : Integer.Sparse Master := [(Sum.inr 1054, 1), (Sum.inr 2031, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2251, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def sourceForm1704 : Integer.Sparse Master := [(Sum.inr 1053, 1), (Sum.inr 2030, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2274, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

def sourceForm1706 : Integer.Sparse Master := [(Sum.inr 988, 2), (Sum.inr 990, 1), (Sum.inr 998, 1), (Sum.inr 1052, 1), (Sum.inr 2214, 1), (Sum.inr 4080, -1)]

def sourceForm1707 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 1922, 1), (Sum.inr 2118, 1), (Sum.inr 2195, 1), (Sum.inr 2214, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def sourceForm1708 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 1921, 1), (Sum.inr 2117, 1), (Sum.inr 2213, 1), (Sum.inr 2215, 2), (Sum.inr 4082, -1)]

def sourceForm1709 : Integer.Sparse Master := [(Sum.inr 1023, 1), (Sum.inr 2091, 2), (Sum.inr 2234, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

def sourceForm1710 : Integer.Sparse Master := [(Sum.inr 1018, 2), (Sum.inr 1023, 1), (Sum.inr 1034, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

def sourceForm1711 : Integer.Sparse Master := [(Sum.inr 1018, 1), (Sum.inr 2086, 2), (Sum.inr 2191, 1), (Sum.inr 2232, 1), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

def sourceForm1712 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 2085, 2), (Sum.inr 2190, 1), (Sum.inr 2240, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

def sourceForm1713 : Integer.Sparse Master := [(Sum.inr 1045, 1), (Sum.inr 2024, 1), (Sum.inr 2111, 1), (Sum.inr 2246, 1), (Sum.inr 2254, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def sourceForm1714 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 1035, 1), (Sum.inr 1036, 1), (Sum.inr 1045, 1), (Sum.inr 1073, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def sourceForm1715 : Integer.Sparse Master := [(Sum.inr 1036, 1), (Sum.inr 2017, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 2251, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def sourceForm1716 : Integer.Sparse Master := [(Sum.inr 4152, 1), (Sum.inr 4157, 1), (Sum.inr 4158, 2), (Sum.inr 4182, 1), (Sum.inr 4331, 1), (Sum.inr 4332, 2), (Sum.inr 4351, 1), (Sum.inr 4366, 1), (Sum.inr 4371, 1), (Sum.inr 4372, 2), (Sum.inr 4439, 2), (Sum.inr 4442, 2), (Sum.inr 4444, 2), (Sum.inr 4456, 1), (Sum.inr 4458, 2), (Sum.inr 4461, 2), (Sum.inr 4497, 1), (Sum.inr 4805, 1), (Sum.inr 4869, 1), (Sum.inr 4889, 2), (Sum.inr 4893, 1)]

def sourceForm1717 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1522, 2), (Sum.inr 1524, 1), (Sum.inr 1528, 1), (Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1706, 1), (Sum.inr 1711, 1), (Sum.inr 1713, 2), (Sum.inr 1724, 2), (Sum.inr 1726, 1), (Sum.inr 1734, 2), (Sum.inr 1736, 2), (Sum.inr 1737, 2), (Sum.inr 1742, 1), (Sum.inr 1744, 2), (Sum.inr 2214, 1), (Sum.inr 2263, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 2)]

def sourceForm1718 : Integer.Sparse Master := [(Sum.inr 610, 1), (Sum.inr 929, 1), (Sum.inr 1044, 3), (Sum.inr 1081, 1), (Sum.inr 4083, -1)]

def sourceForm1719 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 949, 1), (Sum.inr 950, 2), (Sum.inr 1044, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def sourceForm1720 : Integer.Sparse Master := [(Sum.inr 4104, 1), (Sum.inr 4105, 1), (Sum.inr 4106, 2), (Sum.inr 4126, 1), (Sum.inr 4290, 1), (Sum.inr 4291, 2), (Sum.inr 4307, 1), (Sum.inr 4351, 1), (Sum.inr 4352, 1), (Sum.inr 4354, 2), (Sum.inr 4451, 1), (Sum.inr 4452, 2), (Sum.inr 4461, 2), (Sum.inr 4463, 2), (Sum.inr 4466, 2), (Sum.inr 4489, 1), (Sum.inr 4503, 2), (Sum.inr 5076, 1), (Sum.inr 5172, 1), (Sum.inr 5290, 1), (Sum.inr 5294, 2)]

def sourceForm1723 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 810, 1), (Sum.inr 811, 2), (Sum.inr 827, 1), (Sum.inr 980, 1), (Sum.inr 981, 2), (Sum.inr 990, 1), (Sum.inr 1021, 2), (Sum.inr 1023, 1), (Sum.inr 1041, 2), (Sum.inr 1042, 2), (Sum.inr 1044, 1), (Sum.inr 1045, 2), (Sum.inr 1058, 2), (Sum.inr 1060, 1), (Sum.inr 1086, 1), (Sum.inr 1087, 2), (Sum.inr 1216, 1), (Sum.inr 1267, 2), (Sum.inr 1270, 1), (Sum.inr 1305, 1)]

def sourceForm1724 : Integer.Sparse Master := [(Sum.inr 4150, 1), (Sum.inr 4153, 1), (Sum.inr 4155, 1), (Sum.inr 4158, 1), (Sum.inr 4175, 1), (Sum.inr 4327, 1), (Sum.inr 4329, 1), (Sum.inr 4332, 1), (Sum.inr 4344, 1), (Sum.inr 4364, 1), (Sum.inr 4367, 1), (Sum.inr 4369, 1), (Sum.inr 4372, 1), (Sum.inr 4438, 1), (Sum.inr 4440, 1), (Sum.inr 4444, 1), (Sum.inr 4456, 1), (Sum.inr 4458, 3), (Sum.inr 4461, 1), (Sum.inr 4463, 1), (Sum.inr 4467, 1), (Sum.inr 4497, 1), (Sum.inr 4502, 1), (Sum.inr 4802, 1), (Sum.inr 4866, 1), (Sum.inr 4888, 1), (Sum.inr 4893, 1), (Sum.inr 4895, 1)]

def sourceForm1725 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 626, 1), (Sum.inr 627, 1), (Sum.inr 632, 1), (Sum.inr 644, 1), (Sum.inr 1316, 1), (Sum.inr 1317, 1), (Sum.inr 1318, 1), (Sum.inr 1322, 1), (Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1331, 1), (Sum.inr 1339, 1), (Sum.inr 1386, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1409, 1), (Sum.inr 1410, 1), (Sum.inr 1411, 3), (Sum.inr 1413, 1), (Sum.inr 1420, 1), (Sum.inr 1446, 1), (Sum.inr 1447, 1), (Sum.inr 3184, 1), (Sum.inr 3204, 1), (Sum.inr 3227, 1), (Sum.inr 3228, 1), (Sum.inr 3229, 1)]

def sourceForm1726 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1514, 1), (Sum.inr 1515, 1), (Sum.inr 1517, 1), (Sum.inr 1522, 1), (Sum.inr 1670, 1), (Sum.inr 1671, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1703, 1), (Sum.inr 1705, 1), (Sum.inr 1706, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1723, 1), (Sum.inr 1724, 3), (Sum.inr 1726, 1), (Sum.inr 1734, 1), (Sum.inr 1736, 1), (Sum.inr 1737, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 1753, 1), (Sum.inr 2202, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2263, 1), (Sum.inr 2291, 1)]

def sourceForm1727 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 581, 1), (Sum.inr 583, 1), (Sum.inr 586, 1), (Sum.inr 603, 1), (Sum.inr 1041, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1728 : Integer.Sparse Master := [(Sum.inr 603, 1), (Sum.inr 922, 1), (Sum.inr 1041, 2), (Sum.inr 1081, 1), (Sum.inr 1086, 1), (Sum.inr 4083, -1)]

def sourceForm1729 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 945, 1), (Sum.inr 947, 1), (Sum.inr 950, 1), (Sum.inr 1041, 1), (Sum.inr 2107, 1), (Sum.inr 4083, -1)]

def sourceForm1730 : Integer.Sparse Master := [(Sum.inr 4100, 1), (Sum.inr 4101, 1), (Sum.inr 4102, 1), (Sum.inr 4107, 1), (Sum.inr 4119, 1), (Sum.inr 4287, 1), (Sum.inr 4288, 1), (Sum.inr 4292, 1), (Sum.inr 4301, 1), (Sum.inr 4344, 1), (Sum.inr 4346, 1), (Sum.inr 4349, 1), (Sum.inr 4355, 1), (Sum.inr 4399, 1), (Sum.inr 4401, 1), (Sum.inr 4404, 1), (Sum.inr 4424, 1), (Sum.inr 4456, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4460, 1), (Sum.inr 4467, 1), (Sum.inr 4495, 1), (Sum.inr 4499, 1), (Sum.inr 5073, 1), (Sum.inr 5169, 1), (Sum.inr 5259, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1)]

def sourceForm1732 : Integer.Sparse Master := [(Sum.inr 4249, 1), (Sum.inr 4264, 1), (Sum.inr 4265, 1), (Sum.inr 4267, 1), (Sum.inr 4268, 1), (Sum.inr 4396, 1), (Sum.inr 4397, 1), (Sum.inr 4399, 1), (Sum.inr 4407, 1), (Sum.inr 4436, 1), (Sum.inr 4438, 1), (Sum.inr 4439, 1), (Sum.inr 4452, 1), (Sum.inr 4453, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4459, 1), (Sum.inr 4461, 1), (Sum.inr 4471, 1), (Sum.inr 4474, 1), (Sum.inr 4475, 1), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4502, 1), (Sum.inr 4590, 1), (Sum.inr 4602, 1), (Sum.inr 4603, 1), (Sum.inr 4606, 1), (Sum.inr 4624, 1)]

def sourceForm1733 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 806, 1), (Sum.inr 807, 1), (Sum.inr 810, 1), (Sum.inr 824, 1), (Sum.inr 977, 1), (Sum.inr 978, 1), (Sum.inr 980, 1), (Sum.inr 988, 1), (Sum.inr 1018, 1), (Sum.inr 1020, 1), (Sum.inr 1021, 1), (Sum.inr 1035, 1), (Sum.inr 1036, 1), (Sum.inr 1040, 1), (Sum.inr 1041, 2), (Sum.inr 1042, 1), (Sum.inr 1044, 1), (Sum.inr 1054, 1), (Sum.inr 1057, 1), (Sum.inr 1058, 1), (Sum.inr 1082, 1), (Sum.inr 1083, 1), (Sum.inr 1086, 1), (Sum.inr 1213, 1), (Sum.inr 1262, 1), (Sum.inr 1266, 1), (Sum.inr 1267, 1), (Sum.inr 1301, 1)]

def sourceForm1734 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1236, 1), (Sum.inr 1237, 1), (Sum.inr 1240, 1), (Sum.inr 1301, 1), (Sum.inr 1358, 1), (Sum.inr 1367, 1), (Sum.inr 1368, 1), (Sum.inr 1370, 1), (Sum.inr 1383, 1), (Sum.inr 1384, 1), (Sum.inr 1386, 1), (Sum.inr 1393, 1), (Sum.inr 1395, 1), (Sum.inr 1396, 1), (Sum.inr 1406, 1), (Sum.inr 1407, 1), (Sum.inr 1410, 1), (Sum.inr 1411, 2), (Sum.inr 1412, 1), (Sum.inr 1414, 1), (Sum.inr 1443, 1), (Sum.inr 1447, 1), (Sum.inr 1448, 1), (Sum.inr 1468, 1), (Sum.inr 1475, 1), (Sum.inr 1480, 1), (Sum.inr 1482, 1), (Sum.inr 1483, 1)]

def sourceForm1735 : Integer.Sparse Master := [(Sum.inr 1035, 1), (Sum.inr 2016, 1), (Sum.inr 2101, 1), (Sum.inr 2205, 1), (Sum.inr 2242, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def sourceForm1737 : Integer.Sparse Master := [(Sum.inr 730, 1), (Sum.inr 733, 1), (Sum.inr 734, 1), (Sum.inr 738, 1), (Sum.inr 806, 1), (Sum.inr 1645, 1), (Sum.inr 4069, -1)]

def sourceForm1738 : Integer.Sparse Master := [(Sum.inr 4149, 1), (Sum.inr 4151, 1), (Sum.inr 4154, 2), (Sum.inr 4172, 1), (Sum.inr 4326, 1), (Sum.inr 4328, 2), (Sum.inr 4341, 1), (Sum.inr 4363, 1), (Sum.inr 4365, 1), (Sum.inr 4368, 2), (Sum.inr 4455, 1), (Sum.inr 4457, 2), (Sum.inr 4459, 2), (Sum.inr 4460, 2), (Sum.inr 4466, 2), (Sum.inr 4495, 1), (Sum.inr 4498, 2), (Sum.inr 4801, 1), (Sum.inr 4865, 1), (Sum.inr 4888, 1), (Sum.inr 4894, 2)]

def sourceForm1739 : Integer.Sparse Master := [(Sum.inr 629, 1), (Sum.inr 630, 1), (Sum.inr 631, 2), (Sum.inr 646, 1), (Sum.inr 1319, 1), (Sum.inr 1320, 1), (Sum.inr 1321, 2), (Sum.inr 1329, 1), (Sum.inr 1330, 2), (Sum.inr 1341, 1), (Sum.inr 1405, 1), (Sum.inr 1406, 2), (Sum.inr 1414, 2), (Sum.inr 1416, 2), (Sum.inr 1419, 2), (Sum.inr 1441, 1), (Sum.inr 1448, 2), (Sum.inr 3185, 1), (Sum.inr 3205, 1), (Sum.inr 3227, 1), (Sum.inr 3230, 2)]

def sourceForm1740 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1505, 1), (Sum.inr 1507, 1), (Sum.inr 1511, 2), (Sum.inr 1663, 1), (Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1697, 1), (Sum.inr 1698, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 2), (Sum.inr 1708, 1), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 2), (Sum.inr 1727, 2), (Sum.inr 1738, 2), (Sum.inr 2190, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2264, 2)]

def sourceForm1741 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 579, 1), (Sum.inr 582, 2), (Sum.inr 600, 1), (Sum.inr 1040, 1), (Sum.inr 4084, -1)]

def sourceForm1742 : Integer.Sparse Master := [(Sum.inr 600, 1), (Sum.inr 919, 1), (Sum.inr 1040, 1), (Sum.inr 1079, 1), (Sum.inr 1082, 2), (Sum.inr 4084, -1)]

def sourceForm1743 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 943, 1), (Sum.inr 946, 2), (Sum.inr 1040, 1), (Sum.inr 2106, 1), (Sum.inr 4084, -1)]

def sourceForm1744 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 941, 1), (Sum.inr 1038, 1), (Sum.inr 1040, 3), (Sum.inr 4084, -1)]

def sourceForm1745 : Integer.Sparse Master := [(Sum.inr 4098, 1), (Sum.inr 4099, 1), (Sum.inr 4102, 2), (Sum.inr 4115, 1), (Sum.inr 4286, 1), (Sum.inr 4288, 2), (Sum.inr 4298, 1), (Sum.inr 4341, 1), (Sum.inr 4343, 1), (Sum.inr 4349, 2), (Sum.inr 4396, 2), (Sum.inr 4398, 2), (Sum.inr 4404, 2), (Sum.inr 4419, 2), (Sum.inr 4456, 1), (Sum.inr 4458, 2), (Sum.inr 4495, 1), (Sum.inr 5072, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 2), (Sum.inr 5292, 1)]

def sourceForm1746 : Integer.Sparse Master := [(Sum.inr 535, 1), (Sum.inr 536, 1), (Sum.inr 539, 2), (Sum.inr 552, 1), (Sum.inr 864, 1), (Sum.inr 866, 2), (Sum.inr 876, 1), (Sum.inr 919, 1), (Sum.inr 921, 1), (Sum.inr 927, 2), (Sum.inr 977, 2), (Sum.inr 979, 2), (Sum.inr 985, 2), (Sum.inr 1000, 2), (Sum.inr 1039, 1), (Sum.inr 1041, 2), (Sum.inr 1079, 1), (Sum.inr 2479, 1), (Sum.inr 2594, 1), (Sum.inr 2722, 2), (Sum.inr 2766, 1)]

def sourceForm1747 : Integer.Sparse Master := [(Sum.inr 4248, 1), (Sum.inr 4251, 1), (Sum.inr 4255, 1), (Sum.inr 4264, 2), (Sum.inr 4395, 1), (Sum.inr 4396, 2), (Sum.inr 4406, 1), (Sum.inr 4435, 2), (Sum.inr 4438, 1), (Sum.inr 4450, 2), (Sum.inr 4452, 2), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4470, 2), (Sum.inr 4474, 1), (Sum.inr 4496, 1), (Sum.inr 4498, 2), (Sum.inr 4589, 1), (Sum.inr 4606, 1), (Sum.inr 4607, 2), (Sum.inr 4623, 1)]

def sourceForm1748 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 1240, 1), (Sum.inr 1241, 2), (Sum.inr 1305, 1), (Sum.inr 1360, 1), (Sum.inr 1370, 1), (Sum.inr 1371, 2), (Sum.inr 1386, 1), (Sum.inr 1387, 2), (Sum.inr 1396, 2), (Sum.inr 1398, 1), (Sum.inr 1411, 2), (Sum.inr 1412, 2), (Sum.inr 1414, 1), (Sum.inr 1415, 2), (Sum.inr 1448, 2), (Sum.inr 1451, 1), (Sum.inr 1470, 1), (Sum.inr 1477, 1), (Sum.inr 1478, 1), (Sum.inr 1483, 2)]

def sourceForm1749 : Integer.Sparse Master := [(Sum.inr 1033, 1), (Sum.inr 2015, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 2259, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

def sourceForm1750 : Integer.Sparse Master := [(Sum.inr 981, 1), (Sum.inr 1913, 1), (Sum.inr 2078, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

def sourceForm1751 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 978, 1), (Sum.inr 981, 1), (Sum.inr 998, 1), (Sum.inr 1032, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

def sourceForm1752 : Integer.Sparse Master := [(Sum.inr 978, 1), (Sum.inr 1909, 1), (Sum.inr 2076, 1), (Sum.inr 2195, 1), (Sum.inr 2202, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

def sourceForm1753 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 1912, 1), (Sum.inr 2077, 1), (Sum.inr 2191, 2), (Sum.inr 2204, 1), (Sum.inr 4079, -1)]

def sourceForm1756 : Integer.Sparse Master := [(Sum.inr 980, 3), (Sum.inr 1003, 1), (Sum.inr 1034, 1), (Sum.inr 2204, 1), (Sum.inr 4079, -1)]

def sourceForm1759 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 1908, 1), (Sum.inr 2075, 1), (Sum.inr 2190, 1), (Sum.inr 2202, 1), (Sum.inr 2205, 1), (Sum.inr 4080, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1761 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 866, 1), (Sum.inr 869, 1), (Sum.inr 878, 1), (Sum.inr 977, 1), (Sum.inr 1908, 1), (Sum.inr 4080, -1)]

def sourceForm1762 : Integer.Sparse Master := [(Sum.inr 699, 1), (Sum.inr 700, 1), (Sum.inr 703, 1), (Sum.inr 712, 1), (Sum.inr 806, 1), (Sum.inr 1597, 1), (Sum.inr 4069, -1)]

def sourceForm1763 : Integer.Sparse Master := [(Sum.inr 976, 1), (Sum.inr 1907, 1), (Sum.inr 2074, 1), (Sum.inr 2201, 1), (Sum.inr 2203, 2), (Sum.inr 4081, -1)]

def sourceForm1766 : Integer.Sparse Master := [(Sum.inr 1076, 1), (Sum.inr 2049, 2), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def sourceForm1769 : Integer.Sparse Master := [(Sum.inr 4176, 2), (Sum.inr 4184, 1), (Sum.inr 4185, 1), (Sum.inr 4188, 1), (Sum.inr 4345, 2), (Sum.inr 4353, 2), (Sum.inr 4354, 2), (Sum.inr 4357, 2), (Sum.inr 4459, 2), (Sum.inr 4464, 1), (Sum.inr 4466, 1), (Sum.inr 4475, 2), (Sum.inr 4478, 1), (Sum.inr 4480, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4839, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1)]

def sourceForm1770 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1530, 1), (Sum.inr 1668, 2), (Sum.inr 1681, 2), (Sum.inr 1682, 2), (Sum.inr 1686, 2), (Sum.inr 1708, 2), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1727, 1), (Sum.inr 1728, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 2216, 2), (Sum.inr 2265, 1), (Sum.inr 2278, 1), (Sum.inr 2279, 1)]

def sourceForm1773 : Integer.Sparse Master := [(Sum.inr 4268, 2), (Sum.inr 4276, 1), (Sum.inr 4279, 1), (Sum.inr 4283, 1), (Sum.inr 4400, 2), (Sum.inr 4424, 2), (Sum.inr 4425, 2), (Sum.inr 4427, 2), (Sum.inr 4459, 2), (Sum.inr 4461, 2), (Sum.inr 4462, 2), (Sum.inr 4499, 1), (Sum.inr 4500, 1), (Sum.inr 4502, 1), (Sum.inr 4503, 1), (Sum.inr 4504, 1), (Sum.inr 4506, 1), (Sum.inr 4607, 2), (Sum.inr 4617, 1), (Sum.inr 4619, 1), (Sum.inr 4623, 1)]

def sourceForm1775 : Integer.Sparse Master := [(Sum.inr 4173, 2), (Sum.inr 4178, 1), (Sum.inr 4180, 1), (Sum.inr 4188, 1), (Sum.inr 4342, 2), (Sum.inr 4347, 2), (Sum.inr 4349, 2), (Sum.inr 4357, 2), (Sum.inr 4474, 2), (Sum.inr 4476, 1), (Sum.inr 4480, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 1), (Sum.inr 4499, 2), (Sum.inr 4503, 1), (Sum.inr 4507, 1), (Sum.inr 4511, 1), (Sum.inr 4835, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4901, 1)]

def sourceForm1776 : Integer.Sparse Master := [(Sum.inr 1508, 2), (Sum.inr 1519, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 1665, 2), (Sum.inr 1675, 2), (Sum.inr 1676, 2), (Sum.inr 1682, 2), (Sum.inr 1708, 2), (Sum.inr 1709, 2), (Sum.inr 1727, 1), (Sum.inr 1728, 2), (Sum.inr 1729, 1), (Sum.inr 1739, 1), (Sum.inr 1740, 1), (Sum.inr 1755, 1), (Sum.inr 1756, 1), (Sum.inr 2206, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2293, 1)]

def sourceForm1777 : Integer.Sparse Master := [(Sum.inr 4119, 2), (Sum.inr 4121, 1), (Sum.inr 4122, 1), (Sum.inr 4133, 1), (Sum.inr 4301, 2), (Sum.inr 4303, 2), (Sum.inr 4304, 2), (Sum.inr 4314, 2), (Sum.inr 4424, 2), (Sum.inr 4428, 1), (Sum.inr 4431, 1), (Sum.inr 4458, 2), (Sum.inr 4460, 1), (Sum.inr 4467, 1), (Sum.inr 4495, 2), (Sum.inr 4496, 1), (Sum.inr 4499, 1), (Sum.inr 5102, 2), (Sum.inr 5275, 1), (Sum.inr 5293, 1), (Sum.inr 5306, 1)]

def sourceForm1779 : Integer.Sparse Master := [(Sum.inr 4265, 2), (Sum.inr 4270, 1), (Sum.inr 4273, 1), (Sum.inr 4283, 1), (Sum.inr 4397, 2), (Sum.inr 4419, 2), (Sum.inr 4420, 2), (Sum.inr 4424, 2), (Sum.inr 4453, 2), (Sum.inr 4458, 2), (Sum.inr 4459, 2), (Sum.inr 4491, 1), (Sum.inr 4492, 1), (Sum.inr 4498, 1), (Sum.inr 4500, 1), (Sum.inr 4502, 1), (Sum.inr 4503, 1), (Sum.inr 4603, 2), (Sum.inr 4619, 1), (Sum.inr 4620, 1), (Sum.inr 4624, 1)]

def sourceForm1780 : Integer.Sparse Master := [(Sum.inr 1075, 1), (Sum.inr 2048, 2), (Sum.inr 2229, 1), (Sum.inr 2276, 1), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

def sourceForm1781 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4175, 2), (Sum.inr 4183, 1), (Sum.inr 4186, 2), (Sum.inr 4344, 2), (Sum.inr 4352, 2), (Sum.inr 4355, 4), (Sum.inr 4458, 4), (Sum.inr 4463, 2), (Sum.inr 4467, 2), (Sum.inr 4497, 2), (Sum.inr 4502, 2), (Sum.inr 4838, 2), (Sum.inr 4895, 2)]

def sourceForm1782 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4172, 2), (Sum.inr 4177, 1), (Sum.inr 4180, 1), (Sum.inr 4185, 1), (Sum.inr 4341, 2), (Sum.inr 4346, 2), (Sum.inr 4349, 2), (Sum.inr 4354, 2), (Sum.inr 4457, 2), (Sum.inr 4460, 1), (Sum.inr 4466, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 2), (Sum.inr 4499, 1), (Sum.inr 4503, 1), (Sum.inr 4505, 1), (Sum.inr 4511, 1), (Sum.inr 4834, 2), (Sum.inr 4894, 1), (Sum.inr 4895, 1)]

def sourceForm1783 : Integer.Sparse Master := [(Sum.inr 1074, 1), (Sum.inr 2047, 2), (Sum.inr 2228, 1), (Sum.inr 2261, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def sourceForm1784 : Integer.Sparse Master := [(Sum.inr 4170, 2), (Sum.inr 4174, 1), (Sum.inr 4179, 2), (Sum.inr 4340, 2), (Sum.inr 4343, 2), (Sum.inr 4348, 4), (Sum.inr 4494, 2), (Sum.inr 4496, 4), (Sum.inr 4500, 2), (Sum.inr 4501, 2), (Sum.inr 4510, 2), (Sum.inr 4832, 2), (Sum.inr 4890, 1), (Sum.inr 4897, 2)]

def sourceForm1785 : Integer.Sparse Master := [(Sum.inr 651, 2), (Sum.inr 652, 1), (Sum.inr 653, 2), (Sum.inr 1345, 2), (Sum.inr 1346, 2), (Sum.inr 1347, 4), (Sum.inr 1435, 2), (Sum.inr 1436, 2), (Sum.inr 1451, 4), (Sum.inr 1452, 2), (Sum.inr 1454, 2), (Sum.inr 2755, 1), (Sum.inr 3082, 2), (Sum.inr 3114, 2)]

def sourceForm1786 : Integer.Sparse Master := [(Sum.inr 1503, 2), (Sum.inr 1509, 1), (Sum.inr 1513, 2), (Sum.inr 1662, 2), (Sum.inr 1666, 2), (Sum.inr 1669, 4), (Sum.inr 1700, 2), (Sum.inr 1710, 4), (Sum.inr 1716, 2), (Sum.inr 1730, 2), (Sum.inr 1741, 2), (Sum.inr 2193, 2), (Sum.inr 2247, 1), (Sum.inr 2268, 2)]

def sourceForm1787 : Integer.Sparse Master := [(Sum.inr 598, 2), (Sum.inr 602, 1), (Sum.inr 607, 2), (Sum.inr 1080, 1), (Sum.inr 4085, -1)]

def sourceForm1788 : Integer.Sparse Master := [(Sum.inr 598, 1), (Sum.inr 918, 1), (Sum.inr 1078, 1), (Sum.inr 1080, 3), (Sum.inr 4085, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1792 : Integer.Sparse Master := [(Sum.inr 1252, 2), (Sum.inr 1255, 1), (Sum.inr 1270, 2), (Sum.inr 1272, 2), (Sum.inr 1305, 1), (Sum.inr 1306, 2), (Sum.inr 1398, 2), (Sum.inr 1414, 2), (Sum.inr 1415, 4), (Sum.inr 1427, 4), (Sum.inr 1448, 2), (Sum.inr 1449, 2), (Sum.inr 1478, 2), (Sum.inr 1484, 2)]

def sourceForm1793 : Integer.Sparse Master := [(Sum.inr 1006, 1), (Sum.inr 1948, 1), (Sum.inr 2001, 1), (Sum.inr 2207, 1), (Sum.inr 2221, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

def sourceForm1795 : Integer.Sparse Master := [(Sum.inr 1001, 1), (Sum.inr 1946, 1), (Sum.inr 1998, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def sourceForm1796 : Integer.Sparse Master := [(Sum.inr 1008, 1), (Sum.inr 1949, 1), (Sum.inr 2002, 1), (Sum.inr 2217, 2), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

def sourceForm1797 : Integer.Sparse Master := [(Sum.inr 996, 1), (Sum.inr 1000, 2), (Sum.inr 1008, 1), (Sum.inr 1071, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

def sourceForm1798 : Integer.Sparse Master := [(Sum.inr 1005, 1), (Sum.inr 1947, 1), (Sum.inr 2000, 1), (Sum.inr 2206, 1), (Sum.inr 2216, 1), (Sum.inr 2227, 1), (Sum.inr 4080, -1)]

def sourceForm1800 : Integer.Sparse Master := [(Sum.inr 998, 1), (Sum.inr 1004, 1), (Sum.inr 1005, 2), (Sum.inr 1073, 1), (Sum.inr 2227, 1), (Sum.inr 4080, -1)]

def sourceForm1803 : Integer.Sparse Master := [(Sum.inr 1000, 1), (Sum.inr 1945, 1), (Sum.inr 1997, 1), (Sum.inr 2215, 1), (Sum.inr 2225, 1), (Sum.inr 2229, 1), (Sum.inr 4082, -1)]

def sourceForm1804 : Integer.Sparse Master := [(Sum.inr 876, 1), (Sum.inr 881, 1), (Sum.inr 883, 1), (Sum.inr 891, 1), (Sum.inr 1000, 1), (Sum.inr 1945, 1), (Sum.inr 4082, -1)]

def sourceForm1807 : Integer.Sparse Master := [(Sum.inr 999, 1), (Sum.inr 1944, 1), (Sum.inr 1996, 1), (Sum.inr 2203, 1), (Sum.inr 2224, 1), (Sum.inr 2228, 1), (Sum.inr 4081, -1)]

def sourceForm1809 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 1638, 2), (Sum.inr 1699, 2), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

def sourceForm1811 : Integer.Sparse Master := [(Sum.inr 783, 2), (Sum.inr 786, 1), (Sum.inr 805, 2), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

def sourceForm1812 : Integer.Sparse Master := [(Sum.inr 550, 1), (Sum.inr 803, 2), (Sum.inr 822, 1), (Sum.inr 850, 2), (Sum.inr 4069, -1)]

def sourceForm1813 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 1636, 2), (Sum.inr 1698, 1), (Sum.inr 1706, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

def sourceForm1814 : Integer.Sparse Master := [(Sum.inr 537, 1), (Sum.inr 732, 1), (Sum.inr 783, 2), (Sum.inr 805, 1), (Sum.inr 810, 1), (Sum.inr 4068, -1)]

def sourceForm1815 : Integer.Sparse Master := [(Sum.inr 4068, 1), (Sum.inr 4100, 1), (Sum.inr 4105, 1), (Sum.inr 4107, 2), (Sum.inr 4125, 1), (Sum.inr 4199, 1), (Sum.inr 4201, 2), (Sum.inr 4216, 1), (Sum.inr 4232, 1), (Sum.inr 4237, 1), (Sum.inr 4239, 2), (Sum.inr 4249, 2), (Sum.inr 4253, 2), (Sum.inr 4256, 2), (Sum.inr 4263, 1), (Sum.inr 4267, 4), (Sum.inr 4417, 1), (Sum.inr 4489, 1), (Sum.inr 4495, 2), (Sum.inr 4497, 1)]

def sourceForm1816 : Integer.Sparse Master := [(Sum.inr 662, 1), (Sum.inr 681, 1), (Sum.inr 682, 2), (Sum.inr 687, 1), (Sum.inr 760, 1), (Sum.inr 761, 2), (Sum.inr 766, 1), (Sum.inr 798, 1), (Sum.inr 803, 2), (Sum.inr 805, 1), (Sum.inr 840, 1), (Sum.inr 841, 2), (Sum.inr 847, 2), (Sum.inr 848, 2), (Sum.inr 850, 4), (Sum.inr 998, 1), (Sum.inr 1073, 1), (Sum.inr 1079, 2), (Sum.inr 1081, 1), (Sum.inr 4068, 1)]

def sourceForm1817 : Integer.Sparse Master := [(Sum.inr 732, 1), (Sum.inr 737, 1), (Sum.inr 739, 2), (Sum.inr 810, 1), (Sum.inr 1648, 1), (Sum.inr 4068, -1)]

def sourceForm1818 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4113, 1), (Sum.inr 4118, 1), (Sum.inr 4119, 2), (Sum.inr 4126, 1), (Sum.inr 4209, 1), (Sum.inr 4210, 2), (Sum.inr 4217, 1), (Sum.inr 4249, 2), (Sum.inr 4252, 1), (Sum.inr 4264, 2), (Sum.inr 4265, 2), (Sum.inr 4267, 1), (Sum.inr 4268, 4), (Sum.inr 4275, 1), (Sum.inr 4283, 2), (Sum.inr 4399, 1), (Sum.inr 4458, 2), (Sum.inr 4461, 1), (Sum.inr 4502, 1)]

def sourceForm1821 : Integer.Sparse Master := [(Sum.inr 4057, 2), (Sum.inr 4058, 1), (Sum.inr 4059, 2), (Sum.inr 4063, 2), (Sum.inr 4064, 2), (Sum.inr 4065, 4), (Sum.inr 4068, 2), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4071, 2), (Sum.inr 4080, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2)]

def sourceForm1822 : Integer.Sparse Master := [(Sum.inr 1700, 1), (Sum.inr 3057, 1), (Sum.inr 3072, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def sourceForm1823 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1700, 1), (Sum.inr 1708, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1824 : Integer.Sparse Master := [(Sum.inr 597, 1), (Sum.inr 1038, 1), (Sum.inr 1056, 1), (Sum.inr 1079, 3), (Sum.inr 4084, -1)]

def sourceForm1825 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 3286, 3), (Sum.inr 3292, 1), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def sourceForm1826 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1699, 1), (Sum.inr 1706, 3), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

def sourceForm1827 : Integer.Sparse Master := [(Sum.inr 1316, 3), (Sum.inr 1319, 1), (Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 4091, -1)]

def sourceForm1828 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 3239, 3), (Sum.inr 3244, 1), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

def sourceForm1831 : Integer.Sparse Master := [(Sum.inr 1256, 1), (Sum.inr 2628, 1), (Sum.inr 2671, 1), (Sum.inr 2747, 3), (Sum.inr 4087, -1)]

def sourceForm1832 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 3057, 1), (Sum.inr 3289, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def sourceForm1833 : Integer.Sparse Master := [(Sum.inr 1126, 1), (Sum.inr 1127, 1), (Sum.inr 1130, 2), (Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 4092, -1)]

def sourceForm1834 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 1260, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def sourceForm1835 : Integer.Sparse Master := [(Sum.inr 1636, 2), (Sum.inr 1638, 1), (Sum.inr 1644, 1), (Sum.inr 1706, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

def sourceForm1836 : Integer.Sparse Master := [(Sum.inr 1593, 1), (Sum.inr 1595, 1), (Sum.inr 1600, 2), (Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

def sourceForm1837 : Integer.Sparse Master := [(Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

def sourceForm1838 : Integer.Sparse Master := [(Sum.inr 1600, 1), (Sum.inr 3239, 1), (Sum.inr 3286, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

def sourceForm1839 : Integer.Sparse Master := [(Sum.inr 1706, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 2), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

def sourceForm1841 : Integer.Sparse Master := [(Sum.inr 1648, 1), (Sum.inr 3072, 1), (Sum.inr 3286, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def sourceForm1842 : Integer.Sparse Master := [(Sum.inr 1636, 1), (Sum.inr 1639, 1), (Sum.inr 1641, 1), (Sum.inr 1648, 1), (Sum.inr 1708, 1), (Sum.inr 3303, 1), (Sum.inr 4068, -1)]

def sourceForm1843 : Integer.Sparse Master := [(Sum.inr 4164, 1), (Sum.inr 4165, 3), (Sum.inr 4182, 1), (Sum.inr 4537, 3), (Sum.inr 4550, 1), (Sum.inr 4569, 1), (Sum.inr 4570, 3), (Sum.inr 4618, 3), (Sum.inr 4619, 6), (Sum.inr 4623, 3), (Sum.inr 5166, 1), (Sum.inr 5301, 1), (Sum.inr 5306, 3)]

def sourceForm1844 : Integer.Sparse Master := [(Sum.inr 592, 1), (Sum.inr 593, 3), (Sum.inr 610, 1), (Sum.inr 1122, 3), (Sum.inr 1135, 1), (Sum.inr 1187, 1), (Sum.inr 1188, 3), (Sum.inr 1293, 3), (Sum.inr 1294, 6), (Sum.inr 1305, 3), (Sum.inr 2953, 1), (Sum.inr 3053, 1), (Sum.inr 3120, 3)]

def sourceForm1845 : Integer.Sparse Master := [(Sum.inr 4169, 1), (Sum.inr 4170, 1), (Sum.inr 4173, 3), (Sum.inr 4540, 1), (Sum.inr 4542, 3), (Sum.inr 4599, 3), (Sum.inr 4600, 3), (Sum.inr 4601, 1), (Sum.inr 4603, 6), (Sum.inr 4606, 3), (Sum.inr 5162, 1), (Sum.inr 5273, 1), (Sum.inr 5290, 3)]

def sourceForm1846 : Integer.Sparse Master := [(Sum.inr 597, 1), (Sum.inr 598, 1), (Sum.inr 601, 3), (Sum.inr 1125, 1), (Sum.inr 1127, 3), (Sum.inr 1233, 3), (Sum.inr 1234, 3), (Sum.inr 1237, 6), (Sum.inr 1265, 1), (Sum.inr 1266, 3), (Sum.inr 2957, 1), (Sum.inr 3099, 3), (Sum.inr 3111, 1)]

def sourceForm1847 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1503, 1), (Sum.inr 1508, 3), (Sum.inr 2688, 1), (Sum.inr 2702, 3), (Sum.inr 3257, 3), (Sum.inr 3289, 3), (Sum.inr 3292, 1), (Sum.inr 3294, 6), (Sum.inr 3299, 3), (Sum.inr 3546, 1), (Sum.inr 3563, 1), (Sum.inr 3581, 3)]

def sourceForm1848 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 640, 3), (Sum.inr 651, 1), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def sourceForm1850 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 1073, 3), (Sum.inr 1081, 1), (Sum.inr 1228, 3), (Sum.inr 1235, 1), (Sum.inr 1256, 1), (Sum.inr 1260, 3), (Sum.inr 1286, 3), (Sum.inr 1291, 6), (Sum.inr 1299, 3), (Sum.inr 1405, 1), (Sum.inr 1435, 1), (Sum.inr 1441, 3)]

def sourceForm1851 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 1648, 3), (Sum.inr 1726, 1), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def sourceForm1852 : Integer.Sparse Master := [(Sum.inr 4171, 1), (Sum.inr 4172, 2), (Sum.inr 4175, 2), (Sum.inr 4541, 2), (Sum.inr 4544, 2), (Sum.inr 4601, 2), (Sum.inr 4602, 4), (Sum.inr 4606, 2), (Sum.inr 4622, 2), (Sum.inr 4623, 2), (Sum.inr 4624, 4), (Sum.inr 5167, 1), (Sum.inr 5292, 2), (Sum.inr 5307, 2)]

def sourceForm1853 : Integer.Sparse Master := [(Sum.inr 599, 1), (Sum.inr 600, 2), (Sum.inr 603, 2), (Sum.inr 1126, 2), (Sum.inr 1129, 2), (Sum.inr 1235, 2), (Sum.inr 1236, 4), (Sum.inr 1240, 2), (Sum.inr 1299, 2), (Sum.inr 1300, 2), (Sum.inr 1301, 4), (Sum.inr 2958, 1), (Sum.inr 3100, 2), (Sum.inr 3122, 2)]

def sourceForm1854 : Integer.Sparse Master := [(Sum.inr 4456, 2), (Sum.inr 4495, 4), (Sum.inr 4497, 4), (Sum.inr 4599, 4), (Sum.inr 4601, 4), (Sum.inr 4616, 4), (Sum.inr 4618, 4), (Sum.inr 4622, 4)]

def sourceForm1855 : Integer.Sparse Master := [(Sum.inr 1228, 1), (Sum.inr 2503, 1), (Sum.inr 2703, 1), (Sum.inr 2718, 2), (Sum.inr 2728, 1), (Sum.inr 4090, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1856 : Integer.Sparse Master := [(Sum.inr 4149, 1), (Sum.inr 4150, 3), (Sum.inr 4169, 1), (Sum.inr 4544, 3), (Sum.inr 4550, 1), (Sum.inr 4589, 3), (Sum.inr 4590, 6), (Sum.inr 4599, 3), (Sum.inr 4606, 3), (Sum.inr 4618, 1), (Sum.inr 5100, 1), (Sum.inr 5257, 3), (Sum.inr 5273, 1)]

def sourceForm1857 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 578, 3), (Sum.inr 597, 1), (Sum.inr 1161, 1), (Sum.inr 1162, 3), (Sum.inr 1212, 3), (Sum.inr 1213, 6), (Sum.inr 1233, 3), (Sum.inr 1266, 3), (Sum.inr 1298, 1), (Sum.inr 2999, 1), (Sum.inr 3087, 3), (Sum.inr 3111, 1)]

def sourceForm1858 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1502, 1), (Sum.inr 1504, 3), (Sum.inr 3263, 3), (Sum.inr 3269, 1), (Sum.inr 3288, 3), (Sum.inr 3289, 3), (Sum.inr 3290, 6), (Sum.inr 3299, 3), (Sum.inr 3304, 1), (Sum.inr 3469, 1), (Sum.inr 3532, 3), (Sum.inr 3546, 1)]

def sourceForm1859 : Integer.Sparse Master := [(Sum.inr 625, 3), (Sum.inr 629, 1), (Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

def sourceForm1860 : Integer.Sparse Master := [(Sum.inr 4139, 3), (Sum.inr 4143, 1), (Sum.inr 4171, 1), (Sum.inr 4513, 3), (Sum.inr 4516, 1), (Sum.inr 4581, 3), (Sum.inr 4601, 1), (Sum.inr 4602, 6), (Sum.inr 4606, 3), (Sum.inr 4622, 3), (Sum.inr 5202, 1), (Sum.inr 5283, 1), (Sum.inr 5292, 3)]

def sourceForm1861 : Integer.Sparse Master := [(Sum.inr 567, 3), (Sum.inr 571, 1), (Sum.inr 599, 1), (Sum.inr 1097, 3), (Sum.inr 1100, 1), (Sum.inr 1200, 3), (Sum.inr 1235, 1), (Sum.inr 1236, 6), (Sum.inr 1240, 3), (Sum.inr 1299, 3), (Sum.inr 2880, 1), (Sum.inr 3076, 1), (Sum.inr 3100, 3)]

def sourceForm1863 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 2398, 1), (Sum.inr 2669, 2), (Sum.inr 2676, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

def sourceForm1864 : Integer.Sparse Master := [(Sum.inr 1187, 1), (Sum.inr 2402, 1), (Sum.inr 2671, 4), (Sum.inr 4087, -1)]

def sourceForm1865 : Integer.Sparse Master := [(Sum.inr 1100, 4), (Sum.inr 1187, 1), (Sum.inr 2402, 1), (Sum.inr 4087, -1)]

def sourceForm1867 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 2127, 1), (Sum.inr 2214, 1), (Sum.inr 2250, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def sourceForm1868 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 2098, 1), (Sum.inr 2202, 1), (Sum.inr 2240, 1), (Sum.inr 2250, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def sourceForm1869 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 2100, 1), (Sum.inr 2204, 1), (Sum.inr 2241, 3), (Sum.inr 4079, -1)]

def sourceForm1870 : Integer.Sparse Master := [(Sum.inr 732, 3), (Sum.inr 736, 1), (Sum.inr 805, 1), (Sum.inr 1644, 1), (Sum.inr 4068, -1)]

def sourceForm1871 : Integer.Sparse Master := [(Sum.inr 4150, 2), (Sum.inr 4152, 2), (Sum.inr 4171, 1), (Sum.inr 4364, 2), (Sum.inr 4366, 2), (Sum.inr 4438, 2), (Sum.inr 4439, 4), (Sum.inr 4456, 2), (Sum.inr 4458, 4), (Sum.inr 4461, 2), (Sum.inr 4497, 2), (Sum.inr 4864, 1), (Sum.inr 4887, 2), (Sum.inr 4893, 2)]

def sourceForm1872 : Integer.Sparse Master := [(Sum.inr 1504, 2), (Sum.inr 1506, 1), (Sum.inr 1510, 2), (Sum.inr 1703, 2), (Sum.inr 1705, 2), (Sum.inr 1706, 2), (Sum.inr 1711, 2), (Sum.inr 1713, 4), (Sum.inr 1724, 4), (Sum.inr 1726, 2), (Sum.inr 1737, 2), (Sum.inr 2241, 1), (Sum.inr 2243, 2), (Sum.inr 2263, 2)]

def sourceForm1873 : Integer.Sparse Master := [(Sum.inr 599, 1), (Sum.inr 1039, 3), (Sum.inr 1081, 2), (Sum.inr 4083, -1)]

def sourceForm1874 : Integer.Sparse Master := [(Sum.inr 4098, 2), (Sum.inr 4100, 2), (Sum.inr 4113, 1), (Sum.inr 4341, 2), (Sum.inr 4344, 2), (Sum.inr 4396, 4), (Sum.inr 4399, 2), (Sum.inr 4417, 2), (Sum.inr 4457, 2), (Sum.inr 4458, 4), (Sum.inr 4495, 2), (Sum.inr 5167, 1), (Sum.inr 5257, 2), (Sum.inr 5292, 2)]

def sourceForm1875 : Integer.Sparse Master := [(Sum.inr 535, 2), (Sum.inr 537, 2), (Sum.inr 550, 1), (Sum.inr 919, 2), (Sum.inr 922, 2), (Sum.inr 977, 4), (Sum.inr 980, 2), (Sum.inr 998, 2), (Sum.inr 1040, 2), (Sum.inr 1041, 4), (Sum.inr 1079, 2), (Sum.inr 2593, 1), (Sum.inr 2721, 2), (Sum.inr 2766, 2)]

def sourceForm1876 : Integer.Sparse Master := [(Sum.inr 4249, 2), (Sum.inr 4252, 1), (Sum.inr 4263, 2), (Sum.inr 4449, 4), (Sum.inr 4451, 2), (Sum.inr 4455, 2), (Sum.inr 4456, 4), (Sum.inr 4469, 2), (Sum.inr 4473, 2), (Sum.inr 4495, 2), (Sum.inr 4497, 2), (Sum.inr 4599, 2), (Sum.inr 4601, 2), (Sum.inr 4622, 1)]

def sourceForm1877 : Integer.Sparse Master := [(Sum.inr 1070, 1), (Sum.inr 2043, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def sourceForm1878 : Integer.Sparse Master := [(Sum.inr 1071, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 2), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

def sourceForm1879 : Integer.Sparse Master := [(Sum.inr 1073, 1), (Sum.inr 2046, 1), (Sum.inr 2227, 1), (Sum.inr 2260, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def sourceForm1880 : Integer.Sparse Master := [(Sum.inr 4169, 1), (Sum.inr 4172, 1), (Sum.inr 4173, 1), (Sum.inr 4176, 2), (Sum.inr 4341, 1), (Sum.inr 4342, 1), (Sum.inr 4345, 2), (Sum.inr 4455, 1), (Sum.inr 4457, 1), (Sum.inr 4459, 2), (Sum.inr 4473, 1), (Sum.inr 4474, 1), (Sum.inr 4475, 2), (Sum.inr 4495, 2), (Sum.inr 4498, 2), (Sum.inr 4499, 2), (Sum.inr 4503, 2), (Sum.inr 4831, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4895, 2)]

def sourceForm1881 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1512, 2), (Sum.inr 1664, 1), (Sum.inr 1665, 1), (Sum.inr 1668, 2), (Sum.inr 1698, 1), (Sum.inr 1699, 1), (Sum.inr 1707, 1), (Sum.inr 1708, 2), (Sum.inr 1709, 1), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1727, 2), (Sum.inr 1728, 2), (Sum.inr 1739, 2), (Sum.inr 2191, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2265, 2)]

def sourceForm1884 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4171, 1), (Sum.inr 4175, 3), (Sum.inr 4182, 1), (Sum.inr 4344, 3), (Sum.inr 4351, 1), (Sum.inr 4456, 3), (Sum.inr 4458, 6), (Sum.inr 4461, 3), (Sum.inr 4497, 1), (Sum.inr 4502, 3), (Sum.inr 4833, 1), (Sum.inr 4893, 3)]

def sourceForm1885 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 2219, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

def sourceForm1886 : Integer.Sparse Master := [(Sum.inr 996, 1), (Sum.inr 1941, 1), (Sum.inr 2213, 2), (Sum.inr 2225, 2), (Sum.inr 4082, -1)]

def sourceForm1887 : Integer.Sparse Master := [(Sum.inr 4079, 1), (Sum.inr 4143, 4), (Sum.inr 4164, 1), (Sum.inr 4306, 4), (Sum.inr 4399, 12), (Sum.inr 4451, 4), (Sum.inr 4833, 4)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1889 : Integer.Sparse Master := [(Sum.inr 4068, 1), (Sum.inr 4100, 3), (Sum.inr 4104, 1), (Sum.inr 4117, 1), (Sum.inr 4232, 3), (Sum.inr 4236, 1), (Sum.inr 4249, 6), (Sum.inr 4252, 3), (Sum.inr 4263, 3), (Sum.inr 4267, 3), (Sum.inr 4451, 1), (Sum.inr 4456, 3), (Sum.inr 4497, 1)]

def sourceForm1890 : Integer.Sparse Master := [(Sum.inr 4056, 1), (Sum.inr 4057, 4), (Sum.inr 4063, 4), (Sum.inr 4068, 4), (Sum.inr 4069, 12), (Sum.inr 4079, 1), (Sum.inr 4083, 4)]

def sourceForm1891 : Integer.Sparse Master := [(Sum.inr 940, 1), (Sum.inr 1820, 1), (Sum.inr 1971, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

def sourceForm1892 : Integer.Sparse Master := [(Sum.inr 2220, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def sourceForm1893 : Integer.Sparse Master := [(Sum.inr 931, 1), (Sum.inr 1813, 1), (Sum.inr 1965, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

def sourceForm1894 : Integer.Sparse Master := [(Sum.inr 914, 1), (Sum.inr 1797, 1), (Sum.inr 1957, 1), (Sum.inr 1980, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

def sourceForm1895 : Integer.Sparse Master := [(Sum.inr 949, 1), (Sum.inr 1828, 1), (Sum.inr 1976, 1), (Sum.inr 2092, 2), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def sourceForm1897 : Integer.Sparse Master := [(Sum.inr 2219, 1), (Sum.inr 2220, 2), (Sum.inr 2221, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

def sourceForm1898 : Integer.Sparse Master := [(Sum.inr 925, 1), (Sum.inr 1808, 1), (Sum.inr 1961, 1), (Sum.inr 2035, 1), (Sum.inr 2054, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def sourceForm1899 : Integer.Sparse Master := [(Sum.inr 1137, 1), (Sum.inr 2340, 1), (Sum.inr 2430, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def sourceForm1900 : Integer.Sparse Master := [(Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3358, 1), (Sum.inr 3437, 1), (Sum.inr 3472, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

def sourceForm1901 : Integer.Sparse Master := [(Sum.inr 1910, 1), (Sum.inr 1916, 1), (Sum.inr 1917, 1), (Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

def sourceForm1902 : Integer.Sparse Master := [(Sum.inr 2201, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

def sourceForm1903 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 1790, 1), (Sum.inr 1973, 1), (Sum.inr 2009, 1), (Sum.inr 2020, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

def sourceForm1904 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 2323, 1), (Sum.inr 2440, 1), (Sum.inr 2471, 2), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

def sourceForm1905 : Integer.Sparse Master := [(Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 3350, 1), (Sum.inr 3466, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

def sourceForm1907 : Integer.Sparse Master := [(Sum.inr 909, 1), (Sum.inr 1793, 1), (Sum.inr 1976, 1), (Sum.inr 2010, 2), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

def sourceForm1908 : Integer.Sparse Master := [(Sum.inr 1903, 1), (Sum.inr 1904, 1), (Sum.inr 1913, 1), (Sum.inr 1925, 1), (Sum.inr 2196, 1), (Sum.inr 3464, 1), (Sum.inr 4080, -1)]

def sourceForm1909 : Integer.Sparse Master := [(Sum.inr 954, 1), (Sum.inr 1832, 1), (Sum.inr 1980, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def sourceForm1910 : Integer.Sparse Master := [(Sum.inr 945, 1), (Sum.inr 1825, 1), (Sum.inr 1973, 1), (Sum.inr 2090, 1), (Sum.inr 2107, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

def sourceForm1911 : Integer.Sparse Master := [(Sum.inr 1121, 1), (Sum.inr 2327, 1), (Sum.inr 2423, 1), (Sum.inr 2443, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

def sourceForm1912 : Integer.Sparse Master := [(Sum.inr 1946, 1), (Sum.inr 2259, 1), (Sum.inr 3355, 1), (Sum.inr 3434, 1), (Sum.inr 3481, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

def sourceForm1913 : Integer.Sparse Master := [(Sum.inr 2259, 2), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 2287, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

def sourceForm1914 : Integer.Sparse Master := [(Sum.inr 1923, 1), (Sum.inr 1927, 1), (Sum.inr 1928, 1), (Sum.inr 1949, 1), (Sum.inr 2217, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

def sourceForm1915 : Integer.Sparse Master := [(Sum.inr 1146, 1), (Sum.inr 2346, 1), (Sum.inr 2435, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

def sourceForm1916 : Integer.Sparse Master := [(Sum.inr 1951, 1), (Sum.inr 2267, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

def sourceForm1917 : Integer.Sparse Master := [(Sum.inr 1132, 1), (Sum.inr 2335, 1), (Sum.inr 2426, 1), (Sum.inr 2495, 1), (Sum.inr 2512, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

def sourceForm1918 : Integer.Sparse Master := [(Sum.inr 1917, 1), (Sum.inr 3343, 1), (Sum.inr 3368, 1), (Sum.inr 3385, 1), (Sum.inr 3468, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

def sourceForm1919 : Integer.Sparse Master := [(Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 3472, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm192 : Integer.Sparse Master := [(Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3196, 1), (Sum.inr 3198, 1), (Sum.inr 3222, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def sourceForm193 : Integer.Sparse Master := [(Sum.inr 1465, 1), (Sum.inr 2474, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def sourceForm197 : Integer.Sparse Master := [(Sum.inr 2233, 1), (Sum.inr 3567, 3), (Sum.inr 3618, 1), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

def sourceForm198 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1015, 1), (Sum.inr 1021, 3), (Sum.inr 2233, 1), (Sum.inr 4083, -1)]

def sourceForm199 : Integer.Sparse Master := [(Sum.inr 1021, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 2243, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

def sourceForm200 : Integer.Sparse Master := [(Sum.inr 2083, 1), (Sum.inr 2084, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 3567, 1), (Sum.inr 4083, -1)]

def sourceForm201 : Integer.Sparse Master := [(Sum.inr 1015, 1), (Sum.inr 2084, 3), (Sum.inr 2233, 2), (Sum.inr 4083, -1)]

def sourceForm203 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 778, 1), (Sum.inr 784, 3), (Sum.inr 2009, 3), (Sum.inr 2012, 3), (Sum.inr 2021, 6), (Sum.inr 2187, 1), (Sum.inr 2192, 3), (Sum.inr 2232, 1), (Sum.inr 2240, 3), (Sum.inr 3847, 3), (Sum.inr 3899, 1), (Sum.inr 3909, 1)]

def sourceForm205 : Integer.Sparse Master := [(Sum.inr 3221, 1), (Sum.inr 3801, 3), (Sum.inr 3899, 1), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

def sourceForm206 : Integer.Sparse Master := [(Sum.inr 1464, 3), (Sum.inr 1467, 1), (Sum.inr 1474, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def sourceForm207 : Integer.Sparse Master := [(Sum.inr 1464, 1), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def sourceForm208 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 3199, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

def sourceForm209 : Integer.Sparse Master := [(Sum.inr 1467, 1), (Sum.inr 3179, 1), (Sum.inr 3199, 3), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def sourceForm210 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 3197, 3), (Sum.inr 3221, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

def sourceForm211 : Integer.Sparse Master := [(Sum.inr 1474, 1), (Sum.inr 2471, 3), (Sum.inr 2707, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def sourceForm214 : Integer.Sparse Master := [(Sum.inr 1354, 3), (Sum.inr 1366, 1), (Sum.inr 1405, 1), (Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3077, 3), (Sum.inr 3146, 3), (Sum.inr 3155, 1), (Sum.inr 3165, 3), (Sum.inr 3179, 1), (Sum.inr 3222, 6), (Sum.inr 3223, 3), (Sum.inr 3227, 3)]

def sourceForm215 : Integer.Sparse Master := [(Sum.inr 2252, 1), (Sum.inr 2507, 1), (Sum.inr 3576, 1), (Sum.inr 3625, 3), (Sum.inr 4084, -1)]

def sourceForm217 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 2131, 1), (Sum.inr 2252, 1), (Sum.inr 2277, 3), (Sum.inr 4084, -1)]

def sourceForm219 : Integer.Sparse Master := [(Sum.inr 1038, 1), (Sum.inr 2104, 1), (Sum.inr 2252, 1), (Sum.inr 2262, 3), (Sum.inr 4084, -1)]

def sourceForm222 : Integer.Sparse Master := [(Sum.inr 2059, 2), (Sum.inr 2063, 1), (Sum.inr 2064, 1), (Sum.inr 2267, 1), (Sum.inr 2670, 2), (Sum.inr 2683, 1), (Sum.inr 2685, 1), (Sum.inr 2740, 1), (Sum.inr 3015, 2), (Sum.inr 3022, 2), (Sum.inr 3024, 2), (Sum.inr 3035, 2), (Sum.inr 3038, 2), (Sum.inr 3049, 1), (Sum.inr 3054, 1), (Sum.inr 3075, 2), (Sum.inr 3098, 1), (Sum.inr 3101, 1), (Sum.inr 3156, 2), (Sum.inr 3161, 1), (Sum.inr 3224, 1)]

def sourceForm223 : Integer.Sparse Master := [(Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 2), (Sum.inr 3626, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1920 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 2320, 1), (Sum.inr 2437, 1), (Sum.inr 2470, 1), (Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

def sourceForm1921 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 3339, 1), (Sum.inr 3443, 1), (Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 4081, -1)]

def sourceForm1923 : Integer.Sparse Master := [(Sum.inr 1317, 1), (Sum.inr 2426, 1), (Sum.inr 2434, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

def sourceForm1924 : Integer.Sparse Master := [(Sum.inr 1155, 1), (Sum.inr 2352, 1), (Sum.inr 2434, 1), (Sum.inr 2524, 1), (Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

def sourceForm1925 : Integer.Sparse Master := [(Sum.inr 1337, 1), (Sum.inr 2437, 1), (Sum.inr 2442, 1), (Sum.inr 2485, 1), (Sum.inr 2618, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

def sourceForm1926 : Integer.Sparse Master := [(Sum.inr 2047, 1), (Sum.inr 3385, 1), (Sum.inr 3443, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

def sourceForm1927 : Integer.Sparse Master := [(Sum.inr 1998, 1), (Sum.inr 2004, 1), (Sum.inr 2006, 1), (Sum.inr 2049, 1), (Sum.inr 2230, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

def sourceForm1929 : Integer.Sparse Master := [(Sum.inr 3468, 2), (Sum.inr 3519, 1), (Sum.inr 3523, 2), (Sum.inr 3615, 1), (Sum.inr 4081, -1)]

def sourceForm1930 : Integer.Sparse Master := [(Sum.inr 2006, 1), (Sum.inr 3339, 1), (Sum.inr 3343, 1), (Sum.inr 3353, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

def sourceForm1931 : Integer.Sparse Master := [(Sum.inr 2118, 1), (Sum.inr 2121, 1), (Sum.inr 2123, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

def sourceForm1932 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 2347, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 2542, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

def sourceForm1933 : Integer.Sparse Master := [(Sum.inr 3432, 1), (Sum.inr 3434, 1), (Sum.inr 3437, 1), (Sum.inr 3481, 1), (Sum.inr 3513, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

def sourceForm1934 : Integer.Sparse Master := [(Sum.inr 1986, 1), (Sum.inr 1989, 1), (Sum.inr 1996, 1), (Sum.inr 2015, 1), (Sum.inr 2203, 1), (Sum.inr 3513, 1), (Sum.inr 4081, -1)]

def sourceForm1935 : Integer.Sparse Master := [(Sum.inr 1996, 1), (Sum.inr 3368, 1), (Sum.inr 3432, 1), (Sum.inr 3468, 1), (Sum.inr 3513, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

def sourceForm1936 : Integer.Sparse Master := [(Sum.inr 2203, 1), (Sum.inr 3468, 1), (Sum.inr 3481, 1), (Sum.inr 3513, 1), (Sum.inr 3530, 1), (Sum.inr 3608, 1), (Sum.inr 4081, -1)]

def sourceForm1937 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 2422, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

def sourceForm1938 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 2349, 1), (Sum.inr 2429, 1), (Sum.inr 2543, 2), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

def sourceForm1939 : Integer.Sparse Master := [(Sum.inr 2071, 1), (Sum.inr 2073, 1), (Sum.inr 2077, 1), (Sum.inr 2086, 1), (Sum.inr 2191, 1), (Sum.inr 3558, 1), (Sum.inr 4079, -1)]

def sourceForm1940 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2456, 1), (Sum.inr 2462, 1), (Sum.inr 2491, 1), (Sum.inr 2698, 1), (Sum.inr 3796, 1), (Sum.inr 4090, -1)]

def sourceForm1942 : Integer.Sparse Master := [(Sum.inr 1992, 1), (Sum.inr 1994, 1), (Sum.inr 2000, 1), (Sum.inr 2031, 1), (Sum.inr 2216, 1), (Sum.inr 3517, 1), (Sum.inr 4080, -1)]

def sourceForm1943 : Integer.Sparse Master := [(Sum.inr 4551, 4), (Sum.inr 4555, 1), (Sum.inr 4559, 2), (Sum.inr 4625, 2), (Sum.inr 4970, 4), (Sum.inr 4979, 1), (Sum.inr 5113, 2), (Sum.inr 5168, 4), (Sum.inr 5171, 4), (Sum.inr 5176, 2), (Sum.inr 5308, 2), (Sum.inr 5312, 1), (Sum.inr 5441, 1)]

def sourceForm1944 : Integer.Sparse Master := [(Sum.inr 1136, 4), (Sum.inr 1140, 1), (Sum.inr 1145, 2), (Sum.inr 1307, 2), (Sum.inr 2815, 4), (Sum.inr 2820, 1), (Sum.inr 2894, 2), (Sum.inr 2963, 4), (Sum.inr 2965, 4), (Sum.inr 2968, 2), (Sum.inr 3124, 2), (Sum.inr 3126, 1), (Sum.inr 4037, 1)]

def sourceForm1945 : Integer.Sparse Master := [(Sum.inr 4346, 4), (Sum.inr 4350, 1), (Sum.inr 4360, 2), (Sum.inr 4460, 2), (Sum.inr 4943, 4), (Sum.inr 4952, 1), (Sum.inr 5033, 2), (Sum.inr 5075, 4), (Sum.inr 5169, 4), (Sum.inr 5177, 2), (Sum.inr 5261, 1), (Sum.inr 5293, 2), (Sum.inr 5487, 1)]

def sourceForm1946 : Integer.Sparse Master := [(Sum.inr 924, 4), (Sum.inr 928, 1), (Sum.inr 938, 2), (Sum.inr 1043, 2), (Sum.inr 2334, 4), (Sum.inr 2344, 1), (Sum.inr 2425, 2), (Sum.inr 2482, 4), (Sum.inr 2595, 4), (Sum.inr 2605, 2), (Sum.inr 2726, 1), (Sum.inr 2767, 2), (Sum.inr 4000, 1)]

def sourceForm1947 : Integer.Sparse Master := [(Sum.inr 4352, 2), (Sum.inr 4356, 1), (Sum.inr 4361, 1), (Sum.inr 4463, 1), (Sum.inr 4546, 2), (Sum.inr 4558, 1), (Sum.inr 4625, 1), (Sum.inr 4948, 2), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5037, 2), (Sum.inr 5078, 2), (Sum.inr 5169, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 2), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5294, 1), (Sum.inr 5296, 1), (Sum.inr 5309, 1), (Sum.inr 5442, 1)]

def sourceForm1948 : Integer.Sparse Master := [(Sum.inr 930, 2), (Sum.inr 934, 1), (Sum.inr 939, 1), (Sum.inr 1046, 1), (Sum.inr 1131, 2), (Sum.inr 1144, 1), (Sum.inr 1304, 1), (Sum.inr 2339, 2), (Sum.inr 2345, 1), (Sum.inr 2429, 2), (Sum.inr 2434, 2), (Sum.inr 2485, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 2), (Sum.inr 2604, 1), (Sum.inr 2768, 1), (Sum.inr 2770, 1), (Sum.inr 2960, 2), (Sum.inr 2969, 1), (Sum.inr 3123, 1), (Sum.inr 4001, 1)]

def sourceForm1949 : Integer.Sparse Master := [(Sum.inr 4807, 4), (Sum.inr 4841, 2), (Sum.inr 4843, 2), (Sum.inr 4871, 2), (Sum.inr 5075, 4), (Sum.inr 5078, 4), (Sum.inr 5107, 2), (Sum.inr 5109, 2), (Sum.inr 5128, 2), (Sum.inr 5139, 4), (Sum.inr 5171, 2)]

def sourceForm1950 : Integer.Sparse Master := [(Sum.inr 4237, 2), (Sum.inr 4240, 1), (Sum.inr 4243, 1), (Sum.inr 4276, 1), (Sum.inr 4538, 2), (Sum.inr 4557, 1), (Sum.inr 4621, 1), (Sum.inr 4686, 2), (Sum.inr 4693, 1), (Sum.inr 4723, 2), (Sum.inr 4727, 2), (Sum.inr 4747, 2), (Sum.inr 4869, 2), (Sum.inr 4871, 2), (Sum.inr 4874, 1), (Sum.inr 4898, 1), (Sum.inr 4899, 1), (Sum.inr 5170, 2), (Sum.inr 5176, 1), (Sum.inr 5310, 1), (Sum.inr 5443, 1)]

def sourceForm1951 : Integer.Sparse Master := [(Sum.inr 737, 2), (Sum.inr 740, 1), (Sum.inr 743, 1), (Sum.inr 828, 1), (Sum.inr 1123, 2), (Sum.inr 1143, 1), (Sum.inr 1297, 1), (Sum.inr 1812, 2), (Sum.inr 1819, 1), (Sum.inr 1877, 2), (Sum.inr 1881, 2), (Sum.inr 1926, 2), (Sum.inr 2110, 2), (Sum.inr 2112, 2), (Sum.inr 2115, 1), (Sum.inr 2279, 1), (Sum.inr 2281, 1), (Sum.inr 2954, 2), (Sum.inr 2968, 1), (Sum.inr 3121, 1), (Sum.inr 3889, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1952 : Integer.Sparse Master := [(Sum.inr 4353, 2), (Sum.inr 4358, 1), (Sum.inr 4362, 1), (Sum.inr 4367, 2), (Sum.inr 4374, 1), (Sum.inr 4463, 1), (Sum.inr 4464, 1), (Sum.inr 4699, 2), (Sum.inr 4705, 1), (Sum.inr 4772, 2), (Sum.inr 4777, 2), (Sum.inr 4807, 2), (Sum.inr 4853, 2), (Sum.inr 4866, 2), (Sum.inr 4875, 1), (Sum.inr 4890, 1), (Sum.inr 4895, 1), (Sum.inr 5173, 2), (Sum.inr 5175, 1), (Sum.inr 5295, 1), (Sum.inr 5304, 1)]

def sourceForm1953 : Integer.Sparse Master := [(Sum.inr 1686, 2), (Sum.inr 1687, 1), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1745, 1), (Sum.inr 1748, 1), (Sum.inr 1750, 1), (Sum.inr 2198, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2256, 2), (Sum.inr 2259, 2), (Sum.inr 2260, 2), (Sum.inr 2286, 1), (Sum.inr 2288, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 1), (Sum.inr 2735, 2), (Sum.inr 2761, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1)]

def sourceForm1954 : Integer.Sparse Master := [(Sum.inr 953, 1), (Sum.inr 1831, 1), (Sum.inr 1979, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

def sourceForm1955 : Integer.Sparse Master := [(Sum.inr 1336, 1), (Sum.inr 1973, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2112, 1), (Sum.inr 2952, 1), (Sum.inr 4083, -1)]

def sourceForm1956 : Integer.Sparse Master := [(Sum.inr 4486, 2), (Sum.inr 4490, 1), (Sum.inr 4492, 1), (Sum.inr 4504, 1), (Sum.inr 4807, 2), (Sum.inr 4808, 2), (Sum.inr 4824, 2), (Sum.inr 4827, 2), (Sum.inr 4829, 2), (Sum.inr 4840, 2), (Sum.inr 4841, 1), (Sum.inr 4843, 2), (Sum.inr 4844, 1), (Sum.inr 4853, 2), (Sum.inr 4868, 1), (Sum.inr 4872, 1), (Sum.inr 4881, 1), (Sum.inr 5109, 1), (Sum.inr 5139, 2), (Sum.inr 5174, 1)]

def sourceForm1957 : Integer.Sparse Master := [(Sum.inr 1639, 2), (Sum.inr 1650, 1), (Sum.inr 1651, 1), (Sum.inr 1659, 1), (Sum.inr 2025, 2), (Sum.inr 2060, 1), (Sum.inr 2062, 1), (Sum.inr 2071, 2), (Sum.inr 2079, 2), (Sum.inr 2080, 2), (Sum.inr 2090, 2), (Sum.inr 2092, 2), (Sum.inr 2109, 1), (Sum.inr 2113, 1), (Sum.inr 2121, 2), (Sum.inr 2134, 1), (Sum.inr 2136, 1), (Sum.inr 2601, 1), (Sum.inr 2618, 2), (Sum.inr 2640, 1), (Sum.inr 2642, 1)]

def sourceForm1958 : Integer.Sparse Master := [(Sum.inr 1159, 1), (Sum.inr 2355, 1), (Sum.inr 2436, 1), (Sum.inr 2482, 1), (Sum.inr 2569, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

def sourceForm1959 : Integer.Sparse Master := [(Sum.inr 1320, 1), (Sum.inr 2815, 1), (Sum.inr 2847, 1), (Sum.inr 2865, 2), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

def sourceForm1960 : Integer.Sparse Master := [(Sum.inr 1334, 1), (Sum.inr 2797, 1), (Sum.inr 2802, 1), (Sum.inr 2815, 1), (Sum.inr 2865, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

def sourceForm1961 : Integer.Sparse Master := [(Sum.inr 2018, 1), (Sum.inr 2074, 1), (Sum.inr 2081, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

def sourceForm1962 : Integer.Sparse Master := [(Sum.inr 2015, 1), (Sum.inr 2018, 1), (Sum.inr 2027, 1), (Sum.inr 2047, 1), (Sum.inr 2261, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

def sourceForm1965 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4330, 1), (Sum.inr 4335, 1), (Sum.inr 4347, 1), (Sum.inr 4440, 1), (Sum.inr 4528, 1), (Sum.inr 4535, 1), (Sum.inr 4551, 1), (Sum.inr 4591, 1), (Sum.inr 4930, 2), (Sum.inr 4935, 1), (Sum.inr 4944, 1), (Sum.inr 4948, 1), (Sum.inr 5034, 1), (Sum.inr 5037, 1), (Sum.inr 5065, 1), (Sum.inr 5073, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5104, 1), (Sum.inr 5128, 1), (Sum.inr 5139, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5170, 1), (Sum.inr 5252, 1), (Sum.inr 5259, 1), (Sum.inr 5284, 1), (Sum.inr 5410, 1)]

def sourceForm1966 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 908, 1), (Sum.inr 913, 1), (Sum.inr 925, 1), (Sum.inr 1022, 1), (Sum.inr 1148, 1), (Sum.inr 1154, 1), (Sum.inr 1163, 1), (Sum.inr 1215, 1), (Sum.inr 2320, 1), (Sum.inr 2326, 1), (Sum.inr 2335, 1), (Sum.inr 2422, 1), (Sum.inr 2426, 1), (Sum.inr 2470, 1), (Sum.inr 2526, 1), (Sum.inr 2531, 1), (Sum.inr 2543, 1), (Sum.inr 2558, 1), (Sum.inr 2570, 1), (Sum.inr 2572, 1), (Sum.inr 2576, 1), (Sum.inr 2596, 1), (Sum.inr 2712, 1), (Sum.inr 2753, 1), (Sum.inr 2987, 1), (Sum.inr 2991, 1), (Sum.inr 3000, 1), (Sum.inr 3088, 1), (Sum.inr 3996, 1)]

def sourceForm1967 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1672, 1), (Sum.inr 1676, 1), (Sum.inr 1689, 1), (Sum.inr 1723, 1), (Sum.inr 3260, 1), (Sum.inr 3272, 1), (Sum.inr 3273, 1), (Sum.inr 3291, 1), (Sum.inr 3408, 2), (Sum.inr 3413, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3451, 1), (Sum.inr 3455, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3483, 1), (Sum.inr 3519, 1), (Sum.inr 3523, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3816, 1)]

def sourceForm1968 : Integer.Sparse Master := [(Sum.inr 1136, 1), (Sum.inr 2339, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 2), (Sum.inr 2514, 1), (Sum.inr 4091, -1)]

def sourceForm1971 : Integer.Sparse Master := [(Sum.inr 4199, 1), (Sum.inr 4202, 1), (Sum.inr 4205, 1), (Sum.inr 4219, 1), (Sum.inr 4253, 1), (Sum.inr 4521, 1), (Sum.inr 4525, 1), (Sum.inr 4543, 1), (Sum.inr 4605, 1), (Sum.inr 4633, 1), (Sum.inr 4638, 1), (Sum.inr 4650, 1), (Sum.inr 4707, 1), (Sum.inr 4713, 1), (Sum.inr 4729, 1), (Sum.inr 4764, 1), (Sum.inr 4770, 1), (Sum.inr 4805, 1), (Sum.inr 4807, 2), (Sum.inr 4810, 1), (Sum.inr 4839, 1), (Sum.inr 4843, 1), (Sum.inr 4889, 1), (Sum.inr 4890, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5172, 1), (Sum.inr 5294, 1), (Sum.inr 5435, 1)]

def sourceForm1973 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4331, 1), (Sum.inr 4333, 1), (Sum.inr 4335, 1), (Sum.inr 4336, 1), (Sum.inr 4352, 1), (Sum.inr 4353, 1), (Sum.inr 4442, 1), (Sum.inr 4463, 1), (Sum.inr 4664, 1), (Sum.inr 4670, 1), (Sum.inr 4686, 1), (Sum.inr 4757, 1), (Sum.inr 4764, 1), (Sum.inr 4772, 1), (Sum.inr 4777, 1), (Sum.inr 4792, 1), (Sum.inr 4802, 1), (Sum.inr 4807, 2), (Sum.inr 4811, 1), (Sum.inr 4838, 1), (Sum.inr 4871, 1), (Sum.inr 4890, 1), (Sum.inr 4895, 1), (Sum.inr 5150, 1), (Sum.inr 5151, 1), (Sum.inr 5173, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 1)]

def sourceForm1974 : Integer.Sparse Master := [(Sum.inr 909, 1), (Sum.inr 911, 1), (Sum.inr 914, 1), (Sum.inr 931, 1), (Sum.inr 1024, 1), (Sum.inr 1327, 1), (Sum.inr 1333, 1), (Sum.inr 1340, 1), (Sum.inr 1413, 1), (Sum.inr 2323, 1), (Sum.inr 2327, 1), (Sum.inr 2340, 1), (Sum.inr 2423, 1), (Sum.inr 2430, 1), (Sum.inr 2471, 1), (Sum.inr 2528, 1), (Sum.inr 2532, 1), (Sum.inr 2573, 1), (Sum.inr 2574, 2), (Sum.inr 2575, 1), (Sum.inr 2600, 1), (Sum.inr 2602, 1), (Sum.inr 2754, 1), (Sum.inr 2755, 1), (Sum.inr 3109, 1), (Sum.inr 3204, 1), (Sum.inr 3207, 1), (Sum.inr 3213, 1), (Sum.inr 3229, 1)]

def sourceForm1975 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1684, 1), (Sum.inr 1685, 1), (Sum.inr 1686, 1), (Sum.inr 1688, 1), (Sum.inr 1689, 1), (Sum.inr 1690, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 1), (Sum.inr 2147, 1), (Sum.inr 2164, 1), (Sum.inr 2165, 1), (Sum.inr 2181, 1), (Sum.inr 2182, 1), (Sum.inr 2198, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 1), (Sum.inr 2223, 1), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2227, 1), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 1), (Sum.inr 2681, 1), (Sum.inr 2700, 1), (Sum.inr 2735, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 1)]

def sourceForm1976 : Integer.Sparse Master := [(Sum.inr 913, 1), (Sum.inr 1796, 1), (Sum.inr 1956, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

def sourceForm1977 : Integer.Sparse Master := [(Sum.inr 1326, 1), (Sum.inr 1956, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 2923, 1), (Sum.inr 4083, -1)]

def sourceForm1978 : Integer.Sparse Master := [(Sum.inr 930, 1), (Sum.inr 1812, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 2057, 1), (Sum.inr 4083, -1)]

def sourceForm1979 : Integer.Sparse Master := [(Sum.inr 4414, 1), (Sum.inr 4418, 1), (Sum.inr 4420, 1), (Sum.inr 4425, 1), (Sum.inr 4486, 1), (Sum.inr 4729, 1), (Sum.inr 4741, 1), (Sum.inr 4742, 1), (Sum.inr 4747, 1), (Sum.inr 4779, 1), (Sum.inr 4780, 1), (Sum.inr 4783, 1), (Sum.inr 4792, 1), (Sum.inr 4793, 1), (Sum.inr 4804, 1), (Sum.inr 4807, 2), (Sum.inr 4808, 2), (Sum.inr 4817, 1), (Sum.inr 4819, 1), (Sum.inr 4824, 1), (Sum.inr 4841, 1), (Sum.inr 4843, 1), (Sum.inr 4853, 1), (Sum.inr 4871, 1), (Sum.inr 5078, 2), (Sum.inr 5128, 1), (Sum.inr 5174, 1)]

def sourceForm1981 : Integer.Sparse Master := [(Sum.inr 2390, 1), (Sum.inr 2393, 1), (Sum.inr 2395, 1), (Sum.inr 2404, 1), (Sum.inr 2678, 1), (Sum.inr 3771, 1), (Sum.inr 4088, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm1987 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 1901, 1), (Sum.inr 1912, 2), (Sum.inr 2191, 1), (Sum.inr 3460, 1), (Sum.inr 4079, -1)]

def sourceForm1991 : Integer.Sparse Master := [(Sum.inr 2076, 1), (Sum.inr 2080, 1), (Sum.inr 2082, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 3565, 1), (Sum.inr 4080, -1)]

def sourceForm1993 : Integer.Sparse Master := [(Sum.inr 1325, 1), (Sum.inr 2811, 2), (Sum.inr 2820, 1), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

def sourceForm1996 : Integer.Sparse Master := [(Sum.inr 4367, 2), (Sum.inr 4370, 1), (Sum.inr 4374, 1), (Sum.inr 4476, 1), (Sum.inr 4547, 2), (Sum.inr 4559, 1), (Sum.inr 4609, 1), (Sum.inr 4944, 2), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5034, 2), (Sum.inr 5087, 2), (Sum.inr 5102, 2), (Sum.inr 5111, 1), (Sum.inr 5139, 2), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5268, 1), (Sum.inr 5275, 1), (Sum.inr 5302, 1), (Sum.inr 5413, 1)]

def sourceForm1997 : Integer.Sparse Master := [(Sum.inr 1720, 2), (Sum.inr 1722, 1), (Sum.inr 1729, 1), (Sum.inr 1748, 1), (Sum.inr 3266, 2), (Sum.inr 3277, 1), (Sum.inr 3302, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3451, 2), (Sum.inr 3457, 2), (Sum.inr 3471, 2), (Sum.inr 3472, 2), (Sum.inr 3485, 1), (Sum.inr 3523, 2), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3817, 1)]

def sourceForm1998 : Integer.Sparse Master := [(Sum.inr 4219, 2), (Sum.inr 4225, 1), (Sum.inr 4229, 1), (Sum.inr 4270, 1), (Sum.inr 4514, 2), (Sum.inr 4519, 1), (Sum.inr 4605, 1), (Sum.inr 4650, 2), (Sum.inr 4657, 1), (Sum.inr 4713, 2), (Sum.inr 4719, 2), (Sum.inr 4742, 2), (Sum.inr 4807, 2), (Sum.inr 4839, 2), (Sum.inr 4845, 1), (Sum.inr 4890, 1), (Sum.inr 4896, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5294, 1), (Sum.inr 5443, 1)]

def sourceForm2000 : Integer.Sparse Master := [(Sum.inr 4347, 2), (Sum.inr 4358, 1), (Sum.inr 4361, 1), (Sum.inr 4371, 2), (Sum.inr 4375, 1), (Sum.inr 4478, 1), (Sum.inr 4507, 1), (Sum.inr 4682, 2), (Sum.inr 4693, 1), (Sum.inr 4761, 2), (Sum.inr 4770, 2), (Sum.inr 4817, 2), (Sum.inr 4835, 2), (Sum.inr 4843, 2), (Sum.inr 4846, 1), (Sum.inr 4899, 1), (Sum.inr 4901, 1), (Sum.inr 5205, 2), (Sum.inr 5206, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1)]

def sourceForm2001 : Integer.Sparse Master := [(Sum.inr 1676, 2), (Sum.inr 1694, 1), (Sum.inr 1695, 1), (Sum.inr 1742, 2), (Sum.inr 1743, 1), (Sum.inr 1746, 1), (Sum.inr 1756, 1), (Sum.inr 2153, 2), (Sum.inr 2169, 1), (Sum.inr 2175, 2), (Sum.inr 2186, 2), (Sum.inr 2206, 2), (Sum.inr 2207, 2), (Sum.inr 2229, 1), (Sum.inr 2230, 2), (Sum.inr 2293, 1), (Sum.inr 2294, 1), (Sum.inr 2687, 1), (Sum.inr 2706, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 1)]

def sourceForm2002 : Integer.Sparse Master := [(Sum.inr 939, 1), (Sum.inr 1819, 1), (Sum.inr 1970, 2), (Sum.inr 2062, 1), (Sum.inr 2066, 1), (Sum.inr 4084, -1)]

def sourceForm2003 : Integer.Sparse Master := [(Sum.inr 1315, 1), (Sum.inr 1961, 1), (Sum.inr 1970, 1), (Sum.inr 2062, 2), (Sum.inr 2879, 1), (Sum.inr 4084, -1)]

def sourceForm2008 : Integer.Sparse Master := [(Sum.inr 2128, 2), (Sum.inr 2130, 1), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

def sourceForm2009 : Integer.Sparse Master := [(Sum.inr 2085, 1), (Sum.inr 2087, 1), (Sum.inr 2093, 1), (Sum.inr 2101, 1), (Sum.inr 2242, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

def sourceForm2011 : Integer.Sparse Master := [(Sum.inr 2492, 1), (Sum.inr 2606, 1), (Sum.inr 2608, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 3811, 1), (Sum.inr 4088, -1)]

def sourceForm2012 : Integer.Sparse Master := [(Sum.inr 2030, 1), (Sum.inr 2032, 1), (Sum.inr 2038, 1), (Sum.inr 2048, 1), (Sum.inr 2276, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

def sourceForm2014 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2609, 1), (Sum.inr 2613, 2), (Sum.inr 2694, 1), (Sum.inr 3799, 1), (Sum.inr 4090, -1)]

def sourceForm2015 : Integer.Sparse Master := [(Sum.inr 2008, 1), (Sum.inr 2011, 1), (Sum.inr 2016, 2), (Sum.inr 2242, 1), (Sum.inr 3524, 1), (Sum.inr 4080, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2016 : Integer.Sparse Master := [(Sum.inr 2117, 1), (Sum.inr 2119, 1), (Sum.inr 2122, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2681, 1), (Sum.inr 4082, -1)]

def sourceForm2017 : Integer.Sparse Master := [(Sum.inr 2070, 1), (Sum.inr 2072, 1), (Sum.inr 2075, 1), (Sum.inr 2085, 1), (Sum.inr 2190, 1), (Sum.inr 3557, 1), (Sum.inr 4080, -1)]

def sourceForm2018 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2455, 1), (Sum.inr 2459, 1), (Sum.inr 2490, 1), (Sum.inr 2697, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

def sourceForm2019 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2533, 1), (Sum.inr 2536, 1), (Sum.inr 2565, 1), (Sum.inr 2672, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

def sourceForm2020 : Integer.Sparse Master := [(Sum.inr 1991, 1), (Sum.inr 1993, 1), (Sum.inr 1997, 1), (Sum.inr 2030, 1), (Sum.inr 2215, 1), (Sum.inr 3516, 1), (Sum.inr 4082, -1)]

def sourceForm2021 : Integer.Sparse Master := [(Sum.inr 4365, 2), (Sum.inr 4370, 1), (Sum.inr 4373, 1), (Sum.inr 4460, 1), (Sum.inr 4552, 2), (Sum.inr 4560, 1), (Sum.inr 4621, 1), (Sum.inr 4697, 2), (Sum.inr 4704, 1), (Sum.inr 4771, 2), (Sum.inr 4776, 2), (Sum.inr 4804, 2), (Sum.inr 4865, 2), (Sum.inr 4868, 2), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 4897, 1), (Sum.inr 5161, 2), (Sum.inr 5175, 1), (Sum.inr 5291, 1), (Sum.inr 5305, 1)]

def sourceForm2022 : Integer.Sparse Master := [(Sum.inr 1137, 2), (Sum.inr 1142, 1), (Sum.inr 1146, 1), (Sum.inr 1308, 1), (Sum.inr 1320, 2), (Sum.inr 1325, 1), (Sum.inr 1416, 1), (Sum.inr 2816, 2), (Sum.inr 2821, 1), (Sum.inr 2895, 2), (Sum.inr 2899, 2), (Sum.inr 2941, 2), (Sum.inr 2964, 2), (Sum.inr 2966, 2), (Sum.inr 2967, 1), (Sum.inr 3103, 1), (Sum.inr 3114, 1), (Sum.inr 3125, 1), (Sum.inr 3185, 2), (Sum.inr 3187, 1), (Sum.inr 3230, 1)]

def sourceForm2023 : Integer.Sparse Master := [(Sum.inr 1704, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 1), (Sum.inr 1735, 1), (Sum.inr 2189, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2212, 2), (Sum.inr 2239, 2), (Sum.inr 2242, 2), (Sum.inr 2258, 1), (Sum.inr 2261, 2), (Sum.inr 2264, 1), (Sum.inr 2273, 1), (Sum.inr 2276, 1), (Sum.inr 2289, 1), (Sum.inr 2292, 1), (Sum.inr 2719, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 1), (Sum.inr 2783, 1)]

def sourceForm2024 : Integer.Sparse Master := [(Sum.inr 952, 1), (Sum.inr 1830, 1), (Sum.inr 1978, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def sourceForm2025 : Integer.Sparse Master := [(Sum.inr 1157, 1), (Sum.inr 1972, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2109, 1), (Sum.inr 2588, 1), (Sum.inr 4084, -1)]

def sourceForm2026 : Integer.Sparse Master := [(Sum.inr 943, 1), (Sum.inr 1823, 1), (Sum.inr 1972, 1), (Sum.inr 2106, 1), (Sum.inr 2109, 2), (Sum.inr 4084, -1)]

def sourceForm2027 : Integer.Sparse Master := [(Sum.inr 4233, 2), (Sum.inr 4235, 1), (Sum.inr 4242, 1), (Sum.inr 4272, 1), (Sum.inr 4338, 2), (Sum.inr 4359, 1), (Sum.inr 4454, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4721, 2), (Sum.inr 4726, 2), (Sum.inr 4744, 2), (Sum.inr 4827, 2), (Sum.inr 4845, 1), (Sum.inr 4866, 2), (Sum.inr 4875, 1), (Sum.inr 4896, 1), (Sum.inr 5163, 2), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5451, 1)]

def sourceForm2028 : Integer.Sparse Master := [(Sum.inr 733, 2), (Sum.inr 735, 1), (Sum.inr 742, 1), (Sum.inr 826, 1), (Sum.inr 916, 2), (Sum.inr 937, 1), (Sum.inr 1037, 1), (Sum.inr 1807, 2), (Sum.inr 1818, 1), (Sum.inr 1875, 2), (Sum.inr 1880, 2), (Sum.inr 1924, 2), (Sum.inr 2079, 2), (Sum.inr 2107, 2), (Sum.inr 2116, 1), (Sum.inr 2218, 1), (Sum.inr 2278, 1), (Sum.inr 2590, 2), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 3888, 1)]

def sourceForm2031 : Integer.Sparse Master := [(Sum.inr 4527, 1), (Sum.inr 4528, 1), (Sum.inr 4531, 1), (Sum.inr 4534, 1), (Sum.inr 4535, 1), (Sum.inr 4546, 1), (Sum.inr 4547, 1), (Sum.inr 4591, 1), (Sum.inr 4608, 1), (Sum.inr 4929, 1), (Sum.inr 4934, 1), (Sum.inr 4943, 1), (Sum.inr 4954, 1), (Sum.inr 4965, 1), (Sum.inr 5033, 1), (Sum.inr 5041, 1), (Sum.inr 5072, 1), (Sum.inr 5075, 1), (Sum.inr 5080, 1), (Sum.inr 5101, 1), (Sum.inr 5107, 1), (Sum.inr 5127, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5147, 1), (Sum.inr 5163, 1), (Sum.inr 5258, 1), (Sum.inr 5261, 1), (Sum.inr 5274, 1), (Sum.inr 5409, 1)]

def sourceForm2032 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3260, 1), (Sum.inr 3262, 1), (Sum.inr 3264, 1), (Sum.inr 3266, 1), (Sum.inr 3268, 1), (Sum.inr 3272, 1), (Sum.inr 3291, 1), (Sum.inr 3300, 1), (Sum.inr 3403, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3449, 1), (Sum.inr 3452, 1), (Sum.inr 3458, 1), (Sum.inr 3459, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3484, 1), (Sum.inr 3513, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3545, 1), (Sum.inr 3547, 1), (Sum.inr 3564, 1), (Sum.inr 3807, 1)]

def sourceForm2033 : Integer.Sparse Master := [(Sum.inr 1119, 1), (Sum.inr 2325, 1), (Sum.inr 2347, 1), (Sum.inr 2355, 1), (Sum.inr 2482, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

def sourceForm2034 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 2319, 1), (Sum.inr 2436, 1), (Sum.inr 2479, 1), (Sum.inr 2482, 2), (Sum.inr 4092, -1)]

def sourceForm2035 : Integer.Sparse Master := [(Sum.inr 1131, 1), (Sum.inr 2334, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 2511, 1), (Sum.inr 2517, 1), (Sum.inr 4092, -1)]

def sourceForm2036 : Integer.Sparse Master := [(Sum.inr 4287, 1), (Sum.inr 4289, 1), (Sum.inr 4295, 1), (Sum.inr 4303, 1), (Sum.inr 4322, 1), (Sum.inr 4325, 1), (Sum.inr 4346, 1), (Sum.inr 4401, 1), (Sum.inr 4460, 1), (Sum.inr 4902, 1), (Sum.inr 4907, 1), (Sum.inr 4913, 1), (Sum.inr 4927, 1), (Sum.inr 4943, 1), (Sum.inr 4986, 1), (Sum.inr 5000, 1), (Sum.inr 5033, 1), (Sum.inr 5047, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5081, 1), (Sum.inr 5102, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5169, 1), (Sum.inr 5171, 1), (Sum.inr 5259, 1), (Sum.inr 5261, 1), (Sum.inr 5293, 1), (Sum.inr 5483, 1)]

def sourceForm2039 : Integer.Sparse Master := [(Sum.inr 4326, 1), (Sum.inr 4330, 1), (Sum.inr 4334, 1), (Sum.inr 4346, 1), (Sum.inr 4460, 1), (Sum.inr 4532, 1), (Sum.inr 4536, 1), (Sum.inr 4552, 1), (Sum.inr 4605, 1), (Sum.inr 4663, 1), (Sum.inr 4669, 1), (Sum.inr 4681, 1), (Sum.inr 4756, 1), (Sum.inr 4760, 1), (Sum.inr 4771, 1), (Sum.inr 4776, 1), (Sum.inr 4801, 1), (Sum.inr 4804, 2), (Sum.inr 4810, 1), (Sum.inr 4834, 1), (Sum.inr 4841, 1), (Sum.inr 4868, 1), (Sum.inr 4894, 1), (Sum.inr 4897, 1), (Sum.inr 5133, 1), (Sum.inr 5140, 1), (Sum.inr 5161, 1), (Sum.inr 5258, 1), (Sum.inr 5272, 1)]

def sourceForm2040 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 1118, 1), (Sum.inr 1121, 1), (Sum.inr 1137, 1), (Sum.inr 1271, 1), (Sum.inr 1329, 1), (Sum.inr 1334, 1), (Sum.inr 1342, 1), (Sum.inr 1416, 1), (Sum.inr 2800, 1), (Sum.inr 2803, 1), (Sum.inr 2816, 1), (Sum.inr 2890, 1), (Sum.inr 2895, 1), (Sum.inr 2901, 1), (Sum.inr 2904, 1), (Sum.inr 2940, 1), (Sum.inr 2941, 2), (Sum.inr 2942, 1), (Sum.inr 2964, 1), (Sum.inr 2966, 1), (Sum.inr 3004, 1), (Sum.inr 3089, 1), (Sum.inr 3113, 1), (Sum.inr 3114, 1), (Sum.inr 3205, 1), (Sum.inr 3206, 1), (Sum.inr 3214, 1), (Sum.inr 3230, 1)]

def sourceForm2041 : Integer.Sparse Master := [(Sum.inr 1663, 1), (Sum.inr 1672, 1), (Sum.inr 1674, 1), (Sum.inr 1679, 1), (Sum.inr 1725, 1), (Sum.inr 2140, 1), (Sum.inr 2149, 1), (Sum.inr 2151, 1), (Sum.inr 2155, 1), (Sum.inr 2172, 1), (Sum.inr 2173, 1), (Sum.inr 2176, 1), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2200, 1), (Sum.inr 2203, 2), (Sum.inr 2205, 1), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2226, 1), (Sum.inr 2228, 1), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2292, 1), (Sum.inr 2670, 1), (Sum.inr 2693, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 1), (Sum.inr 2740, 1)]

def sourceForm2042 : Integer.Sparse Master := [(Sum.inr 912, 1), (Sum.inr 1795, 1), (Sum.inr 1955, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

def sourceForm2043 : Integer.Sparse Master := [(Sum.inr 1147, 1), (Sum.inr 1955, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 2), (Sum.inr 2552, 1), (Sum.inr 4084, -1)]

def sourceForm2044 : Integer.Sparse Master := [(Sum.inr 904, 1), (Sum.inr 1789, 1), (Sum.inr 1972, 1), (Sum.inr 2019, 1), (Sum.inr 2022, 2), (Sum.inr 4084, -1)]

def sourceForm2045 : Integer.Sparse Master := [(Sum.inr 924, 1), (Sum.inr 1807, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 1), (Sum.inr 2053, 1), (Sum.inr 2060, 1), (Sum.inr 4084, -1)]

def sourceForm2046 : Integer.Sparse Master := [(Sum.inr 4196, 1), (Sum.inr 4198, 1), (Sum.inr 4204, 1), (Sum.inr 4212, 1), (Sum.inr 4251, 1), (Sum.inr 4320, 1), (Sum.inr 4324, 1), (Sum.inr 4343, 1), (Sum.inr 4398, 1), (Sum.inr 4631, 1), (Sum.inr 4637, 1), (Sum.inr 4644, 1), (Sum.inr 4706, 1), (Sum.inr 4709, 1), (Sum.inr 4728, 1), (Sum.inr 4760, 1), (Sum.inr 4769, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4802, 1), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4832, 1), (Sum.inr 4835, 1), (Sum.inr 4888, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 1), (Sum.inr 5434, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2051 : Integer.Sparse Master := [(Sum.inr 2391, 1), (Sum.inr 2535, 1), (Sum.inr 2539, 1), (Sum.inr 2585, 1), (Sum.inr 2686, 1), (Sum.inr 3770, 1), (Sum.inr 4089, -1)]

def sourceForm2052 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 1924, 1), (Sum.inr 1928, 1), (Sum.inr 1945, 1), (Sum.inr 2215, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

def sourceForm2054 : Integer.Sparse Master := [(Sum.inr 1924, 1), (Sum.inr 2534, 1), (Sum.inr 2538, 1), (Sum.inr 2584, 1), (Sum.inr 2685, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

def sourceForm2056 : Integer.Sparse Master := [(Sum.inr 2377, 1), (Sum.inr 2379, 1), (Sum.inr 2382, 2), (Sum.inr 2661, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

def sourceForm2057 : Integer.Sparse Master := [(Sum.inr 2377, 1), (Sum.inr 2541, 1), (Sum.inr 2551, 2), (Sum.inr 2705, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

def sourceForm2059 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 2540, 1), (Sum.inr 2550, 2), (Sum.inr 2704, 1), (Sum.inr 3459, 1), (Sum.inr 4080, -1)]

def sourceForm2061 : Integer.Sparse Master := [(Sum.inr 2075, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2101, 1), (Sum.inr 2205, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

def sourceForm2062 : Integer.Sparse Master := [(Sum.inr 1123, 1), (Sum.inr 1875, 1), (Sum.inr 1880, 1), (Sum.inr 1914, 1), (Sum.inr 2079, 1), (Sum.inr 2504, 1), (Sum.inr 4080, -1)]

def sourceForm2064 : Integer.Sparse Master := [(Sum.inr 916, 1), (Sum.inr 1799, 1), (Sum.inr 1874, 1), (Sum.inr 1911, 1), (Sum.inr 2018, 1), (Sum.inr 2047, 1), (Sum.inr 4081, -1)]

def sourceForm2065 : Integer.Sparse Master := [(Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2461, 1), (Sum.inr 2477, 1), (Sum.inr 2694, 1), (Sum.inr 3793, 1), (Sum.inr 4090, -1)]

def sourceForm2072 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4346, 2), (Sum.inr 4356, 1), (Sum.inr 4360, 1), (Sum.inr 4505, 1), (Sum.inr 4543, 2), (Sum.inr 4557, 1), (Sum.inr 4605, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4760, 2), (Sum.inr 4769, 2), (Sum.inr 4804, 2), (Sum.inr 4834, 2), (Sum.inr 4841, 2), (Sum.inr 4846, 1), (Sum.inr 4897, 1), (Sum.inr 5099, 2), (Sum.inr 5110, 1), (Sum.inr 5272, 1), (Sum.inr 5274, 1)]

def sourceForm2073 : Integer.Sparse Master := [(Sum.inr 1674, 2), (Sum.inr 1692, 1), (Sum.inr 1693, 1), (Sum.inr 1754, 1), (Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2173, 2), (Sum.inr 2184, 2), (Sum.inr 2185, 2), (Sum.inr 2203, 2), (Sum.inr 2205, 2), (Sum.inr 2226, 1), (Sum.inr 2228, 2), (Sum.inr 2229, 1), (Sum.inr 2292, 1), (Sum.inr 2685, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 2742, 1), (Sum.inr 4084, 1)]

def sourceForm2074 : Integer.Sparse Master := [(Sum.inr 2382, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2403, 1), (Sum.inr 2672, 1), (Sum.inr 3766, 1), (Sum.inr 4088, -1)]

def sourceForm2077 : Integer.Sparse Master := [(Sum.inr 2385, 1), (Sum.inr 2459, 1), (Sum.inr 2468, 1), (Sum.inr 2505, 1), (Sum.inr 2705, 1), (Sum.inr 3766, 1), (Sum.inr 4088, -1)]

def sourceForm2079 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4287, 1), (Sum.inr 4293, 1), (Sum.inr 4295, 1), (Sum.inr 4308, 1), (Sum.inr 4401, 1), (Sum.inr 4521, 1), (Sum.inr 4525, 1), (Sum.inr 4538, 1), (Sum.inr 4583, 1), (Sum.inr 4631, 1), (Sum.inr 4637, 1), (Sum.inr 4649, 1), (Sum.inr 4706, 1), (Sum.inr 4712, 1), (Sum.inr 4721, 1), (Sum.inr 4726, 1), (Sum.inr 4728, 1), (Sum.inr 4736, 1), (Sum.inr 4741, 1), (Sum.inr 4745, 1), (Sum.inr 4779, 1), (Sum.inr 4827, 1), (Sum.inr 4832, 1), (Sum.inr 4834, 1), (Sum.inr 5014, 1), (Sum.inr 5055, 1), (Sum.inr 5094, 1), (Sum.inr 5099, 1), (Sum.inr 5101, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2084 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4304, 2), (Sum.inr 4317, 1), (Sum.inr 4319, 1), (Sum.inr 4431, 1), (Sum.inr 4643, 2), (Sum.inr 4645, 2), (Sum.inr 4655, 1), (Sum.inr 4657, 1), (Sum.inr 4710, 2), (Sum.inr 4719, 2), (Sum.inr 4741, 2), (Sum.inr 4742, 2), (Sum.inr 4754, 1), (Sum.inr 4788, 2), (Sum.inr 4841, 1), (Sum.inr 4843, 1), (Sum.inr 5000, 2), (Sum.inr 5021, 1), (Sum.inr 5107, 1), (Sum.inr 5109, 1)]

def sourceForm2085 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4343, 4), (Sum.inr 4350, 1), (Sum.inr 4359, 2), (Sum.inr 4501, 2), (Sum.inr 4678, 4), (Sum.inr 4691, 1), (Sum.inr 4759, 2), (Sum.inr 4832, 4), (Sum.inr 4837, 4), (Sum.inr 4845, 2), (Sum.inr 4897, 2), (Sum.inr 5261, 1)]

def sourceForm2086 : Integer.Sparse Master := [(Sum.inr 1666, 4), (Sum.inr 1677, 1), (Sum.inr 1683, 2), (Sum.inr 1730, 2), (Sum.inr 2143, 4), (Sum.inr 2159, 1), (Sum.inr 2170, 2), (Sum.inr 2193, 4), (Sum.inr 2208, 4), (Sum.inr 2218, 2), (Sum.inr 2268, 2), (Sum.inr 2726, 1), (Sum.inr 4085, 1)]

def sourceForm2087 : Integer.Sparse Master := [(Sum.inr 937, 1), (Sum.inr 1804, 2), (Sum.inr 1817, 1), (Sum.inr 2056, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

def sourceForm2088 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4286, 1), (Sum.inr 4289, 1), (Sum.inr 4294, 1), (Sum.inr 4302, 1), (Sum.inr 4320, 1), (Sum.inr 4324, 1), (Sum.inr 4338, 1), (Sum.inr 4398, 1), (Sum.inr 4426, 1), (Sum.inr 4630, 1), (Sum.inr 4636, 1), (Sum.inr 4643, 1), (Sum.inr 4658, 1), (Sum.inr 4673, 1), (Sum.inr 4708, 1), (Sum.inr 4720, 1), (Sum.inr 4728, 1), (Sum.inr 4738, 1), (Sum.inr 4741, 1), (Sum.inr 4744, 1), (Sum.inr 4778, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4800, 1), (Sum.inr 4804, 1), (Sum.inr 4827, 1), (Sum.inr 4837, 1), (Sum.inr 4841, 1), (Sum.inr 5075, 1)]

def sourceForm2089 : Integer.Sparse Master := [(Sum.inr 4064, 4), (Sum.inr 4066, 1), (Sum.inr 4067, 2), (Sum.inr 4070, 2), (Sum.inr 4074, 4), (Sum.inr 4076, 1), (Sum.inr 4077, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 4), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4085, 1), (Sum.inr 4092, 1)]

def sourceForm2091 : Integer.Sparse Master := [(Sum.inr 2340, 1), (Sum.inr 2816, 1), (Sum.inr 3162, 1), (Sum.inr 3174, 1), (Sum.inr 3198, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

def sourceForm2092 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def sourceForm2093 : Integer.Sparse Master := [(Sum.inr 910, 1), (Sum.inr 1794, 1), (Sum.inr 1977, 1), (Sum.inr 2012, 1), (Sum.inr 2020, 1), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

def sourceForm2094 : Integer.Sparse Master := [(Sum.inr 2323, 1), (Sum.inr 2800, 1), (Sum.inr 3189, 1), (Sum.inr 3199, 2), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

def sourceForm2095 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2396, 1), (Sum.inr 3476, 1), (Sum.inr 3610, 1), (Sum.inr 3612, 2), (Sum.inr 4082, -1)]

def sourceForm2097 : Integer.Sparse Master := [(Sum.inr 3193, 1), (Sum.inr 3648, 1), (Sum.inr 3653, 1), (Sum.inr 3659, 1), (Sum.inr 3762, 2), (Sum.inr 4088, -1)]

def sourceForm2098 : Integer.Sparse Master := [(Sum.inr 950, 1), (Sum.inr 1829, 1), (Sum.inr 1977, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def sourceForm2099 : Integer.Sparse Master := [(Sum.inr 2327, 1), (Sum.inr 2803, 1), (Sum.inr 3133, 1), (Sum.inr 3138, 1), (Sum.inr 3174, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def sourceForm2100 : Integer.Sparse Master := [(Sum.inr 2274, 1), (Sum.inr 2401, 1), (Sum.inr 3536, 1), (Sum.inr 3612, 1), (Sum.inr 3630, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

def sourceForm2101 : Integer.Sparse Master := [(Sum.inr 2274, 2), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 2288, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

def sourceForm2102 : Integer.Sparse Master := [(Sum.inr 3166, 1), (Sum.inr 3658, 1), (Sum.inr 3660, 1), (Sum.inr 3666, 1), (Sum.inr 3772, 2), (Sum.inr 4089, -1)]

def sourceForm2103 : Integer.Sparse Master := [(Sum.inr 2346, 1), (Sum.inr 2821, 1), (Sum.inr 3129, 2), (Sum.inr 3161, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

def sourceForm2104 : Integer.Sparse Master := [(Sum.inr 3147, 1), (Sum.inr 3372, 1), (Sum.inr 3473, 1), (Sum.inr 3480, 2), (Sum.inr 3611, 1), (Sum.inr 4082, -1)]

def sourceForm2105 : Integer.Sparse Master := [(Sum.inr 1141, 1), (Sum.inr 2343, 1), (Sum.inr 2433, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def sourceForm2106 : Integer.Sparse Master := [(Sum.inr 2335, 1), (Sum.inr 2811, 1), (Sum.inr 2846, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 1), (Sum.inr 3705, 1), (Sum.inr 4092, -1)]

def sourceForm2108 : Integer.Sparse Master := [(Sum.inr 3476, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 3482, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def sourceForm2110 : Integer.Sparse Master := [(Sum.inr 1928, 1), (Sum.inr 2674, 1), (Sum.inr 3348, 1), (Sum.inr 3430, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

def sourceForm2111 : Integer.Sparse Master := [(Sum.inr 1117, 1), (Sum.inr 2324, 1), (Sum.inr 2441, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2112 : Integer.Sparse Master := [(Sum.inr 2320, 1), (Sum.inr 2797, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2981, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

def sourceForm2114 : Integer.Sparse Master := [(Sum.inr 1941, 1), (Sum.inr 3351, 1), (Sum.inr 3476, 2), (Sum.inr 3482, 2), (Sum.inr 4082, -1)]

def sourceForm2115 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 2668, 1), (Sum.inr 3345, 1), (Sum.inr 3476, 1), (Sum.inr 3478, 2), (Sum.inr 4082, -1)]

def sourceForm2118 : Integer.Sparse Master := [(Sum.inr 1807, 1), (Sum.inr 2427, 1), (Sum.inr 2435, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

def sourceForm2119 : Integer.Sparse Master := [(Sum.inr 1347, 1), (Sum.inr 2831, 1), (Sum.inr 2902, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 2964, 1), (Sum.inr 4091, -1)]

def sourceForm2120 : Integer.Sparse Master := [(Sum.inr 2584, 1), (Sum.inr 2668, 1), (Sum.inr 2670, 1), (Sum.inr 2674, 1), (Sum.inr 2681, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

def sourceForm2121 : Integer.Sparse Master := [(Sum.inr 2670, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3614, 1), (Sum.inr 4082, -1)]

def sourceForm2122 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2423, 1), (Sum.inr 2431, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

def sourceForm2123 : Integer.Sparse Master := [(Sum.inr 1151, 1), (Sum.inr 2350, 1), (Sum.inr 2431, 1), (Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2557, 1), (Sum.inr 4092, -1)]

def sourceForm2124 : Integer.Sparse Master := [(Sum.inr 1330, 1), (Sum.inr 2824, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2928, 1), (Sum.inr 4091, -1)]

def sourceForm2125 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2890, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 2), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

def sourceForm2126 : Integer.Sparse Master := [(Sum.inr 2534, 1), (Sum.inr 3430, 1), (Sum.inr 3433, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 2), (Sum.inr 4082, -1)]

def sourceForm2129 : Integer.Sparse Master := [(Sum.inr 2422, 2), (Sum.inr 2432, 1), (Sum.inr 2489, 1), (Sum.inr 2546, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

def sourceForm2130 : Integer.Sparse Master := [(Sum.inr 1152, 1), (Sum.inr 2351, 1), (Sum.inr 2432, 1), (Sum.inr 2546, 1), (Sum.inr 2556, 2), (Sum.inr 4091, -1)]

def sourceForm2132 : Integer.Sparse Master := [(Sum.inr 1997, 2), (Sum.inr 2002, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 3520, 1), (Sum.inr 4082, -1)]

def sourceForm2133 : Integer.Sparse Master := [(Sum.inr 3482, 1), (Sum.inr 3520, 1), (Sum.inr 3522, 2), (Sum.inr 3542, 1), (Sum.inr 3616, 1), (Sum.inr 4082, -1)]

def sourceForm2134 : Integer.Sparse Master := [(Sum.inr 2905, 1), (Sum.inr 3680, 1), (Sum.inr 3683, 1), (Sum.inr 3696, 1), (Sum.inr 3796, 1), (Sum.inr 3873, 1), (Sum.inr 4090, -1)]

def sourceForm2135 : Integer.Sparse Master := [(Sum.inr 4553, 2), (Sum.inr 4557, 1), (Sum.inr 4559, 1), (Sum.inr 4627, 1), (Sum.inr 4686, 2), (Sum.inr 4693, 1), (Sum.inr 4871, 1), (Sum.inr 4970, 2), (Sum.inr 4973, 2), (Sum.inr 4979, 1), (Sum.inr 5114, 2), (Sum.inr 5168, 2), (Sum.inr 5170, 2), (Sum.inr 5171, 1), (Sum.inr 5176, 2), (Sum.inr 5308, 1), (Sum.inr 5310, 1), (Sum.inr 5387, 2), (Sum.inr 5389, 1), (Sum.inr 5441, 1), (Sum.inr 5443, 1)]

def sourceForm2136 : Integer.Sparse Master := [(Sum.inr 1138, 2), (Sum.inr 1143, 1), (Sum.inr 1145, 1), (Sum.inr 1311, 1), (Sum.inr 1812, 2), (Sum.inr 1819, 1), (Sum.inr 2112, 1), (Sum.inr 2815, 2), (Sum.inr 2817, 2), (Sum.inr 2820, 1), (Sum.inr 2896, 2), (Sum.inr 2954, 2), (Sum.inr 2963, 2), (Sum.inr 2965, 1), (Sum.inr 2968, 2), (Sum.inr 3121, 1), (Sum.inr 3124, 1), (Sum.inr 3739, 2), (Sum.inr 3740, 1), (Sum.inr 3889, 1), (Sum.inr 4037, 1)]

def sourceForm2137 : Integer.Sparse Master := [(Sum.inr 4354, 2), (Sum.inr 4359, 1), (Sum.inr 4361, 1), (Sum.inr 4466, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4868, 1), (Sum.inr 4949, 2), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5038, 2), (Sum.inr 5080, 2), (Sum.inr 5163, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5442, 1), (Sum.inr 5451, 1)]

def sourceForm2138 : Integer.Sparse Master := [(Sum.inr 932, 2), (Sum.inr 937, 1), (Sum.inr 939, 1), (Sum.inr 1049, 1), (Sum.inr 1807, 2), (Sum.inr 1818, 1), (Sum.inr 2109, 1), (Sum.inr 2341, 2), (Sum.inr 2345, 1), (Sum.inr 2431, 2), (Sum.inr 2434, 2), (Sum.inr 2488, 2), (Sum.inr 2590, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 1), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 3737, 2), (Sum.inr 3741, 1), (Sum.inr 3888, 1), (Sum.inr 4001, 1)]

def sourceForm2139 : Integer.Sparse Master := [(Sum.inr 4810, 2), (Sum.inr 4845, 1), (Sum.inr 4846, 1), (Sum.inr 4874, 1), (Sum.inr 5080, 4), (Sum.inr 5110, 2), (Sum.inr 5111, 2), (Sum.inr 5129, 2), (Sum.inr 5140, 2), (Sum.inr 5141, 2), (Sum.inr 5151, 2), (Sum.inr 5152, 2), (Sum.inr 5175, 1), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5188, 2), (Sum.inr 5206, 1), (Sum.inr 5207, 1)]

def sourceForm2140 : Integer.Sparse Master := [(Sum.inr 2488, 2), (Sum.inr 2522, 1), (Sum.inr 2523, 1), (Sum.inr 2604, 1), (Sum.inr 2867, 2), (Sum.inr 2888, 1), (Sum.inr 2889, 1), (Sum.inr 2916, 2), (Sum.inr 2930, 2), (Sum.inr 2931, 2), (Sum.inr 2942, 2), (Sum.inr 2943, 2), (Sum.inr 2967, 1), (Sum.inr 2969, 1), (Sum.inr 2990, 2), (Sum.inr 3005, 1), (Sum.inr 3006, 1), (Sum.inr 3095, 1), (Sum.inr 3187, 1), (Sum.inr 3206, 2), (Sum.inr 3216, 1)]

def sourceForm2141 : Integer.Sparse Master := [(Sum.inr 4554, 2), (Sum.inr 4558, 2), (Sum.inr 4628, 1), (Sum.inr 4948, 4), (Sum.inr 4953, 2), (Sum.inr 4974, 2), (Sum.inr 5115, 2), (Sum.inr 5169, 4), (Sum.inr 5174, 2), (Sum.inr 5177, 2), (Sum.inr 5309, 2), (Sum.inr 5390, 1), (Sum.inr 5418, 2), (Sum.inr 5442, 2)]

def sourceForm2142 : Integer.Sparse Master := [(Sum.inr 1139, 2), (Sum.inr 1144, 2), (Sum.inr 1312, 1), (Sum.inr 2339, 4), (Sum.inr 2345, 2), (Sum.inr 2601, 2), (Sum.inr 2818, 2), (Sum.inr 2897, 2), (Sum.inr 2960, 4), (Sum.inr 2969, 2), (Sum.inr 3123, 2), (Sum.inr 3741, 1), (Sum.inr 3933, 2), (Sum.inr 4001, 2)]

def sourceForm2143 : Integer.Sparse Master := [(Sum.inr 4355, 2), (Sum.inr 4360, 2), (Sum.inr 4467, 1), (Sum.inr 4943, 4), (Sum.inr 4950, 2), (Sum.inr 4952, 2), (Sum.inr 5039, 2), (Sum.inr 5081, 2), (Sum.inr 5169, 4), (Sum.inr 5171, 2), (Sum.inr 5293, 2), (Sum.inr 5465, 2), (Sum.inr 5466, 1), (Sum.inr 5487, 2)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2144 : Integer.Sparse Master := [(Sum.inr 933, 2), (Sum.inr 938, 2), (Sum.inr 1050, 1), (Sum.inr 2334, 4), (Sum.inr 2342, 2), (Sum.inr 2344, 2), (Sum.inr 2432, 2), (Sum.inr 2489, 2), (Sum.inr 2595, 4), (Sum.inr 2598, 2), (Sum.inr 2767, 2), (Sum.inr 3931, 2), (Sum.inr 3934, 1), (Sum.inr 4000, 2)]

def sourceForm2145 : Integer.Sparse Master := [(Sum.inr 4811, 2), (Sum.inr 4846, 2), (Sum.inr 4875, 1), (Sum.inr 5081, 4), (Sum.inr 5111, 4), (Sum.inr 5130, 2), (Sum.inr 5141, 4), (Sum.inr 5152, 4), (Sum.inr 5176, 2), (Sum.inr 5177, 1), (Sum.inr 5189, 2), (Sum.inr 5207, 2)]

def sourceForm2146 : Integer.Sparse Master := [(Sum.inr 3482, 2), (Sum.inr 3485, 2), (Sum.inr 3616, 2), (Sum.inr 4082, -1)]

def sourceForm2147 : Integer.Sparse Master := [(Sum.inr 1171, 1), (Sum.inr 2362, 1), (Sum.inr 2529, 1), (Sum.inr 2575, 1), (Sum.inr 2590, 1), (Sum.inr 2600, 1), (Sum.inr 4092, -1)]

def sourceForm2148 : Integer.Sparse Master := [(Sum.inr 1812, 1), (Sum.inr 2892, 1), (Sum.inr 2899, 1), (Sum.inr 2930, 2), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

def sourceForm2149 : Integer.Sparse Master := [(Sum.inr 2396, 1), (Sum.inr 2399, 1), (Sum.inr 2401, 1), (Sum.inr 2405, 1), (Sum.inr 2681, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def sourceForm2152 : Integer.Sparse Master := [(Sum.inr 4332, 1), (Sum.inr 4334, 1), (Sum.inr 4335, 1), (Sum.inr 4357, 1), (Sum.inr 4444, 1), (Sum.inr 4930, 1), (Sum.inr 4933, 1), (Sum.inr 4934, 1), (Sum.inr 4935, 1), (Sum.inr 4948, 1), (Sum.inr 4951, 1), (Sum.inr 4954, 1), (Sum.inr 4970, 1), (Sum.inr 5040, 1), (Sum.inr 5067, 1), (Sum.inr 5078, 1), (Sum.inr 5117, 1), (Sum.inr 5145, 1), (Sum.inr 5147, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5164, 1), (Sum.inr 5170, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5369, 1), (Sum.inr 5410, 1), (Sum.inr 5473, 1)]

def sourceForm2153 : Integer.Sparse Master := [(Sum.inr 910, 1), (Sum.inr 912, 1), (Sum.inr 913, 1), (Sum.inr 935, 1), (Sum.inr 1026, 1), (Sum.inr 2324, 1), (Sum.inr 2325, 1), (Sum.inr 2326, 1), (Sum.inr 2343, 1), (Sum.inr 2347, 1), (Sum.inr 2357, 1), (Sum.inr 2422, 1), (Sum.inr 2433, 1), (Sum.inr 2473, 1), (Sum.inr 2530, 1), (Sum.inr 2531, 1), (Sum.inr 2567, 1), (Sum.inr 2569, 1), (Sum.inr 2570, 1), (Sum.inr 2572, 1), (Sum.inr 2576, 1), (Sum.inr 2591, 1), (Sum.inr 2596, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 3926, 1), (Sum.inr 3936, 1), (Sum.inr 3940, 1), (Sum.inr 3995, 1), (Sum.inr 3996, 1)]

def sourceForm2154 : Integer.Sparse Master := [(Sum.inr 1678, 1), (Sum.inr 1679, 1), (Sum.inr 1682, 1), (Sum.inr 1689, 1), (Sum.inr 1736, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3415, 1), (Sum.inr 3418, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3476, 1), (Sum.inr 3481, 1), (Sum.inr 3530, 1), (Sum.inr 3562, 1), (Sum.inr 3565, 1), (Sum.inr 3580, 1), (Sum.inr 3588, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3764, 1), (Sum.inr 3773, 1), (Sum.inr 3774, 1), (Sum.inr 3816, 1), (Sum.inr 3961, 1)]

def sourceForm2155 : Integer.Sparse Master := [(Sum.inr 2326, 1), (Sum.inr 2802, 1), (Sum.inr 2822, 1), (Sum.inr 2827, 1), (Sum.inr 2931, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def sourceForm2156 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 2822, 1), (Sum.inr 2893, 1), (Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

def sourceForm2157 : Integer.Sparse Master := [(Sum.inr 1338, 1), (Sum.inr 2827, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 4091, -1)]

def sourceForm2160 : Integer.Sparse Master := [(Sum.inr 2399, 1), (Sum.inr 3433, 1), (Sum.inr 3439, 1), (Sum.inr 3485, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def sourceForm2161 : Integer.Sparse Master := [(Sum.inr 2910, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3357, 1), (Sum.inr 3479, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

def sourceForm2168 : Integer.Sparse Master := [(Sum.inr 2355, 1), (Sum.inr 2438, 1), (Sum.inr 2443, 1), (Sum.inr 2488, 1), (Sum.inr 2620, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def sourceForm2169 : Integer.Sparse Master := [(Sum.inr 2352, 1), (Sum.inr 2798, 1), (Sum.inr 2803, 1), (Sum.inr 2817, 1), (Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def sourceForm2170 : Integer.Sparse Master := [(Sum.inr 1321, 1), (Sum.inr 2817, 1), (Sum.inr 2848, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 2885, 1), (Sum.inr 4092, -1)]

def sourceForm2171 : Integer.Sparse Master := [(Sum.inr 2538, 1), (Sum.inr 3345, 1), (Sum.inr 3348, 1), (Sum.inr 3354, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

def sourceForm2172 : Integer.Sparse Master := [(Sum.inr 2048, 1), (Sum.inr 3386, 1), (Sum.inr 3491, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3542, 1), (Sum.inr 4082, -1)]

def sourceForm2175 : Integer.Sparse Master := [(Sum.inr 2799, 1), (Sum.inr 2802, 2), (Sum.inr 2818, 1), (Sum.inr 2868, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2176 : Integer.Sparse Master := [(Sum.inr 1322, 1), (Sum.inr 2818, 1), (Sum.inr 2849, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 2), (Sum.inr 4091, -1)]

def sourceForm2177 : Integer.Sparse Master := [(Sum.inr 1819, 1), (Sum.inr 2812, 2), (Sum.inr 2821, 1), (Sum.inr 2888, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

def sourceForm2180 : Integer.Sparse Master := [(Sum.inr 4372, 2), (Sum.inr 4373, 1), (Sum.inr 4374, 1), (Sum.inr 4480, 1), (Sum.inr 4944, 2), (Sum.inr 4953, 1), (Sum.inr 4965, 2), (Sum.inr 4977, 2), (Sum.inr 4979, 1), (Sum.inr 5044, 2), (Sum.inr 5090, 2), (Sum.inr 5109, 1), (Sum.inr 5199, 2), (Sum.inr 5201, 1), (Sum.inr 5204, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5368, 2), (Sum.inr 5371, 1), (Sum.inr 5413, 1), (Sum.inr 5475, 1)]

def sourceForm2181 : Integer.Sparse Master := [(Sum.inr 1734, 2), (Sum.inr 1735, 1), (Sum.inr 1740, 1), (Sum.inr 1748, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3474, 2), (Sum.inr 3475, 2), (Sum.inr 3480, 2), (Sum.inr 3486, 1), (Sum.inr 3578, 2), (Sum.inr 3579, 1), (Sum.inr 3584, 1), (Sum.inr 3595, 2), (Sum.inr 3596, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3767, 2), (Sum.inr 3775, 1), (Sum.inr 3817, 1), (Sum.inr 3963, 1)]

def sourceForm2182 : Integer.Sparse Master := [(Sum.inr 2345, 1), (Sum.inr 2813, 2), (Sum.inr 2820, 1), (Sum.inr 2889, 1), (Sum.inr 3707, 1), (Sum.inr 4092, -1)]

def sourceForm2189 : Integer.Sparse Master := [(Sum.inr 2533, 1), (Sum.inr 3679, 1), (Sum.inr 3681, 1), (Sum.inr 3695, 1), (Sum.inr 3795, 1), (Sum.inr 3832, 1), (Sum.inr 4088, -1)]

def sourceForm2190 : Integer.Sparse Master := [(Sum.inr 4533, 1), (Sum.inr 4534, 1), (Sum.inr 4535, 1), (Sum.inr 4556, 1), (Sum.inr 4612, 1), (Sum.inr 4929, 1), (Sum.inr 4934, 1), (Sum.inr 4943, 1), (Sum.inr 4955, 1), (Sum.inr 4956, 1), (Sum.inr 4959, 1), (Sum.inr 4966, 1), (Sum.inr 4972, 1), (Sum.inr 5036, 1), (Sum.inr 5075, 1), (Sum.inr 5111, 1), (Sum.inr 5112, 1), (Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5139, 1), (Sum.inr 5141, 1), (Sum.inr 5163, 1), (Sum.inr 5164, 1), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5367, 1), (Sum.inr 5409, 1), (Sum.inr 5428, 1)]

def sourceForm2191 : Integer.Sparse Master := [(Sum.inr 1117, 1), (Sum.inr 1119, 1), (Sum.inr 1120, 1), (Sum.inr 1141, 1), (Sum.inr 1274, 1), (Sum.inr 2349, 1), (Sum.inr 2352, 1), (Sum.inr 2358, 1), (Sum.inr 2618, 1), (Sum.inr 2801, 1), (Sum.inr 2802, 1), (Sum.inr 2819, 1), (Sum.inr 2823, 1), (Sum.inr 2828, 1), (Sum.inr 2898, 1), (Sum.inr 2903, 1), (Sum.inr 2934, 1), (Sum.inr 2937, 1), (Sum.inr 2939, 1), (Sum.inr 2943, 1), (Sum.inr 2955, 1), (Sum.inr 2961, 1), (Sum.inr 3006, 1), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3728, 1), (Sum.inr 3937, 1), (Sum.inr 3941, 1), (Sum.inr 4003, 1), (Sum.inr 4035, 1)]

def sourceForm2192 : Integer.Sparse Master := [(Sum.inr 3267, 1), (Sum.inr 3268, 1), (Sum.inr 3271, 1), (Sum.inr 3272, 1), (Sum.inr 3301, 1), (Sum.inr 3403, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3450, 1), (Sum.inr 3457, 1), (Sum.inr 3468, 1), (Sum.inr 3485, 1), (Sum.inr 3508, 1), (Sum.inr 3510, 1), (Sum.inr 3512, 1), (Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 3522, 1), (Sum.inr 3523, 1), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3757, 1), (Sum.inr 3766, 1), (Sum.inr 3770, 1), (Sum.inr 3807, 1), (Sum.inr 3845, 1)]

def sourceForm2193 : Integer.Sparse Master := [(Sum.inr 2325, 1), (Sum.inr 2348, 1), (Sum.inr 2352, 1), (Sum.inr 2356, 1), (Sum.inr 2561, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def sourceForm2194 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 2348, 1), (Sum.inr 2428, 1), (Sum.inr 2553, 1), (Sum.inr 2554, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

def sourceForm2195 : Integer.Sparse Master := [(Sum.inr 2319, 1), (Sum.inr 2524, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 2), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

def sourceForm2196 : Integer.Sparse Master := [(Sum.inr 1160, 1), (Sum.inr 2356, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 1), (Sum.inr 2590, 1), (Sum.inr 2591, 1), (Sum.inr 4092, -1)]

def sourceForm2197 : Integer.Sparse Master := [(Sum.inr 4323, 1), (Sum.inr 4324, 1), (Sum.inr 4325, 1), (Sum.inr 4349, 1), (Sum.inr 4404, 1), (Sum.inr 4631, 1), (Sum.inr 4637, 1), (Sum.inr 4644, 1), (Sum.inr 4804, 1), (Sum.inr 4902, 1), (Sum.inr 4907, 1), (Sum.inr 4913, 1), (Sum.inr 4928, 1), (Sum.inr 4946, 1), (Sum.inr 4987, 1), (Sum.inr 5003, 1), (Sum.inr 5036, 1), (Sum.inr 5050, 1), (Sum.inr 5075, 1), (Sum.inr 5134, 1), (Sum.inr 5137, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5368, 1), (Sum.inr 5434, 1), (Sum.inr 5483, 1)]

def sourceForm2203 : Integer.Sparse Master := [(Sum.inr 2541, 1), (Sum.inr 3646, 1), (Sum.inr 3650, 2), (Sum.inr 3757, 2), (Sum.inr 4088, -1)]

def sourceForm2207 : Integer.Sparse Master := [(Sum.inr 2456, 1), (Sum.inr 2756, 1), (Sum.inr 3680, 1), (Sum.inr 3776, 1), (Sum.inr 3796, 2), (Sum.inr 4090, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2210 : Integer.Sparse Master := [(Sum.inr 4529, 1), (Sum.inr 4534, 1), (Sum.inr 4536, 1), (Sum.inr 4553, 1), (Sum.inr 4592, 1), (Sum.inr 4664, 1), (Sum.inr 4670, 1), (Sum.inr 4682, 1), (Sum.inr 4853, 1), (Sum.inr 4931, 1), (Sum.inr 4934, 1), (Sum.inr 4949, 1), (Sum.inr 4954, 1), (Sum.inr 4965, 1), (Sum.inr 5038, 1), (Sum.inr 5042, 1), (Sum.inr 5072, 1), (Sum.inr 5074, 1), (Sum.inr 5075, 1), (Sum.inr 5101, 1), (Sum.inr 5105, 1), (Sum.inr 5129, 1), (Sum.inr 5188, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 1), (Sum.inr 5384, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1)]

def sourceForm2211 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2149, 1), (Sum.inr 2153, 1), (Sum.inr 2164, 1), (Sum.inr 2259, 1), (Sum.inr 3258, 1), (Sum.inr 3268, 1), (Sum.inr 3270, 1), (Sum.inr 3295, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3459, 1), (Sum.inr 3462, 1), (Sum.inr 3463, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3475, 1), (Sum.inr 3479, 1), (Sum.inr 3516, 1), (Sum.inr 3533, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1)]

def sourceForm2212 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2325, 1), (Sum.inr 2327, 1), (Sum.inr 2341, 1), (Sum.inr 2488, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def sourceForm2217 : Integer.Sparse Master := [(Sum.inr 4530, 1), (Sum.inr 4535, 2), (Sum.inr 4554, 1), (Sum.inr 4593, 1), (Sum.inr 4930, 2), (Sum.inr 4932, 1), (Sum.inr 4935, 2), (Sum.inr 4944, 2), (Sum.inr 4950, 1), (Sum.inr 5039, 1), (Sum.inr 5043, 1), (Sum.inr 5073, 2), (Sum.inr 5078, 2), (Sum.inr 5104, 2), (Sum.inr 5130, 1), (Sum.inr 5189, 1), (Sum.inr 5259, 2), (Sum.inr 5356, 1), (Sum.inr 5393, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 2)]

def sourceForm2218 : Integer.Sparse Master := [(Sum.inr 3261, 1), (Sum.inr 3272, 2), (Sum.inr 3274, 1), (Sum.inr 3297, 1), (Sum.inr 3408, 2), (Sum.inr 3409, 1), (Sum.inr 3413, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3456, 1), (Sum.inr 3465, 1), (Sum.inr 3467, 2), (Sum.inr 3481, 2), (Sum.inr 3483, 2), (Sum.inr 3520, 1), (Sum.inr 3542, 1), (Sum.inr 3544, 2), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 2)]

def sourceForm2219 : Integer.Sparse Master := [(Sum.inr 2322, 1), (Sum.inr 2326, 2), (Sum.inr 2342, 1), (Sum.inr 2489, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def sourceForm2229 : Integer.Sparse Master := [(Sum.inr 4548, 2), (Sum.inr 4557, 1), (Sum.inr 4560, 1), (Sum.inr 4611, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4699, 2), (Sum.inr 4705, 1), (Sum.inr 4841, 1), (Sum.inr 4881, 1), (Sum.inr 4945, 2), (Sum.inr 5035, 2), (Sum.inr 5099, 2), (Sum.inr 5103, 2), (Sum.inr 5140, 2), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5272, 1), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5302, 1)]

def sourceForm2230 : Integer.Sparse Master := [(Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2228, 1), (Sum.inr 2256, 2), (Sum.inr 2258, 1), (Sum.inr 2267, 1), (Sum.inr 2286, 1), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2670, 2), (Sum.inr 2672, 2), (Sum.inr 2683, 1), (Sum.inr 2686, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 2742, 1), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3054, 1)]

def sourceForm2235 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4549, 2), (Sum.inr 4558, 1), (Sum.inr 4559, 1), (Sum.inr 4612, 1), (Sum.inr 4943, 2), (Sum.inr 4946, 2), (Sum.inr 4952, 1), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5036, 2), (Sum.inr 5101, 2), (Sum.inr 5102, 2), (Sum.inr 5107, 1), (Sum.inr 5109, 1), (Sum.inr 5141, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5367, 2), (Sum.inr 5371, 1), (Sum.inr 5413, 1)]

def sourceForm2236 : Integer.Sparse Master := [(Sum.inr 3265, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3301, 1), (Sum.inr 3411, 2), (Sum.inr 3412, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3450, 2), (Sum.inr 3457, 2), (Sum.inr 3470, 2), (Sum.inr 3471, 2), (Sum.inr 3484, 1), (Sum.inr 3486, 1), (Sum.inr 3522, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3766, 2), (Sum.inr 3775, 1), (Sum.inr 3817, 1), (Sum.inr 4092, 1)]

def sourceForm2238 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4522, 1), (Sum.inr 4526, 2), (Sum.inr 4539, 1), (Sum.inr 4586, 1), (Sum.inr 4902, 2), (Sum.inr 4907, 2), (Sum.inr 4918, 2), (Sum.inr 4926, 1), (Sum.inr 4937, 1), (Sum.inr 5000, 2), (Sum.inr 5025, 1), (Sum.inr 5032, 1), (Sum.inr 5056, 2), (Sum.inr 5063, 1), (Sum.inr 5095, 2), (Sum.inr 5126, 1), (Sum.inr 5248, 2), (Sum.inr 5323, 1), (Sum.inr 5327, 1), (Sum.inr 5367, 2)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm224 : Integer.Sparse Master := [(Sum.inr 1238, 2), (Sum.inr 1244, 1), (Sum.inr 1245, 1), (Sum.inr 1296, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def sourceForm225 : Integer.Sparse Master := [(Sum.inr 1296, 1), (Sum.inr 2138, 1), (Sum.inr 2592, 2), (Sum.inr 2744, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

def sourceForm226 : Integer.Sparse Master := [(Sum.inr 2513, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 2744, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

def sourceForm227 : Integer.Sparse Master := [(Sum.inr 1238, 1), (Sum.inr 2133, 1), (Sum.inr 2513, 1), (Sum.inr 2555, 1), (Sum.inr 2738, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def sourceForm228 : Integer.Sparse Master := [(Sum.inr 2555, 1), (Sum.inr 2559, 1), (Sum.inr 2560, 1), (Sum.inr 2592, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def sourceForm229 : Integer.Sparse Master := [(Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 2), (Sum.inr 2740, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def sourceForm230 : Integer.Sparse Master := [(Sum.inr 2133, 2), (Sum.inr 2136, 1), (Sum.inr 2138, 1), (Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def sourceForm231 : Integer.Sparse Master := [(Sum.inr 1244, 1), (Sum.inr 2136, 1), (Sum.inr 2520, 1), (Sum.inr 2559, 2), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def sourceForm233 : Integer.Sparse Master := [(Sum.inr 1006, 2), (Sum.inr 1010, 1), (Sum.inr 1011, 1), (Sum.inr 1084, 1), (Sum.inr 2405, 2), (Sum.inr 2408, 1), (Sum.inr 2409, 1), (Sum.inr 2463, 2), (Sum.inr 2465, 2), (Sum.inr 2466, 2), (Sum.inr 2513, 2), (Sum.inr 2732, 2), (Sum.inr 2734, 1), (Sum.inr 2735, 2), (Sum.inr 2737, 1), (Sum.inr 2776, 1), (Sum.inr 2781, 1), (Sum.inr 3573, 2), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3889, 1)]

def sourceForm234 : Integer.Sparse Master := [(Sum.inr 1184, 2), (Sum.inr 1186, 1), (Sum.inr 1192, 1), (Sum.inr 1292, 1), (Sum.inr 1610, 2), (Sum.inr 1628, 1), (Sum.inr 1716, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 2906, 2), (Sum.inr 2910, 2), (Sum.inr 2952, 2), (Sum.inr 3024, 2), (Sum.inr 3051, 2), (Sum.inr 3055, 1), (Sum.inr 3098, 1), (Sum.inr 3119, 1), (Sum.inr 3541, 2), (Sum.inr 3549, 1), (Sum.inr 3626, 1), (Sum.inr 3862, 1)]

def sourceForm235 : Integer.Sparse Master := [(Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 2782, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def sourceForm236 : Integer.Sparse Master := [(Sum.inr 1282, 1), (Sum.inr 1422, 2), (Sum.inr 1424, 1), (Sum.inr 1436, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def sourceForm237 : Integer.Sparse Master := [(Sum.inr 1436, 1), (Sum.inr 2759, 2), (Sum.inr 2769, 1), (Sum.inr 2777, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

def sourceForm238 : Integer.Sparse Master := [(Sum.inr 1283, 1), (Sum.inr 2582, 2), (Sum.inr 2651, 1), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def sourceForm239 : Integer.Sparse Master := [(Sum.inr 1422, 1), (Sum.inr 2580, 1), (Sum.inr 2582, 1), (Sum.inr 2600, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

def sourceForm240 : Integer.Sparse Master := [(Sum.inr 1280, 1), (Sum.inr 2580, 1), (Sum.inr 2647, 1), (Sum.inr 2759, 1), (Sum.inr 2773, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def sourceForm241 : Integer.Sparse Master := [(Sum.inr 1280, 2), (Sum.inr 1282, 1), (Sum.inr 1283, 1), (Sum.inr 1306, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def sourceForm244 : Integer.Sparse Master := [(Sum.inr 1060, 2), (Sum.inr 1061, 1), (Sum.inr 1062, 1), (Sum.inr 1088, 1), (Sum.inr 2496, 2), (Sum.inr 2497, 2), (Sum.inr 2498, 2), (Sum.inr 2516, 2), (Sum.inr 2641, 2), (Sum.inr 2642, 1), (Sum.inr 2643, 1), (Sum.inr 2748, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 1), (Sum.inr 2771, 1), (Sum.inr 2777, 2), (Sum.inr 2778, 1), (Sum.inr 2789, 1), (Sum.inr 3086, 2), (Sum.inr 3110, 1), (Sum.inr 3121, 1)]

def sourceForm245 : Integer.Sparse Master := [(Sum.inr 2603, 1), (Sum.inr 3050, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

def sourceForm246 : Integer.Sparse Master := [(Sum.inr 1374, 1), (Sum.inr 2888, 1), (Sum.inr 2978, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

def sourceForm247 : Integer.Sparse Master := [(Sum.inr 2035, 1), (Sum.inr 2597, 1), (Sum.inr 2973, 1), (Sum.inr 2978, 1), (Sum.inr 3052, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

def sourceForm250 : Integer.Sparse Master := [(Sum.inr 3052, 1), (Sum.inr 3540, 2), (Sum.inr 3548, 1), (Sum.inr 3582, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def sourceForm251 : Integer.Sparse Master := [(Sum.inr 2062, 1), (Sum.inr 2879, 2), (Sum.inr 2888, 1), (Sum.inr 3052, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

def sourceForm253 : Integer.Sparse Master := [(Sum.inr 1210, 1), (Sum.inr 1211, 1), (Sum.inr 1219, 1), (Sum.inr 1230, 1), (Sum.inr 1261, 1), (Sum.inr 2071, 1), (Sum.inr 2080, 1), (Sum.inr 2090, 1), (Sum.inr 2197, 1), (Sum.inr 2860, 1), (Sum.inr 2867, 1), (Sum.inr 2876, 1), (Sum.inr 2916, 1), (Sum.inr 2922, 1), (Sum.inr 2933, 1), (Sum.inr 2984, 1), (Sum.inr 2990, 1), (Sum.inr 2997, 1), (Sum.inr 3016, 1), (Sum.inr 3025, 1), (Sum.inr 3038, 1), (Sum.inr 3085, 1), (Sum.inr 3089, 1), (Sum.inr 3097, 1), (Sum.inr 3109, 1), (Sum.inr 3814, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3982, 1)]

def sourceForm254 : Integer.Sparse Master := [(Sum.inr 2043, 1), (Sum.inr 2045, 1), (Sum.inr 2049, 1), (Sum.inr 2055, 1), (Sum.inr 2259, 1), (Sum.inr 3285, 1), (Sum.inr 3287, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 1), (Sum.inr 3463, 1), (Sum.inr 3478, 1), (Sum.inr 3479, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3525, 1), (Sum.inr 3527, 1), (Sum.inr 3528, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3560, 1), (Sum.inr 3572, 1), (Sum.inr 3575, 1), (Sum.inr 3577, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3856, 1)]

def sourceForm255 : Integer.Sparse Master := [(Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3903, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2244 : Integer.Sparse Master := [(Sum.inr 2379, 1), (Sum.inr 3646, 1), (Sum.inr 3718, 2), (Sum.inr 3757, 1), (Sum.inr 3759, 1), (Sum.inr 4088, -1)]

def sourceForm2245 : Integer.Sparse Master := [(Sum.inr 2388, 1), (Sum.inr 3654, 1), (Sum.inr 3681, 1), (Sum.inr 3702, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 4088, -1)]

def sourceForm2249 : Integer.Sparse Master := [(Sum.inr 4089, 1), (Sum.inr 4515, 2), (Sum.inr 4520, 2), (Sum.inr 4575, 1), (Sum.inr 4913, 4), (Sum.inr 4915, 2), (Sum.inr 4924, 2), (Sum.inr 4985, 2), (Sum.inr 5015, 4), (Sum.inr 5021, 2), (Sum.inr 5125, 2), (Sum.inr 5238, 2), (Sum.inr 5327, 2), (Sum.inr 5371, 2)]

def sourceForm2251 : Integer.Sparse Master := [(Sum.inr 4368, 2), (Sum.inr 4373, 1), (Sum.inr 4375, 1), (Sum.inr 4466, 1), (Sum.inr 4687, 2), (Sum.inr 4694, 1), (Sum.inr 4700, 2), (Sum.inr 4704, 1), (Sum.inr 4773, 2), (Sum.inr 4776, 2), (Sum.inr 4810, 2), (Sum.inr 4865, 2), (Sum.inr 4867, 2), (Sum.inr 4868, 1), (Sum.inr 4872, 1), (Sum.inr 4894, 1), (Sum.inr 4896, 1), (Sum.inr 5264, 2), (Sum.inr 5291, 1), (Sum.inr 5297, 1), (Sum.inr 5300, 1)]

def sourceForm2252 : Integer.Sparse Master := [(Sum.inr 1321, 2), (Sum.inr 1323, 1), (Sum.inr 1325, 1), (Sum.inr 1419, 1), (Sum.inr 1813, 2), (Sum.inr 1820, 1), (Sum.inr 2113, 1), (Sum.inr 2816, 2), (Sum.inr 2821, 1), (Sum.inr 2966, 1), (Sum.inr 3040, 2), (Sum.inr 3055, 1), (Sum.inr 3056, 1), (Sum.inr 3103, 1), (Sum.inr 3131, 2), (Sum.inr 3163, 2), (Sum.inr 3180, 2), (Sum.inr 3185, 2), (Sum.inr 3206, 2), (Sum.inr 3225, 1), (Sum.inr 3230, 1)]

def sourceForm2253 : Integer.Sparse Master := [(Sum.inr 1712, 2), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1743, 1), (Sum.inr 2162, 2), (Sum.inr 2163, 1), (Sum.inr 2194, 2), (Sum.inr 2212, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 2), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2273, 1), (Sum.inr 2278, 1), (Sum.inr 2282, 1), (Sum.inr 2729, 2), (Sum.inr 2765, 1), (Sum.inr 2771, 1), (Sum.inr 2774, 1)]

def sourceForm2254 : Integer.Sparse Master := [(Sum.inr 1826, 2), (Sum.inr 1830, 1), (Sum.inr 1832, 1), (Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

def sourceForm2255 : Integer.Sparse Master := [(Sum.inr 946, 1), (Sum.inr 1826, 1), (Sum.inr 1974, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def sourceForm2256 : Integer.Sparse Master := [(Sum.inr 4238, 2), (Sum.inr 4241, 1), (Sum.inr 4243, 1), (Sum.inr 4278, 1), (Sum.inr 4673, 2), (Sum.inr 4688, 2), (Sum.inr 4691, 1), (Sum.inr 4693, 1), (Sum.inr 4724, 2), (Sum.inr 4727, 2), (Sum.inr 4749, 2), (Sum.inr 4860, 2), (Sum.inr 4862, 1), (Sum.inr 4869, 2), (Sum.inr 4871, 1), (Sum.inr 4874, 1), (Sum.inr 4898, 1), (Sum.inr 5384, 2), (Sum.inr 5389, 1), (Sum.inr 5443, 1), (Sum.inr 5449, 1)]

def sourceForm2257 : Integer.Sparse Master := [(Sum.inr 738, 2), (Sum.inr 741, 1), (Sum.inr 743, 1), (Sum.inr 830, 1), (Sum.inr 1799, 2), (Sum.inr 1814, 2), (Sum.inr 1817, 1), (Sum.inr 1819, 1), (Sum.inr 1878, 2), (Sum.inr 1881, 2), (Sum.inr 1928, 2), (Sum.inr 2101, 2), (Sum.inr 2103, 1), (Sum.inr 2110, 2), (Sum.inr 2112, 1), (Sum.inr 2276, 1), (Sum.inr 2279, 1), (Sum.inr 3732, 2), (Sum.inr 3740, 1), (Sum.inr 3886, 1), (Sum.inr 3889, 1)]

def sourceForm2259 : Integer.Sparse Master := [(Sum.inr 1640, 2), (Sum.inr 1652, 1), (Sum.inr 1653, 1), (Sum.inr 1660, 1), (Sum.inr 2028, 2), (Sum.inr 2065, 1), (Sum.inr 2066, 1), (Sum.inr 2072, 2), (Sum.inr 2081, 2), (Sum.inr 2082, 2), (Sum.inr 2093, 2), (Sum.inr 2094, 2), (Sum.inr 2114, 1), (Sum.inr 2116, 1), (Sum.inr 2122, 2), (Sum.inr 2137, 1), (Sum.inr 2138, 1), (Sum.inr 2604, 1), (Sum.inr 2620, 2), (Sum.inr 2643, 1), (Sum.inr 2644, 1)]

def sourceForm2260 : Integer.Sparse Master := [(Sum.inr 1371, 2), (Sum.inr 1373, 1), (Sum.inr 1374, 1), (Sum.inr 1444, 1), (Sum.inr 2867, 2), (Sum.inr 2872, 2), (Sum.inr 2887, 1), (Sum.inr 2888, 1), (Sum.inr 2889, 1), (Sum.inr 2968, 1), (Sum.inr 3095, 1), (Sum.inr 3151, 2), (Sum.inr 3159, 2), (Sum.inr 3160, 1), (Sum.inr 3161, 1), (Sum.inr 3168, 2), (Sum.inr 3174, 2), (Sum.inr 3178, 2), (Sum.inr 3188, 1), (Sum.inr 3206, 2), (Sum.inr 3216, 1)]

def sourceForm2261 : Integer.Sparse Master := [(Sum.inr 4369, 2), (Sum.inr 4374, 2), (Sum.inr 4467, 1), (Sum.inr 4701, 2), (Sum.inr 4705, 2), (Sum.inr 4774, 2), (Sum.inr 4777, 4), (Sum.inr 4811, 2), (Sum.inr 4866, 4), (Sum.inr 4871, 2), (Sum.inr 4895, 2), (Sum.inr 5269, 2), (Sum.inr 5303, 1), (Sum.inr 5304, 2)]

def sourceForm2262 : Integer.Sparse Master := [(Sum.inr 1322, 2), (Sum.inr 1324, 2), (Sum.inr 1420, 1), (Sum.inr 2340, 4), (Sum.inr 2346, 2), (Sum.inr 2602, 2), (Sum.inr 3108, 2), (Sum.inr 3118, 1), (Sum.inr 3119, 2), (Sum.inr 3132, 2), (Sum.inr 3164, 2), (Sum.inr 3184, 4), (Sum.inr 3207, 2), (Sum.inr 3229, 2)]

def sourceForm2263 : Integer.Sparse Master := [(Sum.inr 1721, 2), (Sum.inr 1748, 2), (Sum.inr 1751, 1), (Sum.inr 2199, 2), (Sum.inr 2223, 4), (Sum.inr 2225, 2), (Sum.inr 2257, 2), (Sum.inr 2260, 4), (Sum.inr 2286, 2), (Sum.inr 2287, 2), (Sum.inr 2291, 2), (Sum.inr 2736, 2), (Sum.inr 2779, 1), (Sum.inr 2782, 2)]

def sourceForm2264 : Integer.Sparse Master := [(Sum.inr 1827, 2), (Sum.inr 1831, 2), (Sum.inr 2116, 1), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

def sourceForm2265 : Integer.Sparse Master := [(Sum.inr 947, 1), (Sum.inr 1827, 1), (Sum.inr 1975, 1), (Sum.inr 2107, 2), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

def sourceForm2266 : Integer.Sparse Master := [(Sum.inr 4239, 2), (Sum.inr 4242, 2), (Sum.inr 4279, 1), (Sum.inr 4689, 2), (Sum.inr 4692, 2), (Sum.inr 4725, 2), (Sum.inr 4726, 4), (Sum.inr 4750, 2), (Sum.inr 4866, 4), (Sum.inr 4868, 2), (Sum.inr 4896, 2), (Sum.inr 5390, 1), (Sum.inr 5404, 2), (Sum.inr 5451, 2)]

def sourceForm2267 : Integer.Sparse Master := [(Sum.inr 739, 2), (Sum.inr 742, 2), (Sum.inr 831, 1), (Sum.inr 1815, 2), (Sum.inr 1818, 2), (Sum.inr 1879, 2), (Sum.inr 1880, 4), (Sum.inr 1929, 2), (Sum.inr 2107, 4), (Sum.inr 2109, 2), (Sum.inr 2278, 2), (Sum.inr 3741, 1), (Sum.inr 3790, 2), (Sum.inr 3888, 2)]

def sourceForm2268 : Integer.Sparse Master := [(Sum.inr 4487, 2), (Sum.inr 4491, 2), (Sum.inr 4506, 1), (Sum.inr 4811, 2), (Sum.inr 4825, 2), (Sum.inr 4828, 4), (Sum.inr 4842, 2), (Sum.inr 4846, 2), (Sum.inr 4856, 4), (Sum.inr 4874, 2), (Sum.inr 4884, 2), (Sum.inr 5177, 1), (Sum.inr 5189, 2), (Sum.inr 5207, 2)]

def sourceForm2269 : Integer.Sparse Master := [(Sum.inr 1641, 2), (Sum.inr 1653, 2), (Sum.inr 1661, 1), (Sum.inr 2029, 2), (Sum.inr 2066, 2), (Sum.inr 2073, 2), (Sum.inr 2082, 4), (Sum.inr 2094, 4), (Sum.inr 2115, 2), (Sum.inr 2123, 2), (Sum.inr 2138, 2), (Sum.inr 2605, 1), (Sum.inr 2621, 2), (Sum.inr 2644, 2)]

def sourceForm2271 : Integer.Sparse Master := [(Sum.inr 1876, 1), (Sum.inr 1880, 1), (Sum.inr 1881, 1), (Sum.inr 1918, 1), (Sum.inr 2082, 1), (Sum.inr 3448, 1), (Sum.inr 4080, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2273 : Integer.Sparse Master := [(Sum.inr 4328, 1), (Sum.inr 4334, 1), (Sum.inr 4336, 1), (Sum.inr 4354, 1), (Sum.inr 4466, 1), (Sum.inr 4665, 1), (Sum.inr 4667, 1), (Sum.inr 4669, 1), (Sum.inr 4671, 1), (Sum.inr 4687, 1), (Sum.inr 4688, 1), (Sum.inr 4756, 1), (Sum.inr 4766, 1), (Sum.inr 4773, 1), (Sum.inr 4776, 1), (Sum.inr 4801, 1), (Sum.inr 4803, 1), (Sum.inr 4804, 1), (Sum.inr 4808, 1), (Sum.inr 4810, 1), (Sum.inr 4834, 1), (Sum.inr 4839, 1), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 4896, 1), (Sum.inr 5232, 1), (Sum.inr 5243, 1), (Sum.inr 5258, 1), (Sum.inr 5264, 1), (Sum.inr 5266, 1)]

def sourceForm2274 : Integer.Sparse Master := [(Sum.inr 1330, 1), (Sum.inr 1332, 1), (Sum.inr 1334, 1), (Sum.inr 1343, 1), (Sum.inr 1419, 1), (Sum.inr 1793, 1), (Sum.inr 1797, 1), (Sum.inr 1813, 1), (Sum.inr 2092, 1), (Sum.inr 2800, 1), (Sum.inr 2803, 1), (Sum.inr 2816, 1), (Sum.inr 2941, 1), (Sum.inr 3030, 1), (Sum.inr 3039, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3089, 1), (Sum.inr 3134, 1), (Sum.inr 3141, 1), (Sum.inr 3163, 1), (Sum.inr 3187, 1), (Sum.inr 3190, 1), (Sum.inr 3202, 1), (Sum.inr 3205, 1), (Sum.inr 3206, 1), (Sum.inr 3210, 1), (Sum.inr 3214, 1), (Sum.inr 3225, 1), (Sum.inr 3230, 1)]

def sourceForm2275 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1679, 1), (Sum.inr 1681, 1), (Sum.inr 1685, 1), (Sum.inr 1738, 1), (Sum.inr 2144, 1), (Sum.inr 2155, 1), (Sum.inr 2157, 1), (Sum.inr 2160, 1), (Sum.inr 2161, 1), (Sum.inr 2162, 1), (Sum.inr 2176, 1), (Sum.inr 2177, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 1), (Sum.inr 2195, 1), (Sum.inr 2203, 1), (Sum.inr 2205, 1), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2220, 1), (Sum.inr 2264, 1), (Sum.inr 2276, 1), (Sum.inr 2278, 1), (Sum.inr 2677, 1), (Sum.inr 2697, 1), (Sum.inr 2722, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1)]

def sourceForm2276 : Integer.Sparse Master := [(Sum.inr 1791, 1), (Sum.inr 1795, 1), (Sum.inr 1797, 1), (Sum.inr 1814, 1), (Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 4084, -1)]

def sourceForm2277 : Integer.Sparse Master := [(Sum.inr 932, 1), (Sum.inr 1814, 1), (Sum.inr 1966, 1), (Sum.inr 2028, 1), (Sum.inr 2053, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

def sourceForm2278 : Integer.Sparse Master := [(Sum.inr 906, 1), (Sum.inr 1791, 1), (Sum.inr 1974, 1), (Sum.inr 2019, 1), (Sum.inr 2021, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

def sourceForm2279 : Integer.Sparse Master := [(Sum.inr 4200, 1), (Sum.inr 4203, 1), (Sum.inr 4205, 1), (Sum.inr 4223, 1), (Sum.inr 4255, 1), (Sum.inr 4634, 1), (Sum.inr 4636, 1), (Sum.inr 4638, 1), (Sum.inr 4653, 1), (Sum.inr 4658, 1), (Sum.inr 4678, 1), (Sum.inr 4707, 1), (Sum.inr 4716, 1), (Sum.inr 4731, 1), (Sum.inr 4766, 1), (Sum.inr 4770, 1), (Sum.inr 4798, 1), (Sum.inr 4800, 1), (Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4810, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4865, 1), (Sum.inr 4889, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 1), (Sum.inr 5387, 1), (Sum.inr 5432, 1), (Sum.inr 5435, 1)]

def sourceForm2283 : Integer.Sparse Master := [(Sum.inr 4329, 1), (Sum.inr 4335, 2), (Sum.inr 4355, 1), (Sum.inr 4467, 1), (Sum.inr 4666, 1), (Sum.inr 4670, 2), (Sum.inr 4689, 1), (Sum.inr 4757, 2), (Sum.inr 4767, 1), (Sum.inr 4774, 1), (Sum.inr 4777, 2), (Sum.inr 4802, 2), (Sum.inr 4807, 2), (Sum.inr 4811, 1), (Sum.inr 4838, 2), (Sum.inr 4875, 1), (Sum.inr 4895, 2), (Sum.inr 5236, 1), (Sum.inr 5246, 1), (Sum.inr 5269, 1), (Sum.inr 5271, 2)]

def sourceForm2284 : Integer.Sparse Master := [(Sum.inr 1331, 1), (Sum.inr 1333, 2), (Sum.inr 1344, 1), (Sum.inr 1420, 1), (Sum.inr 2323, 2), (Sum.inr 2327, 2), (Sum.inr 2340, 2), (Sum.inr 2574, 2), (Sum.inr 3104, 1), (Sum.inr 3108, 1), (Sum.inr 3109, 2), (Sum.inr 3115, 1), (Sum.inr 3135, 1), (Sum.inr 3142, 1), (Sum.inr 3164, 1), (Sum.inr 3188, 1), (Sum.inr 3191, 1), (Sum.inr 3204, 2), (Sum.inr 3207, 1), (Sum.inr 3213, 2), (Sum.inr 3229, 2)]

def sourceForm2285 : Integer.Sparse Master := [(Sum.inr 1671, 1), (Sum.inr 1689, 2), (Sum.inr 1691, 1), (Sum.inr 1751, 1), (Sum.inr 2148, 1), (Sum.inr 2164, 2), (Sum.inr 2166, 1), (Sum.inr 2181, 2), (Sum.inr 2183, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2227, 2), (Sum.inr 2288, 1), (Sum.inr 2291, 2), (Sum.inr 2682, 1), (Sum.inr 2701, 1), (Sum.inr 2736, 1), (Sum.inr 2739, 2)]

def sourceForm2286 : Integer.Sparse Master := [(Sum.inr 1792, 1), (Sum.inr 1796, 2), (Sum.inr 1815, 1), (Sum.inr 2029, 1), (Sum.inr 3380, 1), (Sum.inr 4083, -1)]

def sourceForm2287 : Integer.Sparse Master := [(Sum.inr 933, 1), (Sum.inr 1815, 1), (Sum.inr 1967, 1), (Sum.inr 2029, 1), (Sum.inr 2057, 2), (Sum.inr 4083, -1)]

def sourceForm2288 : Integer.Sparse Master := [(Sum.inr 907, 1), (Sum.inr 1792, 1), (Sum.inr 1975, 1), (Sum.inr 2020, 2), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

def sourceForm2289 : Integer.Sparse Master := [(Sum.inr 4201, 1), (Sum.inr 4204, 2), (Sum.inr 4224, 1), (Sum.inr 4256, 1), (Sum.inr 4635, 1), (Sum.inr 4637, 2), (Sum.inr 4654, 1), (Sum.inr 4706, 2), (Sum.inr 4717, 1), (Sum.inr 4732, 1), (Sum.inr 4767, 1), (Sum.inr 4769, 2), (Sum.inr 4802, 2), (Sum.inr 4804, 2), (Sum.inr 4811, 1), (Sum.inr 4835, 2), (Sum.inr 4888, 2), (Sum.inr 5356, 1), (Sum.inr 5393, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2)]

def sourceForm2291 : Integer.Sparse Master := [(Sum.inr 4415, 1), (Sum.inr 4419, 2), (Sum.inr 4427, 1), (Sum.inr 4487, 1), (Sum.inr 4732, 1), (Sum.inr 4745, 2), (Sum.inr 4750, 1), (Sum.inr 4782, 2), (Sum.inr 4785, 1), (Sum.inr 4795, 2), (Sum.inr 4810, 2), (Sum.inr 4811, 1), (Sum.inr 4821, 2), (Sum.inr 4825, 1), (Sum.inr 4846, 2), (Sum.inr 4856, 2), (Sum.inr 4875, 1), (Sum.inr 5081, 1), (Sum.inr 5130, 1), (Sum.inr 5152, 2), (Sum.inr 5177, 1)]

def sourceForm2295 : Integer.Sparse Master := [(Sum.inr 4348, 2), (Sum.inr 4359, 1), (Sum.inr 4362, 1), (Sum.inr 4510, 1), (Sum.inr 4678, 2), (Sum.inr 4683, 2), (Sum.inr 4691, 1), (Sum.inr 4694, 1), (Sum.inr 4702, 2), (Sum.inr 4762, 2), (Sum.inr 4832, 2), (Sum.inr 4836, 2), (Sum.inr 4837, 1), (Sum.inr 4844, 1), (Sum.inr 4845, 2), (Sum.inr 4897, 1), (Sum.inr 4899, 1), (Sum.inr 5222, 2), (Sum.inr 5235, 1), (Sum.inr 5261, 1), (Sum.inr 5268, 1)]

def sourceForm2296 : Integer.Sparse Master := [(Sum.inr 1347, 2), (Sum.inr 1348, 1), (Sum.inr 1349, 1), (Sum.inr 1454, 1), (Sum.inr 1828, 2), (Sum.inr 1832, 1), (Sum.inr 2136, 1), (Sum.inr 2716, 2), (Sum.inr 2734, 1), (Sum.inr 2778, 1), (Sum.inr 3031, 2), (Sum.inr 3033, 2), (Sum.inr 3046, 1), (Sum.inr 3062, 2), (Sum.inr 3082, 2), (Sum.inr 3090, 1), (Sum.inr 3095, 2), (Sum.inr 3114, 1), (Sum.inr 3143, 2), (Sum.inr 3145, 1), (Sum.inr 3215, 1)]

def sourceForm2297 : Integer.Sparse Master := [(Sum.inr 1669, 2), (Sum.inr 1683, 1), (Sum.inr 1687, 1), (Sum.inr 1741, 1), (Sum.inr 2143, 2), (Sum.inr 2146, 2), (Sum.inr 2159, 1), (Sum.inr 2163, 1), (Sum.inr 2171, 2), (Sum.inr 2180, 2), (Sum.inr 2193, 2), (Sum.inr 2197, 2), (Sum.inr 2208, 1), (Sum.inr 2218, 2), (Sum.inr 2222, 1), (Sum.inr 2268, 1), (Sum.inr 2281, 1), (Sum.inr 2664, 2), (Sum.inr 2680, 1), (Sum.inr 2726, 1), (Sum.inr 2734, 1)]

def sourceForm2298 : Integer.Sparse Master := [(Sum.inr 1809, 2), (Sum.inr 1817, 1), (Sum.inr 1820, 1), (Sum.inr 2065, 1), (Sum.inr 3396, 1), (Sum.inr 4085, -1)]

def sourceForm2302 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4349, 2), (Sum.inr 4360, 1), (Sum.inr 4361, 1), (Sum.inr 4511, 1), (Sum.inr 4684, 2), (Sum.inr 4692, 1), (Sum.inr 4693, 1), (Sum.inr 4763, 2), (Sum.inr 4769, 2), (Sum.inr 4770, 2), (Sum.inr 4834, 2), (Sum.inr 4835, 2), (Sum.inr 4841, 1), (Sum.inr 4843, 1), (Sum.inr 4846, 2), (Sum.inr 4901, 1), (Sum.inr 5238, 1), (Sum.inr 5248, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1)]

def sourceForm2303 : Integer.Sparse Master := [(Sum.inr 1675, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 1755, 1), (Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2174, 2), (Sum.inr 2185, 2), (Sum.inr 2186, 2), (Sum.inr 2205, 2), (Sum.inr 2206, 2), (Sum.inr 2228, 1), (Sum.inr 2229, 2), (Sum.inr 2230, 1), (Sum.inr 2293, 1), (Sum.inr 2686, 1), (Sum.inr 2705, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 4084, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2304 : Integer.Sparse Master := [(Sum.inr 1810, 2), (Sum.inr 1818, 1), (Sum.inr 1819, 1), (Sum.inr 2066, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

def sourceForm2308 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4288, 1), (Sum.inr 4295, 1), (Sum.inr 4296, 1), (Sum.inr 4311, 1), (Sum.inr 4404, 1), (Sum.inr 4632, 1), (Sum.inr 4637, 1), (Sum.inr 4638, 1), (Sum.inr 4652, 1), (Sum.inr 4706, 1), (Sum.inr 4707, 1), (Sum.inr 4715, 1), (Sum.inr 4722, 1), (Sum.inr 4726, 1), (Sum.inr 4727, 1), (Sum.inr 4736, 1), (Sum.inr 4737, 1), (Sum.inr 4741, 1), (Sum.inr 4742, 1), (Sum.inr 4752, 1), (Sum.inr 4782, 1), (Sum.inr 4828, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 5015, 1), (Sum.inr 5056, 1), (Sum.inr 5095, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1)]

def sourceForm2310 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4298, 1), (Sum.inr 4303, 1), (Sum.inr 4305, 1), (Sum.inr 4313, 1), (Sum.inr 4419, 1), (Sum.inr 4640, 1), (Sum.inr 4644, 1), (Sum.inr 4646, 1), (Sum.inr 4653, 1), (Sum.inr 4709, 1), (Sum.inr 4711, 1), (Sum.inr 4716, 1), (Sum.inr 4731, 1), (Sum.inr 4732, 1), (Sum.inr 4744, 1), (Sum.inr 4745, 2), (Sum.inr 4749, 1), (Sum.inr 4750, 1), (Sum.inr 4753, 1), (Sum.inr 4782, 1), (Sum.inr 4810, 1), (Sum.inr 4811, 1), (Sum.inr 4846, 1), (Sum.inr 5003, 1), (Sum.inr 5050, 1), (Sum.inr 5080, 1), (Sum.inr 5081, 1), (Sum.inr 5111, 1)]

def sourceForm2311 : Integer.Sparse Master := [(Sum.inr 4065, 2), (Sum.inr 4067, 2), (Sum.inr 4071, 1), (Sum.inr 4074, 4), (Sum.inr 4075, 2), (Sum.inr 4076, 2), (Sum.inr 4078, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4088, 2), (Sum.inr 4089, 1), (Sum.inr 4092, 2)]

def sourceForm2312 : Integer.Sparse Master := [(Sum.inr 923, 1), (Sum.inr 1806, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2051, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

def sourceForm2313 : Integer.Sparse Master := [(Sum.inr 2440, 1), (Sum.inr 3062, 1), (Sum.inr 3189, 1), (Sum.inr 3202, 2), (Sum.inr 3789, 1), (Sum.inr 4091, -1)]

def sourceForm2315 : Integer.Sparse Master := [(Sum.inr 920, 1), (Sum.inr 1803, 1), (Sum.inr 2033, 1), (Sum.inr 2051, 1), (Sum.inr 2054, 2), (Sum.inr 4084, -1)]

def sourceForm2316 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 3164, 2), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

def sourceForm2318 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 3162, 1), (Sum.inr 3163, 1), (Sum.inr 3170, 1), (Sum.inr 3196, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

def sourceForm2319 : Integer.Sparse Master := [(Sum.inr 2443, 1), (Sum.inr 3033, 1), (Sum.inr 3136, 1), (Sum.inr 3138, 1), (Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def sourceForm2320 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 1822, 1), (Sum.inr 2088, 1), (Sum.inr 2105, 1), (Sum.inr 2107, 2), (Sum.inr 4083, -1)]

def sourceForm2321 : Integer.Sparse Master := [(Sum.inr 2890, 1), (Sum.inr 3135, 2), (Sum.inr 3137, 1), (Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

def sourceForm2322 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 1824, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def sourceForm2323 : Integer.Sparse Master := [(Sum.inr 2423, 1), (Sum.inr 3133, 1), (Sum.inr 3134, 1), (Sum.inr 3136, 1), (Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

def sourceForm2325 : Integer.Sparse Master := [(Sum.inr 2899, 1), (Sum.inr 3128, 1), (Sum.inr 3132, 2), (Sum.inr 3158, 1), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

def sourceForm2326 : Integer.Sparse Master := [(Sum.inr 2435, 1), (Sum.inr 3127, 1), (Sum.inr 3129, 1), (Sum.inr 3131, 1), (Sum.inr 3156, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

def sourceForm2327 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 2333, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2508, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def sourceForm2328 : Integer.Sparse Master := [(Sum.inr 2437, 1), (Sum.inr 2900, 1), (Sum.inr 2902, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3787, 1), (Sum.inr 4091, -1)]

def sourceForm2330 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 2331, 1), (Sum.inr 2493, 1), (Sum.inr 2508, 1), (Sum.inr 2512, 2), (Sum.inr 4092, -1)]

def sourceForm2331 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2849, 2), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

def sourceForm2333 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2846, 1), (Sum.inr 2848, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

def sourceForm2334 : Integer.Sparse Master := [(Sum.inr 1960, 1), (Sum.inr 2427, 2), (Sum.inr 2509, 1), (Sum.inr 2552, 1), (Sum.inr 3493, 1), (Sum.inr 4084, -1)]

def sourceForm2335 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2428, 1), (Sum.inr 2433, 1), (Sum.inr 2512, 1), (Sum.inr 2554, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2336 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 2431, 1), (Sum.inr 2433, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

def sourceForm2337 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

def sourceForm2338 : Integer.Sparse Master := [(Sum.inr 4550, 1), (Sum.inr 4551, 1), (Sum.inr 4553, 2), (Sum.inr 4623, 1), (Sum.inr 4967, 1), (Sum.inr 4970, 1), (Sum.inr 4973, 2), (Sum.inr 5113, 1), (Sum.inr 5114, 2), (Sum.inr 5166, 1), (Sum.inr 5168, 3), (Sum.inr 5170, 2), (Sum.inr 5171, 2), (Sum.inr 5176, 2), (Sum.inr 5306, 1), (Sum.inr 5308, 2), (Sum.inr 5387, 1), (Sum.inr 5415, 1), (Sum.inr 5439, 1), (Sum.inr 5441, 2)]

def sourceForm2339 : Integer.Sparse Master := [(Sum.inr 1135, 1), (Sum.inr 1136, 1), (Sum.inr 1138, 2), (Sum.inr 1305, 1), (Sum.inr 2814, 1), (Sum.inr 2815, 1), (Sum.inr 2817, 2), (Sum.inr 2894, 1), (Sum.inr 2896, 2), (Sum.inr 2953, 1), (Sum.inr 2954, 2), (Sum.inr 2963, 3), (Sum.inr 2965, 2), (Sum.inr 2968, 2), (Sum.inr 3120, 1), (Sum.inr 3124, 2), (Sum.inr 3739, 1), (Sum.inr 4012, 1), (Sum.inr 4031, 1), (Sum.inr 4037, 2)]

def sourceForm2340 : Integer.Sparse Master := [(Sum.inr 4341, 1), (Sum.inr 4343, 1), (Sum.inr 4349, 2), (Sum.inr 4457, 1), (Sum.inr 4760, 1), (Sum.inr 4769, 1), (Sum.inr 4804, 2), (Sum.inr 4939, 1), (Sum.inr 4946, 2), (Sum.inr 5036, 2), (Sum.inr 5072, 1), (Sum.inr 5134, 2), (Sum.inr 5141, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5258, 2), (Sum.inr 5292, 1), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2), (Sum.inr 5486, 1)]

def sourceForm2341 : Integer.Sparse Master := [(Sum.inr 919, 1), (Sum.inr 921, 1), (Sum.inr 927, 2), (Sum.inr 1040, 1), (Sum.inr 1960, 1), (Sum.inr 1969, 1), (Sum.inr 2022, 2), (Sum.inr 2330, 1), (Sum.inr 2337, 2), (Sum.inr 2428, 2), (Sum.inr 2479, 1), (Sum.inr 2553, 2), (Sum.inr 2561, 2), (Sum.inr 2593, 1), (Sum.inr 2595, 2), (Sum.inr 2722, 2), (Sum.inr 2766, 1), (Sum.inr 3821, 1), (Sum.inr 3824, 1), (Sum.inr 3852, 2), (Sum.inr 3999, 1)]

def sourceForm2342 : Integer.Sparse Master := [(Sum.inr 4544, 1), (Sum.inr 4546, 1), (Sum.inr 4549, 1), (Sum.inr 4554, 1), (Sum.inr 4624, 1), (Sum.inr 4968, 1), (Sum.inr 4972, 1), (Sum.inr 4974, 1), (Sum.inr 4977, 1), (Sum.inr 5037, 1), (Sum.inr 5078, 1), (Sum.inr 5115, 1), (Sum.inr 5117, 1), (Sum.inr 5148, 1), (Sum.inr 5152, 1), (Sum.inr 5167, 1), (Sum.inr 5169, 3), (Sum.inr 5172, 1), (Sum.inr 5174, 1), (Sum.inr 5177, 1), (Sum.inr 5293, 1), (Sum.inr 5307, 1), (Sum.inr 5309, 1), (Sum.inr 5388, 1), (Sum.inr 5416, 1), (Sum.inr 5434, 1), (Sum.inr 5440, 1), (Sum.inr 5442, 1)]

def sourceForm2343 : Integer.Sparse Master := [(Sum.inr 1129, 1), (Sum.inr 1131, 1), (Sum.inr 1134, 1), (Sum.inr 1139, 1), (Sum.inr 1301, 1), (Sum.inr 2429, 1), (Sum.inr 2434, 1), (Sum.inr 2485, 1), (Sum.inr 2601, 1), (Sum.inr 2809, 1), (Sum.inr 2813, 1), (Sum.inr 2818, 1), (Sum.inr 2893, 1), (Sum.inr 2897, 1), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2958, 1), (Sum.inr 2959, 1), (Sum.inr 2960, 3), (Sum.inr 2969, 1), (Sum.inr 3102, 1), (Sum.inr 3122, 1), (Sum.inr 3123, 1), (Sum.inr 3737, 1), (Sum.inr 3967, 1), (Sum.inr 3982, 1), (Sum.inr 4001, 1), (Sum.inr 4036, 1)]

def sourceForm2344 : Integer.Sparse Master := [(Sum.inr 4344, 1), (Sum.inr 4346, 1), (Sum.inr 4349, 1), (Sum.inr 4355, 1), (Sum.inr 4458, 1), (Sum.inr 4941, 1), (Sum.inr 4943, 1), (Sum.inr 4946, 1), (Sum.inr 4950, 1), (Sum.inr 5033, 1), (Sum.inr 5036, 1), (Sum.inr 5039, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5171, 1), (Sum.inr 5177, 1), (Sum.inr 5259, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1), (Sum.inr 5465, 1), (Sum.inr 5476, 1), (Sum.inr 5483, 1), (Sum.inr 5486, 1), (Sum.inr 5487, 1)]

def sourceForm2345 : Integer.Sparse Master := [(Sum.inr 922, 1), (Sum.inr 924, 1), (Sum.inr 927, 1), (Sum.inr 933, 1), (Sum.inr 1041, 1), (Sum.inr 2332, 1), (Sum.inr 2334, 1), (Sum.inr 2337, 1), (Sum.inr 2342, 1), (Sum.inr 2425, 1), (Sum.inr 2428, 1), (Sum.inr 2432, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2593, 1), (Sum.inr 2594, 1), (Sum.inr 2595, 2), (Sum.inr 2598, 1), (Sum.inr 2605, 1), (Sum.inr 2723, 1), (Sum.inr 2766, 1), (Sum.inr 2767, 1), (Sum.inr 3931, 1), (Sum.inr 3965, 1), (Sum.inr 3981, 1), (Sum.inr 3999, 1), (Sum.inr 4000, 1)]

def sourceForm2348 : Integer.Sparse Master := [(Sum.inr 4345, 1), (Sum.inr 4347, 1), (Sum.inr 4348, 1), (Sum.inr 4357, 1), (Sum.inr 4459, 1), (Sum.inr 4942, 1), (Sum.inr 4944, 1), (Sum.inr 4945, 1), (Sum.inr 4951, 1), (Sum.inr 5034, 1), (Sum.inr 5035, 1), (Sum.inr 5040, 1), (Sum.inr 5074, 1), (Sum.inr 5078, 1), (Sum.inr 5138, 1), (Sum.inr 5139, 1), (Sum.inr 5140, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5160, 1), (Sum.inr 5161, 1), (Sum.inr 5164, 1), (Sum.inr 5260, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 1), (Sum.inr 5438, 1), (Sum.inr 5484, 1)]

def sourceForm2349 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1669, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1714, 1), (Sum.inr 2652, 1), (Sum.inr 2658, 1), (Sum.inr 2670, 1), (Sum.inr 2719, 1), (Sum.inr 3407, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3451, 1), (Sum.inr 3454, 1), (Sum.inr 3463, 1), (Sum.inr 3481, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3540, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3572, 1), (Sum.inr 3605, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 1), (Sum.inr 3857, 1), (Sum.inr 3983, 1)]

def sourceForm2350 : Integer.Sparse Master := [(Sum.inr 4541, 1), (Sum.inr 4543, 1), (Sum.inr 4549, 2), (Sum.inr 4623, 1), (Sum.inr 4764, 1), (Sum.inr 4770, 1), (Sum.inr 4807, 2), (Sum.inr 4971, 1), (Sum.inr 4977, 2), (Sum.inr 5117, 2), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 1), (Sum.inr 5294, 2), (Sum.inr 5307, 1), (Sum.inr 5387, 1), (Sum.inr 5417, 1), (Sum.inr 5435, 2), (Sum.inr 5440, 1)]

def sourceForm2351 : Integer.Sparse Master := [(Sum.inr 1126, 1), (Sum.inr 1128, 1), (Sum.inr 1134, 2), (Sum.inr 1300, 1), (Sum.inr 1964, 1), (Sum.inr 1970, 1), (Sum.inr 2025, 2), (Sum.inr 2807, 1), (Sum.inr 2813, 2), (Sum.inr 2893, 2), (Sum.inr 2924, 2), (Sum.inr 2931, 2), (Sum.inr 2958, 1), (Sum.inr 2959, 1), (Sum.inr 2960, 2), (Sum.inr 3101, 2), (Sum.inr 3122, 1), (Sum.inr 3736, 1), (Sum.inr 3823, 1), (Sum.inr 3853, 2), (Sum.inr 4036, 1)]

def sourceForm2352 : Integer.Sparse Master := [(Sum.inr 4351, 1), (Sum.inr 4352, 1), (Sum.inr 4354, 2), (Sum.inr 4461, 1), (Sum.inr 4947, 1), (Sum.inr 4948, 1), (Sum.inr 4949, 2), (Sum.inr 5037, 1), (Sum.inr 5038, 2), (Sum.inr 5076, 1), (Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 2), (Sum.inr 5176, 2), (Sum.inr 5290, 1), (Sum.inr 5294, 2), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5442, 2), (Sum.inr 5485, 1)]

def sourceForm2353 : Integer.Sparse Master := [(Sum.inr 929, 1), (Sum.inr 930, 1), (Sum.inr 932, 2), (Sum.inr 1044, 1), (Sum.inr 2338, 1), (Sum.inr 2339, 1), (Sum.inr 2341, 2), (Sum.inr 2429, 1), (Sum.inr 2431, 2), (Sum.inr 2483, 1), (Sum.inr 2589, 1), (Sum.inr 2590, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 2), (Sum.inr 2604, 2), (Sum.inr 2764, 1), (Sum.inr 2768, 2), (Sum.inr 3933, 1), (Sum.inr 3967, 1), (Sum.inr 3998, 1), (Sum.inr 4001, 2)]

def sourceForm2354 : Integer.Sparse Master := [(Sum.inr 4805, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 2), (Sum.inr 4869, 1), (Sum.inr 5072, 1), (Sum.inr 5076, 1), (Sum.inr 5099, 1), (Sum.inr 5101, 2), (Sum.inr 5104, 1), (Sum.inr 5105, 2), (Sum.inr 5137, 1), (Sum.inr 5138, 2), (Sum.inr 5149, 2), (Sum.inr 5150, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5170, 2), (Sum.inr 5173, 2), (Sum.inr 5187, 1), (Sum.inr 5204, 2), (Sum.inr 5205, 1)]

def sourceForm2355 : Integer.Sparse Master := [(Sum.inr 1156, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2587, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

def sourceForm2356 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 2896, 1), (Sum.inr 2898, 1), (Sum.inr 2928, 2), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

def sourceForm2357 : Integer.Sparse Master := [(Sum.inr 1158, 1), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 2), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

def sourceForm2358 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2893, 1), (Sum.inr 2898, 1), (Sum.inr 2925, 2), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

def sourceForm2359 : Integer.Sparse Master := [(Sum.inr 2922, 1), (Sum.inr 3748, 1), (Sum.inr 3751, 1), (Sum.inr 3758, 1), (Sum.inr 3866, 1), (Sum.inr 3973, 1), (Sum.inr 4087, -1)]

def sourceForm2365 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4328, 1), (Sum.inr 4332, 1), (Sum.inr 4345, 1), (Sum.inr 4439, 1), (Sum.inr 4930, 1), (Sum.inr 4931, 1), (Sum.inr 4933, 1), (Sum.inr 4942, 1), (Sum.inr 5037, 1), (Sum.inr 5078, 1), (Sum.inr 5114, 1), (Sum.inr 5117, 1), (Sum.inr 5128, 1), (Sum.inr 5129, 1), (Sum.inr 5138, 1), (Sum.inr 5144, 1), (Sum.inr 5145, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5160, 1), (Sum.inr 5170, 1), (Sum.inr 5251, 1), (Sum.inr 5281, 1), (Sum.inr 5284, 1), (Sum.inr 5393, 1), (Sum.inr 5396, 1), (Sum.inr 5410, 1), (Sum.inr 5424, 1), (Sum.inr 5478, 1)]

def sourceForm2366 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 906, 1), (Sum.inr 910, 1), (Sum.inr 923, 1), (Sum.inr 1021, 1), (Sum.inr 2320, 1), (Sum.inr 2321, 1), (Sum.inr 2324, 1), (Sum.inr 2333, 1), (Sum.inr 2526, 1), (Sum.inr 2527, 1), (Sum.inr 2530, 1), (Sum.inr 2543, 1), (Sum.inr 2545, 1), (Sum.inr 2557, 1), (Sum.inr 2566, 1), (Sum.inr 2567, 1), (Sum.inr 2570, 1), (Sum.inr 2572, 1), (Sum.inr 2576, 1), (Sum.inr 2587, 1), (Sum.inr 2596, 1), (Sum.inr 2710, 1), (Sum.inr 2750, 1), (Sum.inr 2753, 1), (Sum.inr 3925, 1), (Sum.inr 3988, 1), (Sum.inr 3990, 1), (Sum.inr 3994, 1), (Sum.inr 3996, 1)]

def sourceForm2367 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1668, 1), (Sum.inr 1670, 1), (Sum.inr 1678, 1), (Sum.inr 1713, 1), (Sum.inr 3406, 1), (Sum.inr 3407, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3455, 1), (Sum.inr 3481, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3519, 1), (Sum.inr 3539, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3562, 1), (Sum.inr 3571, 1), (Sum.inr 3597, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3797, 1), (Sum.inr 3798, 1), (Sum.inr 3816, 1), (Sum.inr 3843, 1), (Sum.inr 3974, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2368 : Integer.Sparse Master := [(Sum.inr 2422, 1), (Sum.inr 2822, 1), (Sum.inr 2824, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

def sourceForm2370 : Integer.Sparse Master := [(Sum.inr 1169, 1), (Sum.inr 2361, 1), (Sum.inr 2573, 3), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

def sourceForm2371 : Integer.Sparse Master := [(Sum.inr 1964, 1), (Sum.inr 2892, 2), (Sum.inr 2923, 2), (Sum.inr 3496, 1), (Sum.inr 4083, -1)]

def sourceForm2374 : Integer.Sparse Master := [(Sum.inr 2800, 1), (Sum.inr 2801, 2), (Sum.inr 2814, 1), (Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

def sourceForm2375 : Integer.Sparse Master := [(Sum.inr 2797, 1), (Sum.inr 2799, 1), (Sum.inr 2801, 1), (Sum.inr 2809, 1), (Sum.inr 2862, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

def sourceForm2376 : Integer.Sparse Master := [(Sum.inr 2524, 1), (Sum.inr 2798, 2), (Sum.inr 2807, 1), (Sum.inr 2861, 1), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

def sourceForm2377 : Integer.Sparse Master := [(Sum.inr 2031, 2), (Sum.inr 2036, 1), (Sum.inr 2046, 1), (Sum.inr 2275, 1), (Sum.inr 3537, 1), (Sum.inr 4080, -1)]

def sourceForm2378 : Integer.Sparse Master := [(Sum.inr 2810, 1), (Sum.inr 2816, 1), (Sum.inr 2817, 1), (Sum.inr 2819, 1), (Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

def sourceForm2382 : Integer.Sparse Master := [(Sum.inr 4364, 1), (Sum.inr 4365, 1), (Sum.inr 4369, 2), (Sum.inr 4474, 1), (Sum.inr 4968, 1), (Sum.inr 4970, 1), (Sum.inr 4974, 2), (Sum.inr 5041, 1), (Sum.inr 5043, 2), (Sum.inr 5085, 1), (Sum.inr 5147, 2), (Sum.inr 5185, 2), (Sum.inr 5189, 2), (Sum.inr 5202, 1), (Sum.inr 5203, 2), (Sum.inr 5266, 2), (Sum.inr 5301, 1), (Sum.inr 5369, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1)]

def sourceForm2383 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1704, 1), (Sum.inr 1709, 1), (Sum.inr 1721, 2), (Sum.inr 3458, 1), (Sum.inr 3461, 1), (Sum.inr 3465, 2), (Sum.inr 3529, 2), (Sum.inr 3530, 2), (Sum.inr 3535, 2), (Sum.inr 3542, 2), (Sum.inr 3587, 1), (Sum.inr 3588, 1), (Sum.inr 3592, 2), (Sum.inr 3617, 1), (Sum.inr 3619, 1), (Sum.inr 3621, 2), (Sum.inr 3774, 1), (Sum.inr 3952, 1), (Sum.inr 3961, 2), (Sum.inr 3962, 1)]

def sourceForm2386 : Integer.Sparse Master := [(Sum.inr 4366, 1), (Sum.inr 4367, 1), (Sum.inr 4368, 1), (Sum.inr 4372, 1), (Sum.inr 4475, 1), (Sum.inr 4971, 1), (Sum.inr 4972, 1), (Sum.inr 4973, 1), (Sum.inr 4977, 1), (Sum.inr 5034, 1), (Sum.inr 5042, 1), (Sum.inr 5044, 1), (Sum.inr 5086, 1), (Sum.inr 5109, 1), (Sum.inr 5139, 1), (Sum.inr 5187, 1), (Sum.inr 5188, 1), (Sum.inr 5197, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5204, 1), (Sum.inr 5207, 1), (Sum.inr 5267, 1), (Sum.inr 5299, 1), (Sum.inr 5302, 1), (Sum.inr 5367, 1), (Sum.inr 5395, 1), (Sum.inr 5413, 1), (Sum.inr 5428, 1), (Sum.inr 5473, 1)]

def sourceForm2387 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1712, 1), (Sum.inr 1715, 1), (Sum.inr 1720, 1), (Sum.inr 1734, 1), (Sum.inr 3451, 1), (Sum.inr 3457, 1), (Sum.inr 3462, 1), (Sum.inr 3464, 1), (Sum.inr 3474, 1), (Sum.inr 3486, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3590, 1), (Sum.inr 3591, 1), (Sum.inr 3595, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3766, 1), (Sum.inr 3794, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 1), (Sum.inr 3958, 1)]

def sourceForm2388 : Integer.Sparse Master := [(Sum.inr 1970, 1), (Sum.inr 2806, 1), (Sum.inr 2812, 2), (Sum.inr 2879, 1), (Sum.inr 3498, 1), (Sum.inr 4084, -1)]

def sourceForm2390 : Integer.Sparse Master := [(Sum.inr 2607, 1), (Sum.inr 3067, 1), (Sum.inr 3751, 1), (Sum.inr 3866, 2), (Sum.inr 3867, 1), (Sum.inr 4087, -1)]

def sourceForm2391 : Integer.Sparse Master := [(Sum.inr 4545, 1), (Sum.inr 4547, 1), (Sum.inr 4548, 1), (Sum.inr 4556, 1), (Sum.inr 4619, 1), (Sum.inr 4963, 1), (Sum.inr 4965, 1), (Sum.inr 4966, 1), (Sum.inr 4976, 1), (Sum.inr 5041, 1), (Sum.inr 5075, 1), (Sum.inr 5112, 1), (Sum.inr 5116, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5144, 1), (Sum.inr 5147, 1), (Sum.inr 5151, 1), (Sum.inr 5160, 1), (Sum.inr 5163, 1), (Sum.inr 5164, 1), (Sum.inr 5173, 1), (Sum.inr 5274, 1), (Sum.inr 5291, 1), (Sum.inr 5304, 1), (Sum.inr 5384, 1), (Sum.inr 5400, 1), (Sum.inr 5409, 1), (Sum.inr 5432, 1), (Sum.inr 5438, 1)]

def sourceForm2392 : Integer.Sparse Master := [(Sum.inr 2655, 1), (Sum.inr 2657, 1), (Sum.inr 2659, 1), (Sum.inr 2681, 1), (Sum.inr 2735, 1), (Sum.inr 3259, 1), (Sum.inr 3266, 1), (Sum.inr 3271, 1), (Sum.inr 3305, 1), (Sum.inr 3458, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3547, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3799, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3850, 1), (Sum.inr 3876, 1)]

def sourceForm2393 : Integer.Sparse Master := [(Sum.inr 2353, 1), (Sum.inr 2355, 1), (Sum.inr 2356, 1), (Sum.inr 2362, 1), (Sum.inr 2590, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def sourceForm2394 : Integer.Sparse Master := [(Sum.inr 4337, 1), (Sum.inr 4338, 1), (Sum.inr 4339, 1), (Sum.inr 4354, 1), (Sum.inr 4452, 1), (Sum.inr 4721, 1), (Sum.inr 4726, 1), (Sum.inr 4744, 1), (Sum.inr 4868, 1), (Sum.inr 4936, 1), (Sum.inr 4937, 1), (Sum.inr 4949, 1), (Sum.inr 5032, 1), (Sum.inr 5038, 1), (Sum.inr 5070, 1), (Sum.inr 5123, 1), (Sum.inr 5125, 1), (Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 1), (Sum.inr 5176, 1), (Sum.inr 5228, 1), (Sum.inr 5290, 1), (Sum.inr 5291, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5411, 1), (Sum.inr 5451, 1), (Sum.inr 5485, 1)]

def sourceForm2397 : Integer.Sparse Master := [(Sum.inr 4527, 1), (Sum.inr 4530, 2), (Sum.inr 4542, 1), (Sum.inr 4606, 1), (Sum.inr 4956, 1), (Sum.inr 4958, 2), (Sum.inr 4964, 1), (Sum.inr 5037, 1), (Sum.inr 5039, 2), (Sum.inr 5104, 1), (Sum.inr 5128, 2), (Sum.inr 5130, 2), (Sum.inr 5137, 2), (Sum.inr 5145, 2), (Sum.inr 5162, 1), (Sum.inr 5259, 2), (Sum.inr 5273, 1), (Sum.inr 5380, 1), (Sum.inr 5396, 1), (Sum.inr 5424, 2), (Sum.inr 5427, 1)]

def sourceForm2398 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3299, 1), (Sum.inr 3455, 1), (Sum.inr 3456, 2), (Sum.inr 3483, 1), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3519, 2), (Sum.inr 3520, 2), (Sum.inr 3521, 2), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3554, 1), (Sum.inr 3562, 2), (Sum.inr 3563, 1), (Sum.inr 3798, 1), (Sum.inr 3836, 1), (Sum.inr 3843, 2), (Sum.inr 3844, 1)]

def sourceForm2399 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2351, 2), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2400 : Integer.Sparse Master := [(Sum.inr 4322, 1), (Sum.inr 4323, 2), (Sum.inr 4344, 1), (Sum.inr 4399, 1), (Sum.inr 4927, 1), (Sum.inr 4928, 2), (Sum.inr 4941, 1), (Sum.inr 4986, 1), (Sum.inr 4987, 2), (Sum.inr 4998, 1), (Sum.inr 5075, 2), (Sum.inr 5134, 2), (Sum.inr 5141, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5257, 1), (Sum.inr 5259, 2), (Sum.inr 5460, 1), (Sum.inr 5469, 1), (Sum.inr 5482, 1), (Sum.inr 5483, 2)]

def sourceForm2402 : Integer.Sparse Master := [(Sum.inr 4528, 1), (Sum.inr 4529, 1), (Sum.inr 4533, 1), (Sum.inr 4545, 1), (Sum.inr 4602, 1), (Sum.inr 4954, 1), (Sum.inr 4955, 1), (Sum.inr 4957, 1), (Sum.inr 4963, 1), (Sum.inr 5033, 1), (Sum.inr 5036, 1), (Sum.inr 5038, 1), (Sum.inr 5075, 1), (Sum.inr 5101, 1), (Sum.inr 5127, 1), (Sum.inr 5129, 1), (Sum.inr 5135, 1), (Sum.inr 5138, 1), (Sum.inr 5141, 1), (Sum.inr 5144, 1), (Sum.inr 5160, 1), (Sum.inr 5163, 1), (Sum.inr 5258, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1), (Sum.inr 5378, 1), (Sum.inr 5394, 1), (Sum.inr 5409, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1)]

def sourceForm2403 : Integer.Sparse Master := [(Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3267, 1), (Sum.inr 3293, 1), (Sum.inr 3449, 1), (Sum.inr 3450, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3513, 1), (Sum.inr 3515, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3522, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3547, 1), (Sum.inr 3553, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3793, 1), (Sum.inr 3795, 1), (Sum.inr 3807, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1)]

def sourceForm2404 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2348, 1), (Sum.inr 2350, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

def sourceForm2405 : Integer.Sparse Master := [(Sum.inr 4320, 1), (Sum.inr 4321, 1), (Sum.inr 4323, 1), (Sum.inr 4341, 1), (Sum.inr 4396, 1), (Sum.inr 4706, 1), (Sum.inr 4709, 1), (Sum.inr 4728, 1), (Sum.inr 4804, 1), (Sum.inr 4926, 1), (Sum.inr 4928, 1), (Sum.inr 4939, 1), (Sum.inr 4985, 1), (Sum.inr 4987, 1), (Sum.inr 4996, 1), (Sum.inr 5126, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5241, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5393, 1), (Sum.inr 5395, 1), (Sum.inr 5405, 1), (Sum.inr 5434, 1), (Sum.inr 5482, 1)]

def sourceForm2410 : Integer.Sparse Master := [(Sum.inr 4528, 1), (Sum.inr 4530, 1), (Sum.inr 4533, 1), (Sum.inr 4544, 1), (Sum.inr 4590, 1), (Sum.inr 4930, 1), (Sum.inr 4932, 1), (Sum.inr 4933, 1), (Sum.inr 4941, 1), (Sum.inr 5034, 1), (Sum.inr 5043, 1), (Sum.inr 5044, 1), (Sum.inr 5065, 1), (Sum.inr 5067, 1), (Sum.inr 5073, 2), (Sum.inr 5076, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5100, 1), (Sum.inr 5104, 1), (Sum.inr 5185, 1), (Sum.inr 5250, 1), (Sum.inr 5257, 1), (Sum.inr 5259, 1), (Sum.inr 5352, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5408, 1), (Sum.inr 5410, 1)]

def sourceForm2411 : Integer.Sparse Master := [(Sum.inr 3260, 1), (Sum.inr 3261, 1), (Sum.inr 3263, 1), (Sum.inr 3267, 1), (Sum.inr 3290, 1), (Sum.inr 3408, 1), (Sum.inr 3409, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3451, 1), (Sum.inr 3465, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3469, 1), (Sum.inr 3474, 1), (Sum.inr 3476, 1), (Sum.inr 3477, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3483, 1), (Sum.inr 3529, 1), (Sum.inr 3531, 1), (Sum.inr 3532, 1), (Sum.inr 3544, 1), (Sum.inr 3764, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3806, 1), (Sum.inr 3816, 1)]

def sourceForm2415 : Integer.Sparse Master := [(Sum.inr 1875, 1), (Sum.inr 1876, 1), (Sum.inr 1878, 1), (Sum.inr 1908, 1), (Sum.inr 2075, 1), (Sum.inr 3444, 1), (Sum.inr 4080, -1)]

def sourceForm2416 : Integer.Sparse Master := [(Sum.inr 4527, 1), (Sum.inr 4529, 2), (Sum.inr 4541, 1), (Sum.inr 4589, 1), (Sum.inr 4929, 1), (Sum.inr 4931, 2), (Sum.inr 4939, 1), (Sum.inr 5041, 1), (Sum.inr 5042, 2), (Sum.inr 5074, 2), (Sum.inr 5075, 2), (Sum.inr 5080, 2), (Sum.inr 5098, 1), (Sum.inr 5101, 2), (Sum.inr 5184, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 2), (Sum.inr 5351, 1), (Sum.inr 5400, 1), (Sum.inr 5405, 1), (Sum.inr 5409, 2)]

def sourceForm2417 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 2), (Sum.inr 3288, 1), (Sum.inr 3403, 1), (Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3458, 1), (Sum.inr 3460, 1), (Sum.inr 3462, 2), (Sum.inr 3463, 2), (Sum.inr 3468, 2), (Sum.inr 3470, 2), (Sum.inr 3478, 2), (Sum.inr 3524, 1), (Sum.inr 3525, 1), (Sum.inr 3533, 2), (Sum.inr 3757, 1), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3807, 2)]

def sourceForm2425 : Integer.Sparse Master := [(Sum.inr 4540, 1), (Sum.inr 4543, 1), (Sum.inr 4548, 2), (Sum.inr 4600, 1), (Sum.inr 4760, 1), (Sum.inr 4769, 1), (Sum.inr 4841, 2), (Sum.inr 4938, 1), (Sum.inr 4945, 2), (Sum.inr 5035, 2), (Sum.inr 5097, 1), (Sum.inr 5099, 2), (Sum.inr 5103, 2), (Sum.inr 5110, 2), (Sum.inr 5133, 1), (Sum.inr 5241, 1), (Sum.inr 5248, 1), (Sum.inr 5270, 1), (Sum.inr 5272, 2), (Sum.inr 5274, 2), (Sum.inr 5284, 1)]

def sourceForm2426 : Integer.Sparse Master := [(Sum.inr 2173, 1), (Sum.inr 2184, 1), (Sum.inr 2185, 1), (Sum.inr 2228, 2), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2685, 2), (Sum.inr 2688, 1), (Sum.inr 2689, 1), (Sum.inr 2693, 1), (Sum.inr 2694, 1), (Sum.inr 2702, 1), (Sum.inr 2704, 2), (Sum.inr 2705, 1), (Sum.inr 2740, 2), (Sum.inr 2742, 2), (Sum.inr 3024, 2), (Sum.inr 3058, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2439 : Integer.Sparse Master := [(Sum.inr 4366, 1), (Sum.inr 4371, 1), (Sum.inr 4372, 2), (Sum.inr 4461, 1), (Sum.inr 4698, 1), (Sum.inr 4702, 1), (Sum.inr 4703, 2), (Sum.inr 4765, 1), (Sum.inr 4775, 2), (Sum.inr 4805, 1), (Sum.inr 4808, 2), (Sum.inr 4852, 2), (Sum.inr 4856, 2), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 2), (Sum.inr 4893, 1), (Sum.inr 5263, 1), (Sum.inr 5279, 1), (Sum.inr 5290, 1), (Sum.inr 5299, 2)]

def sourceForm2440 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1734, 2), (Sum.inr 1737, 1), (Sum.inr 1742, 1), (Sum.inr 2179, 1), (Sum.inr 2180, 1), (Sum.inr 2211, 2), (Sum.inr 2214, 1), (Sum.inr 2220, 2), (Sum.inr 2241, 1), (Sum.inr 2248, 1), (Sum.inr 2250, 2), (Sum.inr 2260, 2), (Sum.inr 2263, 1), (Sum.inr 2272, 2), (Sum.inr 2274, 2), (Sum.inr 2277, 2), (Sum.inr 2728, 1), (Sum.inr 2748, 1), (Sum.inr 2764, 1), (Sum.inr 2773, 2)]

def sourceForm2441 : Integer.Sparse Master := [(Sum.inr 1824, 1), (Sum.inr 1828, 1), (Sum.inr 1829, 2), (Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

def sourceForm2442 : Integer.Sparse Master := [(Sum.inr 4236, 1), (Sum.inr 4237, 1), (Sum.inr 4238, 2), (Sum.inr 4275, 1), (Sum.inr 4685, 1), (Sum.inr 4686, 1), (Sum.inr 4688, 2), (Sum.inr 4723, 1), (Sum.inr 4724, 2), (Sum.inr 4746, 1), (Sum.inr 4859, 1), (Sum.inr 4860, 2), (Sum.inr 4869, 3), (Sum.inr 4871, 2), (Sum.inr 4874, 2), (Sum.inr 4898, 2), (Sum.inr 5387, 1), (Sum.inr 5403, 1), (Sum.inr 5443, 2), (Sum.inr 5448, 1)]

def sourceForm2443 : Integer.Sparse Master := [(Sum.inr 736, 1), (Sum.inr 737, 1), (Sum.inr 738, 2), (Sum.inr 827, 1), (Sum.inr 1811, 1), (Sum.inr 1812, 1), (Sum.inr 1814, 2), (Sum.inr 1877, 1), (Sum.inr 1878, 2), (Sum.inr 1925, 1), (Sum.inr 2100, 1), (Sum.inr 2101, 2), (Sum.inr 2110, 2), (Sum.inr 2112, 2), (Sum.inr 2115, 2), (Sum.inr 2275, 1), (Sum.inr 2279, 2), (Sum.inr 3739, 1), (Sum.inr 3789, 1), (Sum.inr 3885, 1), (Sum.inr 3889, 2)]

def sourceForm2445 : Integer.Sparse Master := [(Sum.inr 4364, 1), (Sum.inr 4367, 1), (Sum.inr 4369, 1), (Sum.inr 4372, 1), (Sum.inr 4458, 1), (Sum.inr 4696, 1), (Sum.inr 4699, 1), (Sum.inr 4701, 1), (Sum.inr 4703, 1), (Sum.inr 4772, 1), (Sum.inr 4774, 1), (Sum.inr 4775, 1), (Sum.inr 4802, 1), (Sum.inr 4851, 1), (Sum.inr 4853, 1), (Sum.inr 4856, 1), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4869, 1), (Sum.inr 4871, 1), (Sum.inr 4875, 1), (Sum.inr 4888, 1), (Sum.inr 4893, 1), (Sum.inr 4895, 1), (Sum.inr 5255, 1), (Sum.inr 5288, 1), (Sum.inr 5289, 1), (Sum.inr 5290, 1), (Sum.inr 5304, 1)]

def sourceForm2446 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1724, 1), (Sum.inr 1734, 1), (Sum.inr 2198, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 1), (Sum.inr 2211, 1), (Sum.inr 2238, 1), (Sum.inr 2240, 1), (Sum.inr 2241, 1), (Sum.inr 2256, 1), (Sum.inr 2257, 1), (Sum.inr 2259, 1), (Sum.inr 2260, 2), (Sum.inr 2262, 1), (Sum.inr 2263, 1), (Sum.inr 2272, 1), (Sum.inr 2274, 1), (Sum.inr 2275, 1), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2291, 1), (Sum.inr 2718, 1), (Sum.inr 2760, 1), (Sum.inr 2763, 1), (Sum.inr 2764, 1), (Sum.inr 2782, 1)]

def sourceForm2447 : Integer.Sparse Master := [(Sum.inr 1822, 1), (Sum.inr 1825, 1), (Sum.inr 1827, 1), (Sum.inr 1829, 1), (Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 4083, -1)]

def sourceForm2448 : Integer.Sparse Master := [(Sum.inr 4232, 1), (Sum.inr 4233, 1), (Sum.inr 4234, 1), (Sum.inr 4239, 1), (Sum.inr 4268, 1), (Sum.inr 4679, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4689, 1), (Sum.inr 4721, 1), (Sum.inr 4722, 1), (Sum.inr 4725, 1), (Sum.inr 4740, 1), (Sum.inr 4826, 1), (Sum.inr 4827, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4864, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 2), (Sum.inr 4868, 1), (Sum.inr 4875, 1), (Sum.inr 4889, 1), (Sum.inr 4896, 1), (Sum.inr 5388, 1), (Sum.inr 5401, 1), (Sum.inr 5438, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1)]

def sourceForm2449 : Integer.Sparse Master := [(Sum.inr 732, 1), (Sum.inr 733, 1), (Sum.inr 734, 1), (Sum.inr 739, 1), (Sum.inr 824, 1), (Sum.inr 1805, 1), (Sum.inr 1807, 1), (Sum.inr 1810, 1), (Sum.inr 1815, 1), (Sum.inr 1875, 1), (Sum.inr 1876, 1), (Sum.inr 1879, 1), (Sum.inr 1922, 1), (Sum.inr 2077, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2105, 1), (Sum.inr 2106, 1), (Sum.inr 2107, 2), (Sum.inr 2109, 1), (Sum.inr 2116, 1), (Sum.inr 2216, 1), (Sum.inr 2277, 1), (Sum.inr 2278, 1), (Sum.inr 3737, 1), (Sum.inr 3787, 1), (Sum.inr 3876, 1), (Sum.inr 3887, 1), (Sum.inr 3888, 1)]

def sourceForm2450 : Integer.Sparse Master := [(Sum.inr 4449, 1), (Sum.inr 4452, 1), (Sum.inr 4453, 1), (Sum.inr 4462, 1), (Sum.inr 4489, 1), (Sum.inr 4798, 1), (Sum.inr 4799, 1), (Sum.inr 4802, 1), (Sum.inr 4806, 1), (Sum.inr 4826, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4838, 1), (Sum.inr 4849, 1), (Sum.inr 4851, 1), (Sum.inr 4852, 1), (Sum.inr 4860, 1), (Sum.inr 4861, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 1), (Sum.inr 4867, 1), (Sum.inr 4869, 1), (Sum.inr 4870, 1), (Sum.inr 4879, 1), (Sum.inr 4880, 1), (Sum.inr 5169, 1), (Sum.inr 5185, 1), (Sum.inr 5199, 1), (Sum.inr 5203, 1), (Sum.inr 5204, 1)]

def sourceForm2451 : Integer.Sparse Master := [(Sum.inr 4363, 1), (Sum.inr 4365, 1), (Sum.inr 4368, 2), (Sum.inr 4457, 1), (Sum.inr 4695, 1), (Sum.inr 4697, 1), (Sum.inr 4700, 2), (Sum.inr 4771, 1), (Sum.inr 4773, 2), (Sum.inr 4801, 1), (Sum.inr 4863, 1), (Sum.inr 4865, 2), (Sum.inr 4867, 2), (Sum.inr 4868, 2), (Sum.inr 4874, 2), (Sum.inr 4888, 1), (Sum.inr 4894, 2), (Sum.inr 5249, 1), (Sum.inr 5279, 1), (Sum.inr 5282, 1), (Sum.inr 5291, 2)]

def sourceForm2452 : Integer.Sparse Master := [(Sum.inr 1319, 1), (Sum.inr 1320, 1), (Sum.inr 1321, 2), (Sum.inr 1414, 1), (Sum.inr 2895, 1), (Sum.inr 2899, 1), (Sum.inr 2966, 2), (Sum.inr 3066, 1), (Sum.inr 3078, 1), (Sum.inr 3079, 1), (Sum.inr 3103, 2), (Sum.inr 3130, 1), (Sum.inr 3131, 2), (Sum.inr 3163, 2), (Sum.inr 3179, 1), (Sum.inr 3180, 2), (Sum.inr 3185, 2), (Sum.inr 3187, 2), (Sum.inr 3205, 1), (Sum.inr 3227, 1), (Sum.inr 3230, 2)]

def sourceForm2453 : Integer.Sparse Master := [(Sum.inr 1697, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 1), (Sum.inr 1712, 2), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 2), (Sum.inr 2231, 1), (Sum.inr 2232, 1), (Sum.inr 2239, 1), (Sum.inr 2242, 2), (Sum.inr 2244, 1), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 2), (Sum.inr 2264, 2), (Sum.inr 2276, 2), (Sum.inr 2708, 1), (Sum.inr 2748, 1), (Sum.inr 2751, 1), (Sum.inr 2765, 2)]

def sourceForm2454 : Integer.Sparse Master := [(Sum.inr 1821, 1), (Sum.inr 1823, 1), (Sum.inr 1826, 2), (Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 4084, -1)]

def sourceForm2455 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 1821, 1), (Sum.inr 2104, 1), (Sum.inr 2106, 3), (Sum.inr 4084, -1)]

def sourceForm2456 : Integer.Sparse Master := [(Sum.inr 4230, 1), (Sum.inr 4231, 1), (Sum.inr 4234, 2), (Sum.inr 4255, 1), (Sum.inr 4676, 1), (Sum.inr 4678, 1), (Sum.inr 4684, 2), (Sum.inr 4720, 1), (Sum.inr 4722, 2), (Sum.inr 4731, 1), (Sum.inr 4798, 2), (Sum.inr 4800, 2), (Sum.inr 4810, 2), (Sum.inr 4828, 2), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 1), (Sum.inr 5387, 1), (Sum.inr 5400, 1), (Sum.inr 5432, 2), (Sum.inr 5450, 1)]

def sourceForm2457 : Integer.Sparse Master := [(Sum.inr 730, 1), (Sum.inr 731, 1), (Sum.inr 734, 2), (Sum.inr 823, 1), (Sum.inr 1802, 1), (Sum.inr 1804, 1), (Sum.inr 1810, 2), (Sum.inr 1874, 1), (Sum.inr 1876, 2), (Sum.inr 1921, 1), (Sum.inr 2018, 2), (Sum.inr 2075, 2), (Sum.inr 2082, 2), (Sum.inr 2105, 1), (Sum.inr 2107, 2), (Sum.inr 2215, 2), (Sum.inr 2277, 1), (Sum.inr 3736, 1), (Sum.inr 3786, 1), (Sum.inr 3850, 2), (Sum.inr 3887, 1)]

def sourceForm2458 : Integer.Sparse Master := [(Sum.inr 4435, 1), (Sum.inr 4437, 1), (Sum.inr 4443, 1), (Sum.inr 4452, 2), (Sum.inr 4791, 1), (Sum.inr 4794, 1), (Sum.inr 4798, 2), (Sum.inr 4801, 1), (Sum.inr 4832, 1), (Sum.inr 4834, 2), (Sum.inr 4848, 2), (Sum.inr 4850, 2), (Sum.inr 4851, 1), (Sum.inr 4855, 2), (Sum.inr 4860, 2), (Sum.inr 4866, 2), (Sum.inr 4879, 1), (Sum.inr 5168, 1), (Sum.inr 5184, 1), (Sum.inr 5198, 2), (Sum.inr 5203, 1)]

def sourceForm2460 : Integer.Sparse Master := [(Sum.inr 1877, 1), (Sum.inr 1879, 2), (Sum.inr 1912, 1), (Sum.inr 2077, 1), (Sum.inr 3446, 1), (Sum.inr 4079, -1)]

def sourceForm2461 : Integer.Sparse Master := [(Sum.inr 4331, 1), (Sum.inr 4332, 2), (Sum.inr 4351, 1), (Sum.inr 4461, 1), (Sum.inr 4667, 1), (Sum.inr 4668, 2), (Sum.inr 4685, 1), (Sum.inr 4765, 1), (Sum.inr 4775, 2), (Sum.inr 4793, 2), (Sum.inr 4795, 2), (Sum.inr 4802, 2), (Sum.inr 4805, 2), (Sum.inr 4833, 1), (Sum.inr 4869, 1), (Sum.inr 4889, 2), (Sum.inr 4893, 1), (Sum.inr 5231, 1), (Sum.inr 5257, 1), (Sum.inr 5263, 1), (Sum.inr 5265, 2)]

def sourceForm2462 : Integer.Sparse Master := [(Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1737, 1), (Sum.inr 2154, 2), (Sum.inr 2156, 1), (Sum.inr 2160, 1), (Sum.inr 2179, 1), (Sum.inr 2202, 2), (Sum.inr 2204, 1), (Sum.inr 2211, 2), (Sum.inr 2213, 2), (Sum.inr 2214, 2), (Sum.inr 2219, 2), (Sum.inr 2263, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 2), (Sum.inr 2676, 1), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2730, 2)]

def sourceForm2463 : Integer.Sparse Master := [(Sum.inr 1793, 1), (Sum.inr 1794, 2), (Sum.inr 1811, 1), (Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2464 : Integer.Sparse Master := [(Sum.inr 4199, 1), (Sum.inr 4200, 2), (Sum.inr 4217, 1), (Sum.inr 4252, 1), (Sum.inr 4633, 1), (Sum.inr 4634, 2), (Sum.inr 4648, 1), (Sum.inr 4764, 1), (Sum.inr 4766, 2), (Sum.inr 4798, 2), (Sum.inr 4805, 1), (Sum.inr 4807, 2), (Sum.inr 4810, 2), (Sum.inr 4826, 1), (Sum.inr 4839, 2), (Sum.inr 4864, 1), (Sum.inr 4889, 2), (Sum.inr 5354, 1), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5435, 2)]

def sourceForm2466 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4329, 1), (Sum.inr 4332, 1), (Sum.inr 4344, 1), (Sum.inr 4458, 1), (Sum.inr 4664, 1), (Sum.inr 4666, 1), (Sum.inr 4668, 1), (Sum.inr 4679, 1), (Sum.inr 4772, 1), (Sum.inr 4774, 1), (Sum.inr 4775, 1), (Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4811, 1), (Sum.inr 4833, 1), (Sum.inr 4838, 1), (Sum.inr 4866, 1), (Sum.inr 4888, 1), (Sum.inr 4893, 1), (Sum.inr 4895, 1), (Sum.inr 5226, 1), (Sum.inr 5255, 1), (Sum.inr 5256, 1), (Sum.inr 5257, 1), (Sum.inr 5271, 1)]

def sourceForm2467 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1331, 1), (Sum.inr 1339, 1), (Sum.inr 1411, 1), (Sum.inr 2423, 1), (Sum.inr 2430, 1), (Sum.inr 2471, 1), (Sum.inr 2574, 1), (Sum.inr 3084, 1), (Sum.inr 3085, 1), (Sum.inr 3087, 1), (Sum.inr 3091, 1), (Sum.inr 3109, 1), (Sum.inr 3133, 1), (Sum.inr 3135, 1), (Sum.inr 3139, 1), (Sum.inr 3162, 1), (Sum.inr 3164, 1), (Sum.inr 3184, 1), (Sum.inr 3199, 1), (Sum.inr 3203, 1), (Sum.inr 3204, 2), (Sum.inr 3207, 1), (Sum.inr 3212, 1), (Sum.inr 3213, 1), (Sum.inr 3227, 1), (Sum.inr 3228, 1), (Sum.inr 3229, 1)]

def sourceForm2468 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1671, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1724, 1), (Sum.inr 2147, 1), (Sum.inr 2148, 1), (Sum.inr 2150, 1), (Sum.inr 2154, 1), (Sum.inr 2198, 1), (Sum.inr 2199, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2204, 1), (Sum.inr 2211, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 1), (Sum.inr 2224, 1), (Sum.inr 2225, 1), (Sum.inr 2227, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2263, 1), (Sum.inr 2291, 1), (Sum.inr 2669, 1), (Sum.inr 2718, 1), (Sum.inr 2720, 1), (Sum.inr 2721, 1), (Sum.inr 2739, 1)]

def sourceForm2469 : Integer.Sparse Master := [(Sum.inr 1790, 1), (Sum.inr 1792, 1), (Sum.inr 1794, 1), (Sum.inr 1805, 1), (Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 4083, -1)]

def sourceForm2470 : Integer.Sparse Master := [(Sum.inr 4196, 1), (Sum.inr 4197, 1), (Sum.inr 4201, 1), (Sum.inr 4210, 1), (Sum.inr 4249, 1), (Sum.inr 4631, 1), (Sum.inr 4632, 1), (Sum.inr 4635, 1), (Sum.inr 4642, 1), (Sum.inr 4760, 1), (Sum.inr 4763, 1), (Sum.inr 4767, 1), (Sum.inr 4779, 1), (Sum.inr 4782, 1), (Sum.inr 4787, 1), (Sum.inr 4801, 1), (Sum.inr 4802, 2), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4831, 2), (Sum.inr 4835, 1), (Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 5352, 1), (Sum.inr 5416, 1), (Sum.inr 5424, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 1)]

def sourceForm2471 : Integer.Sparse Master := [(Sum.inr 4396, 1), (Sum.inr 4397, 1), (Sum.inr 4400, 1), (Sum.inr 4417, 1), (Sum.inr 4449, 1), (Sum.inr 4736, 1), (Sum.inr 4737, 1), (Sum.inr 4739, 1), (Sum.inr 4740, 1), (Sum.inr 4798, 1), (Sum.inr 4799, 1), (Sum.inr 4801, 1), (Sum.inr 4802, 1), (Sum.inr 4803, 1), (Sum.inr 4805, 1), (Sum.inr 4813, 1), (Sum.inr 4815, 1), (Sum.inr 4816, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4838, 1), (Sum.inr 4849, 1), (Sum.inr 4851, 1), (Sum.inr 4852, 1), (Sum.inr 4866, 1), (Sum.inr 5073, 1), (Sum.inr 5145, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 1), (Sum.inr 5169, 1)]

def sourceForm2472 : Integer.Sparse Master := [(Sum.inr 4326, 1), (Sum.inr 4328, 2), (Sum.inr 4341, 1), (Sum.inr 4457, 1), (Sum.inr 4663, 1), (Sum.inr 4665, 2), (Sum.inr 4676, 1), (Sum.inr 4771, 1), (Sum.inr 4773, 2), (Sum.inr 4803, 2), (Sum.inr 4804, 2), (Sum.inr 4810, 2), (Sum.inr 4831, 1), (Sum.inr 4834, 2), (Sum.inr 4865, 1), (Sum.inr 4888, 1), (Sum.inr 4894, 2), (Sum.inr 5219, 1), (Sum.inr 5249, 1), (Sum.inr 5250, 1), (Sum.inr 5258, 2)]

def sourceForm2473 : Integer.Sparse Master := [(Sum.inr 1329, 1), (Sum.inr 1330, 2), (Sum.inr 1341, 1), (Sum.inr 1414, 1), (Sum.inr 2890, 1), (Sum.inr 2895, 1), (Sum.inr 2941, 2), (Sum.inr 3065, 1), (Sum.inr 3066, 1), (Sum.inr 3069, 1), (Sum.inr 3089, 2), (Sum.inr 3134, 2), (Sum.inr 3140, 1), (Sum.inr 3163, 2), (Sum.inr 3185, 1), (Sum.inr 3202, 2), (Sum.inr 3206, 2), (Sum.inr 3209, 1), (Sum.inr 3214, 2), (Sum.inr 3227, 1), (Sum.inr 3230, 2)]

def sourceForm2474 : Integer.Sparse Master := [(Sum.inr 1663, 1), (Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1707, 1), (Sum.inr 2140, 1), (Sum.inr 2141, 1), (Sum.inr 2144, 2), (Sum.inr 2189, 1), (Sum.inr 2191, 1), (Sum.inr 2194, 2), (Sum.inr 2195, 2), (Sum.inr 2203, 2), (Sum.inr 2205, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2264, 2), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 2709, 1), (Sum.inr 2722, 2)]

def sourceForm2475 : Integer.Sparse Master := [(Sum.inr 4195, 1), (Sum.inr 4197, 2), (Sum.inr 4207, 1), (Sum.inr 4248, 1), (Sum.inr 4630, 1), (Sum.inr 4632, 2), (Sum.inr 4640, 1), (Sum.inr 4759, 1), (Sum.inr 4763, 2), (Sum.inr 4778, 2), (Sum.inr 4782, 4), (Sum.inr 4801, 3), (Sum.inr 4802, 2), (Sum.inr 4831, 1), (Sum.inr 4887, 1), (Sum.inr 5351, 1), (Sum.inr 5415, 1), (Sum.inr 5423, 2), (Sum.inr 5433, 1)]

def sourceForm2476 : Integer.Sparse Master := [(Sum.inr 4390, 1), (Sum.inr 4392, 1), (Sum.inr 4396, 2), (Sum.inr 4435, 1), (Sum.inr 4728, 1), (Sum.inr 4731, 1), (Sum.inr 4736, 2), (Sum.inr 4797, 2), (Sum.inr 4798, 2), (Sum.inr 4802, 2), (Sum.inr 4812, 2), (Sum.inr 4815, 1), (Sum.inr 4832, 1), (Sum.inr 4834, 2), (Sum.inr 4848, 2), (Sum.inr 4851, 1), (Sum.inr 4865, 1), (Sum.inr 5072, 1), (Sum.inr 5144, 2), (Sum.inr 5148, 1), (Sum.inr 5168, 1)]

def sourceForm2477 : Integer.Sparse Master := [(Sum.inr 4345, 1), (Sum.inr 4353, 1), (Sum.inr 4354, 1), (Sum.inr 4357, 1), (Sum.inr 4503, 1), (Sum.inr 4680, 1), (Sum.inr 4687, 1), (Sum.inr 4688, 1), (Sum.inr 4690, 1), (Sum.inr 4765, 1), (Sum.inr 4766, 1), (Sum.inr 4768, 1), (Sum.inr 4803, 1), (Sum.inr 4808, 1), (Sum.inr 4810, 1), (Sum.inr 4816, 1), (Sum.inr 4819, 1), (Sum.inr 4821, 1), (Sum.inr 4831, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4839, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5233, 1), (Sum.inr 5244, 1), (Sum.inr 5259, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1)]

def sourceForm2478 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1681, 1), (Sum.inr 1682, 1), (Sum.inr 1686, 1), (Sum.inr 1739, 1), (Sum.inr 2145, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2162, 1), (Sum.inr 2177, 1), (Sum.inr 2178, 1), (Sum.inr 2179, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 1), (Sum.inr 2196, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2220, 1), (Sum.inr 2221, 1), (Sum.inr 2265, 1), (Sum.inr 2278, 1), (Sum.inr 2279, 1), (Sum.inr 2678, 1), (Sum.inr 2698, 1), (Sum.inr 2723, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1)]

def sourceForm2479 : Integer.Sparse Master := [(Sum.inr 1806, 1), (Sum.inr 1813, 1), (Sum.inr 1814, 1), (Sum.inr 1816, 1), (Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 4084, -1)]

def sourceForm2481 : Integer.Sparse Master := [(Sum.inr 4407, 1), (Sum.inr 4410, 1), (Sum.inr 4412, 1), (Sum.inr 4424, 1), (Sum.inr 4471, 1), (Sum.inr 4740, 1), (Sum.inr 4747, 1), (Sum.inr 4750, 1), (Sum.inr 4752, 1), (Sum.inr 4783, 1), (Sum.inr 4785, 1), (Sum.inr 4787, 1), (Sum.inr 4803, 1), (Sum.inr 4805, 1), (Sum.inr 4806, 1), (Sum.inr 4813, 1), (Sum.inr 4835, 1), (Sum.inr 4836, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 1), (Sum.inr 4840, 1), (Sum.inr 4842, 1), (Sum.inr 4867, 1), (Sum.inr 4869, 1), (Sum.inr 4870, 1), (Sum.inr 5105, 1), (Sum.inr 5138, 1), (Sum.inr 5170, 1), (Sum.inr 5172, 1), (Sum.inr 5173, 1)]

def sourceForm2482 : Integer.Sparse Master := [(Sum.inr 4342, 1), (Sum.inr 4347, 1), (Sum.inr 4349, 1), (Sum.inr 4357, 1), (Sum.inr 4499, 1), (Sum.inr 4677, 1), (Sum.inr 4682, 1), (Sum.inr 4684, 1), (Sum.inr 4690, 1), (Sum.inr 4761, 1), (Sum.inr 4763, 1), (Sum.inr 4768, 1), (Sum.inr 4815, 1), (Sum.inr 4817, 1), (Sum.inr 4821, 1), (Sum.inr 4831, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 2), (Sum.inr 4839, 1), (Sum.inr 4843, 1), (Sum.inr 4846, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4901, 1), (Sum.inr 5229, 1), (Sum.inr 5242, 1), (Sum.inr 5259, 1), (Sum.inr 5260, 1), (Sum.inr 5275, 1)]

def sourceForm2483 : Integer.Sparse Master := [(Sum.inr 1665, 1), (Sum.inr 1675, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1728, 1), (Sum.inr 2142, 1), (Sum.inr 2152, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2174, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 2), (Sum.inr 2207, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2229, 1), (Sum.inr 2230, 1), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2293, 1), (Sum.inr 2673, 1), (Sum.inr 2695, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2743, 1)]

def sourceForm2484 : Integer.Sparse Master := [(Sum.inr 1803, 1), (Sum.inr 1808, 1), (Sum.inr 1810, 1), (Sum.inr 1816, 1), (Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 4084, -1)]

def sourceForm2485 : Integer.Sparse Master := [(Sum.inr 4210, 1), (Sum.inr 4212, 1), (Sum.inr 4213, 1), (Sum.inr 4224, 1), (Sum.inr 4265, 1), (Sum.inr 4642, 1), (Sum.inr 4644, 1), (Sum.inr 4645, 1), (Sum.inr 4654, 1), (Sum.inr 4709, 1), (Sum.inr 4710, 1), (Sum.inr 4717, 1), (Sum.inr 4737, 1), (Sum.inr 4787, 1), (Sum.inr 4788, 2), (Sum.inr 4802, 1), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4831, 1), (Sum.inr 4832, 1), (Sum.inr 4835, 2), (Sum.inr 4888, 2), (Sum.inr 5368, 1), (Sum.inr 5395, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1)]

def sourceForm2486 : Integer.Sparse Master := [(Sum.inr 4397, 1), (Sum.inr 4402, 1), (Sum.inr 4404, 1), (Sum.inr 4424, 1), (Sum.inr 4453, 1), (Sum.inr 4737, 1), (Sum.inr 4742, 1), (Sum.inr 4745, 1), (Sum.inr 4752, 1), (Sum.inr 4780, 1), (Sum.inr 4782, 1), (Sum.inr 4787, 1), (Sum.inr 4799, 2), (Sum.inr 4802, 1), (Sum.inr 4803, 1), (Sum.inr 4828, 1), (Sum.inr 4829, 1), (Sum.inr 4834, 1), (Sum.inr 4836, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 1), (Sum.inr 4861, 1), (Sum.inr 4866, 1), (Sum.inr 4867, 1), (Sum.inr 5102, 1), (Sum.inr 5135, 1), (Sum.inr 5164, 1), (Sum.inr 5169, 1), (Sum.inr 5170, 1)]

def sourceForm2487 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4344, 1), (Sum.inr 4352, 1), (Sum.inr 4355, 2), (Sum.inr 4502, 1), (Sum.inr 4679, 1), (Sum.inr 4686, 1), (Sum.inr 4689, 2), (Sum.inr 4764, 1), (Sum.inr 4767, 2), (Sum.inr 4802, 2), (Sum.inr 4807, 2), (Sum.inr 4811, 2), (Sum.inr 4833, 1), (Sum.inr 4838, 3), (Sum.inr 4895, 2), (Sum.inr 5237, 1), (Sum.inr 5247, 1), (Sum.inr 5271, 2), (Sum.inr 5273, 1)]

def sourceForm2488 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4341, 1), (Sum.inr 4346, 1), (Sum.inr 4349, 1), (Sum.inr 4354, 1), (Sum.inr 4498, 1), (Sum.inr 4676, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4688, 1), (Sum.inr 4760, 1), (Sum.inr 4763, 1), (Sum.inr 4766, 1), (Sum.inr 4801, 1), (Sum.inr 4804, 1), (Sum.inr 4810, 1), (Sum.inr 4831, 1), (Sum.inr 4834, 2), (Sum.inr 4835, 1), (Sum.inr 4839, 1), (Sum.inr 4841, 1), (Sum.inr 4846, 1), (Sum.inr 4894, 1), (Sum.inr 4895, 1), (Sum.inr 5228, 1), (Sum.inr 5241, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5274, 1)]

def sourceForm2489 : Integer.Sparse Master := [(Sum.inr 4340, 1), (Sum.inr 4343, 1), (Sum.inr 4348, 2), (Sum.inr 4496, 1), (Sum.inr 4675, 1), (Sum.inr 4678, 1), (Sum.inr 4683, 2), (Sum.inr 4759, 1), (Sum.inr 4762, 2), (Sum.inr 4830, 1), (Sum.inr 4832, 3), (Sum.inr 4836, 2), (Sum.inr 4837, 2), (Sum.inr 4845, 2), (Sum.inr 4890, 1), (Sum.inr 4897, 2), (Sum.inr 5222, 1), (Sum.inr 5239, 1), (Sum.inr 5252, 1), (Sum.inr 5261, 2)]

def sourceForm2491 : Integer.Sparse Master := [(Sum.inr 1662, 1), (Sum.inr 1666, 1), (Sum.inr 1669, 2), (Sum.inr 1710, 1), (Sum.inr 2139, 1), (Sum.inr 2143, 1), (Sum.inr 2146, 2), (Sum.inr 2170, 1), (Sum.inr 2171, 2), (Sum.inr 2187, 1), (Sum.inr 2193, 3), (Sum.inr 2197, 2), (Sum.inr 2208, 2), (Sum.inr 2218, 2), (Sum.inr 2247, 1), (Sum.inr 2268, 2), (Sum.inr 2664, 1), (Sum.inr 2691, 1), (Sum.inr 2712, 1), (Sum.inr 2726, 2)]

def sourceForm2492 : Integer.Sparse Master := [(Sum.inr 1801, 1), (Sum.inr 1804, 1), (Sum.inr 1809, 2), (Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 4085, -1)]

def sourceForm2493 : Integer.Sparse Master := [(Sum.inr 918, 1), (Sum.inr 1801, 1), (Sum.inr 2050, 1), (Sum.inr 2052, 3), (Sum.inr 4085, -1)]

def sourceForm2494 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4322, 1), (Sum.inr 4323, 2), (Sum.inr 4337, 1), (Sum.inr 4423, 1), (Sum.inr 4660, 1), (Sum.inr 4661, 2), (Sum.inr 4672, 1), (Sum.inr 4712, 1), (Sum.inr 4715, 2), (Sum.inr 4779, 2), (Sum.inr 4782, 2), (Sum.inr 4787, 2), (Sum.inr 4798, 2), (Sum.inr 4826, 1), (Sum.inr 4834, 2), (Sum.inr 4838, 1), (Sum.inr 5058, 1), (Sum.inr 5123, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1)]

def sourceForm2495 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4300, 1), (Sum.inr 4301, 2), (Sum.inr 4307, 1), (Sum.inr 4417, 1), (Sum.inr 4641, 1), (Sum.inr 4642, 2), (Sum.inr 4648, 1), (Sum.inr 4736, 2), (Sum.inr 4737, 2), (Sum.inr 4740, 4), (Sum.inr 4746, 1), (Sum.inr 4752, 2), (Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4838, 1), (Sum.inr 4998, 1), (Sum.inr 5073, 2), (Sum.inr 5076, 1), (Sum.inr 5104, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2496 : Integer.Sparse Master := [(Sum.inr 4063, 1), (Sum.inr 4064, 1), (Sum.inr 4065, 2), (Sum.inr 4069, 1), (Sum.inr 4073, 1), (Sum.inr 4074, 1), (Sum.inr 4075, 2), (Sum.inr 4077, 1), (Sum.inr 4078, 2), (Sum.inr 4079, 1), (Sum.inr 4080, 5), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2), (Sum.inr 4088, 1), (Sum.inr 4090, 1), (Sum.inr 4091, 1), (Sum.inr 4092, 2)]

def sourceForm2497 : Integer.Sparse Master := [(Sum.inr 3128, 3), (Sum.inr 3130, 1), (Sum.inr 3155, 1), (Sum.inr 3390, 1), (Sum.inr 4083, -1)]

def sourceForm2499 : Integer.Sparse Master := [(Sum.inr 4541, 2), (Sum.inr 4544, 2), (Sum.inr 4622, 1), (Sum.inr 4968, 2), (Sum.inr 4971, 2), (Sum.inr 5148, 2), (Sum.inr 5149, 4), (Sum.inr 5169, 4), (Sum.inr 5172, 2), (Sum.inr 5292, 2), (Sum.inr 5307, 2), (Sum.inr 5386, 1), (Sum.inr 5433, 2), (Sum.inr 5440, 2)]

def sourceForm2500 : Integer.Sparse Master := [(Sum.inr 4341, 2), (Sum.inr 4344, 2), (Sum.inr 4456, 1), (Sum.inr 4939, 2), (Sum.inr 4941, 2), (Sum.inr 5134, 4), (Sum.inr 5137, 2), (Sum.inr 5168, 2), (Sum.inr 5169, 4), (Sum.inr 5257, 2), (Sum.inr 5292, 2), (Sum.inr 5464, 1), (Sum.inr 5482, 2), (Sum.inr 5486, 2)]

def sourceForm2502 : Integer.Sparse Master := [(Sum.inr 4540, 1), (Sum.inr 4542, 3), (Sum.inr 4618, 1), (Sum.inr 4964, 3), (Sum.inr 4975, 1), (Sum.inr 5137, 3), (Sum.inr 5145, 6), (Sum.inr 5150, 3), (Sum.inr 5273, 1), (Sum.inr 5290, 3), (Sum.inr 5383, 1), (Sum.inr 5427, 1), (Sum.inr 5431, 3)]

def sourceForm2503 : Integer.Sparse Master := [(Sum.inr 2688, 1), (Sum.inr 2690, 1), (Sum.inr 2700, 3), (Sum.inr 3257, 3), (Sum.inr 3304, 1), (Sum.inr 3521, 3), (Sum.inr 3546, 1), (Sum.inr 3554, 3), (Sum.inr 3562, 6), (Sum.inr 3581, 3), (Sum.inr 3844, 1), (Sum.inr 3867, 1), (Sum.inr 3875, 3)]

def sourceForm2504 : Integer.Sparse Master := [(Sum.inr 4337, 3), (Sum.inr 4351, 1), (Sum.inr 4451, 1), (Sum.inr 4936, 3), (Sum.inr 4947, 1), (Sum.inr 5123, 3), (Sum.inr 5163, 6), (Sum.inr 5172, 3), (Sum.inr 5227, 1), (Sum.inr 5290, 3), (Sum.inr 5447, 1), (Sum.inr 5462, 1), (Sum.inr 5485, 3)]

def sourceForm2508 : Integer.Sparse Master := [(Sum.inr 4364, 2), (Sum.inr 4366, 2), (Sum.inr 4456, 1), (Sum.inr 4696, 2), (Sum.inr 4698, 2), (Sum.inr 4851, 2), (Sum.inr 4852, 4), (Sum.inr 4866, 4), (Sum.inr 4869, 2), (Sum.inr 4887, 2), (Sum.inr 4893, 2), (Sum.inr 5278, 1), (Sum.inr 5281, 2), (Sum.inr 5290, 2)]

def sourceForm2509 : Integer.Sparse Master := [(Sum.inr 1703, 2), (Sum.inr 1706, 1), (Sum.inr 1711, 2), (Sum.inr 2238, 2), (Sum.inr 2240, 2), (Sum.inr 2243, 2), (Sum.inr 2248, 2), (Sum.inr 2250, 4), (Sum.inr 2260, 4), (Sum.inr 2263, 2), (Sum.inr 2275, 2), (Sum.inr 2747, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 2)]

def sourceForm2510 : Integer.Sparse Master := [(Sum.inr 4230, 2), (Sum.inr 4232, 2), (Sum.inr 4252, 1), (Sum.inr 4676, 2), (Sum.inr 4679, 2), (Sum.inr 4798, 4), (Sum.inr 4805, 2), (Sum.inr 4826, 2), (Sum.inr 4865, 2), (Sum.inr 4866, 4), (Sum.inr 4889, 2), (Sum.inr 5386, 1), (Sum.inr 5431, 2), (Sum.inr 5450, 2)]

def sourceForm2511 : Integer.Sparse Master := [(Sum.inr 4436, 2), (Sum.inr 4441, 1), (Sum.inr 4451, 2), (Sum.inr 4831, 2), (Sum.inr 4833, 2), (Sum.inr 4849, 4), (Sum.inr 4854, 2), (Sum.inr 4859, 2), (Sum.inr 4863, 2), (Sum.inr 4864, 4), (Sum.inr 4878, 2), (Sum.inr 5167, 1), (Sum.inr 5197, 2), (Sum.inr 5202, 2)]

def sourceForm2512 : Integer.Sparse Master := [(Sum.inr 4341, 1), (Sum.inr 4342, 1), (Sum.inr 4345, 2), (Sum.inr 4495, 1), (Sum.inr 4676, 1), (Sum.inr 4677, 1), (Sum.inr 4680, 2), (Sum.inr 4801, 1), (Sum.inr 4803, 2), (Sum.inr 4815, 1), (Sum.inr 4816, 2), (Sum.inr 4834, 2), (Sum.inr 4835, 2), (Sum.inr 4839, 2), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4895, 2), (Sum.inr 5220, 1), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5259, 2)]

def sourceForm2513 : Integer.Sparse Master := [(Sum.inr 1664, 1), (Sum.inr 1665, 1), (Sum.inr 1668, 2), (Sum.inr 1708, 1), (Sum.inr 2141, 1), (Sum.inr 2142, 1), (Sum.inr 2145, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 2195, 2), (Sum.inr 2196, 2), (Sum.inr 2205, 2), (Sum.inr 2206, 2), (Sum.inr 2216, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2265, 2), (Sum.inr 2662, 1), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 2723, 2)]

def sourceForm2514 : Integer.Sparse Master := [(Sum.inr 4063, 4), (Sum.inr 4068, 1), (Sum.inr 4073, 4), (Sum.inr 4080, 12), (Sum.inr 4083, 4), (Sum.inr 4087, 1), (Sum.inr 4091, 4)]

def sourceForm2515 : Integer.Sparse Master := [(Sum.inr 1814, 1), (Sum.inr 3131, 1), (Sum.inr 3365, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3395, 1), (Sum.inr 4084, -1)]

def sourceForm2516 : Integer.Sparse Master := [(Sum.inr 2362, 1), (Sum.inr 3032, 1), (Sum.inr 3033, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def sourceForm2519 : Integer.Sparse Master := [(Sum.inr 2343, 1), (Sum.inr 2819, 1), (Sum.inr 3673, 1), (Sum.inr 3699, 1), (Sum.inr 3705, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

def sourceForm2520 : Integer.Sparse Master := [(Sum.inr 2324, 1), (Sum.inr 2801, 1), (Sum.inr 3676, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

def sourceForm2521 : Integer.Sparse Master := [(Sum.inr 2350, 1), (Sum.inr 3134, 1), (Sum.inr 3708, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3722, 1), (Sum.inr 4092, -1)]

def sourceForm2522 : Integer.Sparse Master := [(Sum.inr 2824, 2), (Sum.inr 3709, 1), (Sum.inr 3716, 1), (Sum.inr 3779, 1), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

def sourceForm2523 : Integer.Sparse Master := [(Sum.inr 2351, 1), (Sum.inr 3135, 1), (Sum.inr 3709, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 2), (Sum.inr 4091, -1)]

def sourceForm2524 : Integer.Sparse Master := [(Sum.inr 4688, 4), (Sum.inr 4691, 1), (Sum.inr 4693, 2), (Sum.inr 4874, 2), (Sum.inr 4973, 4), (Sum.inr 4979, 1), (Sum.inr 5176, 2), (Sum.inr 5372, 2), (Sum.inr 5384, 4), (Sum.inr 5387, 4), (Sum.inr 5441, 1), (Sum.inr 5443, 2), (Sum.inr 5449, 1)]

def sourceForm2525 : Integer.Sparse Master := [(Sum.inr 1814, 4), (Sum.inr 1817, 1), (Sum.inr 1819, 2), (Sum.inr 2115, 2), (Sum.inr 2817, 4), (Sum.inr 2820, 1), (Sum.inr 2968, 2), (Sum.inr 3708, 2), (Sum.inr 3732, 4), (Sum.inr 3739, 4), (Sum.inr 3886, 1), (Sum.inr 3889, 2), (Sum.inr 4037, 1)]

def sourceForm2526 : Integer.Sparse Master := [(Sum.inr 5232, 8), (Sum.inr 5235, 2), (Sum.inr 5238, 4), (Sum.inr 5297, 2), (Sum.inr 5355, 8), (Sum.inr 5371, 2), (Sum.inr 5376, 2), (Sum.inr 5390, 2)]

def sourceForm2527 : Integer.Sparse Master := [(Sum.inr 4689, 2), (Sum.inr 4692, 2), (Sum.inr 4875, 1), (Sum.inr 4949, 4), (Sum.inr 4953, 2), (Sum.inr 4974, 2), (Sum.inr 5176, 2), (Sum.inr 5177, 1), (Sum.inr 5373, 2), (Sum.inr 5388, 4), (Sum.inr 5404, 2), (Sum.inr 5418, 2), (Sum.inr 5442, 2), (Sum.inr 5451, 2)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2528 : Integer.Sparse Master := [(Sum.inr 1815, 2), (Sum.inr 1818, 2), (Sum.inr 2116, 1), (Sum.inr 2341, 4), (Sum.inr 2345, 2), (Sum.inr 2604, 2), (Sum.inr 2818, 2), (Sum.inr 2969, 1), (Sum.inr 3709, 2), (Sum.inr 3737, 4), (Sum.inr 3790, 2), (Sum.inr 3888, 2), (Sum.inr 3933, 2), (Sum.inr 4001, 2)]

def sourceForm2529 : Integer.Sparse Master := [(Sum.inr 5236, 4), (Sum.inr 5238, 4), (Sum.inr 5303, 1), (Sum.inr 5355, 8), (Sum.inr 5356, 4), (Sum.inr 5371, 4), (Sum.inr 5377, 2), (Sum.inr 5389, 2), (Sum.inr 5466, 1)]

def sourceForm2532 : Integer.Sparse Master := [(Sum.inr 4668, 1), (Sum.inr 4669, 1), (Sum.inr 4670, 1), (Sum.inr 4690, 1), (Sum.inr 4856, 1), (Sum.inr 4931, 1), (Sum.inr 4934, 1), (Sum.inr 4949, 1), (Sum.inr 4955, 1), (Sum.inr 4957, 1), (Sum.inr 4959, 1), (Sum.inr 4966, 1), (Sum.inr 4973, 1), (Sum.inr 5080, 1), (Sum.inr 5141, 1), (Sum.inr 5188, 1), (Sum.inr 5336, 1), (Sum.inr 5339, 1), (Sum.inr 5351, 1), (Sum.inr 5353, 1), (Sum.inr 5367, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5384, 1), (Sum.inr 5385, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1), (Sum.inr 5428, 1), (Sum.inr 5446, 1)]

def sourceForm2533 : Integer.Sparse Master := [(Sum.inr 1794, 1), (Sum.inr 1795, 1), (Sum.inr 1796, 1), (Sum.inr 1816, 1), (Sum.inr 2094, 1), (Sum.inr 2350, 1), (Sum.inr 2352, 1), (Sum.inr 2359, 1), (Sum.inr 2620, 1), (Sum.inr 2801, 1), (Sum.inr 2802, 1), (Sum.inr 2819, 1), (Sum.inr 2824, 1), (Sum.inr 2829, 1), (Sum.inr 2943, 1), (Sum.inr 2990, 1), (Sum.inr 3710, 1), (Sum.inr 3711, 1), (Sum.inr 3724, 1), (Sum.inr 3727, 1), (Sum.inr 3733, 1), (Sum.inr 3738, 1), (Sum.inr 3783, 1), (Sum.inr 3831, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3937, 1), (Sum.inr 3941, 1), (Sum.inr 4003, 1), (Sum.inr 4035, 1)]

def sourceForm2534 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2155, 1), (Sum.inr 2158, 1), (Sum.inr 2164, 1), (Sum.inr 2274, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3512, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3555, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3757, 1), (Sum.inr 3760, 1), (Sum.inr 3761, 1), (Sum.inr 3766, 1), (Sum.inr 3771, 1), (Sum.inr 3795, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3845, 1), (Sum.inr 3868, 1), (Sum.inr 3884, 1)]

def sourceForm2535 : Integer.Sparse Master := [(Sum.inr 2348, 1), (Sum.inr 3133, 1), (Sum.inr 3671, 1), (Sum.inr 3693, 1), (Sum.inr 3719, 1), (Sum.inr 3720, 1), (Sum.inr 4092, -1)]

def sourceForm2536 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2798, 1), (Sum.inr 3674, 1), (Sum.inr 3689, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def sourceForm2537 : Integer.Sparse Master := [(Sum.inr 2356, 1), (Sum.inr 3138, 1), (Sum.inr 3674, 1), (Sum.inr 3693, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 4092, -1)]

def sourceForm2545 : Integer.Sparse Master := [(Sum.inr 4684, 2), (Sum.inr 4692, 1), (Sum.inr 4693, 1), (Sum.inr 4703, 2), (Sum.inr 4704, 1), (Sum.inr 4705, 1), (Sum.inr 4846, 1), (Sum.inr 4884, 1), (Sum.inr 4945, 2), (Sum.inr 4976, 2), (Sum.inr 5110, 1), (Sum.inr 5206, 1), (Sum.inr 5215, 2), (Sum.inr 5228, 2), (Sum.inr 5229, 2), (Sum.inr 5248, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5287, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1)]

def sourceForm2546 : Integer.Sparse Master := [(Sum.inr 1829, 2), (Sum.inr 1830, 1), (Sum.inr 1831, 1), (Sum.inr 2138, 1), (Sum.inr 2362, 2), (Sum.inr 2363, 1), (Sum.inr 2643, 1), (Sum.inr 2758, 2), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 2831, 2), (Sum.inr 2832, 1), (Sum.inr 3005, 1), (Sum.inr 3083, 2), (Sum.inr 3092, 2), (Sum.inr 3094, 2), (Sum.inr 3106, 2), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3144, 2), (Sum.inr 3216, 1)]

def sourceForm2547 : Integer.Sparse Master := [(Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2229, 1), (Sum.inr 2272, 2), (Sum.inr 2273, 1), (Sum.inr 2280, 1), (Sum.inr 2286, 1), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2672, 2), (Sum.inr 2673, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 2705, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 3025, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1)]

def sourceForm2550 : Integer.Sparse Master := [(Sum.inr 4950, 8), (Sum.inr 4952, 4), (Sum.inr 5177, 4), (Sum.inr 5457, 2), (Sum.inr 5465, 8), (Sum.inr 5487, 4)]

def sourceForm2551 : Integer.Sparse Master := [(Sum.inr 2342, 8), (Sum.inr 2344, 4), (Sum.inr 2605, 4), (Sum.inr 3917, 2), (Sum.inr 3931, 8), (Sum.inr 4000, 4)]

def sourceForm2552 : Integer.Sparse Master := [(Sum.inr 5356, 16), (Sum.inr 5371, 8), (Sum.inr 5390, 4), (Sum.inr 5458, 2)]

def sourceForm2553 : Integer.Sparse Master := [(Sum.inr 4932, 1), (Sum.inr 4933, 2), (Sum.inr 4934, 2), (Sum.inr 4935, 2), (Sum.inr 4950, 1), (Sum.inr 4951, 2), (Sum.inr 4958, 1), (Sum.inr 4974, 1), (Sum.inr 5081, 1), (Sum.inr 5152, 2), (Sum.inr 5189, 1), (Sum.inr 5337, 1), (Sum.inr 5340, 1), (Sum.inr 5352, 2), (Sum.inr 5369, 2), (Sum.inr 5393, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 2), (Sum.inr 5459, 1), (Sum.inr 5463, 1), (Sum.inr 5473, 2)]

def sourceForm2555 : Integer.Sparse Master := [(Sum.inr 3409, 1), (Sum.inr 3414, 2), (Sum.inr 3415, 2), (Sum.inr 3418, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3482, 1), (Sum.inr 3511, 1), (Sum.inr 3542, 1), (Sum.inr 3592, 1), (Sum.inr 3612, 2), (Sum.inr 3756, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3774, 2), (Sum.inr 3797, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 2), (Sum.inr 3951, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 2)]

def sourceForm2556 : Integer.Sparse Master := [(Sum.inr 2822, 2), (Sum.inr 3672, 1), (Sum.inr 3694, 1), (Sum.inr 3779, 1), (Sum.inr 3920, 1), (Sum.inr 4091, -1)]

def sourceForm2557 : Integer.Sparse Master := [(Sum.inr 2322, 1), (Sum.inr 2799, 1), (Sum.inr 3675, 1), (Sum.inr 3690, 2), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def sourceForm2558 : Integer.Sparse Master := [(Sum.inr 2827, 2), (Sum.inr 3675, 1), (Sum.inr 3694, 1), (Sum.inr 3790, 1), (Sum.inr 3929, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm256 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 1218, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1263, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def sourceForm257 : Integer.Sparse Master := [(Sum.inr 1263, 1), (Sum.inr 2568, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 2758, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

def sourceForm258 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

def sourceForm259 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 2481, 1), (Sum.inr 2616, 1), (Sum.inr 2714, 1), (Sum.inr 2720, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def sourceForm260 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 2545, 1), (Sum.inr 2557, 1), (Sum.inr 2568, 1), (Sum.inr 2724, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

def sourceForm261 : Integer.Sparse Master := [(Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2739, 1), (Sum.inr 4092, -1)]

def sourceForm262 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2619, 1), (Sum.inr 2620, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def sourceForm263 : Integer.Sparse Master := [(Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 2620, 1), (Sum.inr 2722, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def sourceForm264 : Integer.Sparse Master := [(Sum.inr 2714, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def sourceForm265 : Integer.Sparse Master := [(Sum.inr 1218, 1), (Sum.inr 2486, 1), (Sum.inr 2544, 1), (Sum.inr 2619, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def sourceForm268 : Integer.Sparse Master := [(Sum.inr 1607, 1), (Sum.inr 1608, 1), (Sum.inr 1612, 1), (Sum.inr 1619, 1), (Sum.inr 1714, 1), (Sum.inr 2534, 1), (Sum.inr 2538, 1), (Sum.inr 2588, 1), (Sum.inr 2670, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3355, 1), (Sum.inr 3431, 1), (Sum.inr 3434, 1), (Sum.inr 3463, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 1), (Sum.inr 3543, 1), (Sum.inr 3572, 1), (Sum.inr 3606, 1), (Sum.inr 3625, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3884, 1), (Sum.inr 3997, 1)]

def sourceForm269 : Integer.Sparse Master := [(Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3902, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def sourceForm270 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 1394, 1), (Sum.inr 1400, 1), (Sum.inr 1406, 1), (Sum.inr 1425, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def sourceForm271 : Integer.Sparse Master := [(Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

def sourceForm272 : Integer.Sparse Master := [(Sum.inr 2624, 1), (Sum.inr 2949, 1), (Sum.inr 3013, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

def sourceForm273 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 2933, 1), (Sum.inr 3013, 1), (Sum.inr 3064, 1), (Sum.inr 3084, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def sourceForm274 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2947, 1), (Sum.inr 2984, 1), (Sum.inr 2992, 1), (Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

def sourceForm275 : Integer.Sparse Master := [(Sum.inr 1425, 1), (Sum.inr 2992, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 2), (Sum.inr 3108, 1), (Sum.inr 4091, -1)]

def sourceForm276 : Integer.Sparse Master := [(Sum.inr 2618, 1), (Sum.inr 2933, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 3086, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def sourceForm277 : Integer.Sparse Master := [(Sum.inr 1400, 1), (Sum.inr 2942, 1), (Sum.inr 2947, 1), (Sum.inr 2949, 1), (Sum.inr 2964, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def sourceForm280 : Integer.Sparse Master := [(Sum.inr 2496, 1), (Sum.inr 2497, 1), (Sum.inr 2498, 1), (Sum.inr 2516, 1), (Sum.inr 2708, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 1), (Sum.inr 2729, 1), (Sum.inr 2765, 1), (Sum.inr 2777, 1), (Sum.inr 3028, 1), (Sum.inr 3035, 1), (Sum.inr 3038, 1), (Sum.inr 3042, 1), (Sum.inr 3063, 1), (Sum.inr 3064, 1), (Sum.inr 3067, 1), (Sum.inr 3080, 1), (Sum.inr 3086, 2), (Sum.inr 3088, 1), (Sum.inr 3092, 1), (Sum.inr 3098, 1), (Sum.inr 3101, 1), (Sum.inr 3110, 1), (Sum.inr 3121, 1), (Sum.inr 3197, 1), (Sum.inr 3198, 1), (Sum.inr 3211, 1), (Sum.inr 3225, 1)]

def sourceForm281 : Integer.Sparse Master := [(Sum.inr 2588, 1), (Sum.inr 3502, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3540, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

def sourceForm282 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2035, 1), (Sum.inr 2039, 1), (Sum.inr 2054, 1), (Sum.inr 2278, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

def sourceForm283 : Integer.Sparse Master := [(Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 3540, 2), (Sum.inr 3632, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def sourceForm286 : Integer.Sparse Master := [(Sum.inr 2973, 1), (Sum.inr 3490, 1), (Sum.inr 3494, 1), (Sum.inr 3502, 1), (Sum.inr 3540, 2), (Sum.inr 4084, -1)]

def sourceForm287 : Integer.Sparse Master := [(Sum.inr 2039, 1), (Sum.inr 2592, 1), (Sum.inr 3383, 1), (Sum.inr 3490, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2565 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4946, 4), (Sum.inr 4952, 1), (Sum.inr 4953, 2), (Sum.inr 4977, 4), (Sum.inr 4979, 1), (Sum.inr 5111, 2), (Sum.inr 5207, 2), (Sum.inr 5335, 2), (Sum.inr 5367, 4), (Sum.inr 5368, 4), (Sum.inr 5413, 2), (Sum.inr 5475, 1)]

def sourceForm2566 : Integer.Sparse Master := [(Sum.inr 3412, 4), (Sum.inr 3422, 1), (Sum.inr 3423, 2), (Sum.inr 3485, 2), (Sum.inr 3595, 4), (Sum.inr 3596, 1), (Sum.inr 3631, 2), (Sum.inr 3753, 2), (Sum.inr 3766, 4), (Sum.inr 3767, 4), (Sum.inr 3817, 2), (Sum.inr 3963, 1), (Sum.inr 4092, 1)]

def sourceForm2571 : Integer.Sparse Master := [(Sum.inr 4075, 8), (Sum.inr 4076, 4), (Sum.inr 4082, 4), (Sum.inr 4086, 2), (Sum.inr 4088, 8), (Sum.inr 4092, 4)]

def sourceForm2572 : Integer.Sparse Master := [(Sum.inr 4685, 1), (Sum.inr 4686, 1), (Sum.inr 4688, 2), (Sum.inr 4869, 1), (Sum.inr 4967, 1), (Sum.inr 4970, 1), (Sum.inr 4973, 2), (Sum.inr 5114, 1), (Sum.inr 5168, 1), (Sum.inr 5176, 2), (Sum.inr 5372, 2), (Sum.inr 5383, 1), (Sum.inr 5384, 2), (Sum.inr 5387, 2), (Sum.inr 5389, 2), (Sum.inr 5403, 1), (Sum.inr 5415, 1), (Sum.inr 5439, 1), (Sum.inr 5441, 2), (Sum.inr 5443, 2), (Sum.inr 5448, 1)]

def sourceForm2573 : Integer.Sparse Master := [(Sum.inr 4676, 1), (Sum.inr 4678, 1), (Sum.inr 4684, 2), (Sum.inr 4766, 1), (Sum.inr 4770, 1), (Sum.inr 4810, 2), (Sum.inr 4865, 1), (Sum.inr 4971, 1), (Sum.inr 4977, 2), (Sum.inr 5172, 1), (Sum.inr 5336, 2), (Sum.inr 5355, 2), (Sum.inr 5378, 2), (Sum.inr 5386, 1), (Sum.inr 5388, 2), (Sum.inr 5400, 1), (Sum.inr 5417, 1), (Sum.inr 5432, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 1), (Sum.inr 5450, 1)]

def sourceForm2574 : Integer.Sparse Master := [(Sum.inr 5219, 1), (Sum.inr 5222, 1), (Sum.inr 5228, 2), (Sum.inr 5231, 1), (Sum.inr 5233, 2), (Sum.inr 5237, 1), (Sum.inr 5243, 1), (Sum.inr 5248, 1), (Sum.inr 5264, 2), (Sum.inr 5279, 1), (Sum.inr 5351, 1), (Sum.inr 5354, 1), (Sum.inr 5367, 2), (Sum.inr 5369, 1), (Sum.inr 5370, 2), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5381, 2), (Sum.inr 5384, 2), (Sum.inr 5388, 2), (Sum.inr 5418, 1)]

def sourceForm2575 : Integer.Sparse Master := [(Sum.inr 4679, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4689, 1), (Sum.inr 4866, 1), (Sum.inr 4968, 1), (Sum.inr 4972, 1), (Sum.inr 4974, 1), (Sum.inr 4977, 1), (Sum.inr 5038, 1), (Sum.inr 5080, 1), (Sum.inr 5169, 1), (Sum.inr 5176, 1), (Sum.inr 5336, 1), (Sum.inr 5355, 1), (Sum.inr 5373, 1), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5401, 1), (Sum.inr 5416, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1), (Sum.inr 5440, 1), (Sum.inr 5442, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1)]

def sourceForm2576 : Integer.Sparse Master := [(Sum.inr 5226, 2), (Sum.inr 5228, 2), (Sum.inr 5229, 2), (Sum.inr 5237, 2), (Sum.inr 5288, 1), (Sum.inr 5352, 2), (Sum.inr 5367, 2), (Sum.inr 5368, 2), (Sum.inr 5369, 2), (Sum.inr 5378, 2), (Sum.inr 5379, 2), (Sum.inr 5380, 2), (Sum.inr 5384, 2), (Sum.inr 5385, 1), (Sum.inr 5387, 2), (Sum.inr 5388, 1), (Sum.inr 5465, 1)]

def sourceForm2579 : Integer.Sparse Master := [(Sum.inr 4680, 1), (Sum.inr 4682, 1), (Sum.inr 4683, 1), (Sum.inr 4690, 1), (Sum.inr 4867, 1), (Sum.inr 4963, 1), (Sum.inr 4965, 1), (Sum.inr 4966, 1), (Sum.inr 4976, 1), (Sum.inr 5042, 1), (Sum.inr 5080, 1), (Sum.inr 5163, 1), (Sum.inr 5188, 1), (Sum.inr 5216, 1), (Sum.inr 5232, 1), (Sum.inr 5264, 1), (Sum.inr 5339, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 1), (Sum.inr 5381, 1), (Sum.inr 5382, 1), (Sum.inr 5385, 1), (Sum.inr 5400, 1), (Sum.inr 5402, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1), (Sum.inr 5432, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5446, 1)]

def sourceForm2580 : Integer.Sparse Master := [(Sum.inr 2145, 1), (Sum.inr 2146, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2251, 1), (Sum.inr 2654, 1), (Sum.inr 2659, 1), (Sum.inr 2677, 1), (Sum.inr 2729, 1), (Sum.inr 3462, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3564, 1), (Sum.inr 3760, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3799, 1), (Sum.inr 3802, 1), (Sum.inr 3807, 1), (Sum.inr 3813, 1), (Sum.inr 3834, 1), (Sum.inr 3850, 1), (Sum.inr 3854, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1)]

def sourceForm2582 : Integer.Sparse Master := [(Sum.inr 4660, 1), (Sum.inr 4661, 2), (Sum.inr 4679, 1), (Sum.inr 4826, 1), (Sum.inr 4960, 1), (Sum.inr 4961, 2), (Sum.inr 4968, 1), (Sum.inr 5030, 1), (Sum.inr 5080, 2), (Sum.inr 5148, 1), (Sum.inr 5333, 2), (Sum.inr 5355, 2), (Sum.inr 5363, 1), (Sum.inr 5378, 2), (Sum.inr 5386, 1), (Sum.inr 5388, 2), (Sum.inr 5422, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5438, 2)]

def sourceForm2583 : Integer.Sparse Master := [(Sum.inr 4663, 1), (Sum.inr 4666, 2), (Sum.inr 4677, 1), (Sum.inr 4851, 1), (Sum.inr 4956, 1), (Sum.inr 4958, 2), (Sum.inr 4964, 1), (Sum.inr 5114, 1), (Sum.inr 5129, 2), (Sum.inr 5137, 1), (Sum.inr 5373, 2), (Sum.inr 5377, 2), (Sum.inr 5379, 2), (Sum.inr 5380, 2), (Sum.inr 5383, 1), (Sum.inr 5396, 1), (Sum.inr 5422, 1), (Sum.inr 5424, 2), (Sum.inr 5427, 1), (Sum.inr 5430, 2), (Sum.inr 5447, 1)]

def sourceForm2584 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2142, 1), (Sum.inr 2148, 2), (Sum.inr 2240, 1), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3516, 2), (Sum.inr 3521, 1), (Sum.inr 3554, 1), (Sum.inr 3597, 1), (Sum.inr 3792, 2), (Sum.inr 3798, 1), (Sum.inr 3832, 2), (Sum.inr 3835, 2), (Sum.inr 3836, 2), (Sum.inr 3843, 2), (Sum.inr 3844, 1), (Sum.inr 3848, 2), (Sum.inr 3867, 1), (Sum.inr 3900, 1), (Sum.inr 3909, 1)]

def sourceForm2587 : Integer.Sparse Master := [(Sum.inr 4664, 1), (Sum.inr 4665, 1), (Sum.inr 4668, 1), (Sum.inr 4680, 1), (Sum.inr 4852, 1), (Sum.inr 4954, 1), (Sum.inr 4955, 1), (Sum.inr 4957, 1), (Sum.inr 4963, 1), (Sum.inr 5038, 1), (Sum.inr 5080, 1), (Sum.inr 5129, 1), (Sum.inr 5134, 1), (Sum.inr 5336, 1), (Sum.inr 5355, 1), (Sum.inr 5372, 1), (Sum.inr 5376, 1), (Sum.inr 5379, 1), (Sum.inr 5381, 2), (Sum.inr 5382, 1), (Sum.inr 5384, 1), (Sum.inr 5394, 1), (Sum.inr 5397, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5445, 1)]

def sourceForm2588 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2145, 1), (Sum.inr 2147, 1), (Sum.inr 2154, 1), (Sum.inr 2250, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3514, 1), (Sum.inr 3516, 1), (Sum.inr 3553, 1), (Sum.inr 3754, 1), (Sum.inr 3770, 1), (Sum.inr 3791, 1), (Sum.inr 3793, 1), (Sum.inr 3796, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3866, 1), (Sum.inr 3880, 1)]

def sourceForm2591 : Integer.Sparse Master := [(Sum.inr 4679, 1), (Sum.inr 4686, 1), (Sum.inr 4689, 2), (Sum.inr 4696, 1), (Sum.inr 4697, 1), (Sum.inr 4701, 2), (Sum.inr 4838, 1), (Sum.inr 4879, 1), (Sum.inr 5116, 1), (Sum.inr 5151, 2), (Sum.inr 5217, 2), (Sum.inr 5226, 2), (Sum.inr 5227, 1), (Sum.inr 5236, 2), (Sum.inr 5237, 2), (Sum.inr 5247, 1), (Sum.inr 5271, 2), (Sum.inr 5273, 1), (Sum.inr 5286, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2592 : Integer.Sparse Master := [(Sum.inr 2150, 1), (Sum.inr 2165, 1), (Sum.inr 2166, 2), (Sum.inr 2227, 1), (Sum.inr 2238, 1), (Sum.inr 2239, 1), (Sum.inr 2246, 1), (Sum.inr 2257, 2), (Sum.inr 2655, 1), (Sum.inr 2656, 2), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2681, 2), (Sum.inr 2682, 2), (Sum.inr 2684, 2), (Sum.inr 2703, 1), (Sum.inr 2739, 2), (Sum.inr 2741, 1), (Sum.inr 3023, 1), (Sum.inr 3051, 2), (Sum.inr 3053, 1)]

def sourceForm2595 : Integer.Sparse Master := [(Sum.inr 4676, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4688, 1), (Sum.inr 4698, 1), (Sum.inr 4699, 1), (Sum.inr 4700, 1), (Sum.inr 4703, 1), (Sum.inr 4834, 1), (Sum.inr 4880, 1), (Sum.inr 5035, 1), (Sum.inr 5110, 1), (Sum.inr 5140, 1), (Sum.inr 5215, 1), (Sum.inr 5216, 1), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5238, 1), (Sum.inr 5241, 1), (Sum.inr 5254, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5274, 1), (Sum.inr 5302, 1)]

def sourceForm2596 : Integer.Sparse Master := [(Sum.inr 2141, 1), (Sum.inr 2151, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2205, 1), (Sum.inr 2248, 1), (Sum.inr 2249, 1), (Sum.inr 2254, 1), (Sum.inr 2256, 1), (Sum.inr 2272, 1), (Sum.inr 2652, 1), (Sum.inr 2653, 1), (Sum.inr 2654, 1), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2694, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2742, 1), (Sum.inr 3016, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3054, 1)]

def sourceForm2597 : Integer.Sparse Master := [(Sum.inr 4947, 2), (Sum.inr 4948, 2), (Sum.inr 4949, 4), (Sum.inr 5115, 1), (Sum.inr 5172, 2), (Sum.inr 5177, 2), (Sum.inr 5373, 2), (Sum.inr 5390, 2), (Sum.inr 5404, 2), (Sum.inr 5416, 2), (Sum.inr 5418, 2), (Sum.inr 5442, 4), (Sum.inr 5462, 1), (Sum.inr 5485, 2)]

def sourceForm2598 : Integer.Sparse Master := [(Sum.inr 4767, 1), (Sum.inr 4769, 2), (Sum.inr 4811, 2), (Sum.inr 4939, 2), (Sum.inr 4946, 4), (Sum.inr 5168, 2), (Sum.inr 5337, 2), (Sum.inr 5356, 2), (Sum.inr 5393, 2), (Sum.inr 5416, 2), (Sum.inr 5434, 4), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5486, 2)]

def sourceForm2599 : Integer.Sparse Master := [(Sum.inr 4941, 2), (Sum.inr 4943, 2), (Sum.inr 4946, 2), (Sum.inr 4950, 2), (Sum.inr 5039, 1), (Sum.inr 5081, 1), (Sum.inr 5169, 2), (Sum.inr 5177, 1), (Sum.inr 5337, 1), (Sum.inr 5356, 1), (Sum.inr 5418, 1), (Sum.inr 5457, 1), (Sum.inr 5460, 1), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5466, 1), (Sum.inr 5476, 2), (Sum.inr 5483, 2), (Sum.inr 5486, 2), (Sum.inr 5487, 2)]

def sourceForm2602 : Integer.Sparse Master := [(Sum.inr 4942, 2), (Sum.inr 4944, 2), (Sum.inr 4945, 2), (Sum.inr 4951, 2), (Sum.inr 5043, 1), (Sum.inr 5081, 1), (Sum.inr 5170, 2), (Sum.inr 5189, 1), (Sum.inr 5217, 1), (Sum.inr 5236, 1), (Sum.inr 5269, 1), (Sum.inr 5340, 1), (Sum.inr 5356, 1), (Sum.inr 5393, 1), (Sum.inr 5401, 2), (Sum.inr 5410, 2), (Sum.inr 5419, 1), (Sum.inr 5438, 2), (Sum.inr 5461, 1), (Sum.inr 5463, 1), (Sum.inr 5484, 2)]

def sourceForm2603 : Integer.Sparse Master := [(Sum.inr 2656, 1), (Sum.inr 2658, 2), (Sum.inr 2682, 1), (Sum.inr 2736, 1), (Sum.inr 3407, 2), (Sum.inr 3413, 2), (Sum.inr 3418, 2), (Sum.inr 3465, 1), (Sum.inr 3482, 1), (Sum.inr 3542, 1), (Sum.inr 3606, 2), (Sum.inr 3763, 1), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3804, 2), (Sum.inr 3816, 2), (Sum.inr 3842, 1), (Sum.inr 3857, 2), (Sum.inr 3960, 1), (Sum.inr 3973, 1), (Sum.inr 3983, 2)]

def sourceForm2607 : Integer.Sparse Master := [(Sum.inr 4930, 2), (Sum.inr 4931, 2), (Sum.inr 4933, 2), (Sum.inr 4942, 2), (Sum.inr 5039, 1), (Sum.inr 5081, 1), (Sum.inr 5130, 1), (Sum.inr 5149, 2), (Sum.inr 5337, 1), (Sum.inr 5356, 1), (Sum.inr 5373, 1), (Sum.inr 5377, 1), (Sum.inr 5396, 2), (Sum.inr 5404, 1), (Sum.inr 5410, 2), (Sum.inr 5419, 2), (Sum.inr 5424, 2), (Sum.inr 5459, 1), (Sum.inr 5461, 1), (Sum.inr 5478, 2)]

def sourceForm2608 : Integer.Sparse Master := [(Sum.inr 3406, 2), (Sum.inr 3407, 2), (Sum.inr 3408, 2), (Sum.inr 3414, 2), (Sum.inr 3456, 1), (Sum.inr 3482, 1), (Sum.inr 3520, 1), (Sum.inr 3605, 2), (Sum.inr 3756, 1), (Sum.inr 3773, 1), (Sum.inr 3792, 1), (Sum.inr 3798, 2), (Sum.inr 3815, 1), (Sum.inr 3816, 2), (Sum.inr 3835, 1), (Sum.inr 3842, 2), (Sum.inr 3843, 2), (Sum.inr 3951, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 2)]

def sourceForm2611 : Integer.Sparse Master := [(Sum.inr 4756, 1), (Sum.inr 4757, 1), (Sum.inr 4768, 1), (Sum.inr 4795, 2), (Sum.inr 4933, 2), (Sum.inr 4947, 1), (Sum.inr 4955, 2), (Sum.inr 4967, 1), (Sum.inr 5076, 1), (Sum.inr 5184, 1), (Sum.inr 5338, 2), (Sum.inr 5348, 2), (Sum.inr 5352, 2), (Sum.inr 5354, 2), (Sum.inr 5366, 1), (Sum.inr 5403, 1), (Sum.inr 5406, 2), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5429, 2), (Sum.inr 5472, 1)]

def sourceForm2612 : Integer.Sparse Master := [(Sum.inr 2176, 1), (Sum.inr 2178, 1), (Sum.inr 2181, 1), (Sum.inr 2213, 2), (Sum.inr 3414, 2), (Sum.inr 3416, 1), (Sum.inr 3477, 1), (Sum.inr 3508, 2), (Sum.inr 3524, 1), (Sum.inr 3585, 1), (Sum.inr 3755, 2), (Sum.inr 3764, 2), (Sum.inr 3765, 1), (Sum.inr 3768, 2), (Sum.inr 3769, 2), (Sum.inr 3806, 1), (Sum.inr 3810, 1), (Sum.inr 3812, 2), (Sum.inr 3869, 1), (Sum.inr 3874, 2), (Sum.inr 3957, 1)]

def sourceForm2614 : Integer.Sparse Master := [(Sum.inr 4930, 1), (Sum.inr 4932, 1), (Sum.inr 4933, 1), (Sum.inr 4941, 1), (Sum.inr 4954, 1), (Sum.inr 4955, 1), (Sum.inr 4958, 1), (Sum.inr 4968, 1), (Sum.inr 5040, 1), (Sum.inr 5067, 1), (Sum.inr 5073, 1), (Sum.inr 5152, 1), (Sum.inr 5185, 1), (Sum.inr 5338, 1), (Sum.inr 5340, 1), (Sum.inr 5348, 1), (Sum.inr 5352, 2), (Sum.inr 5354, 1), (Sum.inr 5356, 1), (Sum.inr 5366, 1), (Sum.inr 5369, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5408, 1), (Sum.inr 5410, 1), (Sum.inr 5470, 1), (Sum.inr 5471, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 1)]

def sourceForm2615 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3409, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3467, 1), (Sum.inr 3476, 1), (Sum.inr 3508, 1), (Sum.inr 3511, 1), (Sum.inr 3529, 1), (Sum.inr 3587, 1), (Sum.inr 3612, 1), (Sum.inr 3755, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3765, 1), (Sum.inr 3768, 1), (Sum.inr 3769, 1), (Sum.inr 3773, 1), (Sum.inr 3774, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3806, 1), (Sum.inr 3816, 1), (Sum.inr 3955, 1), (Sum.inr 3956, 1), (Sum.inr 3957, 1), (Sum.inr 3961, 1)]

def sourceForm2618 : Integer.Sparse Master := [(Sum.inr 4929, 1), (Sum.inr 4931, 2), (Sum.inr 4939, 1), (Sum.inr 4956, 1), (Sum.inr 4957, 2), (Sum.inr 4971, 1), (Sum.inr 5072, 1), (Sum.inr 5112, 1), (Sum.inr 5141, 2), (Sum.inr 5187, 1), (Sum.inr 5339, 2), (Sum.inr 5353, 2), (Sum.inr 5355, 2), (Sum.inr 5365, 1), (Sum.inr 5367, 2), (Sum.inr 5400, 1), (Sum.inr 5405, 1), (Sum.inr 5409, 2), (Sum.inr 5414, 1), (Sum.inr 5428, 2), (Sum.inr 5471, 1)]

def sourceForm2619 : Integer.Sparse Master := [(Sum.inr 3403, 1), (Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3459, 1), (Sum.inr 3509, 2), (Sum.inr 3510, 1), (Sum.inr 3522, 2), (Sum.inr 3537, 1), (Sum.inr 3556, 1), (Sum.inr 3590, 1), (Sum.inr 3758, 1), (Sum.inr 3760, 2), (Sum.inr 3761, 2), (Sum.inr 3766, 2), (Sum.inr 3770, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3807, 2), (Sum.inr 3845, 2), (Sum.inr 3869, 1), (Sum.inr 3953, 1)]

def sourceForm2621 : Integer.Sparse Master := [(Sum.inr 4775, 1), (Sum.inr 4776, 1), (Sum.inr 4777, 1), (Sum.inr 4821, 1), (Sum.inr 4856, 1), (Sum.inr 4942, 1), (Sum.inr 4949, 1), (Sum.inr 4951, 1), (Sum.inr 4963, 1), (Sum.inr 4966, 1), (Sum.inr 4973, 1), (Sum.inr 5105, 1), (Sum.inr 5198, 1), (Sum.inr 5336, 1), (Sum.inr 5338, 1), (Sum.inr 5353, 1), (Sum.inr 5355, 1), (Sum.inr 5360, 1), (Sum.inr 5361, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5397, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5421, 1), (Sum.inr 5436, 1), (Sum.inr 5446, 1), (Sum.inr 5473, 1)]

def sourceForm2622 : Integer.Sparse Master := [(Sum.inr 2211, 1), (Sum.inr 2212, 1), (Sum.inr 2217, 1), (Sum.inr 2223, 1), (Sum.inr 2274, 1), (Sum.inr 3407, 1), (Sum.inr 3417, 1), (Sum.inr 3418, 1), (Sum.inr 3479, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3570, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 1), (Sum.inr 3762, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 3770, 1), (Sum.inr 3772, 1), (Sum.inr 3796, 1), (Sum.inr 3808, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3958, 1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2624 : Integer.Sparse Master := [(Sum.inr 4940, 1), (Sum.inr 4944, 1), (Sum.inr 4946, 1), (Sum.inr 4951, 1), (Sum.inr 4964, 1), (Sum.inr 4965, 1), (Sum.inr 4966, 1), (Sum.inr 4977, 1), (Sum.inr 5044, 1), (Sum.inr 5090, 1), (Sum.inr 5102, 1), (Sum.inr 5199, 1), (Sum.inr 5207, 1), (Sum.inr 5335, 1), (Sum.inr 5338, 1), (Sum.inr 5359, 1), (Sum.inr 5361, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5371, 1), (Sum.inr 5395, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5413, 1), (Sum.inr 5446, 1), (Sum.inr 5468, 1), (Sum.inr 5473, 1), (Sum.inr 5475, 1)]

def sourceForm2625 : Integer.Sparse Master := [(Sum.inr 3405, 1), (Sum.inr 3412, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3471, 1), (Sum.inr 3474, 1), (Sum.inr 3475, 1), (Sum.inr 3480, 1), (Sum.inr 3554, 1), (Sum.inr 3555, 1), (Sum.inr 3578, 1), (Sum.inr 3595, 1), (Sum.inr 3631, 1), (Sum.inr 3753, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3775, 1), (Sum.inr 3794, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3817, 1), (Sum.inr 3950, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1)]

def sourceForm2627 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 4941, 1), (Sum.inr 4948, 1), (Sum.inr 4950, 2), (Sum.inr 4968, 1), (Sum.inr 4970, 1), (Sum.inr 4974, 2), (Sum.inr 5104, 1), (Sum.inr 5117, 1), (Sum.inr 5152, 2), (Sum.inr 5203, 1), (Sum.inr 5337, 2), (Sum.inr 5352, 2), (Sum.inr 5356, 2), (Sum.inr 5366, 1), (Sum.inr 5369, 2), (Sum.inr 5396, 1), (Sum.inr 5410, 2), (Sum.inr 5469, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1)]

def sourceForm2628 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4939, 1), (Sum.inr 4943, 1), (Sum.inr 4946, 1), (Sum.inr 4949, 1), (Sum.inr 4971, 1), (Sum.inr 4972, 1), (Sum.inr 4973, 1), (Sum.inr 4977, 1), (Sum.inr 5036, 1), (Sum.inr 5101, 1), (Sum.inr 5111, 1), (Sum.inr 5141, 1), (Sum.inr 5204, 1), (Sum.inr 5335, 1), (Sum.inr 5336, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5371, 1), (Sum.inr 5394, 1), (Sum.inr 5395, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5413, 1), (Sum.inr 5428, 1), (Sum.inr 5473, 1)]

def sourceForm2629 : Integer.Sparse Master := [(Sum.inr 4763, 1), (Sum.inr 4769, 1), (Sum.inr 4770, 1), (Sum.inr 4846, 2), (Sum.inr 4938, 1), (Sum.inr 4945, 2), (Sum.inr 4975, 1), (Sum.inr 4976, 2), (Sum.inr 5099, 1), (Sum.inr 5205, 1), (Sum.inr 5215, 2), (Sum.inr 5238, 2), (Sum.inr 5241, 1), (Sum.inr 5242, 1), (Sum.inr 5248, 2), (Sum.inr 5274, 2), (Sum.inr 5275, 2), (Sum.inr 5277, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5287, 2)]

def sourceForm2630 : Integer.Sparse Master := [(Sum.inr 2174, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2229, 2), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2686, 2), (Sum.inr 2689, 1), (Sum.inr 2690, 1), (Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 2), (Sum.inr 2706, 1), (Sum.inr 2742, 2), (Sum.inr 2743, 2), (Sum.inr 3025, 2), (Sum.inr 3059, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1)]

def sourceForm2632 : Integer.Sparse Master := [(Sum.inr 4090, 1), (Sum.inr 4927, 1), (Sum.inr 4928, 2), (Sum.inr 4936, 1), (Sum.inr 4960, 1), (Sum.inr 4961, 2), (Sum.inr 4969, 1), (Sum.inr 5029, 1), (Sum.inr 5050, 2), (Sum.inr 5058, 1), (Sum.inr 5192, 1), (Sum.inr 5332, 2), (Sum.inr 5341, 2), (Sum.inr 5346, 2), (Sum.inr 5349, 2), (Sum.inr 5363, 1), (Sum.inr 5392, 1), (Sum.inr 5394, 2), (Sum.inr 5395, 2), (Sum.inr 5396, 1), (Sum.inr 5469, 1)]

def sourceForm2633 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4986, 1), (Sum.inr 4987, 2), (Sum.inr 5017, 1), (Sum.inr 5025, 1), (Sum.inr 5030, 1), (Sum.inr 5056, 2), (Sum.inr 5123, 1), (Sum.inr 5314, 2), (Sum.inr 5333, 2), (Sum.inr 5344, 2), (Sum.inr 5345, 1), (Sum.inr 5346, 2), (Sum.inr 5367, 2), (Sum.inr 5369, 1), (Sum.inr 5374, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5391, 1), (Sum.inr 5393, 2), (Sum.inr 5460, 1)]

def sourceForm2638 : Integer.Sparse Master := [(Sum.inr 4073, 2), (Sum.inr 4074, 2), (Sum.inr 4075, 4), (Sum.inr 4078, 1), (Sum.inr 4080, 2), (Sum.inr 4082, 2), (Sum.inr 4086, 2), (Sum.inr 4087, 1), (Sum.inr 4088, 4), (Sum.inr 4089, 2), (Sum.inr 4090, 2), (Sum.inr 4091, 2), (Sum.inr 4092, 4)]

def sourceForm2639 : Integer.Sparse Master := [(Sum.inr 4672, 3), (Sum.inr 4685, 1), (Sum.inr 4859, 1), (Sum.inr 4967, 1), (Sum.inr 4969, 3), (Sum.inr 5166, 1), (Sum.inr 5374, 3), (Sum.inr 5383, 1), (Sum.inr 5384, 6), (Sum.inr 5387, 3), (Sum.inr 5437, 1), (Sum.inr 5439, 3), (Sum.inr 5448, 3)]

def sourceForm2640 : Integer.Sparse Master := [(Sum.inr 4675, 1), (Sum.inr 4677, 3), (Sum.inr 4863, 1), (Sum.inr 4964, 3), (Sum.inr 4975, 1), (Sum.inr 5162, 1), (Sum.inr 5243, 3), (Sum.inr 5379, 6), (Sum.inr 5380, 3), (Sum.inr 5427, 1), (Sum.inr 5429, 3), (Sum.inr 5431, 3), (Sum.inr 5447, 1)]

def sourceForm2641 : Integer.Sparse Master := [(Sum.inr 2139, 1), (Sum.inr 2142, 3), (Sum.inr 2232, 1), (Sum.inr 2690, 1), (Sum.inr 2697, 3), (Sum.inr 3554, 3), (Sum.inr 3563, 1), (Sum.inr 3832, 6), (Sum.inr 3836, 3), (Sum.inr 3844, 1), (Sum.inr 3846, 3), (Sum.inr 3875, 3), (Sum.inr 3909, 1)]

def sourceForm2642 : Integer.Sparse Master := [(Sum.inr 4676, 2), (Sum.inr 4679, 2), (Sum.inr 4864, 1), (Sum.inr 4968, 2), (Sum.inr 4971, 2), (Sum.inr 5167, 1), (Sum.inr 5378, 4), (Sum.inr 5380, 2), (Sum.inr 5387, 2), (Sum.inr 5388, 4), (Sum.inr 5431, 2), (Sum.inr 5433, 2), (Sum.inr 5440, 2), (Sum.inr 5450, 2)]

def sourceForm2644 : Integer.Sparse Master := [(Sum.inr 4679, 3), (Sum.inr 4685, 1), (Sum.inr 4695, 1), (Sum.inr 4696, 3), (Sum.inr 4833, 1), (Sum.inr 4878, 1), (Sum.inr 5226, 6), (Sum.inr 5231, 3), (Sum.inr 5237, 3), (Sum.inr 5257, 3), (Sum.inr 5265, 3), (Sum.inr 5273, 1), (Sum.inr 5301, 1)]

def sourceForm2645 : Integer.Sparse Master := [(Sum.inr 2150, 3), (Sum.inr 2156, 1), (Sum.inr 2204, 1), (Sum.inr 2231, 1), (Sum.inr 2234, 1), (Sum.inr 2238, 3), (Sum.inr 2669, 6), (Sum.inr 2676, 3), (Sum.inr 2684, 3), (Sum.inr 2721, 3), (Sum.inr 2741, 1), (Sum.inr 3037, 3), (Sum.inr 3053, 1)]

def sourceForm2647 : Integer.Sparse Master := [(Sum.inr 4939, 4), (Sum.inr 4941, 4), (Sum.inr 5167, 2), (Sum.inr 5393, 4), (Sum.inr 5418, 2), (Sum.inr 5460, 2), (Sum.inr 5465, 4), (Sum.inr 5482, 4), (Sum.inr 5486, 4)]

def sourceForm2649 : Integer.Sparse Master := [(Sum.inr 4073, 8), (Sum.inr 4079, 2), (Sum.inr 4088, 12), (Sum.inr 4091, 8)]

def sourceForm2650 : Integer.Sparse Master := [(Sum.inr 5113, 1), (Sum.inr 5114, 4), (Sum.inr 5168, 4), (Sum.inr 5372, 4), (Sum.inr 5387, 4), (Sum.inr 5403, 4), (Sum.inr 5439, 4), (Sum.inr 5441, 4), (Sum.inr 5488, 1)]

def sourceForm2651 : Integer.Sparse Master := [(Sum.inr 4759, 1), (Sum.inr 4763, 4), (Sum.inr 4801, 4), (Sum.inr 5335, 4), (Sum.inr 5351, 4), (Sum.inr 5416, 4), (Sum.inr 5423, 4), (Sum.inr 5433, 4), (Sum.inr 5497, 1)]

def sourceForm2652 : Integer.Sparse Master := [(Sum.inr 4761, 1), (Sum.inr 4762, 1), (Sum.inr 4768, 1), (Sum.inr 4803, 2), (Sum.inr 5044, 2), (Sum.inr 5076, 1), (Sum.inr 5187, 1), (Sum.inr 5215, 2), (Sum.inr 5219, 1), (Sum.inr 5249, 1), (Sum.inr 5338, 2), (Sum.inr 5353, 2), (Sum.inr 5354, 1), (Sum.inr 5401, 2), (Sum.inr 5406, 2), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5481, 1)]

def sourceForm2653 : Integer.Sparse Master := [(Sum.inr 2171, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2195, 2), (Sum.inr 2653, 2), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 3474, 2), (Sum.inr 3477, 1), (Sum.inr 3537, 1), (Sum.inr 3755, 2), (Sum.inr 3761, 2), (Sum.inr 3769, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 1), (Sum.inr 3812, 2), (Sum.inr 3840, 2), (Sum.inr 3849, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2), (Sum.inr 3979, 1)]

def sourceForm2654 : Integer.Sparse Master := [(Sum.inr 4077, 1), (Sum.inr 4078, 4), (Sum.inr 4080, 4), (Sum.inr 4086, 4), (Sum.inr 4088, 4), (Sum.inr 4090, 4), (Sum.inr 4091, 4), (Sum.inr 4092, 4), (Sum.inr 4095, 1)]

def sourceForm2655 : Integer.Sparse Master := [(Sum.inr 1534, 4), (Sum.inr 1541, 2), (Sum.inr 4062, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2656 : Integer.Sparse Master := [(Sum.inr 686, 4), (Sum.inr 697, 1), (Sum.inr 1541, 1), (Sum.inr 4062, -1)]

def sourceForm2657 : Integer.Sparse Master := [(Sum.inr 1521, 1), (Sum.inr 1532, 3), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 4060, -1)]

def sourceForm2658 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1521, 1), (Sum.inr 1537, 2), (Sum.inr 4060, -1)]

def sourceForm2659 : Integer.Sparse Master := [(Sum.inr 683, 3), (Sum.inr 691, 1), (Sum.inr 695, 1), (Sum.inr 1537, 1), (Sum.inr 4060, -1)]

def sourceForm2663 : Integer.Sparse Master := [(Sum.inr 1527, 1), (Sum.inr 1529, 3), (Sum.inr 1531, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def sourceForm2664 : Integer.Sparse Master := [(Sum.inr 1523, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def sourceForm2665 : Integer.Sparse Master := [(Sum.inr 1533, 3), (Sum.inr 1538, 2), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def sourceForm2667 : Integer.Sparse Master := [(Sum.inr 696, 1), (Sum.inr 1496, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def sourceForm2669 : Integer.Sparse Master := [(Sum.inr 693, 1), (Sum.inr 1495, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 4061, -1)]

def sourceForm2671 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1518, 2), (Sum.inr 1520, 1), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

def sourceForm2672 : Integer.Sparse Master := [(Sum.inr 1509, 1), (Sum.inr 1528, 2), (Sum.inr 1530, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

def sourceForm2673 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1509, 1), (Sum.inr 1518, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

def sourceForm2679 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1513, 1), (Sum.inr 1519, 1), (Sum.inr 1525, 2), (Sum.inr 4059, -1)]

def sourceForm2680 : Integer.Sparse Master := [(Sum.inr 1519, 1), (Sum.inr 1522, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1536, 1), (Sum.inr 4059, -1)]

def sourceForm2681 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1519, 2), (Sum.inr 1536, 2), (Sum.inr 4059, -1)]

def sourceForm2687 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1503, 1), (Sum.inr 1507, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2688 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1517, 3), (Sum.inr 4057, -1)]

def sourceForm2689 : Integer.Sparse Master := [(Sum.inr 1507, 1), (Sum.inr 1510, 1), (Sum.inr 1512, 2), (Sum.inr 1517, 1), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

def sourceForm2691 : Integer.Sparse Master := [(Sum.inr 687, 1), (Sum.inr 1491, 1), (Sum.inr 1517, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

def sourceForm2696 : Integer.Sparse Master := [(Sum.inr 1502, 2), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

def sourceForm2697 : Integer.Sparse Master := [(Sum.inr 666, 1), (Sum.inr 1497, 1), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

def sourceForm2699 : Integer.Sparse Master := [(Sum.inr 1688, 2), (Sum.inr 1692, 2), (Sum.inr 1695, 2), (Sum.inr 4066, -1)]

def sourceForm2700 : Integer.Sparse Master := [(Sum.inr 1692, 2), (Sum.inr 3262, 2), (Sum.inr 3275, 2), (Sum.inr 4066, -1)]

def sourceForm2703 : Integer.Sparse Master := [(Sum.inr 1685, 2), (Sum.inr 1687, 1), (Sum.inr 1694, 1), (Sum.inr 1743, 1), (Sum.inr 2167, 1), (Sum.inr 4067, -1)]

def sourceForm2704 : Integer.Sparse Master := [(Sum.inr 1679, 2), (Sum.inr 1683, 1), (Sum.inr 1693, 1), (Sum.inr 1735, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def sourceForm2705 : Integer.Sparse Master := [(Sum.inr 1689, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 1748, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

def sourceForm2706 : Integer.Sparse Master := [(Sum.inr 1683, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2258, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def sourceForm2707 : Integer.Sparse Master := [(Sum.inr 1694, 1), (Sum.inr 2167, 1), (Sum.inr 3268, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def sourceForm2708 : Integer.Sparse Master := [(Sum.inr 1693, 1), (Sum.inr 3272, 2), (Sum.inr 3276, 2), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def sourceForm2710 : Integer.Sparse Master := [(Sum.inr 1579, 1), (Sum.inr 3237, 1), (Sum.inr 3252, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def sourceForm2712 : Integer.Sparse Master := [(Sum.inr 1576, 1), (Sum.inr 1849, 2), (Sum.inr 1858, 1), (Sum.inr 2167, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2720 : Integer.Sparse Master := [(Sum.inr 1690, 1), (Sum.inr 2184, 1), (Sum.inr 3255, 1), (Sum.inr 3264, 2), (Sum.inr 3273, 1), (Sum.inr 4064, -1)]

def sourceForm2725 : Integer.Sparse Master := [(Sum.inr 1681, 1), (Sum.inr 2657, 1), (Sum.inr 3258, 1), (Sum.inr 3265, 1), (Sum.inr 3270, 2), (Sum.inr 4065, -1)]

def sourceForm2726 : Integer.Sparse Master := [(Sum.inr 1691, 1), (Sum.inr 3261, 1), (Sum.inr 3265, 2), (Sum.inr 3274, 2), (Sum.inr 4065, -1)]

def sourceForm2728 : Integer.Sparse Master := [(Sum.inr 2161, 2), (Sum.inr 2163, 2), (Sum.inr 2169, 2), (Sum.inr 4076, -1)]

def sourceForm2729 : Integer.Sparse Master := [(Sum.inr 2155, 2), (Sum.inr 2159, 1), (Sum.inr 2168, 1), (Sum.inr 2273, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

def sourceForm2730 : Integer.Sparse Master := [(Sum.inr 2164, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2286, 1), (Sum.inr 3423, 1), (Sum.inr 4076, -1)]

def sourceForm2731 : Integer.Sparse Master := [(Sum.inr 2168, 1), (Sum.inr 3415, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

def sourceForm2732 : Integer.Sparse Master := [(Sum.inr 3419, 2), (Sum.inr 3422, 2), (Sum.inr 3423, 2), (Sum.inr 4076, -1)]

def sourceForm2733 : Integer.Sparse Master := [(Sum.inr 2169, 2), (Sum.inr 3423, 2), (Sum.inr 3512, 2), (Sum.inr 4076, -1)]

def sourceForm2740 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2151, 1), (Sum.inr 2153, 1), (Sum.inr 2165, 1), (Sum.inr 2256, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

def sourceForm2741 : Integer.Sparse Master := [(Sum.inr 2160, 1), (Sum.inr 2162, 2), (Sum.inr 2165, 1), (Sum.inr 2180, 1), (Sum.inr 2186, 1), (Sum.inr 4074, -1)]

def sourceForm2742 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2143, 1), (Sum.inr 2151, 2), (Sum.inr 2239, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

def sourceForm2743 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3411, 2), (Sum.inr 3413, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

def sourceForm2744 : Integer.Sparse Master := [(Sum.inr 2181, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2223, 2), (Sum.inr 3420, 1), (Sum.inr 4074, -1)]

def sourceForm2745 : Integer.Sparse Master := [(Sum.inr 2185, 1), (Sum.inr 3403, 1), (Sum.inr 3411, 2), (Sum.inr 3420, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

def sourceForm2747 : Integer.Sparse Master := [(Sum.inr 2143, 1), (Sum.inr 2176, 1), (Sum.inr 2185, 1), (Sum.inr 2212, 2), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

def sourceForm2748 : Integer.Sparse Master := [(Sum.inr 2165, 1), (Sum.inr 2186, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 2), (Sum.inr 3510, 1), (Sum.inr 4074, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm2756 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2146, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2249, 1), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

def sourceForm2757 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2166, 1), (Sum.inr 2272, 1), (Sum.inr 3595, 1), (Sum.inr 4075, -1)]

def sourceForm2758 : Integer.Sparse Master := [(Sum.inr 2148, 1), (Sum.inr 2152, 2), (Sum.inr 2166, 1), (Sum.inr 2257, 1), (Sum.inr 3592, 1), (Sum.inr 4075, -1)]

def sourceForm2759 : Integer.Sparse Master := [(Sum.inr 2658, 1), (Sum.inr 3406, 1), (Sum.inr 3412, 1), (Sum.inr 3417, 2), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

def sourceForm2766 : Integer.Sparse Master := [(Sum.inr 2182, 2), (Sum.inr 3455, 4), (Sum.inr 4077, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceForm288 : Integer.Sparse Master := [(Sum.inr 3533, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

def sourceForm289 : Integer.Sparse Master := [(Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 3494, 1), (Sum.inr 3540, 1), (Sum.inr 3544, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

def sourceForm291 : Integer.Sparse Master := [(Sum.inr 1180, 1), (Sum.inr 1181, 1), (Sum.inr 1182, 1), (Sum.inr 1189, 1), (Sum.inr 1262, 1), (Sum.inr 2454, 1), (Sum.inr 2465, 1), (Sum.inr 2495, 1), (Sum.inr 2734, 1), (Sum.inr 2834, 1), (Sum.inr 2835, 1), (Sum.inr 2841, 1), (Sum.inr 2905, 1), (Sum.inr 2909, 1), (Sum.inr 2934, 1), (Sum.inr 2976, 1), (Sum.inr 2979, 1), (Sum.inr 2998, 1), (Sum.inr 3037, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3051, 1), (Sum.inr 3055, 1), (Sum.inr 3109, 1), (Sum.inr 3110, 1), (Sum.inr 3573, 1), (Sum.inr 3853, 1), (Sum.inr 3872, 1), (Sum.inr 3883, 1), (Sum.inr 3889, 1)]

def sourceForm292 : Integer.Sparse Master := [(Sum.inr 2836, 1), (Sum.inr 2837, 1), (Sum.inr 2838, 1), (Sum.inr 2841, 1), (Sum.inr 3051, 1), (Sum.inr 3241, 1), (Sum.inr 3242, 1), (Sum.inr 3243, 1), (Sum.inr 3246, 1), (Sum.inr 3294, 1), (Sum.inr 3437, 1), (Sum.inr 3461, 1), (Sum.inr 3471, 1), (Sum.inr 3472, 1), (Sum.inr 3480, 1), (Sum.inr 3515, 1), (Sum.inr 3518, 1), (Sum.inr 3526, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3559, 1), (Sum.inr 3573, 1), (Sum.inr 3584, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1)]

def sourceForm293 : Integer.Sparse Master := [(Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3906, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def sourceForm294 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 1224, 1), (Sum.inr 1226, 1), (Sum.inr 1237, 1), (Sum.inr 1277, 1), (Sum.inr 2731, 1), (Sum.inr 4092, -1)]

def sourceForm295 : Integer.Sparse Master := [(Sum.inr 1277, 1), (Sum.inr 2577, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

def sourceForm296 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2495, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2731, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

def sourceForm297 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 2493, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 4092, -1)]

def sourceForm298 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2549, 1), (Sum.inr 2554, 1), (Sum.inr 2577, 1), (Sum.inr 2731, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

def sourceForm299 : Integer.Sparse Master := [(Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 2554, 1), (Sum.inr 2731, 1), (Sum.inr 2739, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def sourceForm300 : Integer.Sparse Master := [(Sum.inr 2645, 1), (Sum.inr 2647, 1), (Sum.inr 2649, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

def sourceForm301 : Integer.Sparse Master := [(Sum.inr 1226, 1), (Sum.inr 2499, 1), (Sum.inr 2549, 1), (Sum.inr 2649, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 4092, -1)]

def sourceForm303 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 989, 1), (Sum.inr 993, 1), (Sum.inr 1001, 1), (Sum.inr 1057, 1), (Sum.inr 2390, 1), (Sum.inr 2391, 1), (Sum.inr 2395, 1), (Sum.inr 2401, 1), (Sum.inr 2453, 1), (Sum.inr 2456, 1), (Sum.inr 2460, 1), (Sum.inr 2493, 1), (Sum.inr 2569, 1), (Sum.inr 2615, 1), (Sum.inr 2621, 1), (Sum.inr 2637, 1), (Sum.inr 2664, 1), (Sum.inr 2698, 1), (Sum.inr 2706, 1), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 2738, 1), (Sum.inr 2775, 1), (Sum.inr 3880, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 1), (Sum.inr 3995, 1)]

def sourceForm305 : Integer.Sparse Master := [(Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 3910, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

def sourceForm306 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 1361, 1), (Sum.inr 1363, 1), (Sum.inr 1370, 1), (Sum.inr 1423, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def sourceForm307 : Integer.Sparse Master := [(Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 2), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

def sourceForm308 : Integer.Sparse Master := [(Sum.inr 2627, 1), (Sum.inr 2946, 1), (Sum.inr 3008, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

def sourceForm309 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 2862, 1), (Sum.inr 3008, 1), (Sum.inr 3029, 1), (Sum.inr 3037, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def sourceForm310 : Integer.Sparse Master := [(Sum.inr 2625, 1), (Sum.inr 2918, 1), (Sum.inr 2972, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

def sourceForm311 : Integer.Sparse Master := [(Sum.inr 1423, 1), (Sum.inr 2625, 1), (Sum.inr 2627, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def sourceForm312 : Integer.Sparse Master := [(Sum.inr 2862, 1), (Sum.inr 2865, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 1), (Sum.inr 3039, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

def sourceForm313 : Integer.Sparse Master := [(Sum.inr 1363, 1), (Sum.inr 2868, 1), (Sum.inr 2972, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 2), (Sum.inr 4091, -1)]

def sourceForm314 : Integer.Sparse Master := [(Sum.inr 2641, 1), (Sum.inr 3029, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def sourceForm315 : Integer.Sparse Master := [(Sum.inr 1361, 1), (Sum.inr 2865, 1), (Sum.inr 2918, 1), (Sum.inr 2946, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def sourceForm316 : Integer.Sparse Master := [(Sum.inr 4803, 1), (Sum.inr 4808, 1), (Sum.inr 4810, 1), (Sum.inr 4839, 1), (Sum.inr 4854, 1), (Sum.inr 4855, 1), (Sum.inr 4870, 1), (Sum.inr 4880, 1), (Sum.inr 4896, 1), (Sum.inr 5220, 1), (Sum.inr 5223, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 2), (Sum.inr 5243, 1), (Sum.inr 5244, 1), (Sum.inr 5250, 1), (Sum.inr 5253, 1), (Sum.inr 5254, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 2), (Sum.inr 5264, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5293, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1)]

def sourceForm317 : Integer.Sparse Master := [(Sum.inr 2127, 1), (Sum.inr 2128, 1), (Sum.inr 2129, 1), (Sum.inr 2133, 1), (Sum.inr 2195, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2220, 1), (Sum.inr 2278, 1), (Sum.inr 2665, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2697, 1), (Sum.inr 2698, 1), (Sum.inr 2709, 1), (Sum.inr 2713, 1), (Sum.inr 2714, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 2767, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 3044, 1), (Sum.inr 3068, 1), (Sum.inr 3088, 1), (Sum.inr 3092, 1), (Sum.inr 3094, 1)]

def sourceForm318 : Integer.Sparse Master := [(Sum.inr 2091, 1), (Sum.inr 2092, 1), (Sum.inr 2093, 1), (Sum.inr 2111, 1), (Sum.inr 2254, 1), (Sum.inr 2662, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2678, 1), (Sum.inr 2723, 1), (Sum.inr 3016, 1), (Sum.inr 3017, 1), (Sum.inr 3019, 1), (Sum.inr 3029, 1), (Sum.inr 3030, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3040, 1), (Sum.inr 3044, 1), (Sum.inr 3045, 1), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3065, 1), (Sum.inr 3088, 1), (Sum.inr 3089, 1), (Sum.inr 3102, 1), (Sum.inr 3202, 1), (Sum.inr 3206, 1), (Sum.inr 3210, 1), (Sum.inr 3225, 1)]

def sourceForm319 : Integer.Sparse Master := [(Sum.inr 3388, 1), (Sum.inr 3391, 1), (Sum.inr 3392, 1), (Sum.inr 3395, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow0 : Integer.Sparse Master := [(Sum.inl 0, 10), (Sum.inl 12, -40), (Sum.inl 1, 30), (Sum.inr 2279, -540), (Sum.inr 2281, -180), (Sum.inr 2294, -180), (Sum.inr 3054, -540), (Sum.inr 3626, -540), (Sum.inr 3633, -180), (Sum.inr 3814, -1080), (Sum.inr 3907, -540)]

def numericRow1 : Integer.Sparse Master := [(Sum.inl 0, 35), (Sum.inl 12, 40), (Sum.inl 1, -75), (Sum.inr 2245, -432), (Sum.inr 2247, -216), (Sum.inr 2266, -432), (Sum.inr 2277, -432), (Sum.inr 2278, -432), (Sum.inr 2290, -216), (Sum.inr 3077, -432), (Sum.inr 3625, -432), (Sum.inr 3632, -432), (Sum.inr 3801, -432), (Sum.inr 3809, -864), (Sum.inr 3812, -432), (Sum.inr 3813, -864), (Sum.inr 3906, -864), (Sum.inr 3907, -432), (Sum.inr 3910, -432), (Sum.inr 3913, -432)]

def numericRow10 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, 5), (Sum.inr 3623, -30), (Sum.inr 3633, -10), (Sum.inr 3902, -60), (Sum.inr 3907, -30)]

def numericRow11 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, 1), (Sum.inr 4084, 24), (Sum.inr 4085, 3), (Sum.inr 4092, 36)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow100 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 9), (Sum.inl 13, 16), (Sum.inl 1, 9), (Sum.inr 1061, 216), (Sum.inr 1064, 72), (Sum.inr 1092, 72), (Sum.inr 1372, 216), (Sum.inr 2497, 432), (Sum.inr 2520, 216), (Sum.inr 2777, 216), (Sum.inr 2789, 72)]

def numericRow101 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, 1), (Sum.inl 3, -16), (Sum.inl 1, -2), (Sum.inr 1729, 432), (Sum.inr 1746, 432), (Sum.inr 1747, 144), (Sum.inr 1756, 144), (Sum.inr 1757, 144), (Sum.inr 2207, 864), (Sum.inr 2230, 432), (Sum.inr 2266, 432), (Sum.inr 2267, 432), (Sum.inr 2744, 432), (Sum.inr 2789, 144)]

def numericRow102 : Integer.Sparse Master := [(Sum.inr 2278, 3), (Sum.inr 2281, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def numericRow103 : Integer.Sparse Master := [(Sum.inr 1064, 1), (Sum.inr 1369, 3), (Sum.inr 1438, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def numericRow104 : Integer.Sparse Master := [(Sum.inr 1369, 1), (Sum.inr 2035, 2), (Sum.inr 2062, 1), (Sum.inr 2281, 1), (Sum.inr 3052, 1), (Sum.inr 4084, -1)]

def numericRow105 : Integer.Sparse Master := [(Sum.inr 1059, 1), (Sum.inr 2035, 2), (Sum.inr 2134, 1), (Sum.inr 2278, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def numericRow106 : Integer.Sparse Master := [(Sum.inr 1438, 1), (Sum.inr 2134, 3), (Sum.inr 2281, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def numericRow107 : Integer.Sparse Master := [(Sum.inr 1091, 1), (Sum.inr 2062, 3), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def numericRow108 : Integer.Sparse Master := [(Sum.inr 1059, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

def numericRow109 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 1094, -120), (Sum.inr 1741, -120), (Sum.inr 2065, -360), (Sum.inr 2218, -360), (Sum.inr 2247, -360), (Sum.inr 2281, -120), (Sum.inr 2290, -360), (Sum.inr 2294, -120), (Sum.inr 3634, -120), (Sum.inr 4500, 1440), (Sum.inr 4508, 480), (Sum.inr 4836, 2880), (Sum.inr 4844, 1440), (Sum.inr 4892, 1440), (Sum.inr 4900, 480), (Sum.inr 5268, 1440)]

def numericRow110 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, -21), (Sum.inl 13, 16), (Sum.inl 1, 3), (Sum.inr 1436, 216), (Sum.inr 1438, 72), (Sum.inr 2136, 216), (Sum.inr 2255, 216), (Sum.inr 2281, 72), (Sum.inr 2285, 72), (Sum.inr 2716, 432), (Sum.inr 2734, 216)]

def numericRow111 : Integer.Sparse Master := [(Sum.inl 0, -2), (Sum.inl 2, -9), (Sum.inl 13, -16), (Sum.inl 1, -3), (Sum.inr 1716, 432), (Sum.inr 1741, 144), (Sum.inr 1747, 144), (Sum.inr 2197, 864), (Sum.inr 2218, 432), (Sum.inr 2222, 432), (Sum.inr 2247, 432), (Sum.inr 2255, 432), (Sum.inr 2285, 144), (Sum.inr 2734, 432)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1000 : Integer.Sparse Master := [(Sum.inr 633, 1), (Sum.inr 1115, 2), (Sum.inr 1140, 1), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

def numericRow1001 : Integer.Sparse Master := [(Sum.inr 1615, 2), (Sum.inr 1620, 1), (Sum.inr 1629, 1), (Sum.inr 1752, 1), (Sum.inr 3298, 1), (Sum.inr 4072, -1)]

def numericRow1002 : Integer.Sparse Master := [(Sum.inr 1752, 2), (Sum.inr 3298, 3), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

def numericRow1003 : Integer.Sparse Master := [(Sum.inr 989, 2), (Sum.inr 994, 1), (Sum.inr 1009, 1), (Sum.inr 1055, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def numericRow1004 : Integer.Sparse Master := [(Sum.inr 994, 1), (Sum.inr 1179, 2), (Sum.inr 1190, 1), (Sum.inr 1258, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def numericRow1005 : Integer.Sparse Master := [(Sum.inr 975, 1), (Sum.inr 982, 2), (Sum.inr 1019, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def numericRow1006 : Integer.Sparse Master := [(Sum.inr 975, 1), (Sum.inr 1194, 1), (Sum.inr 1202, 1), (Sum.inr 1211, 2), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def numericRow1007 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 4), (Sum.inr 615, -144), (Sum.inr 622, -18), (Sum.inr 1140, -216), (Sum.inr 1537, -144), (Sum.inr 1541, -18), (Sum.inr 3275, -216), (Sum.inr 3310, -144)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1008 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 1, -4), (Sum.inr 615, 144), (Sum.inr 622, 18), (Sum.inr 1140, 216)]

def numericRow1009 : Integer.Sparse Master := [(Sum.inr 1051, -4), (Sum.inr 1752, -4), (Sum.inr 4594, 12)]

def numericRow1010 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, 4), (Sum.inl 6, -5), (Sum.inl 1, 2), (Sum.inr 1051, 144), (Sum.inr 1221, 216)]

def numericRow1011 : Integer.Sparse Master := [(Sum.inr 1752, 4), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

def numericRow1012 : Integer.Sparse Master := [(Sum.inr 615, -1), (Sum.inr 934, -3), (Sum.inr 1043, -3), (Sum.inr 1239, -3), (Sum.inr 1297, -1), (Sum.inr 1537, -1), (Sum.inr 1692, -3), (Sum.inr 1725, -3), (Sum.inr 2226, -3), (Sum.inr 2289, -1), (Sum.inr 4156, 12), (Sum.inr 4159, 12), (Sum.inr 4163, 4), (Sum.inr 4189, 4), (Sum.inr 4330, 24), (Sum.inr 4370, 12)]

def numericRow1013 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, -20), (Sum.inl 6, 25), (Sum.inl 2, 30), (Sum.inl 1, 20), (Sum.inr 587, 720), (Sum.inr 591, 240), (Sum.inr 617, 240), (Sum.inr 633, 720), (Sum.inr 1118, 1440), (Sum.inr 1142, 720)]

def numericRow1014 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1532, 3), (Sum.inr 1534, 1), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 1672, 6), (Sum.inr 1692, 3), (Sum.inr 1722, 3), (Sum.inr 1725, 3), (Sum.inr 2226, 3), (Sum.inr 2289, 1)]

def numericRow1015 : Integer.Sparse Master := [(Sum.inr 591, 1), (Sum.inr 628, 3), (Sum.inr 643, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

def numericRow1016 : Integer.Sparse Master := [(Sum.inr 628, 1), (Sum.inr 908, 2), (Sum.inr 934, 1), (Sum.inr 1051, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

def numericRow1017 : Integer.Sparse Master := [(Sum.inr 584, 1), (Sum.inr 908, 2), (Sum.inr 948, 1), (Sum.inr 1043, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

def numericRow1018 : Integer.Sparse Master := [(Sum.inr 643, 1), (Sum.inr 948, 3), (Sum.inr 1051, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def numericRow1019 : Integer.Sparse Master := [(Sum.inr 615, 1), (Sum.inr 934, 3), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

def numericRow1020 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 1, 20), (Sum.inr 545, -2160), (Sum.inr 549, -720), (Sum.inr 564, -720), (Sum.inr 574, -2160), (Sum.inr 609, -720), (Sum.inr 683, -2160), (Sum.inr 686, -720), (Sum.inr 695, -720), (Sum.inr 871, -4320), (Sum.inr 893, -2160), (Sum.inr 934, -2160), (Sum.inr 1046, -2160), (Sum.inr 1091, -720), (Sum.inr 1242, -2160), (Sum.inr 1494, -2160), (Sum.inr 1521, -720), (Sum.inr 1568, -4320), (Sum.inr 1578, -2160), (Sum.inr 1692, -2160), (Sum.inr 1750, -2160), (Sum.inr 1756, -720), (Sum.inr 3300, -2160), (Sum.inr 3310, -720), (Sum.inr 3634, -720)]

def numericRow1021 : Integer.Sparse Master := [(Sum.inl 0, -11), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, -20), (Sum.inr 545, 2160), (Sum.inr 549, 720), (Sum.inr 564, 720), (Sum.inr 574, 2160), (Sum.inr 609, 720), (Sum.inr 871, 4320), (Sum.inr 893, 2160), (Sum.inr 934, 2160), (Sum.inr 1046, 2160), (Sum.inr 1091, 720), (Sum.inr 1242, 2160)]

def numericRow1022 : Integer.Sparse Master := [(Sum.inr 1620, 3), (Sum.inr 1752, 1), (Sum.inr 4072, -1)]

def numericRow1023 : Integer.Sparse Master := [(Sum.inr 826, 3), (Sum.inr 832, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1024 : Integer.Sparse Master := [(Sum.inr 564, 1), (Sum.inr 726, 3), (Sum.inr 832, 1), (Sum.inr 4071, -1)]

def numericRow1025 : Integer.Sparse Master := [(Sum.inr 832, 1), (Sum.inr 1186, 3), (Sum.inr 1289, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

def numericRow1026 : Integer.Sparse Master := [(Sum.inr 785, 2), (Sum.inr 791, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def numericRow1027 : Integer.Sparse Master := [(Sum.inr 545, 1), (Sum.inr 705, 2), (Sum.inr 740, 1), (Sum.inr 791, 1), (Sum.inr 4069, -1)]

def numericRow1028 : Integer.Sparse Master := [(Sum.inr 791, 1), (Sum.inr 1199, 2), (Sum.inr 1231, 2), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def numericRow1029 : Integer.Sparse Master := [(Sum.inr 979, 2), (Sum.inr 986, 1), (Sum.inr 1037, 1), (Sum.inr 4081, -1)]

def numericRow1030 : Integer.Sparse Master := [(Sum.inr 609, -8), (Sum.inr 622, -1), (Sum.inr 928, -12), (Sum.inr 1521, -8), (Sum.inr 1541, -1), (Sum.inr 1677, -12), (Sum.inr 4085, 4)]

def numericRow1031 : Integer.Sparse Master := [(Sum.inr 1521, 8), (Sum.inr 1541, 1), (Sum.inr 1677, 12), (Sum.inr 4085, 1)]

def numericRow1032 : Integer.Sparse Master := [(Sum.inr 609, 4), (Sum.inr 622, 1), (Sum.inr 4085, -1)]

def numericRow1033 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, 10), (Sum.inr 986, -2160), (Sum.inr 1051, -1440), (Sum.inr 1620, -2160), (Sum.inr 1752, -1440), (Sum.inr 3313, -180), (Sum.inr 4072, 720)]

def numericRow1034 : Integer.Sparse Master := [(Sum.inr 540, -3), (Sum.inr 549, -1), (Sum.inr 570, -3), (Sum.inr 596, -1), (Sum.inr 665, -3), (Sum.inr 686, -1), (Sum.inr 701, -6), (Sum.inr 735, -3), (Sum.inr 750, -6), (Sum.inr 765, -3), (Sum.inr 801, -3), (Sum.inr 845, -1), (Sum.inr 1002, -6), (Sum.inr 1077, -2), (Sum.inr 4070, 4)]

def numericRow1035 : Integer.Sparse Master := [(Sum.inr 665, 3), (Sum.inr 686, 1), (Sum.inr 750, 6), (Sum.inr 765, 3), (Sum.inr 801, 3), (Sum.inr 845, 1), (Sum.inr 1002, 3), (Sum.inr 1077, 1), (Sum.inr 4070, 1)]

def numericRow1036 : Integer.Sparse Master := [(Sum.inr 549, 1), (Sum.inr 570, 3), (Sum.inr 596, 1), (Sum.inr 4070, -1)]

def numericRow1037 : Integer.Sparse Master := [(Sum.inr 540, 1), (Sum.inr 701, 2), (Sum.inr 735, 1), (Sum.inr 4070, -1)]

def numericRow1038 : Integer.Sparse Master := [(Sum.inr 596, 1), (Sum.inr 735, 3), (Sum.inr 1077, 1), (Sum.inr 4070, -1)]

def numericRow1039 : Integer.Sparse Master := [(Sum.inr 4060, 8), (Sum.inr 4062, 1), (Sum.inr 4066, 12), (Sum.inr 4070, 8), (Sum.inr 4085, 1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1040 : Integer.Sparse Master := [(Sum.inr 621, 1), (Sum.inr 940, 3), (Sum.inr 1092, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

def numericRow1041 : Integer.Sparse Master := [(Sum.inr 1093, 1), (Sum.inr 1747, 1), (Sum.inr 2064, 3), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def numericRow1042 : Integer.Sparse Master := [(Sum.inr 1745, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def numericRow1043 : Integer.Sparse Master := [(Sum.inr 860, 1), (Sum.inr 1628, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

def numericRow1044 : Integer.Sparse Master := [(Sum.inr 612, 1), (Sum.inr 931, 2), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def numericRow1045 : Integer.Sparse Master := [(Sum.inr 590, 1), (Sum.inr 914, 2), (Sum.inr 954, 1), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

def numericRow1046 : Integer.Sparse Master := [(Sum.inr 951, 1), (Sum.inr 1336, 2), (Sum.inr 1348, 1), (Sum.inr 1408, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

def numericRow1047 : Integer.Sparse Master := [(Sum.inr 1072, 1), (Sum.inr 1745, 1), (Sum.inr 2045, 2), (Sum.inr 2226, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def numericRow1048 : Integer.Sparse Master := [(Sum.inr 1744, 2), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

def numericRow1049 : Integer.Sparse Master := [(Sum.inr 853, 1), (Sum.inr 1619, 2), (Sum.inr 1745, 1), (Sum.inr 1750, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

def numericRow1050 : Integer.Sparse Master := [(Sum.inr 606, 1), (Sum.inr 925, 2), (Sum.inr 1059, 1), (Sum.inr 1083, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

def numericRow1051 : Integer.Sparse Master := [(Sum.inr 1142, 1), (Sum.inr 1317, 2), (Sum.inr 1324, 1), (Sum.inr 1372, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

def numericRow1052 : Integer.Sparse Master := [(Sum.inr 1729, 1), (Sum.inr 1952, 1), (Sum.inr 3242, 2), (Sum.inr 3247, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def numericRow1053 : Integer.Sparse Master := [(Sum.inr 808, 2), (Sum.inr 814, 1), (Sum.inr 815, 1), (Sum.inr 857, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

def numericRow1054 : Integer.Sparse Master := [(Sum.inr 1723, 2), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 1750, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def numericRow1055 : Integer.Sparse Master := [(Sum.inr 857, 1), (Sum.inr 1624, 2), (Sum.inr 1729, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1056 : Integer.Sparse Master := [(Sum.inr 815, 1), (Sum.inr 1604, 2), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

def numericRow1057 : Integer.Sparse Master := [(Sum.inr 936, 1), (Sum.inr 1315, 2), (Sum.inr 1323, 1), (Sum.inr 1369, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def numericRow1058 : Integer.Sparse Master := [(Sum.inr 1011, 1), (Sum.inr 1746, 1), (Sum.inr 1952, 1), (Sum.inr 2005, 2), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

def numericRow1059 : Integer.Sparse Master := [(Sum.inr 581, 1), (Sum.inr 905, 1), (Sum.inr 945, 1), (Sum.inr 1022, 1), (Sum.inr 1041, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

def numericRow1060 : Integer.Sparse Master := [(Sum.inr 1118, 1), (Sum.inr 1327, 1), (Sum.inr 1333, 1), (Sum.inr 1337, 1), (Sum.inr 1388, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

def numericRow1061 : Integer.Sparse Master := [(Sum.inr 1723, 1), (Sum.inr 1942, 1), (Sum.inr 3279, 1), (Sum.inr 3283, 1), (Sum.inr 3300, 2), (Sum.inr 4070, -1)]

def numericRow1062 : Integer.Sparse Master := [(Sum.inr 847, 1), (Sum.inr 1613, 1), (Sum.inr 1723, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 2), (Sum.inr 4070, -1)]

def numericRow1063 : Integer.Sparse Master := [(Sum.inr 804, 1), (Sum.inr 1643, 1), (Sum.inr 1723, 1), (Sum.inr 1725, 2), (Sum.inr 4070, -1)]

def numericRow1064 : Integer.Sparse Master := [(Sum.inr 585, 1), (Sum.inr 909, 1), (Sum.inr 949, 1), (Sum.inr 1024, 2), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

def numericRow1065 : Integer.Sparse Master := [(Sum.inr 911, 1), (Sum.inr 1326, 1), (Sum.inr 1332, 1), (Sum.inr 1336, 1), (Sum.inr 1385, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

def numericRow1066 : Integer.Sparse Master := [(Sum.inr 997, 1), (Sum.inr 1744, 1), (Sum.inr 1942, 1), (Sum.inr 1995, 1), (Sum.inr 2226, 2), (Sum.inr 4070, -1)]

def numericRow1067 : Integer.Sparse Master := [(Sum.inr 1355, 1), (Sum.inr 1902, 1), (Sum.inr 1915, 1), (Sum.inr 1926, 1), (Sum.inr 2197, 1), (Sum.inr 3024, 1), (Sum.inr 4080, -1)]

def numericRow1068 : Integer.Sparse Master := [(Sum.inr 1132, 2), (Sum.inr 1142, 1), (Sum.inr 1145, 1), (Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

def numericRow1069 : Integer.Sparse Master := [(Sum.inr 636, 1), (Sum.inr 1145, 1), (Sum.inr 1155, 2), (Sum.inr 1243, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

def numericRow1070 : Integer.Sparse Master := [(Sum.inr 641, 1), (Sum.inr 1159, 2), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

def numericRow1071 : Integer.Sparse Master := [(Sum.inr 1643, 2), (Sum.inr 1647, 1), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1072 : Integer.Sparse Master := [(Sum.inr 1619, 2), (Sum.inr 1628, 1), (Sum.inr 1630, 1), (Sum.inr 1756, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

def numericRow1073 : Integer.Sparse Master := [(Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 3302, 3), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def numericRow1074 : Integer.Sparse Master := [(Sum.inr 1725, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def numericRow1075 : Integer.Sparse Master := [(Sum.inr 1630, 1), (Sum.inr 3247, 1), (Sum.inr 3283, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

def numericRow1076 : Integer.Sparse Master := [(Sum.inr 1258, 1), (Sum.inr 2119, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2761, 1), (Sum.inr 4082, -1)]

def numericRow1077 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1115, 1), (Sum.inr 1119, 1), (Sum.inr 1131, 1), (Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

def numericRow1078 : Integer.Sparse Master := [(Sum.inr 626, 1), (Sum.inr 1131, 1), (Sum.inr 1148, 1), (Sum.inr 1215, 1), (Sum.inr 1236, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

def numericRow1079 : Integer.Sparse Master := [(Sum.inr 630, 1), (Sum.inr 1136, 1), (Sum.inr 1150, 1), (Sum.inr 1217, 2), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

def numericRow1080 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1118, 1), (Sum.inr 1120, 1), (Sum.inr 1136, 1), (Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

def numericRow1081 : Integer.Sparse Master := [(Sum.inr 1613, 1), (Sum.inr 1617, 1), (Sum.inr 1619, 1), (Sum.inr 1624, 1), (Sum.inr 1750, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

def numericRow1082 : Integer.Sparse Master := [(Sum.inr 1599, 1), (Sum.inr 1604, 1), (Sum.inr 1617, 1), (Sum.inr 1725, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

def numericRow1083 : Integer.Sparse Master := [(Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def numericRow1084 : Integer.Sparse Master := [(Sum.inr 1617, 1), (Sum.inr 3242, 1), (Sum.inr 3279, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def numericRow1085 : Integer.Sparse Master := [(Sum.inr 1599, 1), (Sum.inr 1995, 1), (Sum.inr 2005, 1), (Sum.inr 2045, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

def numericRow1086 : Integer.Sparse Master := [(Sum.inr 1211, 1), (Sum.inr 2070, 1), (Sum.inr 2079, 1), (Sum.inr 2087, 1), (Sum.inr 2193, 1), (Sum.inr 2719, 1), (Sum.inr 4080, -1)]

def numericRow1087 : Integer.Sparse Master := [(Sum.inr 1181, 1), (Sum.inr 2385, 1), (Sum.inr 2453, 1), (Sum.inr 2492, 1), (Sum.inr 2664, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1088 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 1181, 1), (Sum.inr 1182, 1), (Sum.inr 1188, 1), (Sum.inr 1257, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

def numericRow1089 : Integer.Sparse Master := [(Sum.inr 1179, 1), (Sum.inr 1991, 1), (Sum.inr 2003, 1), (Sum.inr 2032, 1), (Sum.inr 2218, 1), (Sum.inr 2670, 1), (Sum.inr 4082, -1)]

def numericRow1090 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 2449, 2), (Sum.inr 2469, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

def numericRow1091 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 1196, 1), (Sum.inr 1200, 1), (Sum.inr 1210, 2), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

def numericRow1092 : Integer.Sparse Master := [(Sum.inr 1194, 1), (Sum.inr 1987, 2), (Sum.inr 2008, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def numericRow1093 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, 100), (Sum.inr 611, -720), (Sum.inr 615, -240), (Sum.inr 620, -240), (Sum.inr 1136, -1440), (Sum.inr 1140, -720), (Sum.inr 1145, -720), (Sum.inr 1535, -720), (Sum.inr 1537, -240), (Sum.inr 1539, -240), (Sum.inr 3273, -1440), (Sum.inr 3275, -720), (Sum.inr 3277, -720), (Sum.inr 3308, -720), (Sum.inr 3310, -720), (Sum.inr 3311, -240), (Sum.inr 3313, -240), (Sum.inr 3608, -720)]

def numericRow1094 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 1, -100), (Sum.inr 611, 720), (Sum.inr 615, 240), (Sum.inr 620, 240), (Sum.inr 1136, 1440), (Sum.inr 1140, 720), (Sum.inr 1145, 720)]

def numericRow1095 : Integer.Sparse Master := [(Sum.inl 0, 5), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 1, -10), (Sum.inr 605, -216), (Sum.inr 609, -72), (Sum.inr 619, -72), (Sum.inr 934, -216), (Sum.inr 1051, -72), (Sum.inr 1131, -432), (Sum.inr 1144, -216), (Sum.inr 1242, -216), (Sum.inr 1518, -216), (Sum.inr 1521, -72), (Sum.inr 1538, -72), (Sum.inr 1692, -216), (Sum.inr 1752, -72), (Sum.inr 3264, -432), (Sum.inr 3276, -216), (Sum.inr 3300, -216), (Sum.inr 3309, -216), (Sum.inr 3312, -72), (Sum.inr 3615, -216), (Sum.inr 3634, -72)]

def numericRow1096 : Integer.Sparse Master := [(Sum.inl 0, -5), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 10), (Sum.inr 605, 216), (Sum.inr 609, 72), (Sum.inr 619, 72), (Sum.inr 934, 216), (Sum.inr 1051, 72), (Sum.inr 1131, 432), (Sum.inr 1144, 216), (Sum.inr 1242, 216)]

def numericRow1097 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 4), (Sum.inr 1043, -432), (Sum.inr 1046, -432), (Sum.inr 1091, -144), (Sum.inr 1239, -432), (Sum.inr 1242, -864), (Sum.inr 1297, -144), (Sum.inr 1725, -432), (Sum.inr 1750, -432), (Sum.inr 1756, -144), (Sum.inr 2226, -432), (Sum.inr 2289, -144), (Sum.inr 3300, -864), (Sum.inr 3310, -144), (Sum.inr 4591, 3456), (Sum.inr 4609, 1728)]

def numericRow1098 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, -20), (Sum.inl 6, 25), (Sum.inl 2, 30), (Sum.inl 1, 20), (Sum.inr 1046, 720), (Sum.inr 1091, 240), (Sum.inr 1217, 1440), (Sum.inr 1242, 720), (Sum.inr 1243, 720)]

def numericRow1099 : Integer.Sparse Master := [(Sum.inr 1750, 3), (Sum.inr 1756, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def numericRow1100 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

def numericRow1101 : Integer.Sparse Master := [(Sum.inr 3300, 3), (Sum.inr 3310, 2), (Sum.inr 4070, -1)]

def numericRow1102 : Integer.Sparse Master := [(Sum.inr 1051, -1), (Sum.inr 1239, -3), (Sum.inr 1752, -1), (Sum.inr 2109, -3), (Sum.inr 2226, -3), (Sum.inr 2261, -3), (Sum.inr 2783, -2), (Sum.inr 4184, 12), (Sum.inr 4189, 4), (Sum.inr 4193, 4), (Sum.inr 4370, 12), (Sum.inr 4552, 24), (Sum.inr 4560, 12), (Sum.inr 4617, 12), (Sum.inr 4626, 4)]

def numericRow1103 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 6, -10), (Sum.inl 2, 40), (Sum.inl 35, 160), (Sum.inl 1, 90), (Sum.inr 612, 2160), (Sum.inr 617, 720), (Sum.inr 621, 720), (Sum.inr 1137, 4320), (Sum.inr 1142, 2160), (Sum.inr 1146, 2160), (Sum.inr 1306, 2160), (Sum.inr 1310, 720)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1104 : Integer.Sparse Master := [(Sum.inr 1530, 3), (Sum.inr 1531, 1), (Sum.inr 1540, 1), (Sum.inr 1722, 3), (Sum.inr 1752, 1), (Sum.inr 2200, 6), (Sum.inr 2226, 3), (Sum.inr 2258, 3), (Sum.inr 2261, 3), (Sum.inr 2737, 3), (Sum.inr 2780, 1), (Sum.inr 2783, 1)]

def numericRow1105 : Integer.Sparse Master := [(Sum.inr 639, 3), (Sum.inr 643, 1), (Sum.inr 654, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def numericRow1106 : Integer.Sparse Master := [(Sum.inr 639, 1), (Sum.inr 1157, 2), (Sum.inr 1239, 1), (Sum.inr 1292, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def numericRow1107 : Integer.Sparse Master := [(Sum.inr 948, 1), (Sum.inr 1157, 2), (Sum.inr 1174, 1), (Sum.inr 1297, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

def numericRow1108 : Integer.Sparse Master := [(Sum.inl 0, 9), (Sum.inl 5, 20), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, 50), (Sum.inr 594, -2160), (Sum.inr 596, -720), (Sum.inr 618, -720), (Sum.inr 740, -2160), (Sum.inr 832, -720), (Sum.inr 842, -2160), (Sum.inr 845, -720), (Sum.inr 862, -720), (Sum.inr 1123, -4320), (Sum.inr 1143, -2160), (Sum.inr 1190, -2160), (Sum.inr 1294, -2160), (Sum.inr 1499, -2160), (Sum.inr 1527, -720), (Sum.inr 1937, -4320), (Sum.inr 1952, -2160), (Sum.inr 2112, -2160), (Sum.inr 2167, -2160), (Sum.inr 2281, -720), (Sum.inr 2287, -2160), (Sum.inr 2294, -720), (Sum.inr 3305, -2160), (Sum.inr 3311, -720), (Sum.inr 3633, -720)]

def numericRow1109 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 5, -20), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, -50), (Sum.inr 594, 2160), (Sum.inr 596, 720), (Sum.inr 618, 720), (Sum.inr 740, 2160), (Sum.inr 832, 720), (Sum.inr 1123, 4320), (Sum.inr 1143, 2160), (Sum.inr 1190, 2160), (Sum.inr 1294, 2160), (Sum.inr 2112, 2160), (Sum.inr 2281, 720)]

def numericRow1110 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 5, 80), (Sum.inl 6, 40), (Sum.inl 2, 40), (Sum.inl 52, -320), (Sum.inl 1, -40), (Sum.inr 1037, 8640), (Sum.inr 1077, 2880), (Sum.inr 1211, 17280), (Sum.inr 1231, 8640), (Sum.inr 1239, 8640), (Sum.inr 1258, 8640), (Sum.inr 1264, 8640), (Sum.inr 1289, 2880), (Sum.inr 1408, 8640), (Sum.inr 1438, 2880)]

def numericRow1111 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 6, 50), (Sum.inl 2, 40), (Sum.inl 35, 160), (Sum.inl 1, 30), (Sum.inr 1047, 2160), (Sum.inr 1091, 720), (Sum.inr 1092, 720), (Sum.inr 1218, 4320), (Sum.inr 1243, 2160), (Sum.inr 1244, 2160), (Sum.inr 1272, 2160), (Sum.inr 1309, 720)]

def numericRow1112 : Integer.Sparse Master := [(Sum.inr 1077, 1), (Sum.inr 1647, 3), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

def numericRow1113 : Integer.Sparse Master := [(Sum.inr 1289, 1), (Sum.inr 1657, 3), (Sum.inr 1741, 1), (Sum.inr 2780, 1), (Sum.inr 4071, -1)]

def numericRow1114 : Integer.Sparse Master := [(Sum.inr 1131, -2), (Sum.inr 1140, -1), (Sum.inr 1144, -1), (Sum.inr 1236, -2), (Sum.inr 1246, -1), (Sum.inr 1294, -1), (Sum.inr 2482, -2), (Sum.inr 2726, -1), (Sum.inr 3264, -2), (Sum.inr 3275, -1), (Sum.inr 3276, -1), (Sum.inr 3293, -2), (Sum.inr 3301, -1), (Sum.inr 3305, -1), (Sum.inr 3468, -2), (Sum.inr 3545, -1), (Sum.inr 4153, 8), (Sum.inr 4156, 4), (Sum.inr 4161, 4), (Sum.inr 4178, 4), (Sum.inr 4528, 8), (Sum.inr 4531, 8), (Sum.inr 4535, 8), (Sum.inr 4547, 8), (Sum.inr 4591, 8), (Sum.inr 4594, 4), (Sum.inr 4609, 4)]

def numericRow1115 : Integer.Sparse Master := [(Sum.inl 0, -13), (Sum.inl 5, 10), (Sum.inl 6, -5), (Sum.inl 2, -15), (Sum.inl 1, 5), (Sum.inr 581, 360), (Sum.inr 584, 180), (Sum.inr 589, 180), (Sum.inr 606, 180), (Sum.inr 1112, 360), (Sum.inr 1115, 360), (Sum.inr 1120, 360), (Sum.inr 1132, 360), (Sum.inr 1217, 360), (Sum.inr 1221, 180), (Sum.inr 1243, 180)]

def numericRow1116 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1516, 1), (Sum.inr 1520, 1), (Sum.inr 1533, 1), (Sum.inr 3260, 2), (Sum.inr 3262, 2), (Sum.inr 3264, 2), (Sum.inr 3266, 2), (Sum.inr 3272, 2), (Sum.inr 3275, 1), (Sum.inr 3276, 1), (Sum.inr 3291, 2), (Sum.inr 3293, 2), (Sum.inr 3298, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3468, 2), (Sum.inr 3545, 1)]

def numericRow1117 : Integer.Sparse Master := [(Sum.inr 626, 2), (Sum.inr 633, 1), (Sum.inr 635, 1), (Sum.inr 641, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

def numericRow1118 : Integer.Sparse Master := [(Sum.inr 1115, 1), (Sum.inr 1148, 1), (Sum.inr 1154, 1), (Sum.inr 1159, 1), (Sum.inr 1242, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

def numericRow1119 : Integer.Sparse Master := [(Sum.inr 1131, 2), (Sum.inr 1140, 1), (Sum.inr 1144, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow112 : Integer.Sparse Master := [(Sum.inr 1094, 1), (Sum.inr 2065, 3), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

def numericRow113 : Integer.Sparse Master := [(Sum.inl 0, 39), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 20), (Sum.inr 787, -2160), (Sum.inr 791, -1080), (Sum.inr 813, -2160), (Sum.inr 847, -2160), (Sum.inr 849, -1080), (Sum.inr 853, -2160), (Sum.inr 1202, -2160), (Sum.inr 1239, -2160), (Sum.inr 1898, -2160), (Sum.inr 1915, -4320), (Sum.inr 1940, -2160), (Sum.inr 1942, -2160), (Sum.inr 1946, -4320), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2224, -4320), (Sum.inr 2226, -2160), (Sum.inr 2230, -2160), (Sum.inr 2245, -2160), (Sum.inr 2266, -2160), (Sum.inr 2277, -2160), (Sum.inr 2278, -2160), (Sum.inr 3077, -2160), (Sum.inr 3625, -2160), (Sum.inr 3632, -2160)]

def numericRow114 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, 10), (Sum.inr 787, 2160), (Sum.inr 791, 1080), (Sum.inr 813, 2160), (Sum.inr 1202, 2160), (Sum.inr 1239, 2160), (Sum.inr 1898, 2160), (Sum.inr 1915, 4320), (Sum.inr 2025, 4320), (Sum.inr 2062, 2160), (Sum.inr 2245, 2160), (Sum.inr 2266, 2160), (Sum.inr 3077, 2160)]

def numericRow115 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 1046, -4320), (Sum.inr 1750, -4320), (Sum.inr 2025, -8640), (Sum.inr 2112, -4320), (Sum.inr 2224, -8640), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 2287, -4320), (Sum.inr 3623, -2160), (Sum.inr 4440, 17280), (Sum.inr 4442, 17280), (Sum.inr 4445, 8640), (Sum.inr 4464, 17280), (Sum.inr 4792, 17280), (Sum.inr 4853, 34560), (Sum.inr 5270, 17280), (Sum.inr 5295, 17280)]

def numericRow116 : Integer.Sparse Master := [(Sum.inl 0, -52), (Sum.inl 2, 15), (Sum.inl 13, -80), (Sum.inl 1, -105), (Sum.inr 1024, 1440), (Sum.inr 1027, 720), (Sum.inr 1047, 1440), (Sum.inr 1388, 1440), (Sum.inr 2471, 1440), (Sum.inr 2486, 2880), (Sum.inr 2754, 1440), (Sum.inr 2769, 1440)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1120 : Integer.Sparse Master := [(Sum.inl 0, 38), (Sum.inl 5, -30), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, -40), (Sum.inl 1, -5), (Sum.inr 572, -2160), (Sum.inr 574, -1080), (Sum.inr 576, -1080), (Sum.inr 605, -1080), (Sum.inr 871, -2160), (Sum.inr 893, -1080), (Sum.inr 1051, -1080), (Sum.inr 1101, -2160), (Sum.inr 1104, -1080), (Sum.inr 1107, -2160), (Sum.inr 1110, -2160), (Sum.inr 1131, -2160), (Sum.inr 1240, -2160), (Sum.inr 1242, -2160), (Sum.inr 1246, -1080), (Sum.inr 1492, -2160), (Sum.inr 1494, -1080), (Sum.inr 1496, -1080), (Sum.inr 1518, -1080), (Sum.inr 1568, -2160), (Sum.inr 1578, -1080), (Sum.inr 1752, -1080), (Sum.inr 2485, -2160), (Sum.inr 2519, -1080), (Sum.inr 3235, -2160), (Sum.inr 3237, -1080), (Sum.inr 3250, -2160), (Sum.inr 3252, -2160), (Sum.inr 3264, -2160), (Sum.inr 3299, -2160), (Sum.inr 3300, -2160), (Sum.inr 3301, -1080), (Sum.inr 3309, -1080), (Sum.inr 3310, -1080), (Sum.inr 3481, -2160), (Sum.inr 3486, -1080), (Sum.inr 3627, -1080), (Sum.inr 3634, -1080)]

def numericRow1121 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 5, 30), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 8, 40), (Sum.inl 1, 5), (Sum.inr 572, 2160), (Sum.inr 574, 1080), (Sum.inr 576, 1080), (Sum.inr 605, 1080), (Sum.inr 871, 2160), (Sum.inr 893, 1080), (Sum.inr 1051, 1080), (Sum.inr 1101, 2160), (Sum.inr 1104, 1080), (Sum.inr 1107, 2160), (Sum.inr 1110, 2160), (Sum.inr 1131, 2160), (Sum.inr 1240, 2160), (Sum.inr 1242, 2160), (Sum.inr 1246, 1080), (Sum.inr 2485, 2160), (Sum.inr 2519, 1080)]

def numericRow1122 : Integer.Sparse Master := [(Sum.inr 1617, 2), (Sum.inr 1630, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

def numericRow1123 : Integer.Sparse Master := [(Sum.inr 934, -1), (Sum.inr 1051, -1), (Sum.inr 1128, -2), (Sum.inr 1143, -1), (Sum.inr 1239, -2), (Sum.inr 1297, -1), (Sum.inr 1692, -1), (Sum.inr 1752, -1), (Sum.inr 2022, -2), (Sum.inr 2167, -1), (Sum.inr 2184, -2), (Sum.inr 2203, -2), (Sum.inr 2226, -2), (Sum.inr 2289, -1), (Sum.inr 2740, -2), (Sum.inr 4157, 8), (Sum.inr 4159, 4), (Sum.inr 4162, 4), (Sum.inr 4184, 4), (Sum.inr 4330, 8), (Sum.inr 4532, 8), (Sum.inr 4536, 8), (Sum.inr 4552, 8), (Sum.inr 4600, 8), (Sum.inr 4611, 4), (Sum.inr 4617, 4)]

def numericRow1124 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, 40), (Sum.inl 6, -40), (Sum.inl 2, 140), (Sum.inl 35, -160), (Sum.inl 1, 110), (Sum.inr 585, 2880), (Sum.inr 587, 1440), (Sum.inr 590, 1440), (Sum.inr 612, 1440), (Sum.inr 1116, 2880), (Sum.inr 1118, 2880), (Sum.inr 1121, 2880), (Sum.inr 1137, 2880), (Sum.inr 1270, 2880), (Sum.inr 1273, 1440), (Sum.inr 1306, 1440)]

def numericRow1125 : Integer.Sparse Master := [(Sum.inr 1528, 2), (Sum.inr 1529, 1), (Sum.inr 1530, 1), (Sum.inr 1532, 1), (Sum.inr 1672, 2), (Sum.inr 1692, 1), (Sum.inr 1752, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2172, 2), (Sum.inr 2184, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2226, 2), (Sum.inr 2289, 1), (Sum.inr 2683, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 1)]

def numericRow1126 : Integer.Sparse Master := [(Sum.inr 624, 2), (Sum.inr 628, 1), (Sum.inr 634, 1), (Sum.inr 639, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

def numericRow1127 : Integer.Sparse Master := [(Sum.inr 624, 1), (Sum.inr 1128, 1), (Sum.inr 1147, 1), (Sum.inr 1234, 1), (Sum.inr 1239, 2), (Sum.inr 4084, -1)]

def numericRow1128 : Integer.Sparse Master := [(Sum.inr 908, 1), (Sum.inr 1147, 1), (Sum.inr 1153, 1), (Sum.inr 1157, 1), (Sum.inr 1239, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

def numericRow1129 : Integer.Sparse Master := [(Sum.inr 934, 1), (Sum.inr 1128, 2), (Sum.inr 1143, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

def numericRow1130 : Integer.Sparse Master := [(Sum.inl 0, 34), (Sum.inl 6, 5), (Sum.inl 2, -25), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 568, -4320), (Sum.inr 570, -2160), (Sum.inr 575, -2160), (Sum.inr 602, -2160), (Sum.inr 705, -4320), (Sum.inr 726, -2160), (Sum.inr 762, -4320), (Sum.inr 765, -2160), (Sum.inr 774, -2160), (Sum.inr 791, -2160), (Sum.inr 849, -2160), (Sum.inr 1098, -4320), (Sum.inr 1103, -2160), (Sum.inr 1105, -4320), (Sum.inr 1109, -4320), (Sum.inr 1128, -4320), (Sum.inr 1202, -4320), (Sum.inr 1236, -4320), (Sum.inr 1239, -2160), (Sum.inr 1246, -2160), (Sum.inr 1489, -4320), (Sum.inr 1495, -2160), (Sum.inr 1509, -2160), (Sum.inr 1849, -4320), (Sum.inr 1858, -2160), (Sum.inr 1887, -4320), (Sum.inr 1894, -4320), (Sum.inr 1942, -4320), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2184, -4320), (Sum.inr 2224, -4320), (Sum.inr 2226, -2160), (Sum.inr 2230, -2160), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 3293, -4320), (Sum.inr 3301, -2160), (Sum.inr 3308, -2160), (Sum.inr 3632, -2160)]

def numericRow1131 : Integer.Sparse Master := [(Sum.inl 0, -34), (Sum.inl 6, -5), (Sum.inl 2, 25), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 568, 4320), (Sum.inr 570, 2160), (Sum.inr 575, 2160), (Sum.inr 602, 2160), (Sum.inr 705, 4320), (Sum.inr 726, 2160), (Sum.inr 791, 2160), (Sum.inr 1098, 4320), (Sum.inr 1103, 2160), (Sum.inr 1105, 4320), (Sum.inr 1109, 4320), (Sum.inr 1128, 4320), (Sum.inr 1202, 4320), (Sum.inr 1236, 4320), (Sum.inr 1239, 2160), (Sum.inr 1246, 2160), (Sum.inr 2025, 4320), (Sum.inr 2062, 2160), (Sum.inr 2247, 2160)]

def numericRow1132 : Integer.Sparse Master := [(Sum.inr 1002, 1), (Sum.inr 1599, 2), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

def numericRow1133 : Integer.Sparse Master := [(Sum.inr 1231, 1), (Sum.inr 1637, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

def numericRow1134 : Integer.Sparse Master := [(Sum.inr 1191, 1), (Sum.inr 2391, 2), (Sum.inr 2407, 1), (Sum.inr 2680, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

def numericRow1135 : Integer.Sparse Master := [(Sum.inr 1185, 2), (Sum.inr 1191, 1), (Sum.inr 1193, 1), (Sum.inr 1288, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1136 : Integer.Sparse Master := [(Sum.inr 1190, 1), (Sum.inr 1924, 2), (Sum.inr 2218, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

def numericRow1137 : Integer.Sparse Master := [(Sum.inr 893, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1190, 1), (Sum.inr 4082, -1)]

def numericRow1138 : Integer.Sparse Master := [(Sum.inr 1184, 2), (Sum.inr 1190, 1), (Sum.inr 1192, 1), (Sum.inr 1287, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

def numericRow1139 : Integer.Sparse Master := [(Sum.inr 1186, 1), (Sum.inr 1608, 2), (Sum.inr 1627, 1), (Sum.inr 1741, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

def numericRow1140 : Integer.Sparse Master := [(Sum.inr 1203, 1), (Sum.inr 2385, 2), (Sum.inr 2664, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def numericRow1141 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 1203, 1), (Sum.inr 1205, 1), (Sum.inr 1230, 2), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def numericRow1142 : Integer.Sparse Master := [(Sum.inr 1202, 1), (Sum.inr 1897, 1), (Sum.inr 2193, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

def numericRow1143 : Integer.Sparse Master := [(Sum.inr 871, 1), (Sum.inr 1105, 1), (Sum.inr 1109, 1), (Sum.inr 1123, 1), (Sum.inr 1202, 1), (Sum.inr 4080, -1)]

def numericRow1144 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 1202, 1), (Sum.inr 1204, 1), (Sum.inr 1229, 2), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

def numericRow1145 : Integer.Sparse Master := [(Sum.inr 1199, 1), (Sum.inr 1602, 2), (Sum.inr 1710, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

def numericRow1146 : Integer.Sparse Master := [(Sum.inr 1055, 1), (Sum.inr 2032, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

def numericRow1147 : Integer.Sparse Master := [(Sum.inr 1053, 2), (Sum.inr 1055, 1), (Sum.inr 1062, 1), (Sum.inr 1075, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

def numericRow1148 : Integer.Sparse Master := [(Sum.inr 991, 1), (Sum.inr 1926, 1), (Sum.inr 1992, 1), (Sum.inr 2121, 1), (Sum.inr 2197, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def numericRow1149 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 991, 1), (Sum.inr 993, 1), (Sum.inr 1005, 1), (Sum.inr 1054, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def numericRow1150 : Integer.Sparse Master := [(Sum.inr 989, 1), (Sum.inr 1924, 1), (Sum.inr 1991, 1), (Sum.inr 2119, 1), (Sum.inr 2215, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def numericRow1151 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 989, 1), (Sum.inr 992, 1), (Sum.inr 1000, 1), (Sum.inr 1053, 1), (Sum.inr 2215, 1), (Sum.inr 4082, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1152 : Integer.Sparse Master := [(Sum.inr 1019, 1), (Sum.inr 2008, 1), (Sum.inr 2087, 2), (Sum.inr 2193, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

def numericRow1153 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 1019, 1), (Sum.inr 1025, 1), (Sum.inr 1035, 2), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

def numericRow1154 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 1898, 1), (Sum.inr 2071, 2), (Sum.inr 2187, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

def numericRow1155 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 980, 2), (Sum.inr 1018, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

def numericRow1156 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 2070, 2), (Sum.inr 2190, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def numericRow1157 : Integer.Sparse Master := [(Sum.inr 973, 1), (Sum.inr 977, 2), (Sum.inr 1017, 1), (Sum.inr 2190, 1), (Sum.inr 4080, -1)]

def numericRow1158 : Integer.Sparse Master := [(Sum.inr 611, -1), (Sum.inr 930, -2), (Sum.inr 1041, -2), (Sum.inr 1046, -1), (Sum.inr 1050, -1), (Sum.inr 1535, -1), (Sum.inr 1690, -2), (Sum.inr 1724, -2), (Sum.inr 1750, -1), (Sum.inr 1751, -1), (Sum.inr 2025, -2), (Sum.inr 2112, -1), (Sum.inr 2224, -2), (Sum.inr 2247, -1), (Sum.inr 2287, -1), (Sum.inr 2290, -1), (Sum.inr 4153, 8), (Sum.inr 4159, 4), (Sum.inr 4161, 4), (Sum.inr 4327, 8), (Sum.inr 4333, 8), (Sum.inr 4335, 8), (Sum.inr 4358, 4), (Sum.inr 4367, 8), (Sum.inr 4374, 4), (Sum.inr 4440, 8), (Sum.inr 4445, 4)]

def numericRow1159 : Integer.Sparse Master := [(Sum.inl 0, -208), (Sum.inl 5, 80), (Sum.inl 6, -80), (Sum.inl 2, -320), (Sum.inl 52, -320), (Sum.inl 1, -400), (Sum.inr 626, 5760), (Sum.inr 628, 2880), (Sum.inr 635, 2880), (Sum.inr 911, 5760), (Sum.inr 936, 2880), (Sum.inr 1027, 2880), (Sum.inr 1317, 5760), (Sum.inr 1324, 2880), (Sum.inr 1327, 5760), (Sum.inr 1333, 5760), (Sum.inr 1388, 5760)]

def numericRow1160 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1532, 1), (Sum.inr 1533, 1), (Sum.inr 1535, 1), (Sum.inr 1670, 2), (Sum.inr 1688, 2), (Sum.inr 1689, 2), (Sum.inr 1690, 2), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1723, 2), (Sum.inr 1724, 2), (Sum.inr 1748, 1), (Sum.inr 1749, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 2224, 2), (Sum.inr 2287, 1), (Sum.inr 2290, 1)]

def numericRow1161 : Integer.Sparse Master := [(Sum.inr 581, 2), (Sum.inr 587, 1), (Sum.inr 589, 1), (Sum.inr 611, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

def numericRow1162 : Integer.Sparse Master := [(Sum.inr 611, 1), (Sum.inr 930, 2), (Sum.inr 1046, 2), (Sum.inr 4083, -1)]

def numericRow1163 : Integer.Sparse Master := [(Sum.inr 945, 2), (Sum.inr 951, 1), (Sum.inr 953, 1), (Sum.inr 1046, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

def numericRow1164 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 911, 1), (Sum.inr 913, 1), (Sum.inr 930, 1), (Sum.inr 1046, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

def numericRow1165 : Integer.Sparse Master := [(Sum.inl 0, 56), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 1, -90), (Sum.inr 542, -4320), (Sum.inr 545, -2160), (Sum.inr 548, -2160), (Sum.inr 559, -2160), (Sum.inr 681, -4320), (Sum.inr 683, -2160), (Sum.inr 685, -2160), (Sum.inr 690, -2160), (Sum.inr 868, -4320), (Sum.inr 871, -4320), (Sum.inr 874, -4320), (Sum.inr 887, -4320), (Sum.inr 930, -4320), (Sum.inr 934, -2160), (Sum.inr 939, -2160), (Sum.inr 1044, -4320), (Sum.inr 1046, -4320), (Sum.inr 1049, -2160), (Sum.inr 1051, -2160), (Sum.inr 1087, -2160), (Sum.inr 1091, -2160), (Sum.inr 1566, -4320), (Sum.inr 1568, -4320), (Sum.inr 1570, -4320), (Sum.inr 1573, -4320), (Sum.inr 1690, -4320), (Sum.inr 1692, -2160), (Sum.inr 1694, -2160), (Sum.inr 1737, -4320), (Sum.inr 1738, -2160), (Sum.inr 1739, -2160), (Sum.inr 1750, -4320), (Sum.inr 1752, -2160), (Sum.inr 1756, -2160), (Sum.inr 2485, -4320), (Sum.inr 3481, -4320), (Sum.inr 3615, -2160), (Sum.inr 3632, -2160), (Sum.inr 3634, -2160)]

def numericRow1166 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 4), (Sum.inr 787, -288), (Sum.inr 813, -144), (Sum.inr 828, -144), (Sum.inr 847, -288), (Sum.inr 853, -144), (Sum.inr 857, -144), (Sum.inr 982, -288), (Sum.inr 1043, -144), (Sum.inr 1046, -288), (Sum.inr 1091, -144), (Sum.inr 1239, -144), (Sum.inr 1242, -144), (Sum.inr 1617, -288), (Sum.inr 1725, -144), (Sum.inr 1750, -288), (Sum.inr 1756, -144), (Sum.inr 2226, -144), (Sum.inr 3300, -144), (Sum.inr 3310, -144), (Sum.inr 4391, 1152), (Sum.inr 4402, 1152), (Sum.inr 4410, 1152), (Sum.inr 4440, 1152), (Sum.inr 4442, 1152), (Sum.inr 4464, 576), (Sum.inr 4476, 576), (Sum.inr 4478, 576), (Sum.inr 4591, 1152)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1168 : Integer.Sparse Master := [(Sum.inr 847, 2), (Sum.inr 853, 1), (Sum.inr 857, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1480 : Integer.Sparse Master := []

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


