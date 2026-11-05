-- Prove2me | Definitions.Def_OAIQ106E123
-- name    : OAIQ106E123
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:46:29.572604+00:00
-- url     : https://prove2.me/theorems/47ef1317-f717-4a9e-8397-96975ab14a03
-- title:
--   Definitions bundle OAIQ106E123 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1033 declarations of OpenAI's Lean: 1033 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.numericRow667`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow668`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow670`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow671`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow672`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow673`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow674`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow675`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow676`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow677`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow678`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow679`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow680`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow681`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow682`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow683`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow684`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow685`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow686`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow687`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow688`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow689`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow69`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow690`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow691`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow692`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow693`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow694`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow695`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow696`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow697`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow698`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow699`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow7`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow70`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow700`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow701`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow702`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow703`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow704` and 993 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic4`, `MutuallyUnbiased_MixedSources_Arithmetic41`, `MutuallyUnbiased_MixedSources_Arithmetic42`, `MutuallyUnbiased_MixedSources_Arithmetic43`, `MutuallyUnbiased_MixedSources_Arithmetic44`, `MutuallyUnbiased_MixedSources_Arithmetic45`, `MutuallyUnbiased_MixedSources_Arithmetic46`, `MutuallyUnbiased_MixedSources_Arithmetic47`, `MutuallyUnbiased_MixedSources_Arithmetic48`, `MutuallyUnbiased_MixedSources_Arithmetic49`, `MutuallyUnbiased_MixedSources_Arithmetic5`, `MutuallyUnbiased_MixedSources_Arithmetic50`, `MutuallyUnbiased_MixedSources_Arithmetic51`, `MutuallyUnbiased_MixedSources_Arithmetic52`, `MutuallyUnbiased_MixedSources_Arithmetic53`, `MutuallyUnbiased_MixedSources_Arithmetic54`, `MutuallyUnbiased_MixedSources_Arithmetic55`, `MutuallyUnbiased_MixedSources_Arithmetic56`, `MutuallyUnbiased_MixedSources_Arithmetic57`, `MutuallyUnbiased_MixedSources_Arithmetic58`, `MutuallyUnbiased_MixedSources_Arithmetic59`, `MutuallyUnbiased_MixedSources_Arithmetic6`, `MutuallyUnbiased_MixedSources_Arithmetic60`, `MutuallyUnbiased_MixedSources_Arithmetic61`, `MutuallyUnbiased_MixedSources_Arithmetic62`, `MutuallyUnbiased_MixedTargets_OriginalBlock10`, `MutuallyUnbiased_MixedTargets_OriginalBlock11`, `MutuallyUnbiased_MixedTargets_OriginalBlock12`, `MutuallyUnbiased_MixedTargets_OriginalBlock13`, `MutuallyUnbiased_MixedTargets_OriginalBlock14`, `MutuallyUnbiased_MixedTargets_OriginalBlock15`, `MutuallyUnbiased_MixedTargets_OriginalBlock16`, `MutuallyUnbiased_MixedTargets_OriginalBlock17`, `MutuallyUnbiased_MixedTargets_OriginalBlock18`, `MutuallyUnbiased_MixedTargets_OriginalBlock19`, `MutuallyUnbiased_MixedTargets_OriginalBlock2`, `MutuallyUnbiased_MixedTargets_OriginalBlock20`, `MutuallyUnbiased_MixedTargets_OriginalBlock21`, `MutuallyUnbiased_MixedTargets_OriginalBlock22`, `MutuallyUnbiased_MixedTargets_OriginalBlock23`, `MutuallyUnbiased_MixedTargets_OriginalBlock24`, `MutuallyUnbiased_MixedTargets_OriginalBlock25`, `MutuallyUnbiased_MixedTargets_OriginalBlock26`, `MutuallyUnbiased_MixedTargets_OriginalBlock27`, `MutuallyUnbiased_MixedTargets_OriginalBlock28`, `MutuallyUnbiased_MixedTargets_OriginalBlock29`, `MutuallyUnbiased_MixedTargets_OriginalBlock3`, `MutuallyUnbiased_MixedTargets_OriginalBlock30`, `MutuallyUnbiased_MixedTargets_OriginalBlock31`, `MutuallyUnbiased_MixedTargets_OriginalBlock32`, `MutuallyUnbiased_MixedTargets_OriginalBlock33`, `MutuallyUnbiased_MixedTargets_OriginalBlock34`, `MutuallyUnbiased_MixedTargets_OriginalBlock35`, `MutuallyUnbiased_MixedTargets_OriginalBlock36`, `MutuallyUnbiased_MixedTargets_OriginalBlock37`, `MutuallyUnbiased_MixedTargets_OriginalBlock38`, `MutuallyUnbiased_MixedTargets_OriginalBlock39`, `MutuallyUnbiased_MixedTargets_OriginalBlock4`, `MutuallyUnbiased_MixedTargets_OriginalBlock40`, `MutuallyUnbiased_MixedTargets_OriginalBlock41`, `MutuallyUnbiased_MixedTargets_OriginalBlock42`, `MutuallyUnbiased_MixedTargets_OriginalBlock43`, `MutuallyUnbiased_MixedTargets_OriginalBlock44`, `MutuallyUnbiased_MixedTargets_OriginalBlock45`, `MutuallyUnbiased_MixedTargets_OriginalBlock46`, `MutuallyUnbiased_MixedTargets_OriginalBlock47`, `MutuallyUnbiased_MixedTargets_OriginalBlock48`, `MutuallyUnbiased_MixedTargets_OriginalBlock49`, `MutuallyUnbiased_MixedTargets_OriginalBlock5`, `MutuallyUnbiased_MixedTargets_OriginalBlock50`, `MutuallyUnbiased_MixedTargets_OriginalBlock51`, `MutuallyUnbiased_MixedTargets_OriginalBlock52`, `MutuallyUnbiased_MixedTargets_OriginalBlock53`, `MutuallyUnbiased_MixedTargets_OriginalBlock54`, `MutuallyUnbiased_MixedTargets_OriginalBlock55`, `MutuallyUnbiased_MixedTargets_OriginalBlock56`, `MutuallyUnbiased_MixedTargets_OriginalBlock57`, `MutuallyUnbiased_MixedTargets_OriginalBlock58`, `MutuallyUnbiased_MixedTargets_OriginalBlock59`, `MutuallyUnbiased_MixedTargets_OriginalBlock6`, `MutuallyUnbiased_MixedTargets_OriginalBlock60`, `MutuallyUnbiased_MixedTargets_OriginalBlock61`, `MutuallyUnbiased_MixedTargets_OriginalBlock62`, `MutuallyUnbiased_MixedTargets_OriginalBlock63`, `MutuallyUnbiased_MixedTargets_OriginalBlock64`, `MutuallyUnbiased_MixedTargets_OriginalBlock65`, `MutuallyUnbiased_MixedTargets_OriginalBlock66`, `MutuallyUnbiased_MixedTargets_OriginalBlock67`, `MutuallyUnbiased_MixedTargets_OriginalBlock68`, `MutuallyUnbiased_MixedTargets_OriginalBlock69`, `MutuallyUnbiased_MixedTargets_OriginalBlock7`, `MutuallyUnbiased_MixedTargets_OriginalBlock70`, `MutuallyUnbiased_MixedTargets_OriginalBlock71`, `MutuallyUnbiased_MixedTargets_OriginalBlock72`, `MutuallyUnbiased_MixedTargets_OriginalBlock73`, `MutuallyUnbiased_MixedTargets_OriginalBlock74`, `MutuallyUnbiased_MixedTargets_OriginalBlock75`, `MutuallyUnbiased_MixedTargets_OriginalBlock76`, `MutuallyUnbiased_MixedTargets_OriginalBlock77`, `MutuallyUnbiased_MixedTargets_OriginalBlock78`, `MutuallyUnbiased_MixedTargets_OriginalBlock79`, `MutuallyUnbiased_MixedTargets_OriginalBlock8`, `MutuallyUnbiased_MixedTargets_OriginalBlock80`, `MutuallyUnbiased_MixedTargets_OriginalBlock81`, `MutuallyUnbiased_MixedTargets_OriginalBlock82`, `MutuallyUnbiased_MixedTargets_OriginalBlock83`, `MutuallyUnbiased_MixedTargets_OriginalBlock84`, `MutuallyUnbiased_MixedTargets_OriginalBlock85`, `MutuallyUnbiased_MixedTargets_OriginalBlock86`, `MutuallyUnbiased_MixedTargets_OriginalBlock87`, `MutuallyUnbiased_MixedTargets_OriginalBlock88`, `MutuallyUnbiased_MixedTargets_OriginalBlock89`, `MutuallyUnbiased_MixedTargets_OriginalBlock9`, `MutuallyUnbiased_MixedTargets_OriginalBlock90`, `MutuallyUnbiased_MixedTargets_OriginalMerge0`, `MutuallyUnbiased_MixedTargets_OriginalMerge1`, `MutuallyUnbiased_MixedTargets_OriginalMerge2`, `MutuallyUnbiased_MixedTargets_OriginalMerge3`, `MutuallyUnbiased_MixedTargets_OriginalMerge4`, `MutuallyUnbiased_MixedTargets_OriginalMerge5`, `MutuallyUnbiased_MixedTargets_ReductionMergeData0`, `MutuallyUnbiased_MixedTargets_ReductionMergeData3`, `MutuallyUnbiased_MixedTargets_ReductionMergeData31`, `MutuallyUnbiased_MixedTargets_ReductionMergeData32`, `MutuallyUnbiased_MixedTargets_ReductionMergeData33`, `MutuallyUnbiased_MixedTargets_ReductionMergeData34`, `MutuallyUnbiased_MixedTargets_ReductionMergeData35`, `MutuallyUnbiased_MixedTargets_ReductionMergeData36`, `MutuallyUnbiased_MixedTargets_ReductionMergeData37`, `MutuallyUnbiased_MixedTargets_ReductionMergeData38`, `MutuallyUnbiased_MixedTargets_ReductionMergeData39`, `MutuallyUnbiased_MixedTargets_ReductionMergeData4`, `MutuallyUnbiased_MixedTargets_ReductionMergeData40`, `MutuallyUnbiased_MixedTargets_ReductionMergeData41`, `MutuallyUnbiased_MixedTargets_ReductionMergeData42`, `MutuallyUnbiased_MixedTargets_ReductionMergeData43`, `MutuallyUnbiased_MixedTargets_ReductionMergeData44`, `MutuallyUnbiased_MixedTargets_ReductionMergeData59`.
--
--   **Imports.** It imports the bundle `OAIQ106E122` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E132`; the statements `OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E122

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow7 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 1, 20), (Sum.inr 3885, -180), (Sum.inr 3886, -45), (Sum.inr 3902, -180), (Sum.inr 3907, -90)]

def numericRow8 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -15), (Sum.inl 3, 160), (Sum.inl 12, 160), (Sum.inl 25, -120), (Sum.inl 1, 120)]

def numericRow9 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3627, -36), (Sum.inr 3632, -36), (Sum.inr 3633, -12), (Sum.inr 3634, -12), (Sum.inr 3903, -72), (Sum.inr 3913, -36)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow69 : Integer.Sparse Master := [(Sum.inr 2065, 1), (Sum.inr 3389, 2), (Sum.inr 3396, 1), (Sum.inr 3545, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def numericRow70 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 2294, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def numericRow71 : Integer.Sparse Master := [(Sum.inr 2294, 2), (Sum.inr 3549, 3), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

def numericRow72 : Integer.Sparse Master := [(Sum.inr 3160, 1), (Sum.inr 3393, 2), (Sum.inr 3396, 2), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def numericRow73 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 3393, 1), (Sum.inr 3495, 1), (Sum.inr 3543, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def numericRow74 : Integer.Sparse Master := [(Sum.inr 3154, 1), (Sum.inr 3389, 2), (Sum.inr 3495, 1), (Sum.inr 3549, 2), (Sum.inr 4085, -1)]

def numericRow75 : Integer.Sparse Master := [(Sum.inr 2063, 2), (Sum.inr 3154, 2), (Sum.inr 3160, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

def numericRow76 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -190), (Sum.inr 1613, 4320), (Sum.inr 1615, 4320), (Sum.inr 1619, 8640), (Sum.inr 1723, 4320), (Sum.inr 3279, 4320), (Sum.inr 3283, 4320), (Sum.inr 3291, 8640), (Sum.inr 3350, 4320), (Sum.inr 3355, 8640), (Sum.inr 3434, 8640), (Sum.inr 3466, 4320), (Sum.inr 3481, 8640), (Sum.inr 3519, 8640), (Sum.inr 3523, 8640), (Sum.inr 3539, 4320), (Sum.inr 3540, 8640), (Sum.inr 3544, 8640), (Sum.inr 3580, 4320), (Sum.inr 3625, 4320)]

def numericRow77 : Integer.Sparse Master := [(Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 2), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

def numericRow78 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1209, 1), (Sum.inr 1217, 2), (Sum.inr 1249, 1), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

def numericRow79 : Integer.Sparse Master := [(Sum.inr 1249, 1), (Sum.inr 2562, 1), (Sum.inr 2624, 2), (Sum.inr 2712, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow667 : Integer.Sparse Master := [(Sum.inl 0, -232), (Sum.inl 5, -40), (Sum.inl 6, 10), (Sum.inl 2, -90), (Sum.inl 51, 480), (Sum.inl 3, 160), (Sum.inl 13, 160), (Sum.inl 52, -160), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 100), (Sum.inl 31, 480), (Sum.inr 1052, 8640), (Sum.inr 1053, 8640), (Sum.inr 1054, 8640), (Sum.inr 1058, 8640), (Sum.inr 1070, 8640), (Sum.inr 2490, 8640), (Sum.inr 2491, 8640), (Sum.inr 2494, 8640), (Sum.inr 2500, 8640), (Sum.inr 2631, 8640), (Sum.inr 2632, 8640), (Sum.inr 2633, 8640), (Sum.inr 2676, 8640), (Sum.inr 2677, 8640), (Sum.inr 2678, 8640), (Sum.inr 2681, 8640), (Sum.inr 2728, 8640), (Sum.inr 2729, 8640), (Sum.inr 2732, 8640), (Sum.inr 2735, 8640), (Sum.inr 2773, 8640), (Sum.inr 2774, 8640), (Sum.inr 2781, 8640), (Sum.inr 3850, 8640), (Sum.inr 3871, 8640), (Sum.inr 3876, 8640)]

def numericRow668 : Integer.Sparse Master := [(Sum.inl 0, -80), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -80), (Sum.inl 25, 240), (Sum.inl 26, -160), (Sum.inl 4, -80), (Sum.inl 1, 175), (Sum.inr 1638, 4320), (Sum.inr 1639, 4320), (Sum.inr 1640, 4320), (Sum.inr 1649, 4320), (Sum.inr 1715, 4320), (Sum.inr 2921, 4320), (Sum.inr 2930, 4320), (Sum.inr 2952, 4320), (Sum.inr 3098, 4320), (Sum.inr 3378, 4320), (Sum.inr 3379, 4320), (Sum.inr 3395, 4320), (Sum.inr 3441, 4320), (Sum.inr 3447, 4320), (Sum.inr 3464, 4320), (Sum.inr 3505, 4320), (Sum.inr 3506, 4320), (Sum.inr 3541, 4320), (Sum.inr 3569, 4320), (Sum.inr 3570, 4320), (Sum.inr 3573, 4320), (Sum.inr 3578, 4320), (Sum.inr 3584, 4320), (Sum.inr 3624, 4320), (Sum.inr 3626, 4320), (Sum.inr 3958, 4320), (Sum.inr 3972, 4320)]

def numericRow670 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 1367, 1), (Sum.inr 1368, 1), (Sum.inr 1371, 1), (Sum.inr 1433, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

def numericRow671 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 2878, 1), (Sum.inr 3036, 1), (Sum.inr 3043, 1), (Sum.inr 3051, 2), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow672 : Integer.Sparse Master := [(Sum.inr 2571, 1), (Sum.inr 2974, 1), (Sum.inr 2975, 1), (Sum.inr 2977, 1), (Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

def numericRow673 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 2881, 1), (Sum.inr 2882, 1), (Sum.inr 2885, 1), (Sum.inr 3051, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

def numericRow674 : Integer.Sparse Master := [(Sum.inr 2575, 1), (Sum.inr 3043, 1), (Sum.inr 3044, 1), (Sum.inr 3045, 1), (Sum.inr 3051, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

def numericRow675 : Integer.Sparse Master := [(Sum.inl 0, -242), (Sum.inl 5, -40), (Sum.inl 2, -220), (Sum.inl 35, -160), (Sum.inl 3, -1440), (Sum.inl 13, -320), (Sum.inl 55, 480), (Sum.inl 12, -480), (Sum.inl 26, -480), (Sum.inl 4, -480), (Sum.inl 27, 120), (Sum.inl 1, -170), (Sum.inr 2118, 8640), (Sum.inr 2119, 8640), (Sum.inr 2123, 8640), (Sum.inr 2132, 8640), (Sum.inr 2220, 8640), (Sum.inr 2250, 8640), (Sum.inr 2274, 8640), (Sum.inr 2275, 8640), (Sum.inr 2277, 8640), (Sum.inr 2565, 8640), (Sum.inr 2575, 8640), (Sum.inr 2585, 8640), (Sum.inr 2727, 8640), (Sum.inr 2728, 8640), (Sum.inr 2730, 8640), (Sum.inr 2748, 8640), (Sum.inr 2750, 8640), (Sum.inr 2756, 8640), (Sum.inr 2757, 8640), (Sum.inr 2763, 8640), (Sum.inr 2764, 8640), (Sum.inr 2772, 8640), (Sum.inr 2773, 17280), (Sum.inr 3091, 8640), (Sum.inr 3115, 8640)]

def numericRow676 : Integer.Sparse Master := [(Sum.inr 2930, 1), (Sum.inr 3376, 1), (Sum.inr 3380, 1), (Sum.inr 3394, 1), (Sum.inr 3534, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow677 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2926, 1), (Sum.inr 3551, 1), (Sum.inr 3567, 1), (Sum.inr 3571, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow678 : Integer.Sparse Master := [(Sum.inr 2092, 1), (Sum.inr 2929, 1), (Sum.inr 3149, 1), (Sum.inr 3152, 1), (Sum.inr 3158, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow679 : Integer.Sparse Master := [(Sum.inr 2926, 1), (Sum.inr 2929, 1), (Sum.inr 2930, 1), (Sum.inr 2956, 1), (Sum.inr 3079, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow680 : Integer.Sparse Master := [(Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 3505, 1), (Sum.inr 3573, 2), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

def numericRow681 : Integer.Sparse Master := [(Sum.inr 3152, 1), (Sum.inr 3380, 1), (Sum.inr 3551, 1), (Sum.inr 3552, 1), (Sum.inr 3573, 2), (Sum.inr 4083, -1)]

def numericRow682 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 2880, -720), (Sum.inr 2884, -2160), (Sum.inr 3617, -720), (Sum.inr 3621, -2160), (Sum.inr 3909, -720), (Sum.inr 3910, -2160), (Sum.inr 4025, -720), (Sum.inr 4473, 2880), (Sum.inr 4474, 8640), (Sum.inr 4494, 2880), (Sum.inr 5085, 8640), (Sum.inr 5097, 2880), (Sum.inr 5265, 8640), (Sum.inr 5266, 17280), (Sum.inr 5270, 8640)]

def numericRow683 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 50), (Sum.inr 1699, 720), (Sum.inr 1700, 720), (Sum.inr 1709, 2160), (Sum.inr 3058, 720), (Sum.inr 3075, 2160), (Sum.inr 3461, 2160), (Sum.inr 3526, 2160), (Sum.inr 3535, 4320), (Sum.inr 3617, 720), (Sum.inr 3621, 2160), (Sum.inr 4025, 720)]

def numericRow684 : Integer.Sparse Master := [(Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 3), (Sum.inr 4091, -1)]

def numericRow685 : Integer.Sparse Master := [(Sum.inr 2746, 1), (Sum.inr 2976, 3), (Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 4091, -1)]

def numericRow686 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2245, -4320), (Sum.inr 2277, -4320), (Sum.inr 2671, -1440), (Sum.inr 2684, -4320), (Sum.inr 3390, -1440), (Sum.inr 3394, -4320), (Sum.inr 3622, -4320), (Sum.inr 4878, 5760), (Sum.inr 4879, 17280), (Sum.inr 4885, 5760), (Sum.inr 4886, 5760), (Sum.inr 5265, 17280), (Sum.inr 5286, 17280), (Sum.inr 5299, 34560)]

def numericRow687 : Integer.Sparse Master := [(Sum.inl 0, -73), (Sum.inl 2, -60), (Sum.inl 3, -240), (Sum.inl 13, -240), (Sum.inl 12, -80), (Sum.inl 1, 45), (Sum.inr 2234, 1440), (Sum.inr 2235, 1440), (Sum.inr 2246, 4320), (Sum.inr 2671, 1440), (Sum.inr 2684, 4320), (Sum.inr 3023, 4320), (Sum.inr 3037, 4320), (Sum.inr 3051, 8640), (Sum.inr 3221, 1440)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow688 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, 50), (Sum.inl 3, 400), (Sum.inl 13, 80), (Sum.inl 12, 280), (Sum.inl 4, 240), (Sum.inl 1, -175), (Sum.inr 2457, 2160), (Sum.inr 2460, 4320), (Sum.inr 2507, 2160), (Sum.inr 2738, 2160), (Sum.inr 3278, 2160), (Sum.inr 3282, 2160), (Sum.inr 3289, 4320), (Sum.inr 3532, 4320), (Sum.inr 3539, 2160), (Sum.inr 3568, 4320), (Sum.inr 3569, 4320), (Sum.inr 3571, 4320), (Sum.inr 3574, 4320), (Sum.inr 3576, 2160), (Sum.inr 3580, 2160), (Sum.inr 3581, 4320), (Sum.inr 3880, 4320)]

def numericRow689 : Integer.Sparse Master := [(Sum.inr 2750, 1), (Sum.inr 3880, 2), (Sum.inr 3901, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

def numericRow690 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1248, 1), (Sum.inr 1250, 1), (Sum.inr 1260, 2), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

def numericRow691 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def numericRow692 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2623, 1), (Sum.inr 2625, 1), (Sum.inr 2631, 1), (Sum.inr 2750, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

def numericRow693 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, -50), (Sum.inr 2924, -8640), (Sum.inr 3077, -4320), (Sum.inr 3605, -8640), (Sum.inr 3625, -4320), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 4435, 17280), (Sum.inr 4436, 17280), (Sum.inr 4439, 17280), (Sum.inr 4449, 34560), (Sum.inr 5144, 34560), (Sum.inr 5145, 34560), (Sum.inr 5160, 34560), (Sum.inr 5219, 17280), (Sum.inr 5220, 17280), (Sum.inr 5226, 34560), (Sum.inr 5249, 17280), (Sum.inr 5251, 17280), (Sum.inr 5255, 34560), (Sum.inr 5282, 17280), (Sum.inr 5289, 34560)]

def numericRow694 : Integer.Sparse Master := [(Sum.inl 0, -115), (Sum.inl 5, -160), (Sum.inl 6, 20), (Sum.inl 2, 260), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 160), (Sum.inl 51, -480), (Sum.inl 3, 1040), (Sum.inl 13, 240), (Sum.inl 52, 160), (Sum.inl 12, 240), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, -525), (Sum.inl 31, -480), (Sum.inr 1017, 4320), (Sum.inr 1018, 4320), (Sum.inr 1021, 4320), (Sum.inr 1032, 8640), (Sum.inr 2566, 8640), (Sum.inr 2567, 8640), (Sum.inr 2587, 8640), (Sum.inr 2661, 4320), (Sum.inr 2662, 4320), (Sum.inr 2669, 8640), (Sum.inr 2708, 4320), (Sum.inr 2710, 4320), (Sum.inr 2718, 8640), (Sum.inr 2751, 4320), (Sum.inr 2763, 8640), (Sum.inr 3849, 4320)]

def numericRow695 : Integer.Sparse Master := [(Sum.inl 0, -48), (Sum.inl 2, 50), (Sum.inl 3, 640), (Sum.inl 12, 320), (Sum.inl 25, -240), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, -230), (Sum.inr 1635, 4320), (Sum.inr 1636, 8640), (Sum.inr 1642, 4320), (Sum.inr 1713, 4320), (Sum.inr 3375, 4320), (Sum.inr 3376, 8640), (Sum.inr 3388, 4320), (Sum.inr 3502, 4320), (Sum.inr 3503, 8640), (Sum.inr 3539, 4320), (Sum.inr 3557, 8640), (Sum.inr 3558, 8640), (Sum.inr 3562, 8640), (Sum.inr 3572, 8640), (Sum.inr 3580, 4320), (Sum.inr 3605, 8640), (Sum.inr 3625, 4320), (Sum.inr 3974, 8640)]

def numericRow696 : Integer.Sparse Master := [(Sum.inr 3074, 1), (Sum.inr 3875, 1), (Sum.inr 3974, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def numericRow697 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1384, 1), (Sum.inr 1387, 1), (Sum.inr 1403, 2), (Sum.inr 3074, 1), (Sum.inr 4091, -1)]

def numericRow698 : Integer.Sparse Master := [(Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

def numericRow699 : Integer.Sparse Master := [(Sum.inr 3068, 1), (Sum.inr 3069, 1), (Sum.inr 3074, 1), (Sum.inr 3091, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

def numericRow700 : Integer.Sparse Master := [(Sum.inl 0, -197), (Sum.inl 5, 20), (Sum.inl 2, -230), (Sum.inl 35, 80), (Sum.inl 3, 80), (Sum.inl 55, -240), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 27, -60), (Sum.inl 1, -145), (Sum.inr 2240, 4320), (Sum.inr 2241, 4320), (Sum.inr 2243, 4320), (Sum.inr 2250, 8640), (Sum.inr 2565, 8640), (Sum.inr 2573, 4320), (Sum.inr 2583, 4320), (Sum.inr 2747, 4320), (Sum.inr 2749, 4320), (Sum.inr 2750, 8640), (Sum.inr 2756, 8640), (Sum.inr 2757, 8640), (Sum.inr 2763, 8640), (Sum.inr 2764, 8640), (Sum.inr 2773, 8640)]

def numericRow701 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 3496, 1), (Sum.inr 3534, 2), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

def numericRow702 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2243, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

def numericRow703 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 2926, 2), (Sum.inr 2950, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow704 : Integer.Sparse Master := [(Sum.inr 2105, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 2), (Sum.inr 3581, 2), (Sum.inr 4083, -1)]

def numericRow705 : Integer.Sparse Master := [(Sum.inr 3550, 1), (Sum.inr 3551, 2), (Sum.inr 3571, 2), (Sum.inr 4083, -1)]

def numericRow706 : Integer.Sparse Master := [(Sum.inl 0, 117), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -170), (Sum.inr 1200, -2160), (Sum.inr 1235, -1440), (Sum.inr 2853, -4320), (Sum.inr 2880, -1440), (Sum.inr 3077, -4320), (Sum.inr 3281, -2160), (Sum.inr 3292, -1440), (Sum.inr 3617, -1440), (Sum.inr 3620, -4320), (Sum.inr 3622, -4320), (Sum.inr 3625, -4320), (Sum.inr 3909, -1440), (Sum.inr 4025, -1440)]

def numericRow707 : Integer.Sparse Master := [(Sum.inl 0, -82), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 1, 95), (Sum.inr 1200, 2160), (Sum.inr 1235, 1440), (Sum.inr 2853, 4320), (Sum.inr 2880, 1440), (Sum.inr 3077, 4320), (Sum.inr 4025, 1440)]

def numericRow708 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2243, -4320), (Sum.inr 2703, -2160), (Sum.inr 3053, -1440), (Sum.inr 3496, -2160), (Sum.inr 3619, -1440), (Sum.inr 3622, -4320), (Sum.inr 4885, 5760), (Sum.inr 5281, 17280), (Sum.inr 5286, 17280)]

def numericRow709 : Integer.Sparse Master := [(Sum.inl 0, -60), (Sum.inl 2, -95), (Sum.inl 3, 80), (Sum.inl 13, 160), (Sum.inl 12, 40), (Sum.inl 1, -95), (Sum.inr 2703, 2160), (Sum.inr 3023, 4320), (Sum.inr 3053, 1440), (Sum.inr 3074, 4320), (Sum.inr 3221, 1440)]

def numericRow710 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 1293, -1080), (Sum.inr 2589, -1080), (Sum.inr 2721, -1080), (Sum.inr 2723, -2160), (Sum.inr 2764, -2160), (Sum.inr 3304, -1080), (Sum.inr 3532, -1080), (Sum.inr 3544, -2160), (Sum.inr 3563, -1080), (Sum.inr 3581, -2160), (Sum.inr 3849, -1080), (Sum.inr 3875, -1080), (Sum.inr 3885, -2160), (Sum.inr 3910, -2160), (Sum.inr 4599, 4320), (Sum.inr 4600, 4320), (Sum.inr 4603, 8640), (Sum.inr 5145, 8640), (Sum.inr 5150, 4320), (Sum.inr 5197, 4320), (Sum.inr 5199, 8640), (Sum.inr 5205, 4320), (Sum.inr 5270, 8640), (Sum.inr 5281, 8640), (Sum.inr 5282, 8640)]

def numericRow711 : Integer.Sparse Master := [(Sum.inl 0, -75), (Sum.inl 2, 85), (Sum.inl 3, 240), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -180), (Sum.inr 1233, 1440), (Sum.inr 1234, 1440), (Sum.inr 1237, 2880), (Sum.inr 2878, 1440), (Sum.inr 2879, 1440), (Sum.inr 2882, 2880), (Sum.inr 2923, 1440), (Sum.inr 2925, 2880), (Sum.inr 3074, 2880), (Sum.inr 3075, 2880), (Sum.inr 3078, 2880)]

def numericRow712 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 50), (Sum.inr 2700, 1080), (Sum.inr 2702, 1080), (Sum.inr 2706, 1080), (Sum.inr 2738, 2160), (Sum.inr 3289, 1080), (Sum.inr 3294, 2160), (Sum.inr 3304, 1080), (Sum.inr 3532, 1080), (Sum.inr 3544, 2160), (Sum.inr 3562, 2160), (Sum.inr 3563, 1080), (Sum.inr 3569, 1080), (Sum.inr 3571, 2160), (Sum.inr 3578, 2160), (Sum.inr 3580, 2160), (Sum.inr 3581, 2160), (Sum.inr 3875, 1080), (Sum.inr 3885, 1080)]

def numericRow713 : Integer.Sparse Master := [(Sum.inr 2764, 1), (Sum.inr 3849, 1), (Sum.inr 3885, 1), (Sum.inr 3910, 2), (Sum.inr 4091, -1)]

def numericRow714 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 1262, 2), (Sum.inr 1270, 1), (Sum.inr 1293, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def numericRow715 : Integer.Sparse Master := [(Sum.inr 1293, 1), (Sum.inr 2589, 1), (Sum.inr 2764, 3), (Sum.inr 4091, -1)]

def numericRow716 : Integer.Sparse Master := [(Sum.inr 2631, 1), (Sum.inr 2633, 2), (Sum.inr 2641, 1), (Sum.inr 2764, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def numericRow717 : Integer.Sparse Master := [(Sum.inl 0, 380), (Sum.inl 6, -5), (Sum.inl 2, -65), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 4, -320), (Sum.inl 1, -500), (Sum.inr 1034, -4320), (Sum.inr 1035, -8640), (Sum.inr 1044, -4320), (Sum.inr 1073, -4320), (Sum.inr 1644, -4320), (Sum.inr 1645, -8640), (Sum.inr 1648, -4320), (Sum.inr 1737, -4320), (Sum.inr 2477, -8640), (Sum.inr 2483, -4320), (Sum.inr 2503, -4320), (Sum.inr 2589, -4320), (Sum.inr 2590, -8640), (Sum.inr 2671, -4320), (Sum.inr 2672, -8640), (Sum.inr 2684, -4320), (Sum.inr 2764, -8640), (Sum.inr 2765, -8640), (Sum.inr 2782, -8640), (Sum.inr 3390, -4320), (Sum.inr 3391, -8640), (Sum.inr 3394, -4320), (Sum.inr 3444, -8640), (Sum.inr 3446, -4320), (Sum.inr 3477, -4320), (Sum.inr 3563, -4320), (Sum.inr 3564, -8640), (Sum.inr 3581, -8640), (Sum.inr 3582, -8640), (Sum.inr 3583, -8640), (Sum.inr 3613, -4320), (Sum.inr 3632, -8640), (Sum.inr 3910, -4320), (Sum.inr 4010, -4320)]

def numericRow718 : Integer.Sparse Master := [(Sum.inl 0, -254), (Sum.inl 6, 5), (Sum.inl 2, 55), (Sum.inl 7, -80), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, 340), (Sum.inr 1034, 4320), (Sum.inr 1035, 8640), (Sum.inr 1044, 4320), (Sum.inr 1073, 4320), (Sum.inr 2477, 8640), (Sum.inr 2483, 4320), (Sum.inr 2503, 4320), (Sum.inr 2589, 4320), (Sum.inr 2590, 8640), (Sum.inr 2671, 4320), (Sum.inr 2672, 8640), (Sum.inr 2684, 4320), (Sum.inr 2764, 8640), (Sum.inr 2765, 8640), (Sum.inr 2782, 8640), (Sum.inr 3910, 4320)]

def numericRow719 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 10), (Sum.inl 1, 15), (Sum.inr 2105, -360), (Sum.inr 2107, -720), (Sum.inr 2110, -360), (Sum.inr 2241, -360), (Sum.inr 2260, -720), (Sum.inr 2275, -360), (Sum.inr 2721, -360), (Sum.inr 2739, -720), (Sum.inr 2764, -360), (Sum.inr 2782, -720), (Sum.inr 3532, -360), (Sum.inr 3534, -720), (Sum.inr 3581, -360), (Sum.inr 3583, -720), (Sum.inr 3622, -720), (Sum.inr 3623, -360), (Sum.inr 5255, 2880), (Sum.inr 5263, 1440), (Sum.inr 5270, 1440), (Sum.inr 5278, 1440), (Sum.inr 5279, 1440), (Sum.inr 5281, 2880), (Sum.inr 5288, 2880), (Sum.inr 5289, 2880), (Sum.inr 5299, 2880)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow720 : Integer.Sparse Master := [(Sum.inl 0, -200), (Sum.inl 2, -200), (Sum.inl 3, -320), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, -160), (Sum.inr 2241, 4320), (Sum.inr 2260, 8640), (Sum.inr 2275, 4320), (Sum.inr 2718, 8640), (Sum.inr 2721, 4320), (Sum.inr 2728, 4320), (Sum.inr 2747, 4320), (Sum.inr 2748, 4320), (Sum.inr 2750, 8640), (Sum.inr 2754, 4320), (Sum.inr 2760, 8640), (Sum.inr 2763, 8640), (Sum.inr 2764, 4320), (Sum.inr 2773, 8640), (Sum.inr 2782, 8640)]

def numericRow721 : Integer.Sparse Master := [(Sum.inl 0, 29), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, 90), (Sum.inr 1235, -2160), (Sum.inr 2480, -4320), (Sum.inr 2483, -2160), (Sum.inr 2721, -4320), (Sum.inr 2723, -4320), (Sum.inr 2764, -2160), (Sum.inr 3292, -2160), (Sum.inr 3467, -4320), (Sum.inr 3477, -2160), (Sum.inr 3532, -4320), (Sum.inr 3544, -4320), (Sum.inr 3581, -2160), (Sum.inr 3849, -2160), (Sum.inr 3875, -2160), (Sum.inr 3901, -4320), (Sum.inr 4589, 8640), (Sum.inr 4590, 17280), (Sum.inr 4599, 8640), (Sum.inr 5185, 17280), (Sum.inr 5187, 8640), (Sum.inr 5197, 8640), (Sum.inr 5251, 17280), (Sum.inr 5281, 17280)]

def numericRow722 : Integer.Sparse Master := [(Sum.inl 0, -129), (Sum.inl 5, -320), (Sum.inl 6, 35), (Sum.inl 2, 300), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 400), (Sum.inl 3, 1200), (Sum.inl 52, 160), (Sum.inl 12, 320), (Sum.inl 25, -120), (Sum.inl 26, 240), (Sum.inl 4, 560), (Sum.inl 1, -510), (Sum.inr 1212, 2160), (Sum.inr 1213, 4320), (Sum.inr 1233, 2160), (Sum.inr 2861, 2160), (Sum.inr 2862, 4320), (Sum.inr 2878, 2160), (Sum.inr 3064, 4320), (Sum.inr 3074, 4320)]

def numericRow723 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, -90), (Sum.inr 3288, 2160), (Sum.inr 3289, 2160), (Sum.inr 3290, 4320), (Sum.inr 3292, 2160), (Sum.inr 3467, 4320), (Sum.inr 3477, 2160), (Sum.inr 3529, 4320), (Sum.inr 3532, 4320), (Sum.inr 3537, 2160), (Sum.inr 3539, 4320), (Sum.inr 3544, 4320), (Sum.inr 3569, 2160), (Sum.inr 3571, 4320), (Sum.inr 3581, 2160), (Sum.inr 3849, 2160)]

def numericRow724 : Integer.Sparse Master := [(Sum.inr 1235, 1), (Sum.inr 2721, 3), (Sum.inr 4091, -1)]

def numericRow725 : Integer.Sparse Master := [(Sum.inr 2615, 2), (Sum.inr 2617, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

def numericRow726 : Integer.Sparse Master := [(Sum.inl 0, 458), (Sum.inl 6, 15), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 4, 160), (Sum.inl 1, -180), (Sum.inr 977, -8640), (Sum.inr 980, -4320), (Sum.inr 998, -4320), (Sum.inr 1039, -4320), (Sum.inr 1597, -8640), (Sum.inr 1600, -4320), (Sum.inr 1616, -4320), (Sum.inr 1706, -4320), (Sum.inr 2382, -8640), (Sum.inr 2383, -4320), (Sum.inr 2398, -4320), (Sum.inr 2553, -8640), (Sum.inr 2556, -4320), (Sum.inr 2694, -8640), (Sum.inr 2703, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -8640), (Sum.inr 2723, -8640), (Sum.inr 2739, -8640), (Sum.inr 3340, -8640), (Sum.inr 3341, -4320), (Sum.inr 3352, -4320), (Sum.inr 3493, -8640), (Sum.inr 3496, -4320), (Sum.inr 3514, -8640), (Sum.inr 3521, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -8640), (Sum.inr 3534, -8640), (Sum.inr 3544, -8640), (Sum.inr 3602, -4320), (Sum.inr 3622, -8640), (Sum.inr 3957, -8640), (Sum.inr 4046, -4320)]

def numericRow727 : Integer.Sparse Master := [(Sum.inl 0, -324), (Sum.inl 6, -15), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 3, 80), (Sum.inl 1, 30), (Sum.inr 977, 8640), (Sum.inr 980, 4320), (Sum.inr 998, 4320), (Sum.inr 1039, 4320), (Sum.inr 2382, 8640), (Sum.inr 2383, 4320), (Sum.inr 2398, 4320), (Sum.inr 2553, 8640), (Sum.inr 2556, 4320), (Sum.inr 2694, 8640), (Sum.inr 2703, 4320), (Sum.inr 2721, 4320), (Sum.inr 2722, 8640), (Sum.inr 2723, 8640), (Sum.inr 2739, 8640), (Sum.inr 3957, 4320)]

def numericRow728 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2020, -2880), (Sum.inr 2023, -1440), (Sum.inr 2202, -2880), (Sum.inr 2214, -1440), (Sum.inr 2671, -1440), (Sum.inr 2721, -5760), (Sum.inr 2739, -2880), (Sum.inr 2764, -1440), (Sum.inr 3390, -1440), (Sum.inr 3532, -5760), (Sum.inr 3534, -2880), (Sum.inr 3581, -1440), (Sum.inr 3622, -4320), (Sum.inr 5226, 11520), (Sum.inr 5231, 5760), (Sum.inr 5255, 11520), (Sum.inr 5263, 5760), (Sum.inr 5265, 17280)]

def numericRow729 : Integer.Sparse Master := [(Sum.inl 0, -175), (Sum.inl 2, -135), (Sum.inl 3, 560), (Sum.inl 26, 320), (Sum.inl 4, 320), (Sum.inl 1, -380), (Sum.inr 2202, 8640), (Sum.inr 2214, 4320), (Sum.inr 2669, 8640), (Sum.inr 2671, 4320), (Sum.inr 2676, 4320), (Sum.inr 2718, 8640), (Sum.inr 2721, 8640), (Sum.inr 2728, 4320), (Sum.inr 2730, 8640), (Sum.inr 2739, 8640), (Sum.inr 2764, 4320), (Sum.inr 3037, 4320)]

def numericRow730 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, 25), (Sum.inr 1294, -2160), (Sum.inr 2590, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -2160), (Sum.inr 2765, -2160), (Sum.inr 3305, -2160), (Sum.inr 3534, -4320), (Sum.inr 3548, -2160), (Sum.inr 3564, -4320), (Sum.inr 3582, -2160), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 4616, 17280), (Sum.inr 4617, 8640), (Sum.inr 4620, 8640), (Sum.inr 5160, 17280), (Sum.inr 5164, 17280), (Sum.inr 5173, 17280), (Sum.inr 5276, 8640), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 8640)]

def numericRow731 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -30), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, 100), (Sum.inr 1291, 2880), (Sum.inr 1292, 1440), (Sum.inr 1295, 1440), (Sum.inr 2951, 2880), (Sum.inr 2952, 2880), (Sum.inr 2955, 2880), (Sum.inr 3051, 2880), (Sum.inr 3052, 1440), (Sum.inr 3055, 1440), (Sum.inr 3097, 2880), (Sum.inr 3098, 1440)]

def numericRow732 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -25), (Sum.inr 2735, 4320), (Sum.inr 2737, 2160), (Sum.inr 2744, 2160), (Sum.inr 2781, 2160), (Sum.inr 3303, 4320), (Sum.inr 3305, 2160), (Sum.inr 3306, 2160), (Sum.inr 3534, 4320), (Sum.inr 3548, 2160), (Sum.inr 3558, 4320), (Sum.inr 3564, 4320), (Sum.inr 3565, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3582, 2160), (Sum.inr 3584, 2160), (Sum.inr 3876, 4320)]

def numericRow733 : Integer.Sparse Master := [(Sum.inl 0, 28), (Sum.inl 2, -7), (Sum.inl 3, 16), (Sum.inl 4, 48), (Sum.inl 1, -31), (Sum.inr 1073, -864), (Sum.inr 1074, -432), (Sum.inr 1075, -432), (Sum.inr 1087, -432), (Sum.inr 1648, -864), (Sum.inr 1650, -432), (Sum.inr 1653, -432), (Sum.inr 1739, -432), (Sum.inr 2503, -864), (Sum.inr 2504, -1728), (Sum.inr 2505, -864), (Sum.inr 2515, -864), (Sum.inr 2522, -432), (Sum.inr 2684, -864), (Sum.inr 2685, -432), (Sum.inr 2686, -432), (Sum.inr 2764, -864), (Sum.inr 2765, -432), (Sum.inr 2782, -864), (Sum.inr 2783, -864), (Sum.inr 3394, -864), (Sum.inr 3397, -432), (Sum.inr 3446, -864), (Sum.inr 3448, -864), (Sum.inr 3479, -864), (Sum.inr 3581, -864), (Sum.inr 3582, -432), (Sum.inr 3583, -864), (Sum.inr 3632, -432), (Sum.inr 3633, -432), (Sum.inr 3913, -432), (Sum.inr 3983, -1728)]

def numericRow734 : Integer.Sparse Master := [(Sum.inl 0, -39), (Sum.inl 2, 20), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 35), (Sum.inr 1073, 2160), (Sum.inr 1074, 1080), (Sum.inr 1075, 1080), (Sum.inr 1087, 1080), (Sum.inr 2503, 2160), (Sum.inr 2504, 2160), (Sum.inr 2505, 2160), (Sum.inr 2515, 2160), (Sum.inr 2684, 2160), (Sum.inr 2685, 1080), (Sum.inr 2686, 1080), (Sum.inr 2764, 2160), (Sum.inr 2765, 1080), (Sum.inr 2782, 2160), (Sum.inr 2783, 1080), (Sum.inr 3913, 1080), (Sum.inr 3983, 2160)]

def numericRow735 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 2107, -2160), (Sum.inr 2112, -1080), (Sum.inr 2116, -1080), (Sum.inr 2260, -2160), (Sum.inr 2287, -1080), (Sum.inr 2288, -1080), (Sum.inr 2739, -2160), (Sum.inr 2764, -2160), (Sum.inr 2782, -2160), (Sum.inr 3534, -2160), (Sum.inr 3581, -2160), (Sum.inr 3583, -2160), (Sum.inr 3623, -2160), (Sum.inr 5173, 8640), (Sum.inr 5175, 4320), (Sum.inr 5255, 8640), (Sum.inr 5269, 8640), (Sum.inr 5288, 8640), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640), (Sum.inr 5303, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow736 : Integer.Sparse Master := [(Sum.inl 0, -102), (Sum.inl 2, -50), (Sum.inl 3, 480), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -420), (Sum.inr 2260, 8640), (Sum.inr 2287, 4320), (Sum.inr 2288, 4320), (Sum.inr 2718, 8640), (Sum.inr 2735, 8640), (Sum.inr 2736, 8640), (Sum.inr 2739, 8640), (Sum.inr 2760, 8640), (Sum.inr 2761, 4320), (Sum.inr 2763, 8640), (Sum.inr 2764, 8640), (Sum.inr 2769, 4320), (Sum.inr 2779, 4320), (Sum.inr 2781, 4320), (Sum.inr 2782, 4320), (Sum.inr 3097, 8640)]

def numericRow737 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3307, -48), (Sum.inr 3308, -24), (Sum.inr 3309, -48), (Sum.inr 3602, -48), (Sum.inr 3607, -96), (Sum.inr 3613, -48), (Sum.inr 3622, -96), (Sum.inr 3627, -48), (Sum.inr 3632, -48)]

def numericRow738 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -195), (Sum.inr 1236, -4320), (Sum.inr 2508, -4320), (Sum.inr 2512, -4320), (Sum.inr 2515, -4320), (Sum.inr 2553, -4320), (Sum.inr 2722, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -4320), (Sum.inr 2782, -4320), (Sum.inr 3293, -4320), (Sum.inr 3460, -4320), (Sum.inr 3471, -4320), (Sum.inr 3479, -4320), (Sum.inr 3514, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3548, -4320), (Sum.inr 3583, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 4599, 17280), (Sum.inr 4603, 17280), (Sum.inr 4607, 17280), (Sum.inr 4616, 17280), (Sum.inr 5138, 17280), (Sum.inr 5160, 17280), (Sum.inr 5260, 17280), (Sum.inr 5265, 17280), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5289, 17280), (Sum.inr 5299, 17280)]

def numericRow739 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -80), (Sum.inl 1, 195), (Sum.inr 3289, 4320), (Sum.inr 3293, 4320), (Sum.inr 3294, 4320), (Sum.inr 3296, 4320), (Sum.inr 3303, 4320), (Sum.inr 3460, 4320), (Sum.inr 3471, 4320), (Sum.inr 3479, 4320), (Sum.inr 3514, 4320), (Sum.inr 3517, 4320), (Sum.inr 3526, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3535, 4320), (Sum.inr 3540, 4320), (Sum.inr 3541, 4320), (Sum.inr 3548, 4320), (Sum.inr 3558, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3583, 4320), (Sum.inr 3838, 4320)]

def numericRow740 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 2, 1), (Sum.inl 1, -1), (Sum.inr 998, -72), (Sum.inr 999, -72), (Sum.inr 1000, -72), (Sum.inr 1005, -72), (Sum.inr 1079, -72), (Sum.inr 1600, -72), (Sum.inr 1602, -72), (Sum.inr 1605, -72), (Sum.inr 1623, -72), (Sum.inr 1708, -72), (Sum.inr 2398, -72), (Sum.inr 2399, -72), (Sum.inr 2400, -72), (Sum.inr 2404, -72), (Sum.inr 2458, -144), (Sum.inr 2459, -72), (Sum.inr 2462, -72), (Sum.inr 2467, -72), (Sum.inr 2508, -72), (Sum.inr 2509, -72), (Sum.inr 2703, -72), (Sum.inr 2704, -72), (Sum.inr 2705, -72), (Sum.inr 2721, -72), (Sum.inr 2722, -72), (Sum.inr 2723, -72), (Sum.inr 2739, -144), (Sum.inr 2740, -144), (Sum.inr 2743, -72), (Sum.inr 3341, -72), (Sum.inr 3344, -72), (Sum.inr 3357, -72), (Sum.inr 3429, -72), (Sum.inr 3436, -72), (Sum.inr 3460, -72), (Sum.inr 3496, -72), (Sum.inr 3498, -72), (Sum.inr 3532, -72), (Sum.inr 3533, -72), (Sum.inr 3534, -144), (Sum.inr 3544, -72), (Sum.inr 3548, -72), (Sum.inr 3622, -72), (Sum.inr 3623, -72), (Sum.inr 3958, -72), (Sum.inr 3961, -72), (Sum.inr 3974, -144), (Sum.inr 4010, -72)]

def numericRow741 : Integer.Sparse Master := [(Sum.inl 0, -198), (Sum.inl 2, -65), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 998, 4320), (Sum.inr 999, 4320), (Sum.inr 1000, 4320), (Sum.inr 1005, 4320), (Sum.inr 1079, 4320), (Sum.inr 2398, 4320), (Sum.inr 2399, 4320), (Sum.inr 2400, 4320), (Sum.inr 2404, 4320), (Sum.inr 2458, 4320), (Sum.inr 2459, 4320), (Sum.inr 2462, 4320), (Sum.inr 2508, 4320), (Sum.inr 2703, 4320), (Sum.inr 2704, 4320), (Sum.inr 2705, 4320), (Sum.inr 2721, 4320), (Sum.inr 2722, 4320), (Sum.inr 2723, 4320), (Sum.inr 2739, 8640), (Sum.inr 2740, 4320), (Sum.inr 2743, 4320), (Sum.inr 3961, 4320), (Sum.inr 3974, 4320), (Sum.inr 4010, 4320)]

def numericRow742 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 1, 40), (Sum.inr 2020, -864), (Sum.inr 2025, -864), (Sum.inr 2029, -864), (Sum.inr 2202, -864), (Sum.inr 2224, -864), (Sum.inr 2225, -864), (Sum.inr 2684, -864), (Sum.inr 2703, -864), (Sum.inr 2721, -864), (Sum.inr 2739, -2592), (Sum.inr 2764, -864), (Sum.inr 2782, -864), (Sum.inr 3394, -864), (Sum.inr 3496, -864), (Sum.inr 3532, -864), (Sum.inr 3534, -2592), (Sum.inr 3581, -864), (Sum.inr 3583, -864), (Sum.inr 3622, -864), (Sum.inr 3623, -864), (Sum.inr 5150, 3456), (Sum.inr 5151, 3456), (Sum.inr 5173, 3456), (Sum.inr 5226, 3456), (Sum.inr 5236, 3456), (Sum.inr 5255, 3456), (Sum.inr 5269, 3456), (Sum.inr 5270, 3456), (Sum.inr 5281, 3456), (Sum.inr 5289, 3456), (Sum.inr 5299, 3456)]

def numericRow743 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -90), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, -200), (Sum.inr 2202, 4320), (Sum.inr 2224, 4320), (Sum.inr 2225, 4320), (Sum.inr 2669, 4320), (Sum.inr 2681, 4320), (Sum.inr 2682, 4320), (Sum.inr 2684, 4320), (Sum.inr 2700, 4320), (Sum.inr 2703, 4320), (Sum.inr 2718, 4320), (Sum.inr 2721, 4320), (Sum.inr 2735, 4320), (Sum.inr 2736, 4320), (Sum.inr 2738, 4320), (Sum.inr 2739, 12960), (Sum.inr 2782, 4320), (Sum.inr 3051, 4320), (Sum.inr 3074, 4320), (Sum.inr 3097, 4320)]

def numericRow744 : Integer.Sparse Master := [(Sum.inr 1235, -1), (Sum.inr 1240, -3), (Sum.inr 1293, -1), (Sum.inr 2556, -3), (Sum.inr 2589, -1), (Sum.inr 2721, -3), (Sum.inr 2723, -6), (Sum.inr 2764, -3), (Sum.inr 3292, -1), (Sum.inr 3299, -3), (Sum.inr 3304, -1), (Sum.inr 3521, -3), (Sum.inr 3532, -3), (Sum.inr 3544, -6), (Sum.inr 3563, -1), (Sum.inr 3581, -3), (Sum.inr 4091, 4)]

def numericRow745 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2671, -1440), (Sum.inr 2684, -4320), (Sum.inr 2703, -4320), (Sum.inr 2721, -4320), (Sum.inr 2739, -8640), (Sum.inr 3053, -1440), (Sum.inr 3390, -1440), (Sum.inr 3394, -4320), (Sum.inr 3496, -4320), (Sum.inr 3532, -4320), (Sum.inr 3534, -8640), (Sum.inr 3619, -1440), (Sum.inr 3622, -4320), (Sum.inr 4083, 5760)]

def numericRow746 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 1039, -4320), (Sum.inr 1706, -4320), (Sum.inr 2105, -4320), (Sum.inr 2241, -4320), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2262, -4320), (Sum.inr 2277, -4320), (Sum.inr 3622, -4320), (Sum.inr 4439, 17280), (Sum.inr 4851, 17280), (Sum.inr 4852, 34560), (Sum.inr 4885, 17280), (Sum.inr 5281, 17280)]

def numericRow747 : Integer.Sparse Master := [(Sum.inl 0, -47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 1706, 4320), (Sum.inr 1713, 4320), (Sum.inr 2240, 4320), (Sum.inr 2241, 4320), (Sum.inr 2243, 4320), (Sum.inr 2250, 8640), (Sum.inr 2252, 4320), (Sum.inr 2262, 4320), (Sum.inr 2277, 4320), (Sum.inr 2750, 4320)]

def numericRow748 : Integer.Sparse Master := [(Sum.inl 0, 64), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -120), (Sum.inl 4, -160), (Sum.inl 1, 15), (Sum.inr 782, -2160), (Sum.inr 783, -4320), (Sum.inr 803, -4320), (Sum.inr 2019, -4320), (Sum.inr 2020, -8640), (Sum.inr 2051, -4320), (Sum.inr 2190, -4320), (Sum.inr 2191, -4320), (Sum.inr 2202, -8640), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 3901, -4320)]

def numericRow749 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 1039, -2160), (Sum.inr 1041, -4320), (Sum.inr 1044, -2160), (Sum.inr 1706, -2160), (Sum.inr 1724, -4320), (Sum.inr 1737, -2160), (Sum.inr 2020, -4320), (Sum.inr 2023, -2160), (Sum.inr 2105, -2160), (Sum.inr 2107, -4320), (Sum.inr 2110, -2160), (Sum.inr 2202, -4320), (Sum.inr 2214, -2160), (Sum.inr 2241, -2160), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2260, -4320), (Sum.inr 2262, -4320), (Sum.inr 2275, -2160), (Sum.inr 2277, -4320), (Sum.inr 2721, -2160), (Sum.inr 2764, -2160), (Sum.inr 3532, -2160), (Sum.inr 3581, -2160), (Sum.inr 3622, -4320), (Sum.inr 4083, 8640)]

def numericRow750 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, 1), (Sum.inr 4068, 16), (Sum.inr 4069, 24), (Sum.inr 4079, 16), (Sum.inr 4080, 48), (Sum.inr 4083, 48), (Sum.inr 4084, 48), (Sum.inr 4091, 16)]

def numericRow751 : Integer.Sparse Master := [(Sum.inl 0, -44), (Sum.inl 2, 10), (Sum.inl 3, 560), (Sum.inl 13, 80), (Sum.inl 12, 320), (Sum.inl 4, 240), (Sum.inl 1, -170), (Sum.inr 1902, 4320), (Sum.inr 1904, 4320), (Sum.inr 1910, 4320), (Sum.inr 1923, 4320), (Sum.inr 2253, 4320), (Sum.inr 2970, 4320), (Sum.inr 2974, 4320), (Sum.inr 2984, 4320), (Sum.inr 3016, 4320), (Sum.inr 3463, 4320), (Sum.inr 3464, 4320), (Sum.inr 3473, 4320), (Sum.inr 3528, 4320), (Sum.inr 3648, 4320), (Sum.inr 3658, 4320), (Sum.inr 3761, 4320), (Sum.inr 3762, 4320), (Sum.inr 3780, 4320), (Sum.inr 3783, 4320), (Sum.inr 3788, 4320), (Sum.inr 3800, 4320), (Sum.inr 3801, 4320), (Sum.inr 3802, 4320), (Sum.inr 3803, 4320), (Sum.inr 3813, 4320), (Sum.inr 3814, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow752 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 3691, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 3805, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

def numericRow753 : Integer.Sparse Master := [(Sum.inr 2474, 1), (Sum.inr 2475, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

def numericRow754 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3698, 1), (Sum.inr 3803, 1), (Sum.inr 3812, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def numericRow755 : Integer.Sparse Master := [(Sum.inr 3217, 1), (Sum.inr 3686, 1), (Sum.inr 3691, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

def numericRow756 : Integer.Sparse Master := [(Sum.inr 2475, 2), (Sum.inr 3686, 2), (Sum.inr 3803, 2), (Sum.inr 4092, -1)]

def numericRow757 : Integer.Sparse Master := [(Sum.inl 0, 48), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 3719, -4320), (Sum.inr 3782, -8640), (Sum.inr 3795, -4320), (Sum.inr 3796, -8640), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3814, -8640), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3903, -4320), (Sum.inr 4812, 17280), (Sum.inr 4813, 17280), (Sum.inr 4816, 17280), (Sum.inr 4824, 17280), (Sum.inr 4852, 17280), (Sum.inr 5129, 17280), (Sum.inr 5138, 17280), (Sum.inr 5146, 17280), (Sum.inr 5260, 17280), (Sum.inr 5357, 17280), (Sum.inr 5358, 17280), (Sum.inr 5360, 17280), (Sum.inr 5376, 17280), (Sum.inr 5381, 34560), (Sum.inr 5420, 17280), (Sum.inr 5421, 17280), (Sum.inr 5426, 17280), (Sum.inr 5430, 17280), (Sum.inr 5436, 17280), (Sum.inr 5445, 17280)]

def numericRow758 : Integer.Sparse Master := [(Sum.inl 0, -179), (Sum.inl 6, -5), (Sum.inl 2, -40), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 51, -240), (Sum.inl 3, 1520), (Sum.inl 13, 240), (Sum.inl 52, 80), (Sum.inl 23, -480), (Sum.inl 54, -240), (Sum.inl 24, -240), (Sum.inl 55, -480), (Sum.inl 12, 480), (Sum.inl 25, -480), (Sum.inl 26, 400), (Sum.inl 4, 480), (Sum.inl 27, 60), (Sum.inl 1, -20), (Sum.inr 2071, 4320), (Sum.inr 2072, 4320), (Sum.inr 2078, 4320), (Sum.inr 2089, 4320), (Sum.inr 2196, 4320), (Sum.inr 2916, 4320), (Sum.inr 2922, 4320), (Sum.inr 2933, 4320), (Sum.inr 3086, 4320), (Sum.inr 3715, 4320), (Sum.inr 3718, 4320), (Sum.inr 3722, 4320), (Sum.inr 3723, 4320), (Sum.inr 3752, 4320), (Sum.inr 3762, 4320), (Sum.inr 3796, 4320), (Sum.inr 3814, 4320), (Sum.inr 3841, 4320), (Sum.inr 3870, 4320), (Sum.inr 3873, 4320), (Sum.inr 3877, 4320), (Sum.inr 3880, 4320), (Sum.inr 3972, 4320)]

def numericRow759 : Integer.Sparse Master := [(Sum.inl 0, -204), (Sum.inl 5, 80), (Sum.inl 6, -10), (Sum.inl 2, -70), (Sum.inl 35, 160), (Sum.inl 51, -480), (Sum.inl 3, 640), (Sum.inl 13, 160), (Sum.inl 52, 160), (Sum.inl 55, -480), (Sum.inl 12, 480), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 27, -120), (Sum.inl 1, -160), (Sum.inr 2030, 8640), (Sum.inr 2031, 8640), (Sum.inr 2034, 8640), (Sum.inr 2043, 8640), (Sum.inr 2250, 8640), (Sum.inr 3516, 8640), (Sum.inr 3517, 8640), (Sum.inr 3540, 8640), (Sum.inr 3560, 8640), (Sum.inr 3695, 8640), (Sum.inr 3696, 8640), (Sum.inr 3698, 8640), (Sum.inr 3795, 8640), (Sum.inr 3796, 8640), (Sum.inr 3813, 8640), (Sum.inr 3826, 8640), (Sum.inr 3827, 8640), (Sum.inr 3833, 8640), (Sum.inr 3834, 17280), (Sum.inr 3837, 8640), (Sum.inr 3838, 8640), (Sum.inr 3841, 8640), (Sum.inr 3854, 8640), (Sum.inr 3871, 8640), (Sum.inr 3880, 8640)]

def numericRow760 : Integer.Sparse Master := [(Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3946, 1), (Sum.inr 4022, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

def numericRow761 : Integer.Sparse Master := [(Sum.inr 3168, 1), (Sum.inr 3715, 1), (Sum.inr 3722, 1), (Sum.inr 3725, 1), (Sum.inr 3839, 1), (Sum.inr 4022, 1), (Sum.inr 4092, -1)]

def numericRow762 : Integer.Sparse Master := [(Sum.inr 2568, 1), (Sum.inr 3725, 1), (Sum.inr 3780, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

def numericRow763 : Integer.Sparse Master := [(Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 3782, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

def numericRow764 : Integer.Sparse Master := [(Sum.inr 2557, 1), (Sum.inr 3722, 1), (Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 3843, 1), (Sum.inr 4092, -1)]

def numericRow765 : Integer.Sparse Master := [(Sum.inr 3175, 1), (Sum.inr 3723, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

def numericRow766 : Integer.Sparse Master := [(Sum.inr 2545, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3723, 1), (Sum.inr 3837, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

def numericRow767 : Integer.Sparse Master := [(Sum.inr 3196, 1), (Sum.inr 3780, 1), (Sum.inr 3782, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow768 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 3168, 1), (Sum.inr 3170, 1), (Sum.inr 3175, 1), (Sum.inr 3196, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

def numericRow769 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, 40), (Sum.inl 6, -5), (Sum.inl 2, 160), (Sum.inl 35, 80), (Sum.inl 51, -240), (Sum.inl 3, 1280), (Sum.inl 13, 320), (Sum.inl 52, 80), (Sum.inl 55, -240), (Sum.inl 12, 240), (Sum.inl 26, 240), (Sum.inl 4, 480), (Sum.inl 27, -60), (Sum.inl 1, -470), (Sum.inl 31, -240), (Sum.inr 1991, 4320), (Sum.inr 1994, 4320), (Sum.inr 1998, 4320), (Sum.inr 2033, 4320), (Sum.inr 2195, 4320), (Sum.inr 2533, 4320), (Sum.inr 2535, 4320), (Sum.inr 2566, 4320), (Sum.inr 2661, 4320), (Sum.inr 3536, 4320), (Sum.inr 3537, 4320), (Sum.inr 3539, 4320), (Sum.inr 3574, 4320), (Sum.inr 3680, 4320), (Sum.inr 3697, 4320), (Sum.inr 3743, 4320), (Sum.inr 3761, 4320), (Sum.inr 3810, 4320), (Sum.inr 3812, 4320), (Sum.inr 3825, 4320), (Sum.inr 3840, 8640), (Sum.inr 3848, 4320), (Sum.inr 3849, 4320), (Sum.inr 3871, 4320), (Sum.inr 3880, 4320)]

def numericRow770 : Integer.Sparse Master := [(Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3875, 1), (Sum.inr 3880, 1), (Sum.inr 3901, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

def numericRow771 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2919, 1), (Sum.inr 3195, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def numericRow772 : Integer.Sparse Master := [(Sum.inr 3197, 1), (Sum.inr 3872, 2), (Sum.inr 3878, 1), (Sum.inr 3899, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

def numericRow773 : Integer.Sparse Master := [(Sum.inr 2612, 1), (Sum.inr 2945, 1), (Sum.inr 3783, 1), (Sum.inr 3863, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def numericRow774 : Integer.Sparse Master := [(Sum.inr 3202, 1), (Sum.inr 3783, 1), (Sum.inr 3789, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

def numericRow775 : Integer.Sparse Master := [(Sum.inr 2623, 1), (Sum.inr 2920, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

def numericRow776 : Integer.Sparse Master := [(Sum.inr 3195, 1), (Sum.inr 3863, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 2), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

def numericRow777 : Integer.Sparse Master := [(Sum.inr 2617, 1), (Sum.inr 3069, 1), (Sum.inr 3789, 1), (Sum.inr 3872, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

def numericRow778 : Integer.Sparse Master := [(Sum.inr 2919, 1), (Sum.inr 2920, 1), (Sum.inr 2928, 1), (Sum.inr 2945, 1), (Sum.inr 3069, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def numericRow779 : Integer.Sparse Master := [(Sum.inl 0, -50), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, 25), (Sum.inr 2906, 2160), (Sum.inr 2907, 2160), (Sum.inr 2909, 2160), (Sum.inr 2951, 2160), (Sum.inr 3051, 2160), (Sum.inr 3430, 2160), (Sum.inr 3437, 2160), (Sum.inr 3464, 2160), (Sum.inr 3518, 2160), (Sum.inr 3535, 2160), (Sum.inr 3541, 2160), (Sum.inr 3559, 2160), (Sum.inr 3712, 2160), (Sum.inr 3714, 2160), (Sum.inr 3730, 2160), (Sum.inr 3762, 2160), (Sum.inr 3794, 2160), (Sum.inr 3809, 2160), (Sum.inr 3832, 2160), (Sum.inr 3838, 2160), (Sum.inr 3841, 2160), (Sum.inr 3845, 2160), (Sum.inr 3872, 2160), (Sum.inr 3877, 2160), (Sum.inr 3972, 2160)]

def numericRow780 : Integer.Sparse Master := [(Sum.inl 0, -176), (Sum.inl 5, 20), (Sum.inl 6, -5), (Sum.inl 2, -40), (Sum.inl 51, -240), (Sum.inl 3, 400), (Sum.inl 52, 80), (Sum.inl 12, 80), (Sum.inl 26, 80), (Sum.inl 4, 160), (Sum.inl 1, 145), (Sum.inl 31, -240), (Sum.inr 2454, 4320), (Sum.inr 2455, 4320), (Sum.inr 2463, 4320), (Sum.inr 2494, 4320), (Sum.inr 2732, 4320), (Sum.inr 2905, 4320), (Sum.inr 2909, 4320), (Sum.inr 3039, 4320), (Sum.inr 3558, 4320), (Sum.inr 3559, 4320), (Sum.inr 3561, 4320), (Sum.inr 3573, 4320), (Sum.inr 3679, 4320), (Sum.inr 3698, 4320), (Sum.inr 3714, 4320), (Sum.inr 3724, 4320), (Sum.inr 3838, 4320), (Sum.inr 3839, 4320), (Sum.inr 3841, 4320), (Sum.inr 3866, 4320), (Sum.inr 3871, 4320), (Sum.inr 3876, 4320), (Sum.inr 3877, 4320)]

def numericRow781 : Integer.Sparse Master := [(Sum.inr 2587, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

def numericRow782 : Integer.Sparse Master := [(Sum.inr 2577, 2), (Sum.inr 3729, 1), (Sum.inr 3840, 2), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

def numericRow783 : Integer.Sparse Master := [(Sum.inr 2974, 1), (Sum.inr 3780, 1), (Sum.inr 3781, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow784 : Integer.Sparse Master := [(Sum.inr 2971, 1), (Sum.inr 3717, 1), (Sum.inr 3720, 1), (Sum.inr 3729, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

def numericRow785 : Integer.Sparse Master := [(Sum.inr 2549, 1), (Sum.inr 2578, 1), (Sum.inr 3717, 1), (Sum.inr 3780, 1), (Sum.inr 3840, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

def numericRow786 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 5, 40), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 35, 80), (Sum.inl 51, -240), (Sum.inl 3, 640), (Sum.inl 13, 80), (Sum.inl 52, 80), (Sum.inl 55, -240), (Sum.inl 12, 240), (Sum.inl 26, 160), (Sum.inl 4, 400), (Sum.inl 27, -60), (Sum.inl 1, -40), (Sum.inr 1992, 4320), (Sum.inr 1993, 4320), (Sum.inr 2001, 4320), (Sum.inr 2034, 4320), (Sum.inr 2196, 4320), (Sum.inr 2905, 4320), (Sum.inr 2907, 4320), (Sum.inr 2933, 4320), (Sum.inr 3038, 4320), (Sum.inr 3517, 4320), (Sum.inr 3518, 4320), (Sum.inr 3541, 4320), (Sum.inr 3561, 4320), (Sum.inr 3679, 4320), (Sum.inr 3698, 4320), (Sum.inr 3712, 4320), (Sum.inr 3723, 4320), (Sum.inr 3762, 4320), (Sum.inr 3796, 4320), (Sum.inr 3814, 4320), (Sum.inr 3834, 4320), (Sum.inr 3838, 4320), (Sum.inr 3839, 4320), (Sum.inr 3840, 4320), (Sum.inr 3872, 8640)]

def numericRow787 : Integer.Sparse Master := [(Sum.inl 0, 111), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 200), (Sum.inl 1, 640), (Sum.inr 2110, -2160), (Sum.inr 2112, -1080), (Sum.inr 2115, -1080), (Sum.inr 2275, -2160), (Sum.inr 2276, -1080), (Sum.inr 2279, -2160), (Sum.inr 2287, -1080), (Sum.inr 2954, -2160), (Sum.inr 3606, -2160), (Sum.inr 3614, -1080), (Sum.inr 3633, -1080), (Sum.inr 3732, -2160), (Sum.inr 3789, -2160), (Sum.inr 3810, -2160), (Sum.inr 3811, -2160), (Sum.inr 3814, -4320), (Sum.inr 3885, -4320), (Sum.inr 3886, -2160), (Sum.inr 3891, -2160), (Sum.inr 3893, -1080), (Sum.inr 3902, -2160), (Sum.inr 3907, -3240)]

def numericRow788 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -310), (Sum.inr 2110, 1440), (Sum.inr 2112, 720), (Sum.inr 2115, 720), (Sum.inr 2279, 720), (Sum.inr 2954, 1440), (Sum.inr 3732, 1440), (Sum.inr 3789, 1440), (Sum.inr 3814, 1440), (Sum.inr 3885, 1440), (Sum.inr 3886, 720), (Sum.inr 3907, 720)]

def numericRow789 : Integer.Sparse Master := [(Sum.inl 0, 211), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 4, -160), (Sum.inl 1, -260), (Sum.inr 2058, -4320), (Sum.inr 2062, -2160), (Sum.inr 2065, -2160), (Sum.inr 2216, -4320), (Sum.inr 2218, -2160), (Sum.inr 2230, -2160), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2672, -4320), (Sum.inr 2686, -2160), (Sum.inr 2765, -2160), (Sum.inr 2881, -4320), (Sum.inr 2889, -2160), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3582, -2160), (Sum.inr 3624, -4320), (Sum.inr 3631, -2160), (Sum.inr 3632, -2160), (Sum.inr 3706, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3796, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3906, -4320), (Sum.inr 3910, -4320), (Sum.inr 3913, -4320)]

def numericRow790 : Integer.Sparse Master := [(Sum.inl 0, -75), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 140), (Sum.inr 2058, 2160), (Sum.inr 2062, 1080), (Sum.inr 2065, 1080), (Sum.inr 2266, 1080), (Sum.inr 2881, 2160), (Sum.inr 2889, 1080), (Sum.inr 3391, 2160), (Sum.inr 3397, 1080), (Sum.inr 3582, 1080), (Sum.inr 3706, 2160), (Sum.inr 3782, 2160), (Sum.inr 3809, 2160), (Sum.inr 3857, 2160), (Sum.inr 3913, 1080)]

def numericRow791 : Integer.Sparse Master := [(Sum.inl 0, 69), (Sum.inl 2, 30), (Sum.inl 12, 80), (Sum.inl 4, -80), (Sum.inl 1, -135), (Sum.inr 2743, -2160), (Sum.inr 2782, -2160), (Sum.inr 3054, -2160), (Sum.inr 3548, -2160), (Sum.inr 3583, -2160), (Sum.inr 3626, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3845, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3906, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5268, 8640), (Sum.inr 5276, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 17280), (Sum.inr 5425, 17280), (Sum.inr 5436, 17280)]

def numericRow792 : Integer.Sparse Master := [(Sum.inl 0, -51), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 110), (Sum.inr 2732, 1440), (Sum.inr 2734, 720), (Sum.inr 2744, 720), (Sum.inr 3039, 1440), (Sum.inr 3055, 720), (Sum.inr 3573, 1440), (Sum.inr 3583, 720), (Sum.inr 3584, 720), (Sum.inr 3872, 1440), (Sum.inr 3876, 1440), (Sum.inr 3877, 1440)]

def numericRow793 : Integer.Sparse Master := [(Sum.inl 0, 641), (Sum.inl 2, -100), (Sum.inl 3, -320), (Sum.inl 4, -400), (Sum.inl 1, -685), (Sum.inr 2483, -4320), (Sum.inr 2485, -4320), (Sum.inr 2488, -4320), (Sum.inr 2515, -4320), (Sum.inr 2931, -4320), (Sum.inr 3477, -4320), (Sum.inr 3478, -4320), (Sum.inr 3479, -4320), (Sum.inr 3481, -4320), (Sum.inr 3607, -4320), (Sum.inr 3612, -4320), (Sum.inr 3627, -4320), (Sum.inr 3632, -4320), (Sum.inr 3692, -4320), (Sum.inr 3693, -4320), (Sum.inr 3706, -4320), (Sum.inr 3721, -4320), (Sum.inr 3769, -4320), (Sum.inr 3770, -4320), (Sum.inr 3771, -4320), (Sum.inr 3836, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3892, -4320), (Sum.inr 3896, -4320), (Sum.inr 3900, -4320), (Sum.inr 3901, -4320), (Sum.inr 3903, -8640), (Sum.inr 3906, -4320), (Sum.inr 3913, -4320), (Sum.inr 3964, -4320), (Sum.inr 3983, -8640)]

def numericRow794 : Integer.Sparse Master := [(Sum.inl 0, -132), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, 145), (Sum.inr 2483, 1080), (Sum.inr 2485, 1080), (Sum.inr 2488, 1080), (Sum.inr 2515, 1080), (Sum.inr 2931, 1080), (Sum.inr 3692, 1080), (Sum.inr 3693, 1080), (Sum.inr 3706, 1080), (Sum.inr 3721, 1080), (Sum.inr 3876, 1080), (Sum.inr 3964, 1080), (Sum.inr 3983, 1080)]

def numericRow795 : Integer.Sparse Master := [(Sum.inl 0, 355), (Sum.inl 2, -40), (Sum.inl 3, -80), (Sum.inl 12, 80), (Sum.inl 4, -80), (Sum.inl 1, 125), (Sum.inr 2020, -2160), (Sum.inr 2022, -2160), (Sum.inr 2029, -2160), (Sum.inr 2054, -2160), (Sum.inr 2202, -2160), (Sum.inr 2203, -2160), (Sum.inr 2206, -2160), (Sum.inr 2225, -2160), (Sum.inr 2244, -2160), (Sum.inr 2262, -2160), (Sum.inr 2553, -2160), (Sum.inr 2561, -2160), (Sum.inr 2722, -2160), (Sum.inr 3514, -2160), (Sum.inr 3522, -2160), (Sum.inr 3533, -2160), (Sum.inr 3603, -2160), (Sum.inr 3690, -2160), (Sum.inr 3694, -2160), (Sum.inr 3705, -2160), (Sum.inr 3764, -2160), (Sum.inr 3767, -2160), (Sum.inr 3773, -2160), (Sum.inr 3779, -2160), (Sum.inr 3781, -2160), (Sum.inr 3794, -2160), (Sum.inr 3797, -2160), (Sum.inr 3800, -2160), (Sum.inr 3805, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3845, -4320), (Sum.inr 3896, -2160), (Sum.inr 3898, -2160), (Sum.inr 3901, -2160), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320), (Sum.inr 4046, -2160), (Sum.inr 4047, -2160)]

def numericRow796 : Integer.Sparse Master := [(Sum.inl 0, -36), (Sum.inl 2, 5), (Sum.inl 3, 16), (Sum.inl 4, 16), (Sum.inl 1, -19), (Sum.inr 2020, 288), (Sum.inr 2022, 288), (Sum.inr 2029, 288), (Sum.inr 2054, 288), (Sum.inr 2244, 288), (Sum.inr 2553, 288), (Sum.inr 2561, 288), (Sum.inr 2722, 288), (Sum.inr 3690, 288), (Sum.inr 3694, 288), (Sum.inr 3705, 288), (Sum.inr 3779, 288), (Sum.inr 3781, 288), (Sum.inr 3800, 288), (Sum.inr 3838, 288), (Sum.inr 3845, 288), (Sum.inr 3902, 288)]

def numericRow797 : Integer.Sparse Master := [(Sum.inl 0, 186), (Sum.inl 2, 85), (Sum.inl 3, 80), (Sum.inl 12, 160), (Sum.inl 4, -80), (Sum.inl 1, -305), (Sum.inr 2722, -4320), (Sum.inr 2739, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3800, -4320), (Sum.inr 3801, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -8640), (Sum.inr 3812, -4320), (Sum.inr 3813, -8640), (Sum.inr 3814, -8640), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3850, -8640), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 3913, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -4320), (Sum.inr 5260, 17280), (Sum.inr 5289, 17280), (Sum.inr 5425, 17280), (Sum.inr 5429, 17280), (Sum.inr 5430, 17280), (Sum.inr 5436, 17280), (Sum.inr 5446, 17280)]

def numericRow798 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 2, -35), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, 85), (Sum.inr 3086, 1080), (Sum.inr 3097, 1080), (Sum.inr 3801, 1080), (Sum.inr 3809, 1080), (Sum.inr 3814, 1080), (Sum.inr 3872, 1080), (Sum.inr 3877, 1080), (Sum.inr 3954, 1080), (Sum.inr 3958, 1080), (Sum.inr 3959, 1080), (Sum.inr 3972, 1080)]

def numericRow799 : Integer.Sparse Master := [(Sum.inl 0, 573), (Sum.inl 2, -70), (Sum.inl 3, -320), (Sum.inl 12, -560), (Sum.inl 4, 240), (Sum.inl 1, -115), (Sum.inr 2023, -4320), (Sum.inr 2025, -4320), (Sum.inr 2028, -4320), (Sum.inr 2058, -4320), (Sum.inr 2214, -4320), (Sum.inr 2215, -4320), (Sum.inr 2216, -4320), (Sum.inr 2224, -4320), (Sum.inr 2245, -4320), (Sum.inr 2277, -4320), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 3605, -4320), (Sum.inr 3612, -4320), (Sum.inr 3613, -4320), (Sum.inr 3632, -4320), (Sum.inr 3692, -4320), (Sum.inr 3693, -4320), (Sum.inr 3706, -4320), (Sum.inr 3719, -4320), (Sum.inr 3769, -4320), (Sum.inr 3770, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3795, -4320), (Sum.inr 3796, -4320), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3849, -4320), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3875, -4320), (Sum.inr 3876, -4320), (Sum.inr 3891, -4320), (Sum.inr 3897, -4320), (Sum.inr 3901, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -8640), (Sum.inr 3907, -4320), (Sum.inr 3910, -4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow80 : Integer.Sparse Master := [(Sum.inr 1388, 1), (Sum.inr 2470, 1), (Sum.inr 2485, 2), (Sum.inr 2712, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

def numericRow81 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 2470, 1), (Sum.inr 2610, 2), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

def numericRow82 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 2543, 2), (Sum.inr 2562, 1), (Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

def numericRow83 : Integer.Sparse Master := [(Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2618, 1), (Sum.inr 2712, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

def numericRow84 : Integer.Sparse Master := [(Sum.inr 1394, 1), (Sum.inr 2610, 1), (Sum.inr 2618, 1), (Sum.inr 2624, 1), (Sum.inr 2712, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def numericRow85 : Integer.Sparse Master := [(Sum.inr 1209, 1), (Sum.inr 1378, 1), (Sum.inr 1388, 1), (Sum.inr 1394, 2), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

def numericRow86 : Integer.Sparse Master := [(Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 3543, 1), (Sum.inr 3545, 2), (Sum.inr 4085, -1)]

def numericRow87 : Integer.Sparse Master := [(Sum.inr 2050, 1), (Sum.inr 2052, 1), (Sum.inr 2055, 2), (Sum.inr 2290, 1), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

def numericRow88 : Integer.Sparse Master := [(Sum.inr 2290, 2), (Sum.inr 3543, 2), (Sum.inr 3634, 2), (Sum.inr 4085, -1)]

def numericRow89 : Integer.Sparse Master := [(Sum.inr 3387, 1), (Sum.inr 3389, 2), (Sum.inr 3393, 2), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

def numericRow90 : Integer.Sparse Master := [(Sum.inr 2050, 2), (Sum.inr 3387, 1), (Sum.inr 3543, 3), (Sum.inr 4085, -1)]

def numericRow91 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1046, -120), (Sum.inr 1051, -40), (Sum.inr 1091, -40), (Sum.inr 1242, -120), (Sum.inr 1750, -120), (Sum.inr 1752, -40), (Sum.inr 1756, -40), (Sum.inr 2485, -240), (Sum.inr 2519, -120), (Sum.inr 3300, -120), (Sum.inr 3310, -40), (Sum.inr 3481, -240), (Sum.inr 3486, -120), (Sum.inr 3615, -120), (Sum.inr 3627, -120), (Sum.inr 3632, -120), (Sum.inr 3633, -40)]

def numericRow92 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 1046, 120), (Sum.inr 1051, 40), (Sum.inr 1091, 40), (Sum.inr 1242, 120), (Sum.inr 2485, 240), (Sum.inr 2519, 120)]

def numericRow93 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 2247, -240), (Sum.inr 2281, -80), (Sum.inr 2290, -240), (Sum.inr 2294, -80), (Sum.inr 2726, -240), (Sum.inr 3545, -240), (Sum.inr 3634, -120), (Sum.inr 5252, 960), (Sum.inr 5268, 480)]

def numericRow94 : Integer.Sparse Master := [(Sum.inl 0, -3), (Sum.inl 2, -15), (Sum.inr 2247, 120), (Sum.inr 2281, 40), (Sum.inr 2712, 240), (Sum.inr 2726, 120), (Sum.inr 2734, 120)]

def numericRow95 : Integer.Sparse Master := [(Sum.inr 3545, 3), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow800 : Integer.Sparse Master := [(Sum.inl 0, -36), (Sum.inl 2, 5), (Sum.inl 3, 40), (Sum.inl 12, 40), (Sum.inl 1, 5), (Sum.inr 2023, 360), (Sum.inr 2025, 360), (Sum.inr 2028, 360), (Sum.inr 2058, 360), (Sum.inr 2245, 360), (Sum.inr 2924, 360), (Sum.inr 2931, 360), (Sum.inr 3692, 360), (Sum.inr 3693, 360), (Sum.inr 3706, 360), (Sum.inr 3719, 360), (Sum.inr 3782, 360), (Sum.inr 3801, 360), (Sum.inr 3849, 360), (Sum.inr 3850, 360), (Sum.inr 3857, 360), (Sum.inr 3910, 360)]

def numericRow801 : Integer.Sparse Master := [(Sum.inl 0, 96), (Sum.inl 2, 45), (Sum.inl 12, -80), (Sum.inl 4, 80), (Sum.inl 1, -15), (Sum.inr 2739, -4320), (Sum.inr 3534, -4320), (Sum.inr 3801, -4320), (Sum.inr 3809, -4320), (Sum.inr 3812, -4320), (Sum.inr 3813, -4320), (Sum.inr 3814, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -2160), (Sum.inr 3907, -4320), (Sum.inr 5265, 17280), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5299, 17280), (Sum.inr 5425, 17280), (Sum.inr 5426, 8640)]

def numericRow802 : Integer.Sparse Master := [(Sum.inl 0, -224), (Sum.inl 2, -150), (Sum.inl 3, -160), (Sum.inl 12, 320), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, -110), (Sum.inr 2392, 8640), (Sum.inr 2393, 8640), (Sum.inr 2394, 8640), (Sum.inr 2405, 8640), (Sum.inr 2732, 8640), (Sum.inr 2909, 8640), (Sum.inr 2910, 8640), (Sum.inr 2955, 8640), (Sum.inr 3055, 8640), (Sum.inr 3347, 8640), (Sum.inr 3348, 8640), (Sum.inr 3358, 8640), (Sum.inr 3541, 8640), (Sum.inr 3559, 8640), (Sum.inr 3565, 8640), (Sum.inr 3584, 8640), (Sum.inr 3714, 8640), (Sum.inr 3733, 8640), (Sum.inr 3839, 8640), (Sum.inr 3845, 8640), (Sum.inr 3868, 8640), (Sum.inr 3869, 8640), (Sum.inr 3872, 8640), (Sum.inr 3876, 8640), (Sum.inr 3877, 8640), (Sum.inr 3949, 8640)]

def numericRow803 : Integer.Sparse Master := [(Sum.inr 2591, 1), (Sum.inr 3733, 1), (Sum.inr 3819, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

def numericRow804 : Integer.Sparse Master := [(Sum.inl 0, -500), (Sum.inl 5, -80), (Sum.inl 2, -200), (Sum.inl 51, 960), (Sum.inl 3, -1920), (Sum.inl 13, -640), (Sum.inl 55, 960), (Sum.inl 12, -320), (Sum.inl 4, -960), (Sum.inl 27, 240), (Sum.inl 1, 300), (Sum.inl 31, 960), (Sum.inr 2031, 17280), (Sum.inr 2032, 17280), (Sum.inr 2039, 17280), (Sum.inr 2049, 17280), (Sum.inr 2251, 17280), (Sum.inr 2606, 17280), (Sum.inr 2608, 17280), (Sum.inr 2632, 17280), (Sum.inr 2677, 17280), (Sum.inr 3527, 17280), (Sum.inr 3538, 17280), (Sum.inr 3540, 17280), (Sum.inr 3575, 17280), (Sum.inr 3696, 17280), (Sum.inr 3699, 17280), (Sum.inr 3780, 17280), (Sum.inr 3802, 17280), (Sum.inr 3811, 17280), (Sum.inr 3813, 17280), (Sum.inr 3827, 17280), (Sum.inr 3834, 17280), (Sum.inr 3840, 17280), (Sum.inr 3846, 17280), (Sum.inr 3850, 17280), (Sum.inr 3881, 34560)]

def numericRow805 : Integer.Sparse Master := [(Sum.inl 0, -351), (Sum.inl 5, -60), (Sum.inl 2, -225), (Sum.inl 3, -1680), (Sum.inl 13, -240), (Sum.inl 23, 720), (Sum.inl 54, 720), (Sum.inl 12, -720), (Sum.inl 25, 1440), (Sum.inl 26, -240), (Sum.inl 4, -720), (Sum.inl 27, 180), (Sum.inl 1, 330), (Sum.inr 2078, 12960), (Sum.inr 2080, 12960), (Sum.inr 2081, 12960), (Sum.inr 2108, 12960), (Sum.inr 2217, 12960), (Sum.inr 2860, 12960), (Sum.inr 2867, 12960), (Sum.inr 2876, 12960), (Sum.inr 3086, 12960), (Sum.inr 3374, 12960), (Sum.inr 3379, 12960), (Sum.inr 3386, 12960), (Sum.inr 3570, 12960), (Sum.inr 3722, 12960), (Sum.inr 3752, 12960), (Sum.inr 3762, 12960), (Sum.inr 3771, 12960), (Sum.inr 3772, 12960), (Sum.inr 3788, 12960), (Sum.inr 3814, 12960), (Sum.inr 3872, 12960), (Sum.inr 3873, 12960), (Sum.inr 3884, 12960), (Sum.inr 3954, 12960), (Sum.inr 3958, 12960), (Sum.inr 3959, 12960)]

def numericRow806 : Integer.Sparse Master := [(Sum.inr 2619, 1), (Sum.inr 2872, 1), (Sum.inr 3175, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def numericRow807 : Integer.Sparse Master := [(Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 3788, 1), (Sum.inr 3809, 1), (Sum.inr 3877, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def numericRow808 : Integer.Sparse Master := [(Sum.inr 2634, 1), (Sum.inr 2873, 1), (Sum.inr 3699, 1), (Sum.inr 3828, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def numericRow809 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2870, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3874, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def numericRow810 : Integer.Sparse Master := [(Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 3959, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

def numericRow811 : Integer.Sparse Master := [(Sum.inr 3198, 1), (Sum.inr 3698, 1), (Sum.inr 3699, 1), (Sum.inr 3706, 1), (Sum.inr 3814, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def numericRow812 : Integer.Sparse Master := [(Sum.inr 2620, 1), (Sum.inr 3045, 1), (Sum.inr 3723, 1), (Sum.inr 3732, 1), (Sum.inr 3850, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def numericRow813 : Integer.Sparse Master := [(Sum.inl 0, 127), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, 240), (Sum.inl 1, 770), (Sum.inr 1925, -4320), (Sum.inr 1926, -4320), (Sum.inr 1928, -4320), (Sum.inr 1948, -4320), (Sum.inr 2279, -4320), (Sum.inr 2908, -4320), (Sum.inr 2911, -4320), (Sum.inr 2954, -4320), (Sum.inr 3054, -4320), (Sum.inr 3600, -4320), (Sum.inr 3606, -4320), (Sum.inr 3611, -4320), (Sum.inr 3626, -4320), (Sum.inr 3659, -4320), (Sum.inr 3660, -4320), (Sum.inr 3713, -4320), (Sum.inr 3732, -4320), (Sum.inr 3789, -4320), (Sum.inr 3810, -4320), (Sum.inr 3811, -4320), (Sum.inr 3814, -12960), (Sum.inr 3899, -4320), (Sum.inr 3902, -4320), (Sum.inr 3907, -4320)]

def numericRow814 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -195), (Sum.inr 2515, -4320), (Sum.inr 3479, -4320), (Sum.inr 3706, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3796, -4320), (Sum.inr 3801, -4320), (Sum.inr 3809, -12960), (Sum.inr 3812, -4320), (Sum.inr 3813, -12960), (Sum.inr 3814, -8640), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 4816, 17280), (Sum.inr 4817, 17280), (Sum.inr 4821, 17280), (Sum.inr 4836, 17280), (Sum.inr 4891, 17280), (Sum.inr 5086, 17280), (Sum.inr 5090, 17280), (Sum.inr 5254, 17280), (Sum.inr 5260, 17280), (Sum.inr 5267, 34560), (Sum.inr 5287, 17280), (Sum.inr 5360, 34560), (Sum.inr 5361, 17280), (Sum.inr 5407, 17280), (Sum.inr 5425, 17280), (Sum.inr 5426, 17280), (Sum.inr 5436, 17280)]

def numericRow815 : Integer.Sparse Master := [(Sum.inl 0, -124), (Sum.inl 2, -95), (Sum.inl 3, -640), (Sum.inl 13, -240), (Sum.inl 12, -320), (Sum.inl 4, -160), (Sum.inl 1, 265), (Sum.inr 2196, 4320), (Sum.inr 2197, 4320), (Sum.inr 2207, 4320), (Sum.inr 2217, 4320), (Sum.inr 2253, 4320), (Sum.inr 3016, 4320), (Sum.inr 3025, 4320), (Sum.inr 3038, 4320), (Sum.inr 3086, 4320), (Sum.inr 3464, 4320), (Sum.inr 3479, 4320), (Sum.inr 3480, 4320), (Sum.inr 3541, 4320), (Sum.inr 3762, 8640), (Sum.inr 3771, 4320), (Sum.inr 3772, 4320), (Sum.inr 3796, 4320), (Sum.inr 3801, 4320), (Sum.inr 3803, 4320), (Sum.inr 3809, 4320), (Sum.inr 3813, 4320), (Sum.inr 3841, 4320), (Sum.inr 3872, 4320), (Sum.inr 3877, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow816 : Integer.Sparse Master := [(Sum.inl 0, 67), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 90), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3849, -8640), (Sum.inr 3875, -8640), (Sum.inr 3902, -4320), (Sum.inr 3910, -4320), (Sum.inr 3957, -8640), (Sum.inr 4992, 17280), (Sum.inr 4993, 17280), (Sum.inr 4999, 34560), (Sum.inr 5004, 17280), (Sum.inr 5005, 34560), (Sum.inr 5011, 17280), (Sum.inr 5145, 34560), (Sum.inr 5251, 17280), (Sum.inr 5265, 17280), (Sum.inr 5282, 17280), (Sum.inr 5379, 34560), (Sum.inr 5414, 17280), (Sum.inr 5421, 34560), (Sum.inr 5446, 34560), (Sum.inr 5470, 34560)]

def numericRow817 : Integer.Sparse Master := [(Sum.inl 0, -93), (Sum.inl 2, 155), (Sum.inl 3, 2000), (Sum.inl 12, 800), (Sum.inl 25, -480), (Sum.inl 26, 480), (Sum.inl 4, 1120), (Sum.inl 1, -820), (Sum.inr 2378, 4320), (Sum.inr 2379, 4320), (Sum.inr 2384, 8640), (Sum.inr 2710, 4320), (Sum.inr 2912, 4320), (Sum.inr 2925, 8640), (Sum.inr 3078, 4320), (Sum.inr 3337, 4320), (Sum.inr 3342, 8640), (Sum.inr 3526, 4320), (Sum.inr 3720, 8640), (Sum.inr 3869, 4320), (Sum.inr 3946, 8640), (Sum.inr 3955, 8640), (Sum.inr 3957, 4320), (Sum.inr 3959, 8640)]

def numericRow818 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 2, 95), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 4, 160), (Sum.inl 1, -410), (Sum.inl 31, -480), (Sum.inr 2389, 4320), (Sum.inr 2390, 8640), (Sum.inr 2396, 4320), (Sum.inr 2730, 4320), (Sum.inr 3345, 4320), (Sum.inr 3346, 8640), (Sum.inr 3350, 4320), (Sum.inr 3539, 4320), (Sum.inr 3562, 8640), (Sum.inr 3580, 4320), (Sum.inr 3819, 4320), (Sum.inr 3832, 8640), (Sum.inr 3843, 8640), (Sum.inr 3873, 8640), (Sum.inr 3875, 8640), (Sum.inr 3884, 8640), (Sum.inr 3947, 8640)]

def numericRow819 : Integer.Sparse Master := [(Sum.inr 3846, 1), (Sum.inr 3947, 2), (Sum.inr 3949, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def numericRow820 : Integer.Sparse Master := [(Sum.inr 2567, 1), (Sum.inr 3724, 1), (Sum.inr 3827, 1), (Sum.inr 3838, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

def numericRow821 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 3692, -8640), (Sum.inr 3731, -4320), (Sum.inr 3769, -8640), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3849, -4320), (Sum.inr 3867, -4320), (Sum.inr 3875, -4320), (Sum.inr 3909, -4320), (Sum.inr 3957, -17280), (Sum.inr 4025, -4320), (Sum.inr 4046, -4320), (Sum.inr 4791, 17280), (Sum.inr 4795, 17280), (Sum.inr 4799, 34560), (Sum.inr 4863, 17280), (Sum.inr 5181, 17280), (Sum.inr 5184, 34560), (Sum.inr 5243, 17280), (Sum.inr 5348, 17280), (Sum.inr 5350, 34560), (Sum.inr 5379, 34560), (Sum.inr 5414, 34560), (Sum.inr 5429, 34560), (Sum.inr 5430, 34560)]

def numericRow822 : Integer.Sparse Master := [(Sum.inl 0, -297), (Sum.inl 5, -240), (Sum.inl 2, 1290), (Sum.inl 7, 480), (Sum.inl 8, 480), (Sum.inl 51, -2880), (Sum.inl 3, 6960), (Sum.inl 13, 720), (Sum.inl 23, -1440), (Sum.inl 24, -1440), (Sum.inl 55, -2880), (Sum.inl 12, 2880), (Sum.inl 4, 3840), (Sum.inl 27, 720), (Sum.inl 1, -3765), (Sum.inl 31, -2880), (Sum.inr 2008, 12960), (Sum.inr 2012, 12960), (Sum.inr 2017, 25920), (Sum.inr 2232, 12960), (Sum.inr 2609, 12960), (Sum.inr 2614, 25920), (Sum.inr 2697, 12960), (Sum.inr 3685, 12960), (Sum.inr 3688, 25920), (Sum.inr 3819, 25920), (Sum.inr 3832, 25920), (Sum.inr 3846, 25920), (Sum.inr 3848, 25920), (Sum.inr 3867, 12960), (Sum.inr 3875, 12960), (Sum.inr 3909, 12960)]

def numericRow823 : Integer.Sparse Master := [(Sum.inl 0, -56), (Sum.inl 5, 60), (Sum.inl 2, 90), (Sum.inl 7, 80), (Sum.inl 3, 2080), (Sum.inl 13, 160), (Sum.inl 23, -720), (Sum.inl 54, -480), (Sum.inl 12, 1280), (Sum.inl 25, -960), (Sum.inl 26, 160), (Sum.inl 4, 1120), (Sum.inl 27, -180), (Sum.inl 1, -990), (Sum.inr 2074, 4320), (Sum.inr 2076, 8640), (Sum.inr 2104, 4320), (Sum.inr 2213, 4320), (Sum.inr 3488, 4320), (Sum.inr 3491, 4320), (Sum.inr 3524, 8640), (Sum.inr 3720, 8640), (Sum.inr 3750, 8640), (Sum.inr 3768, 4320), (Sum.inr 3769, 8640), (Sum.inr 3812, 4320), (Sum.inr 3869, 8640), (Sum.inr 3871, 8640), (Sum.inr 3874, 8640), (Sum.inr 3957, 8640)]

def numericRow824 : Integer.Sparse Master := [(Sum.inr 3849, 1), (Sum.inr 3954, 1), (Sum.inr 3957, 2), (Sum.inr 4046, 1), (Sum.inr 4091, -1)]

def numericRow825 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 3176, 2), (Sum.inr 3179, 1), (Sum.inr 3199, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def numericRow826 : Integer.Sparse Master := [(Sum.inr 3179, 1), (Sum.inr 3731, 1), (Sum.inr 3954, 3), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

def numericRow827 : Integer.Sparse Master := [(Sum.inr 2859, 1), (Sum.inr 3685, 1), (Sum.inr 3935, 2), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def numericRow828 : Integer.Sparse Master := [(Sum.inr 3176, 1), (Sum.inr 3724, 1), (Sum.inr 3935, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

def numericRow829 : Integer.Sparse Master := [(Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 2), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def numericRow830 : Integer.Sparse Master := [(Sum.inr 3199, 1), (Sum.inr 3685, 1), (Sum.inr 3692, 2), (Sum.inr 3801, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def numericRow831 : Integer.Sparse Master := [(Sum.inr 3030, 1), (Sum.inr 3724, 2), (Sum.inr 3731, 1), (Sum.inr 3849, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow832 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 2859, 1), (Sum.inr 2864, 2), (Sum.inr 3030, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

def numericRow833 : Integer.Sparse Master := [(Sum.inl 0, -204), (Sum.inl 5, 40), (Sum.inl 2, -95), (Sum.inl 51, -480), (Sum.inl 3, 560), (Sum.inl 13, 240), (Sum.inl 55, -240), (Sum.inl 12, 400), (Sum.inl 27, -60), (Sum.inl 1, -35), (Sum.inr 2606, 8640), (Sum.inr 2607, 4320), (Sum.inr 2631, 4320), (Sum.inr 2676, 4320), (Sum.inr 3524, 4320), (Sum.inr 3527, 8640), (Sum.inr 3566, 4320), (Sum.inr 3780, 8640), (Sum.inr 3799, 4320), (Sum.inr 3800, 4320), (Sum.inr 3802, 8640), (Sum.inr 3850, 8640), (Sum.inr 3854, 8640), (Sum.inr 3878, 4320), (Sum.inr 3881, 8640)]

def numericRow834 : Integer.Sparse Master := [(Sum.inl 0, -531), (Sum.inl 5, 120), (Sum.inl 6, -15), (Sum.inl 2, -315), (Sum.inl 7, 240), (Sum.inl 35, 240), (Sum.inl 3, 1680), (Sum.inl 13, 240), (Sum.inl 23, -720), (Sum.inl 54, -720), (Sum.inl 12, 960), (Sum.inl 26, 480), (Sum.inl 4, 480), (Sum.inl 27, -180), (Sum.inl 1, 255), (Sum.inr 2860, 25920), (Sum.inr 2864, 12960), (Sum.inr 2874, 12960), (Sum.inr 3374, 25920), (Sum.inr 3378, 12960), (Sum.inr 3384, 12960), (Sum.inr 3569, 12960), (Sum.inr 3758, 12960), (Sum.inr 3759, 12960), (Sum.inr 3762, 25920), (Sum.inr 3788, 25920), (Sum.inr 3801, 12960), (Sum.inr 3877, 25920), (Sum.inr 3958, 25920), (Sum.inr 3959, 25920)]

def numericRow835 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 3703, 1), (Sum.inr 3874, 1), (Sum.inr 3961, 2), (Sum.inr 4092, -1)]

def numericRow836 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2869, 1), (Sum.inr 3697, 1), (Sum.inr 3874, 1), (Sum.inr 3884, 2), (Sum.inr 4092, -1)]

def numericRow837 : Integer.Sparse Master := [(Sum.inr 3786, 1), (Sum.inr 3788, 2), (Sum.inr 3805, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

def numericRow838 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2870, 2), (Sum.inr 2878, 1), (Sum.inr 3043, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

def numericRow839 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 3043, 1), (Sum.inr 3786, 1), (Sum.inr 3850, 2), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

def numericRow840 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 80), (Sum.inr 2483, -2160), (Sum.inr 3477, -2160), (Sum.inr 3692, -2160), (Sum.inr 3769, -2160), (Sum.inr 3789, -2160), (Sum.inr 3800, -1080), (Sum.inr 3801, -2160), (Sum.inr 3805, -1080), (Sum.inr 3810, -2160), (Sum.inr 3812, -2160), (Sum.inr 3899, -2160), (Sum.inr 3901, -1080), (Sum.inr 3909, -1080), (Sum.inr 4025, -1080), (Sum.inr 4046, -1080), (Sum.inr 4792, 4320), (Sum.inr 4795, 4320), (Sum.inr 4803, 8640), (Sum.inr 4885, 4320), (Sum.inr 5067, 4320), (Sum.inr 5251, 4320), (Sum.inr 5348, 4320), (Sum.inr 5353, 8640), (Sum.inr 5425, 8640), (Sum.inr 5429, 4320), (Sum.inr 5430, 8640)]

def numericRow841 : Integer.Sparse Master := [(Sum.inl 0, -218), (Sum.inl 5, -160), (Sum.inl 6, 10), (Sum.inl 2, 505), (Sum.inl 7, 640), (Sum.inl 35, 480), (Sum.inl 8, 160), (Sum.inl 51, -960), (Sum.inl 3, 3680), (Sum.inl 13, 1040), (Sum.inl 52, 320), (Sum.inl 23, -960), (Sum.inl 54, -480), (Sum.inl 24, -480), (Sum.inl 55, -960), (Sum.inl 12, 1600), (Sum.inl 25, -480), (Sum.inl 26, 320), (Sum.inl 4, 1440), (Sum.inl 27, 120), (Sum.inl 1, -1315), (Sum.inr 2009, 4320), (Sum.inr 2012, 4320), (Sum.inr 2021, 8640), (Sum.inr 2233, 4320), (Sum.inr 2981, 4320), (Sum.inr 3064, 4320), (Sum.inr 3685, 4320), (Sum.inr 3691, 8640), (Sum.inr 3839, 8640), (Sum.inr 3846, 4320), (Sum.inr 3848, 8640), (Sum.inr 3899, 4320), (Sum.inr 3909, 4320)]

def numericRow842 : Integer.Sparse Master := [(Sum.inl 0, -61), (Sum.inl 2, 175), (Sum.inl 3, 1520), (Sum.inl 13, 480), (Sum.inl 12, 640), (Sum.inl 4, 800), (Sum.inl 1, -800), (Sum.inr 2195, 8640), (Sum.inr 2201, 4320), (Sum.inr 2213, 4320), (Sum.inr 2252, 4320), (Sum.inr 3476, 4320), (Sum.inr 3477, 8640), (Sum.inr 3539, 4320), (Sum.inr 3761, 8640), (Sum.inr 3768, 4320), (Sum.inr 3769, 8640), (Sum.inr 3805, 4320), (Sum.inr 3810, 8640), (Sum.inr 3812, 8640), (Sum.inr 3840, 8640), (Sum.inr 3871, 8640), (Sum.inr 3874, 4320)]

def numericRow843 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -195), (Sum.inr 2508, -2160), (Sum.inr 3460, -2160), (Sum.inr 3703, -2160), (Sum.inr 3758, -2160), (Sum.inr 3800, -4320), (Sum.inr 3801, -2160), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3812, -2160), (Sum.inr 3813, -4320), (Sum.inr 3814, -8640), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 5085, 8640), (Sum.inr 5086, 17280), (Sum.inr 5254, 17280), (Sum.inr 5265, 17280), (Sum.inr 5286, 8640), (Sum.inr 5359, 8640), (Sum.inr 5360, 17280), (Sum.inr 5407, 17280), (Sum.inr 5429, 8640)]

def numericRow844 : Integer.Sparse Master := [(Sum.inl 0, -319), (Sum.inl 5, 60), (Sum.inl 6, -10), (Sum.inl 2, -135), (Sum.inl 35, 80), (Sum.inl 51, -480), (Sum.inl 3, -400), (Sum.inl 13, -400), (Sum.inl 52, 160), (Sum.inl 55, -240), (Sum.inl 12, -400), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 27, -60), (Sum.inl 1, 510), (Sum.inl 31, -480), (Sum.inr 2974, 8640), (Sum.inr 2976, 4320), (Sum.inr 3037, 4320), (Sum.inr 3526, 4320), (Sum.inr 3528, 8640), (Sum.inr 3567, 4320), (Sum.inr 3780, 8640), (Sum.inr 3800, 4320), (Sum.inr 3801, 4320), (Sum.inr 3803, 8640), (Sum.inr 3846, 4320), (Sum.inr 3878, 4320)]

def numericRow845 : Integer.Sparse Master := [(Sum.inl 0, -86), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 13, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, 75), (Sum.inr 3016, 4320), (Sum.inr 3023, 2160), (Sum.inr 3037, 2160), (Sum.inr 3460, 2160), (Sum.inr 3461, 2160), (Sum.inr 3464, 4320), (Sum.inr 3526, 2160), (Sum.inr 3758, 2160), (Sum.inr 3759, 2160), (Sum.inr 3762, 4320), (Sum.inr 3800, 2160), (Sum.inr 3803, 4320), (Sum.inr 3809, 4320), (Sum.inr 3814, 4320), (Sum.inr 3954, 2160)]

def numericRow846 : Integer.Sparse Master := [(Sum.inr 2508, 1), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 4092, -1)]

def numericRow847 : Integer.Sparse Master := [(Sum.inl 0, -156), (Sum.inl 2, 240), (Sum.inl 3, 640), (Sum.inl 12, 160), (Sum.inl 4, 800), (Sum.inl 1, -1060), (Sum.inl 31, -480), (Sum.inr 2534, 8640), (Sum.inr 2535, 8640), (Sum.inr 2537, 8640), (Sum.inr 2587, 8640), (Sum.inr 2669, 8640), (Sum.inr 3431, 8640), (Sum.inr 3434, 8640), (Sum.inr 3463, 8640), (Sum.inr 3529, 8640), (Sum.inr 3536, 8640), (Sum.inr 3540, 8640), (Sum.inr 3568, 8640), (Sum.inr 3743, 8640), (Sum.inr 3761, 8640), (Sum.inr 3804, 8640), (Sum.inr 3805, 8640), (Sum.inr 3840, 8640), (Sum.inr 3848, 8640), (Sum.inr 3849, 8640), (Sum.inr 3857, 8640), (Sum.inr 3879, 8640), (Sum.inr 3880, 8640), (Sum.inr 3884, 8640), (Sum.inr 3927, 8640), (Sum.inr 3978, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow848 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 3871, 1), (Sum.inr 3927, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def numericRow849 : Integer.Sparse Master := [(Sum.inr 2984, 1), (Sum.inr 3783, 1), (Sum.inr 3787, 1), (Sum.inr 3800, 1), (Sum.inr 3871, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

def numericRow850 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 3091, 1), (Sum.inr 3787, 1), (Sum.inr 3871, 1), (Sum.inr 3875, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def numericRow851 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 3721, -4320), (Sum.inr 3789, -4320), (Sum.inr 3801, -4320), (Sum.inr 3810, -4320), (Sum.inr 3812, -4320), (Sum.inr 3836, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3900, -4320), (Sum.inr 3909, -4320), (Sum.inr 3964, -4320), (Sum.inr 3974, -8640), (Sum.inr 4025, -4320), (Sum.inr 4046, -4320), (Sum.inr 4797, 17280), (Sum.inr 4799, 17280), (Sum.inr 4803, 17280), (Sum.inr 4825, 17280), (Sum.inr 4851, 17280), (Sum.inr 5129, 17280), (Sum.inr 5132, 17280), (Sum.inr 5144, 17280), (Sum.inr 5249, 17280), (Sum.inr 5350, 17280), (Sum.inr 5353, 17280), (Sum.inr 5362, 17280), (Sum.inr 5377, 17280), (Sum.inr 5379, 17280), (Sum.inr 5414, 17280), (Sum.inr 5419, 17280), (Sum.inr 5425, 17280), (Sum.inr 5429, 17280), (Sum.inr 5430, 34560), (Sum.inr 5480, 17280)]

def numericRow852 : Integer.Sparse Master := [(Sum.inl 0, -178), (Sum.inl 6, -10), (Sum.inl 2, 600), (Sum.inl 7, 480), (Sum.inl 35, 320), (Sum.inl 51, -480), (Sum.inl 3, 4960), (Sum.inl 13, 320), (Sum.inl 52, 160), (Sum.inl 23, -480), (Sum.inl 24, -960), (Sum.inl 55, -960), (Sum.inl 12, 1600), (Sum.inl 26, 960), (Sum.inl 4, 2880), (Sum.inl 27, 120), (Sum.inl 1, -2180), (Sum.inl 31, -480), (Sum.inr 2070, 8640), (Sum.inr 2073, 8640), (Sum.inr 2076, 8640), (Sum.inr 2088, 8640), (Sum.inr 2195, 8640), (Sum.inr 2545, 8640), (Sum.inr 2551, 8640), (Sum.inr 2566, 8640), (Sum.inr 2708, 8640), (Sum.inr 3716, 8640), (Sum.inr 3720, 8640), (Sum.inr 3748, 8640), (Sum.inr 3750, 8640), (Sum.inr 3761, 8640), (Sum.inr 3810, 8640), (Sum.inr 3812, 8640), (Sum.inr 3825, 8640), (Sum.inr 3840, 8640), (Sum.inr 3869, 8640), (Sum.inr 3871, 17280), (Sum.inr 3874, 8640), (Sum.inr 3978, 8640)]

def numericRow853 : Integer.Sparse Master := [(Sum.inl 0, -237), (Sum.inl 5, 120), (Sum.inl 6, -15), (Sum.inl 2, 330), (Sum.inl 7, 240), (Sum.inl 35, 240), (Sum.inl 3, 2640), (Sum.inl 13, 1440), (Sum.inl 23, -720), (Sum.inl 54, -720), (Sum.inl 12, 1200), (Sum.inl 25, -720), (Sum.inl 4, 960), (Sum.inl 27, -180), (Sum.inl 1, -1590), (Sum.inr 2015, 12960), (Sum.inr 2017, 12960), (Sum.inr 2021, 12960), (Sum.inr 2044, 12960), (Sum.inr 2240, 12960), (Sum.inr 3499, 12960), (Sum.inr 3502, 12960), (Sum.inr 3516, 12960), (Sum.inr 3557, 12960), (Sum.inr 3688, 12960), (Sum.inr 3691, 12960), (Sum.inr 3700, 12960), (Sum.inr 3819, 12960), (Sum.inr 3832, 12960), (Sum.inr 3835, 12960), (Sum.inr 3836, 12960), (Sum.inr 3839, 12960), (Sum.inr 3842, 12960), (Sum.inr 3843, 12960), (Sum.inr 3846, 12960), (Sum.inr 3848, 25920), (Sum.inr 3900, 12960), (Sum.inr 3909, 12960), (Sum.inr 3974, 12960), (Sum.inr 3978, 12960)]

def numericRow854 : Integer.Sparse Master := [(Sum.inr 2916, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 1), (Sum.inr 3724, 1), (Sum.inr 3838, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

def numericRow855 : Integer.Sparse Master := [(Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 3964, 1), (Sum.inr 3972, 2), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

def numericRow856 : Integer.Sparse Master := [(Sum.inr 3066, 1), (Sum.inr 3789, 1), (Sum.inr 3949, 1), (Sum.inr 3972, 2), (Sum.inr 4091, -1)]

def numericRow857 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -85), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3913, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 5082, 17280), (Sum.inr 5083, 17280), (Sum.inr 5086, 17280), (Sum.inr 5091, 17280), (Sum.inr 5144, 17280), (Sum.inr 5146, 17280), (Sum.inr 5160, 17280), (Sum.inr 5289, 17280), (Sum.inr 5299, 17280), (Sum.inr 5357, 17280), (Sum.inr 5358, 17280), (Sum.inr 5360, 17280), (Sum.inr 5381, 17280), (Sum.inr 5382, 17280), (Sum.inr 5420, 17280), (Sum.inr 5421, 17280), (Sum.inr 5425, 34560), (Sum.inr 5446, 17280)]

def numericRow858 : Integer.Sparse Master := [(Sum.inl 0, -179), (Sum.inl 5, 20), (Sum.inl 6, -5), (Sum.inl 2, -35), (Sum.inl 51, -240), (Sum.inl 3, 160), (Sum.inl 52, 80), (Sum.inl 1, 205), (Sum.inr 2490, 4320), (Sum.inr 2491, 4320), (Sum.inr 2494, 4320), (Sum.inr 2500, 4320), (Sum.inr 2773, 4320), (Sum.inr 3557, 4320), (Sum.inr 3558, 4320), (Sum.inr 3560, 4320), (Sum.inr 3572, 4320), (Sum.inr 3695, 4320), (Sum.inr 3696, 4320), (Sum.inr 3698, 4320), (Sum.inr 3827, 4320), (Sum.inr 3834, 4320), (Sum.inr 3837, 4320), (Sum.inr 3838, 4320), (Sum.inr 3840, 4320), (Sum.inr 3850, 4320), (Sum.inr 3866, 4320), (Sum.inr 3870, 4320), (Sum.inr 3872, 4320), (Sum.inr 3876, 4320), (Sum.inr 3881, 4320)]

def numericRow859 : Integer.Sparse Master := [(Sum.inl 0, -336), (Sum.inl 2, -190), (Sum.inl 3, 800), (Sum.inl 12, 160), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, 250), (Sum.inr 2921, 8640), (Sum.inr 2922, 8640), (Sum.inr 2928, 8640), (Sum.inr 2951, 8640), (Sum.inr 3097, 8640), (Sum.inr 3441, 8640), (Sum.inr 3447, 8640), (Sum.inr 3464, 8640), (Sum.inr 3573, 8640), (Sum.inr 3718, 8640), (Sum.inr 3722, 8640), (Sum.inr 3730, 8640), (Sum.inr 3752, 8640), (Sum.inr 3762, 8640), (Sum.inr 3794, 8640), (Sum.inr 3809, 8640), (Sum.inr 3839, 8640), (Sum.inr 3872, 8640), (Sum.inr 3873, 8640), (Sum.inr 3958, 8640), (Sum.inr 3959, 8640), (Sum.inr 4022, 8640)]

def numericRow860 : Integer.Sparse Master := [(Sum.inr 3781, 1), (Sum.inr 3848, 1), (Sum.inr 3946, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

def numericRow861 : Integer.Sparse Master := [(Sum.inr 2977, 1), (Sum.inr 3723, 1), (Sum.inr 3725, 1), (Sum.inr 3730, 1), (Sum.inr 3848, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

def numericRow862 : Integer.Sparse Master := [(Sum.inr 2975, 1), (Sum.inr 3826, 1), (Sum.inr 3828, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def numericRow863 : Integer.Sparse Master := [(Sum.inl 0, 52), (Sum.inl 2, -3), (Sum.inl 3, 48), (Sum.inl 4, 80), (Sum.inl 1, -51), (Sum.inr 2515, -864), (Sum.inr 2519, -432), (Sum.inr 2522, -432), (Sum.inr 2684, -864), (Sum.inr 2685, -432), (Sum.inr 2686, -432), (Sum.inr 2782, -432), (Sum.inr 2884, -864), (Sum.inr 2889, -432), (Sum.inr 3394, -864), (Sum.inr 3397, -432), (Sum.inr 3479, -864), (Sum.inr 3486, -432), (Sum.inr 3583, -432), (Sum.inr 3621, -864), (Sum.inr 3627, -432), (Sum.inr 3631, -432), (Sum.inr 3633, -432), (Sum.inr 3706, -864), (Sum.inr 3771, -864), (Sum.inr 3900, -864), (Sum.inr 3903, -864), (Sum.inr 3907, -432), (Sum.inr 3910, -864), (Sum.inr 3913, -864), (Sum.inr 3964, -864), (Sum.inr 3983, -1728)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow864 : Integer.Sparse Master := [(Sum.inl 0, -72), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 65), (Sum.inr 2515, 1440), (Sum.inr 2519, 720), (Sum.inr 2522, 720), (Sum.inr 2884, 1440), (Sum.inr 2889, 720), (Sum.inr 3394, 1440), (Sum.inr 3397, 720), (Sum.inr 3583, 720), (Sum.inr 3706, 1440), (Sum.inr 3964, 1440), (Sum.inr 3983, 1440)]

def numericRow865 : Integer.Sparse Master := [(Sum.inl 0, 137), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 2107, -2160), (Sum.inr 2109, -1080), (Sum.inr 2116, -1080), (Sum.inr 2260, -2160), (Sum.inr 2261, -1080), (Sum.inr 2266, -1080), (Sum.inr 2278, -1080), (Sum.inr 2288, -1080), (Sum.inr 2590, -2160), (Sum.inr 2765, -1080), (Sum.inr 3564, -2160), (Sum.inr 3582, -1080), (Sum.inr 3614, -1080), (Sum.inr 3787, -2160), (Sum.inr 3790, -2160), (Sum.inr 3804, -2160), (Sum.inr 3809, -2160), (Sum.inr 3813, -2160), (Sum.inr 3815, -2160), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3892, -2160), (Sum.inr 3894, -1080), (Sum.inr 3907, -1080), (Sum.inr 3910, -2160), (Sum.inr 3913, -1080), (Sum.inr 4010, -2160)]

def numericRow866 : Integer.Sparse Master := [(Sum.inl 0, -72), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 65), (Sum.inr 2107, 1440), (Sum.inr 2109, 720), (Sum.inr 2116, 720), (Sum.inr 2278, 720), (Sum.inr 2590, 1440), (Sum.inr 2765, 720), (Sum.inr 3787, 1440), (Sum.inr 3790, 1440), (Sum.inr 3813, 1440), (Sum.inr 3876, 1440), (Sum.inr 3907, 720)]

def numericRow867 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 2, 30), (Sum.inl 12, -80), (Sum.inl 4, 80), (Sum.inl 1, 15), (Sum.inr 2765, -2160), (Sum.inr 2782, -2160), (Sum.inr 3054, -2160), (Sum.inr 3582, -2160), (Sum.inr 3583, -2160), (Sum.inr 3626, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3886, -4320), (Sum.inr 3903, -4320), (Sum.inr 3907, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 3963, -4320), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 8640), (Sum.inr 5430, 17280), (Sum.inr 5446, 17280)]

def numericRow868 : Integer.Sparse Master := [(Sum.inl 0, -113), (Sum.inl 2, 20), (Sum.inl 3, -480), (Sum.inl 12, -160), (Sum.inl 26, -80), (Sum.inl 4, -240), (Sum.inl 1, -75), (Sum.inl 31, 240), (Sum.inr 2390, 4320), (Sum.inr 2391, 4320), (Sum.inr 2395, 4320), (Sum.inr 2401, 4320), (Sum.inr 2537, 4320), (Sum.inr 2538, 4320), (Sum.inr 2591, 4320), (Sum.inr 2673, 4320), (Sum.inr 2731, 4320), (Sum.inr 3346, 4320), (Sum.inr 3349, 4320), (Sum.inr 3355, 4320), (Sum.inr 3540, 4320), (Sum.inr 3568, 4320), (Sum.inr 3578, 4320), (Sum.inr 3580, 4320), (Sum.inr 3848, 4320), (Sum.inr 3857, 4320), (Sum.inr 3873, 4320), (Sum.inr 3874, 4320), (Sum.inr 3879, 4320), (Sum.inr 3880, 4320), (Sum.inr 3884, 4320), (Sum.inr 3885, 4320), (Sum.inr 3929, 4320), (Sum.inr 3947, 4320)]

def numericRow869 : Integer.Sparse Master := [(Sum.inr 2955, 1), (Sum.inr 3881, 1), (Sum.inr 3929, 1), (Sum.inr 3947, 1), (Sum.inr 3958, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def numericRow870 : Integer.Sparse Master := [(Sum.inr 2633, 1), (Sum.inr 3092, 1), (Sum.inr 3827, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def numericRow871 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 3693, -720), (Sum.inr 3706, -720), (Sum.inr 3732, -720), (Sum.inr 3770, -720), (Sum.inr 3771, -720), (Sum.inr 3809, -1440), (Sum.inr 3811, -720), (Sum.inr 3813, -1440), (Sum.inr 3845, -1440), (Sum.inr 3857, -720), (Sum.inr 3876, -720), (Sum.inr 3958, -720), (Sum.inr 3961, -720), (Sum.inr 4047, -720), (Sum.inr 4849, 2880), (Sum.inr 4850, 2880), (Sum.inr 4856, 2880), (Sum.inr 4861, 2880), (Sum.inr 4867, 2880), (Sum.inr 5183, 2880), (Sum.inr 5188, 2880), (Sum.inr 5198, 2880), (Sum.inr 5264, 2880), (Sum.inr 5353, 2880), (Sum.inr 5379, 2880), (Sum.inr 5382, 2880), (Sum.inr 5385, 5760), (Sum.inr 5399, 2880), (Sum.inr 5402, 2880), (Sum.inr 5421, 2880), (Sum.inr 5436, 2880), (Sum.inr 5445, 2880), (Sum.inr 5446, 2880)]

def numericRow872 : Integer.Sparse Master := [(Sum.inl 0, -2472), (Sum.inl 5, -240), (Sum.inl 2, -1560), (Sum.inl 51, 2880), (Sum.inl 3, -7680), (Sum.inl 13, -960), (Sum.inl 23, 2880), (Sum.inl 24, 2880), (Sum.inl 55, 5760), (Sum.inl 12, -3840), (Sum.inl 4, -2880), (Sum.inl 27, -1440), (Sum.inl 1, 4800), (Sum.inl 31, 2880), (Sum.inr 2086, 51840), (Sum.inr 2087, 51840), (Sum.inr 2094, 51840), (Sum.inr 2102, 51840), (Sum.inr 2251, 51840), (Sum.inr 2613, 51840), (Sum.inr 2620, 51840), (Sum.inr 2632, 51840), (Sum.inr 2729, 51840), (Sum.inr 3724, 51840), (Sum.inr 3733, 51840), (Sum.inr 3783, 51840), (Sum.inr 3785, 51840), (Sum.inr 3802, 51840), (Sum.inr 3811, 51840), (Sum.inr 3813, 51840), (Sum.inr 3827, 51840), (Sum.inr 3854, 51840), (Sum.inr 3866, 51840), (Sum.inr 3868, 51840), (Sum.inr 3876, 51840), (Sum.inr 3880, 51840), (Sum.inr 3884, 51840)]

def numericRow873 : Integer.Sparse Master := [(Sum.inl 0, -393), (Sum.inl 5, -60), (Sum.inl 2, -165), (Sum.inl 3, -1680), (Sum.inl 13, -240), (Sum.inl 23, 720), (Sum.inl 54, 720), (Sum.inl 12, -960), (Sum.inl 25, 720), (Sum.inl 26, -240), (Sum.inl 4, -720), (Sum.inl 27, 180), (Sum.inl 1, 480), (Sum.inr 2098, 12960), (Sum.inr 2099, 12960), (Sum.inr 2102, 12960), (Sum.inr 2108, 12960), (Sum.inr 2274, 12960), (Sum.inr 3501, 12960), (Sum.inr 3506, 12960), (Sum.inr 3538, 12960), (Sum.inr 3570, 12960), (Sum.inr 3730, 12960), (Sum.inr 3733, 12960), (Sum.inr 3761, 12960), (Sum.inr 3770, 12960), (Sum.inr 3771, 12960), (Sum.inr 3785, 12960), (Sum.inr 3788, 12960), (Sum.inr 3813, 12960), (Sum.inr 3832, 12960), (Sum.inr 3845, 12960), (Sum.inr 3868, 12960), (Sum.inr 3873, 12960), (Sum.inr 3877, 12960), (Sum.inr 3880, 12960), (Sum.inr 3881, 12960), (Sum.inr 3958, 12960)]

def numericRow874 : Integer.Sparse Master := [(Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 3720, 1), (Sum.inr 3733, 1), (Sum.inr 3845, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def numericRow875 : Integer.Sparse Master := [(Sum.inr 3174, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3809, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def numericRow876 : Integer.Sparse Master := [(Sum.inr 3040, 1), (Sum.inr 3730, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 3857, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

def numericRow877 : Integer.Sparse Master := [(Sum.inl 0, -824), (Sum.inl 5, -80), (Sum.inl 2, -420), (Sum.inl 51, 960), (Sum.inl 3, -960), (Sum.inl 13, -320), (Sum.inl 12, -640), (Sum.inl 4, -320), (Sum.inl 1, 1140), (Sum.inr 2491, 17280), (Sum.inr 2492, 17280), (Sum.inr 2499, 17280), (Sum.inr 2506, 17280), (Sum.inr 2607, 17280), (Sum.inr 2608, 17280), (Sum.inr 2633, 17280), (Sum.inr 2678, 17280), (Sum.inr 2774, 17280), (Sum.inr 3566, 17280), (Sum.inr 3570, 17280), (Sum.inr 3572, 17280), (Sum.inr 3575, 17280), (Sum.inr 3696, 17280), (Sum.inr 3699, 17280), (Sum.inr 3846, 17280), (Sum.inr 3850, 17280), (Sum.inr 3854, 17280), (Sum.inr 3870, 17280), (Sum.inr 3871, 17280), (Sum.inr 3878, 17280), (Sum.inr 3881, 17280), (Sum.inr 3886, 17280)]

def numericRow878 : Integer.Sparse Master := [(Sum.inl 0, -256), (Sum.inl 2, -170), (Sum.inl 3, -160), (Sum.inl 25, -480), (Sum.inl 26, -160), (Sum.inl 1, 110), (Sum.inr 2874, 8640), (Sum.inr 2875, 8640), (Sum.inr 2876, 8640), (Sum.inr 2885, 8640), (Sum.inr 3097, 8640), (Sum.inr 3384, 8640), (Sum.inr 3385, 8640), (Sum.inr 3386, 8640), (Sum.inr 3395, 8640), (Sum.inr 3447, 8640), (Sum.inr 3480, 8640), (Sum.inr 3578, 8640), (Sum.inr 3584, 8640), (Sum.inr 3752, 8640), (Sum.inr 3759, 8640), (Sum.inr 3767, 8640), (Sum.inr 3772, 8640), (Sum.inr 3809, 8640), (Sum.inr 3877, 8640), (Sum.inr 3954, 8640), (Sum.inr 3958, 8640), (Sum.inr 3959, 8640), (Sum.inr 3963, 8640), (Sum.inr 3972, 8640), (Sum.inr 4022, 8640)]

def numericRow879 : Integer.Sparse Master := [(Sum.inr 2882, 1), (Sum.inr 3705, 1), (Sum.inr 3884, 1), (Sum.inr 3961, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow880 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2871, 1), (Sum.inr 2873, 1), (Sum.inr 2882, 1), (Sum.inr 3044, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def numericRow881 : Integer.Sparse Master := [(Sum.inl 0, -87), (Sum.inl 12, 80), (Sum.inl 4, -80), (Sum.inl 1, 15), (Sum.inr 1913, 2160), (Sum.inr 1915, 2160), (Sum.inr 1917, 2160), (Sum.inr 1949, 2160), (Sum.inr 2266, 2160), (Sum.inr 2853, 2160), (Sum.inr 2856, 2160), (Sum.inr 2881, 2160), (Sum.inr 3077, 2160), (Sum.inr 3370, 2160), (Sum.inr 3372, 2160), (Sum.inr 3391, 2160), (Sum.inr 3564, 2160), (Sum.inr 3653, 2160), (Sum.inr 3666, 2160), (Sum.inr 3778, 2160), (Sum.inr 3782, 2160), (Sum.inr 3801, 2160), (Sum.inr 3804, 2160), (Sum.inr 3809, 6480), (Sum.inr 3815, 2160), (Sum.inr 3913, 2160), (Sum.inr 4010, 2160), (Sum.inr 4025, 2160)]

def numericRow882 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 2488, -4320), (Sum.inr 2515, -4320), (Sum.inr 3478, -4320), (Sum.inr 3479, -4320), (Sum.inr 3693, -4320), (Sum.inr 3706, -4320), (Sum.inr 3719, -4320), (Sum.inr 3732, -4320), (Sum.inr 3770, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3795, -4320), (Sum.inr 3796, -4320), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3811, -4320), (Sum.inr 3813, -4320), (Sum.inr 3814, -17280), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320), (Sum.inr 4852, 17280), (Sum.inr 4853, 17280), (Sum.inr 4856, 17280), (Sum.inr 4867, 17280), (Sum.inr 4891, 17280), (Sum.inr 5074, 17280), (Sum.inr 5260, 17280), (Sum.inr 5353, 17280), (Sum.inr 5402, 17280), (Sum.inr 5407, 17280), (Sum.inr 5425, 17280), (Sum.inr 5436, 17280), (Sum.inr 5445, 17280), (Sum.inr 5446, 34560)]

def numericRow883 : Integer.Sparse Master := [(Sum.inl 0, -154), (Sum.inl 2, -105), (Sum.inl 3, -480), (Sum.inl 13, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, 165), (Sum.inr 2250, 4320), (Sum.inr 2251, 4320), (Sum.inr 2253, 4320), (Sum.inr 2259, 4320), (Sum.inr 2274, 4320), (Sum.inr 3463, 4320), (Sum.inr 3478, 4320), (Sum.inr 3479, 4320), (Sum.inr 3540, 4320), (Sum.inr 3761, 4320), (Sum.inr 3770, 4320), (Sum.inr 3771, 4320), (Sum.inr 3795, 4320), (Sum.inr 3796, 4320), (Sum.inr 3800, 4320), (Sum.inr 3802, 4320), (Sum.inr 3803, 4320), (Sum.inr 3811, 4320), (Sum.inr 3814, 4320), (Sum.inr 3840, 4320), (Sum.inr 3854, 4320), (Sum.inr 3880, 4320), (Sum.inr 3881, 4320), (Sum.inr 3884, 4320)]

def numericRow884 : Integer.Sparse Master := [(Sum.inl 0, 30), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 4, -16), (Sum.inl 1, -29), (Sum.inr 2512, -864), (Sum.inr 3054, -864), (Sum.inr 3471, -864), (Sum.inr 3626, -864), (Sum.inr 3705, -864), (Sum.inr 3767, -864), (Sum.inr 3781, -864), (Sum.inr 3794, -864), (Sum.inr 3801, -864), (Sum.inr 3809, -864), (Sum.inr 3812, -864), (Sum.inr 3813, -864), (Sum.inr 3814, -1728), (Sum.inr 3903, -864), (Sum.inr 3906, -864), (Sum.inr 3907, -864), (Sum.inr 3913, -864), (Sum.inr 5085, 3456), (Sum.inr 5086, 3456), (Sum.inr 5087, 3456), (Sum.inr 5090, 6912), (Sum.inr 5103, 3456), (Sum.inr 5266, 3456), (Sum.inr 5286, 3456), (Sum.inr 5287, 3456), (Sum.inr 5289, 3456), (Sum.inr 5299, 3456), (Sum.inr 5359, 3456), (Sum.inr 5360, 3456), (Sum.inr 5361, 3456), (Sum.inr 5425, 3456), (Sum.inr 5430, 3456), (Sum.inr 5446, 3456)]

def numericRow885 : Integer.Sparse Master := [(Sum.inl 0, -30), (Sum.inl 2, -13), (Sum.inl 3, 16), (Sum.inl 4, 16), (Sum.inl 1, 29), (Sum.inr 3023, 864), (Sum.inr 3024, 864), (Sum.inr 3025, 864), (Sum.inr 3051, 864), (Sum.inr 3097, 864), (Sum.inr 3461, 864), (Sum.inr 3464, 864), (Sum.inr 3471, 864), (Sum.inr 3472, 864), (Sum.inr 3480, 1728), (Sum.inr 3535, 864), (Sum.inr 3626, 864), (Sum.inr 3759, 864), (Sum.inr 3762, 864), (Sum.inr 3767, 864), (Sum.inr 3772, 864), (Sum.inr 3794, 864), (Sum.inr 3801, 864), (Sum.inr 3809, 864), (Sum.inr 3814, 864), (Sum.inr 3839, 864), (Sum.inr 3959, 864), (Sum.inr 3972, 864)]

def numericRow886 : Integer.Sparse Master := [(Sum.inl 0, 8), (Sum.inl 2, -5), (Sum.inl 1, 15), (Sum.inr 3690, -720), (Sum.inr 3764, -720), (Sum.inr 3800, -360), (Sum.inr 3805, -360), (Sum.inr 3849, -360), (Sum.inr 3875, -360), (Sum.inr 3885, -720), (Sum.inr 3957, -1440), (Sum.inr 3958, -720), (Sum.inr 3961, -720), (Sum.inr 4010, -360), (Sum.inr 4046, -360), (Sum.inr 5064, 1440), (Sum.inr 5067, 1440), (Sum.inr 5071, 2880), (Sum.inr 5181, 1440), (Sum.inr 5185, 2880), (Sum.inr 5244, 1440), (Sum.inr 5282, 1440), (Sum.inr 5348, 1440), (Sum.inr 5350, 2880), (Sum.inr 5421, 2880), (Sum.inr 5429, 1440), (Sum.inr 5470, 2880), (Sum.inr 5480, 2880)]

def numericRow887 : Integer.Sparse Master := [(Sum.inl 0, -1140), (Sum.inl 5, -720), (Sum.inl 2, 2670), (Sum.inl 7, 960), (Sum.inl 8, 960), (Sum.inl 51, -2880), (Sum.inl 3, 6720), (Sum.inl 13, 480), (Sum.inl 24, -2880), (Sum.inl 12, 1920), (Sum.inl 4, 4800), (Sum.inl 27, 2880), (Sum.inl 1, -7110), (Sum.inl 30, -2880), (Sum.inl 31, -5760), (Sum.inr 2469, 25920), (Sum.inr 2473, 25920), (Sum.inr 2478, 51840), (Sum.inr 2609, 25920), (Sum.inr 2615, 51840), (Sum.inr 2698, 25920), (Sum.inr 2751, 25920), (Sum.inr 3685, 25920), (Sum.inr 3688, 51840), (Sum.inr 3846, 25920), (Sum.inr 3873, 51840), (Sum.inr 3875, 25920), (Sum.inr 3885, 25920), (Sum.inr 3947, 51840), (Sum.inr 3978, 51840)]

def numericRow888 : Integer.Sparse Master := [(Sum.inl 0, -103), (Sum.inl 2, 125), (Sum.inl 3, 560), (Sum.inl 12, 160), (Sum.inl 26, 160), (Sum.inl 4, 480), (Sum.inl 1, -560), (Sum.inr 3443, 4320), (Sum.inr 3445, 8640), (Sum.inr 3476, 4320), (Sum.inr 3491, 4320), (Sum.inr 3497, 4320), (Sum.inr 3529, 8640), (Sum.inr 3580, 4320), (Sum.inr 3750, 8640), (Sum.inr 3764, 8640), (Sum.inr 3768, 4320), (Sum.inr 3805, 4320), (Sum.inr 3874, 4320), (Sum.inr 3946, 8640), (Sum.inr 3955, 8640), (Sum.inr 3957, 8640), (Sum.inr 3961, 8640), (Sum.inr 3978, 8640)]

def numericRow889 : Integer.Sparse Master := [(Sum.inr 2981, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 2), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

def numericRow890 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 3689, -360), (Sum.inr 3703, -360), (Sum.inr 3757, -360), (Sum.inr 3758, -360), (Sum.inr 3786, -360), (Sum.inr 3799, -360), (Sum.inr 3800, -720), (Sum.inr 3805, -720), (Sum.inr 3845, -1440), (Sum.inr 3857, -720), (Sum.inr 3876, -720), (Sum.inr 3958, -720), (Sum.inr 3961, -720), (Sum.inr 4047, -720), (Sum.inr 5183, 2880), (Sum.inr 5187, 1440), (Sum.inr 5197, 1440), (Sum.inr 5263, 1440), (Sum.inr 5353, 2880), (Sum.inr 5399, 2880), (Sum.inr 5402, 2880), (Sum.inr 5414, 2880), (Sum.inr 5429, 1440), (Sum.inr 5446, 2880)]

def numericRow891 : Integer.Sparse Master := [(Sum.inl 0, -615), (Sum.inl 5, 120), (Sum.inl 6, -15), (Sum.inl 2, -195), (Sum.inl 7, 240), (Sum.inl 35, 240), (Sum.inl 3, 1680), (Sum.inl 13, 240), (Sum.inl 23, -720), (Sum.inl 54, -720), (Sum.inl 12, 480), (Sum.inl 25, -1440), (Sum.inl 26, 480), (Sum.inl 4, 480), (Sum.inl 27, -180), (Sum.inl 1, 555), (Sum.inr 3501, 25920), (Sum.inr 3505, 12960), (Sum.inr 3537, 12960), (Sum.inr 3569, 12960), (Sum.inr 3757, 12960), (Sum.inr 3758, 12960), (Sum.inr 3761, 25920), (Sum.inr 3785, 25920), (Sum.inr 3788, 25920), (Sum.inr 3800, 12960), (Sum.inr 3845, 25920), (Sum.inr 3869, 12960), (Sum.inr 3884, 25920), (Sum.inr 3949, 12960), (Sum.inr 3954, 12960), (Sum.inr 3958, 25920)]

def numericRow892 : Integer.Sparse Master := [(Sum.inl 0, -1992), (Sum.inl 5, -240), (Sum.inl 2, -930), (Sum.inl 7, 480), (Sum.inl 8, 480), (Sum.inl 51, -2880), (Sum.inl 3, 1920), (Sum.inl 13, 480), (Sum.inl 23, -1440), (Sum.inl 24, -1440), (Sum.inl 55, -2880), (Sum.inl 12, 960), (Sum.inl 4, 960), (Sum.inl 27, 720), (Sum.inl 1, 1230), (Sum.inr 2613, 51840), (Sum.inr 2617, 25920), (Sum.inr 2631, 25920), (Sum.inr 2728, 25920), (Sum.inr 3783, 51840), (Sum.inr 3785, 51840), (Sum.inr 3799, 25920), (Sum.inr 3800, 25920), (Sum.inr 3802, 51840), (Sum.inr 3846, 25920), (Sum.inr 3869, 25920), (Sum.inr 3876, 51840), (Sum.inr 3881, 51840), (Sum.inr 3949, 25920)]

def numericRow893 : Integer.Sparse Master := [(Sum.inr 3689, 1), (Sum.inr 3691, 2), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 4092, -1)]

def numericRow894 : Integer.Sparse Master := [(Sum.inl 0, -184), (Sum.inl 5, 40), (Sum.inl 6, -10), (Sum.inl 2, 500), (Sum.inl 51, -480), (Sum.inl 3, 2720), (Sum.inl 13, 320), (Sum.inl 52, 160), (Sum.inl 12, 1120), (Sum.inl 26, 160), (Sum.inl 4, 1760), (Sum.inl 1, -1570), (Sum.inl 31, -960), (Sum.inr 2453, 8640), (Sum.inr 2456, 8640), (Sum.inr 2460, 8640), (Sum.inr 2493, 8640), (Sum.inr 2533, 8640), (Sum.inr 2537, 8640), (Sum.inr 2567, 8640), (Sum.inr 2662, 8640), (Sum.inr 2731, 8640), (Sum.inr 3568, 8640), (Sum.inr 3569, 8640), (Sum.inr 3571, 8640), (Sum.inr 3574, 8640), (Sum.inr 3680, 8640), (Sum.inr 3697, 8640), (Sum.inr 3840, 8640), (Sum.inr 3848, 8640), (Sum.inr 3849, 8640), (Sum.inr 3879, 8640), (Sum.inr 3880, 17280), (Sum.inr 3884, 8640), (Sum.inr 3885, 8640)]

def numericRow895 : Integer.Sparse Master := [(Sum.inr 2976, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 2), (Sum.inr 3909, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow896 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 3719, -1440), (Sum.inr 3782, -1440), (Sum.inr 3795, -1440), (Sum.inr 3796, -1440), (Sum.inr 3809, -1440), (Sum.inr 3813, -1440), (Sum.inr 3838, -1440), (Sum.inr 3843, -1440), (Sum.inr 4047, -720), (Sum.inr 4848, 2880), (Sum.inr 4849, 5760), (Sum.inr 4852, 5760), (Sum.inr 5379, 5760), (Sum.inr 5381, 5760), (Sum.inr 5382, 5760), (Sum.inr 5420, 5760), (Sum.inr 5421, 5760), (Sum.inr 5425, 5760), (Sum.inr 5446, 5760)]

def numericRow897 : Integer.Sparse Master := [(Sum.inl 0, -171), (Sum.inl 6, -5), (Sum.inl 2, 5), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 51, -240), (Sum.inl 3, 1280), (Sum.inl 13, 240), (Sum.inl 52, 80), (Sum.inl 23, -480), (Sum.inl 54, -240), (Sum.inl 24, -240), (Sum.inl 55, -480), (Sum.inl 12, 480), (Sum.inl 25, -240), (Sum.inl 26, 240), (Sum.inl 4, 400), (Sum.inl 27, 60), (Sum.inl 1, 5), (Sum.inr 2085, 4320), (Sum.inr 2086, 4320), (Sum.inr 2089, 4320), (Sum.inr 2098, 4320), (Sum.inr 2250, 4320), (Sum.inr 3723, 4320), (Sum.inr 3724, 4320), (Sum.inr 3730, 4320), (Sum.inr 3795, 4320), (Sum.inr 3796, 4320), (Sum.inr 3813, 4320), (Sum.inr 3826, 4320), (Sum.inr 3827, 4320), (Sum.inr 3832, 4320), (Sum.inr 3834, 4320), (Sum.inr 3838, 4320), (Sum.inr 3840, 4320), (Sum.inr 3866, 4320), (Sum.inr 3870, 4320), (Sum.inr 3872, 4320), (Sum.inr 3873, 4320), (Sum.inr 3881, 4320), (Sum.inr 3884, 4320)]

def numericRow898 : Integer.Sparse Master := [(Sum.inl 0, 763), (Sum.inl 2, -120), (Sum.inl 4, 80), (Sum.inl 1, 645), (Sum.inr 2480, -4320), (Sum.inr 2482, -4320), (Sum.inr 2489, -4320), (Sum.inr 2512, -4320), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2723, -4320), (Sum.inr 3467, -4320), (Sum.inr 3468, -4320), (Sum.inr 3471, -4320), (Sum.inr 3482, -4320), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3544, -4320), (Sum.inr 3607, -4320), (Sum.inr 3627, -4320), (Sum.inr 3690, -4320), (Sum.inr 3694, -4320), (Sum.inr 3705, -4320), (Sum.inr 3764, -4320), (Sum.inr 3767, -4320), (Sum.inr 3773, -4320), (Sum.inr 3903, -4320), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4010, -4320), (Sum.inr 4042, -4320), (Sum.inr 4045, -4320), (Sum.inr 4046, -8640), (Sum.inr 4047, -8640)]

def numericRow899 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 2, 5), (Sum.inl 1, -20), (Sum.inr 2480, 180), (Sum.inr 2482, 180), (Sum.inr 2489, 180), (Sum.inr 2512, 180), (Sum.inr 2556, 180), (Sum.inr 2561, 180), (Sum.inr 2723, 180), (Sum.inr 3690, 180), (Sum.inr 3694, 180), (Sum.inr 3705, 180), (Sum.inr 3945, 180), (Sum.inr 3958, 180)]

def numericRow900 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 40), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -65), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -2160), (Sum.inr 5445, 8640), (Sum.inr 5446, 17280)]

def numericRow901 : Integer.Sparse Master := [(Sum.inl 0, 79), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 230), (Sum.inr 2480, -4320), (Sum.inr 3077, -2160), (Sum.inr 3467, -4320), (Sum.inr 3625, -2160), (Sum.inr 3690, -4320), (Sum.inr 3764, -4320), (Sum.inr 3787, -4320), (Sum.inr 3801, -2160), (Sum.inr 3804, -4320), (Sum.inr 3812, -2160), (Sum.inr 3901, -2160), (Sum.inr 3902, -2160), (Sum.inr 4010, -2160), (Sum.inr 4046, -2160), (Sum.inr 5065, 8640), (Sum.inr 5067, 17280), (Sum.inr 5074, 17280), (Sum.inr 5348, 8640), (Sum.inr 5353, 17280), (Sum.inr 5430, 17280), (Sum.inr 5480, 17280)]

def numericRow902 : Integer.Sparse Master := [(Sum.inl 0, -79), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -230), (Sum.inr 3463, 4320), (Sum.inr 3466, 2160), (Sum.inr 3467, 4320), (Sum.inr 3476, 4320), (Sum.inr 3625, 2160), (Sum.inr 3761, 4320), (Sum.inr 3764, 4320), (Sum.inr 3768, 2160), (Sum.inr 3804, 4320), (Sum.inr 3812, 2160), (Sum.inr 3848, 4320), (Sum.inr 3978, 4320)]

def numericRow903 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 2479, -2160), (Sum.inr 2508, -2160), (Sum.inr 3459, -2160), (Sum.inr 3460, -2160), (Sum.inr 3689, -2160), (Sum.inr 3703, -2160), (Sum.inr 3757, -2160), (Sum.inr 3758, -2160), (Sum.inr 3786, -2160), (Sum.inr 3799, -2160), (Sum.inr 3800, -2160), (Sum.inr 3801, -4320), (Sum.inr 3805, -2160), (Sum.inr 3809, -4320), (Sum.inr 3812, -4320), (Sum.inr 3813, -4320), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320), (Sum.inr 5074, 17280), (Sum.inr 5353, 17280), (Sum.inr 5402, 17280), (Sum.inr 5407, 17280), (Sum.inr 5429, 8640)]

def numericRow904 : Integer.Sparse Master := [(Sum.inl 0, -116), (Sum.inl 2, -25), (Sum.inl 3, 400), (Sum.inl 13, 160), (Sum.inl 12, 240), (Sum.inl 4, 80), (Sum.inl 1, -25), (Sum.inr 3459, 2160), (Sum.inr 3460, 2160), (Sum.inr 3463, 4320), (Sum.inr 3757, 2160), (Sum.inr 3758, 2160), (Sum.inr 3761, 4320), (Sum.inr 3799, 2160), (Sum.inr 3801, 2160), (Sum.inr 3802, 4320), (Sum.inr 3803, 4320), (Sum.inr 3813, 4320), (Sum.inr 3846, 2160)]

def numericRow905 : Integer.Sparse Master := [(Sum.inl 0, 41), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 70), (Sum.inr 2723, -2160), (Sum.inr 2954, -2160), (Sum.inr 3544, -2160), (Sum.inr 3606, -2160), (Sum.inr 3787, -2160), (Sum.inr 3790, -2160), (Sum.inr 3804, -2160), (Sum.inr 3815, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3849, -2160), (Sum.inr 3857, -2160), (Sum.inr 3875, -2160), (Sum.inr 3876, -2160), (Sum.inr 3885, -4320), (Sum.inr 3902, -2160), (Sum.inr 3983, -8640), (Sum.inr 4010, -2160), (Sum.inr 5138, 8640), (Sum.inr 5139, 8640), (Sum.inr 5140, 8640), (Sum.inr 5185, 8640), (Sum.inr 5189, 8640), (Sum.inr 5199, 8640), (Sum.inr 5226, 8640), (Sum.inr 5229, 8640), (Sum.inr 5236, 8640), (Sum.inr 5260, 8640), (Sum.inr 5289, 8640), (Sum.inr 5419, 8640), (Sum.inr 5421, 8640), (Sum.inr 5430, 8640), (Sum.inr 5446, 8640), (Sum.inr 5480, 8640)]

def numericRow906 : Integer.Sparse Master := [(Sum.inl 0, -194), (Sum.inl 2, 60), (Sum.inl 3, -640), (Sum.inl 12, -160), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, -290), (Sum.inr 2669, 8640), (Sum.inr 2670, 8640), (Sum.inr 2673, 8640), (Sum.inr 2682, 8640), (Sum.inr 2763, 8640), (Sum.inr 3517, 8640), (Sum.inr 3523, 8640), (Sum.inr 3529, 8640), (Sum.inr 3540, 8640), (Sum.inr 3542, 8640), (Sum.inr 3544, 8640), (Sum.inr 3578, 8640), (Sum.inr 3606, 8640), (Sum.inr 3804, 8640), (Sum.inr 3815, 8640), (Sum.inr 3842, 8640), (Sum.inr 3843, 8640), (Sum.inr 3848, 8640), (Sum.inr 3849, 8640), (Sum.inr 3857, 8640), (Sum.inr 3873, 8640), (Sum.inr 3884, 8640), (Sum.inr 3885, 8640), (Sum.inr 3978, 8640), (Sum.inr 3983, 8640)]

def numericRow907 : Integer.Sparse Master := [(Sum.inr 2621, 1), (Sum.inr 3115, 1), (Sum.inr 3790, 1), (Sum.inr 3825, 1), (Sum.inr 3876, 2), (Sum.inr 4091, -1)]

def numericRow908 : Integer.Sparse Master := [(Sum.inl 0, 1347), (Sum.inl 5, 60), (Sum.inl 2, 135), (Sum.inl 7, 240), (Sum.inl 3, 720), (Sum.inl 24, -720), (Sum.inl 12, 240), (Sum.inl 27, -180), (Sum.inl 1, -1680), (Sum.inr 2046, -12960), (Sum.inr 2047, -12960), (Sum.inr 2048, -12960), (Sum.inr 2058, -12960), (Sum.inr 2077, -12960), (Sum.inr 2079, -12960), (Sum.inr 2082, -12960), (Sum.inr 2107, -12960), (Sum.inr 2216, -12960), (Sum.inr 2260, -12960), (Sum.inr 2477, -12960), (Sum.inr 2488, -12960), (Sum.inr 2505, -12960), (Sum.inr 2765, -12960), (Sum.inr 3444, -12960), (Sum.inr 3448, -12960), (Sum.inr 3478, -12960), (Sum.inr 3582, -12960), (Sum.inr 3687, -12960), (Sum.inr 3693, -12960), (Sum.inr 3701, -12960), (Sum.inr 3702, -25920), (Sum.inr 3706, -12960), (Sum.inr 3721, -12960), (Sum.inr 3749, -12960), (Sum.inr 3751, -12960), (Sum.inr 3770, -12960), (Sum.inr 3771, -12960), (Sum.inr 3782, -12960), (Sum.inr 3787, -12960), (Sum.inr 3796, -12960), (Sum.inr 3804, -12960), (Sum.inr 3836, -12960), (Sum.inr 3849, -12960), (Sum.inr 3850, -25920), (Sum.inr 3857, -12960), (Sum.inr 3875, -12960), (Sum.inr 3876, -12960), (Sum.inr 3892, -12960), (Sum.inr 3903, -12960), (Sum.inr 3906, -12960), (Sum.inr 3907, -12960), (Sum.inr 3910, -12960), (Sum.inr 3913, -12960), (Sum.inr 3983, -25920)]

def numericRow909 : Integer.Sparse Master := [(Sum.inl 0, -810), (Sum.inl 5, -60), (Sum.inl 2, -45), (Sum.inl 7, -240), (Sum.inl 3, -720), (Sum.inl 24, 720), (Sum.inl 12, -240), (Sum.inl 4, -240), (Sum.inl 27, 180), (Sum.inl 1, 1185), (Sum.inr 2077, 12960), (Sum.inr 2079, 12960), (Sum.inr 2082, 12960), (Sum.inr 2107, 12960), (Sum.inr 2216, 12960), (Sum.inr 2477, 12960), (Sum.inr 2488, 12960), (Sum.inr 2505, 12960), (Sum.inr 2765, 12960), (Sum.inr 3687, 12960), (Sum.inr 3693, 12960), (Sum.inr 3702, 12960), (Sum.inr 3721, 12960), (Sum.inr 3751, 12960), (Sum.inr 3771, 12960), (Sum.inr 3787, 12960), (Sum.inr 3796, 12960), (Sum.inr 3850, 12960), (Sum.inr 3875, 12960), (Sum.inr 3876, 12960), (Sum.inr 3906, 12960), (Sum.inr 3907, 12960), (Sum.inr 3983, 12960)]

def numericRow910 : Integer.Sparse Master := [(Sum.inl 0, 66), (Sum.inl 2, 25), (Sum.inl 3, -160), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, -5), (Sum.inr 2590, -2160), (Sum.inr 2782, -2160), (Sum.inr 3564, -2160), (Sum.inr 3583, -2160), (Sum.inr 3732, -2160), (Sum.inr 3786, -2160), (Sum.inr 3799, -2160), (Sum.inr 3811, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3845, -8640), (Sum.inr 3850, -4320), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 4047, -2160), (Sum.inr 5160, 8640), (Sum.inr 5164, 8640), (Sum.inr 5173, 8640), (Sum.inr 5263, 8640), (Sum.inr 5264, 8640), (Sum.inr 5267, 8640), (Sum.inr 5299, 8640), (Sum.inr 5382, 8640), (Sum.inr 5385, 8640), (Sum.inr 5414, 8640), (Sum.inr 5425, 8640), (Sum.inr 5430, 8640), (Sum.inr 5436, 8640), (Sum.inr 5446, 8640)]

def numericRow911 : Integer.Sparse Master := [(Sum.inl 0, -390), (Sum.inl 2, -230), (Sum.inl 3, 160), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 200), (Sum.inl 31, 480), (Sum.inr 2728, 8640), (Sum.inr 2729, 8640), (Sum.inr 2732, 8640), (Sum.inr 2735, 8640), (Sum.inr 2773, 8640), (Sum.inr 3558, 8640), (Sum.inr 3564, 8640), (Sum.inr 3565, 8640), (Sum.inr 3583, 8640), (Sum.inr 3799, 8640), (Sum.inr 3811, 8640), (Sum.inr 3838, 8640), (Sum.inr 3845, 8640), (Sum.inr 3850, 8640), (Sum.inr 3866, 8640), (Sum.inr 3868, 8640), (Sum.inr 3869, 8640), (Sum.inr 3871, 8640), (Sum.inr 3872, 8640), (Sum.inr 3876, 8640), (Sum.inr 3877, 8640), (Sum.inr 3881, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow912 : Integer.Sparse Master := [(Sum.inl 0, 4974), (Sum.inl 5, -120), (Sum.inl 6, 30), (Sum.inl 2, -660), (Sum.inl 8, -960), (Sum.inl 3, -960), (Sum.inl 4, -1920), (Sum.inl 27, 360), (Sum.inl 1, 6240), (Sum.inl 30, 1440), (Sum.inr 2449, -25920), (Sum.inr 2452, -51840), (Sum.inr 2462, -51840), (Sum.inr 2480, -51840), (Sum.inr 2723, -51840), (Sum.inr 3432, -25920), (Sum.inr 3433, -51840), (Sum.inr 3436, -51840), (Sum.inr 3467, -51840), (Sum.inr 3544, -51840), (Sum.inr 3678, -25920), (Sum.inr 3683, -51840), (Sum.inr 3690, -51840), (Sum.inr 3744, -25920), (Sum.inr 3746, -51840), (Sum.inr 3764, -51840), (Sum.inr 3838, -51840), (Sum.inr 3843, -51840), (Sum.inr 3942, -51840), (Sum.inr 3958, -51840), (Sum.inr 3961, -51840), (Sum.inr 3974, -103680), (Sum.inr 4045, -25920), (Sum.inr 4046, -51840), (Sum.inr 4047, -51840)]

def numericRow913 : Integer.Sparse Master := [(Sum.inl 0, -3318), (Sum.inl 5, 120), (Sum.inl 6, -30), (Sum.inl 2, 660), (Sum.inl 8, 960), (Sum.inl 3, 960), (Sum.inl 4, 1920), (Sum.inl 27, -360), (Sum.inl 1, -4440), (Sum.inl 30, -1440), (Sum.inr 2449, 25920), (Sum.inr 2452, 51840), (Sum.inr 2462, 51840), (Sum.inr 2480, 51840), (Sum.inr 2723, 51840), (Sum.inr 3678, 25920), (Sum.inr 3683, 51840), (Sum.inr 3690, 51840), (Sum.inr 3838, 51840), (Sum.inr 3942, 25920), (Sum.inr 3958, 51840), (Sum.inr 3974, 51840)]

def numericRow914 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 3781, -4320), (Sum.inr 3782, -4320), (Sum.inr 3794, -4320), (Sum.inr 3796, -4320), (Sum.inr 3837, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3903, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -4320), (Sum.inr 5420, 8640), (Sum.inr 5421, 17280), (Sum.inr 5425, 17280), (Sum.inr 5430, 17280), (Sum.inr 5445, 17280)]

def numericRow915 : Integer.Sparse Master := [(Sum.inl 0, -141), (Sum.inl 2, -55), (Sum.inl 3, 480), (Sum.inl 12, 160), (Sum.inl 25, -120), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 10), (Sum.inr 3794, 4320), (Sum.inr 3796, 4320), (Sum.inr 3838, 4320), (Sum.inr 3870, 2160), (Sum.inr 3872, 4320), (Sum.inr 3873, 4320), (Sum.inr 3880, 4320), (Sum.inr 3958, 4320), (Sum.inr 3972, 4320)]

def numericRow916 : Integer.Sparse Master := [(Sum.inl 0, 40), (Sum.inl 2, -30), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, 210), (Sum.inr 2556, -2160), (Sum.inr 2723, -2160), (Sum.inr 2924, -2160), (Sum.inr 3521, -2160), (Sum.inr 3544, -2160), (Sum.inr 3605, -2160), (Sum.inr 3721, -2160), (Sum.inr 3779, -2160), (Sum.inr 3797, -2160), (Sum.inr 3836, -2160), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3849, -2160), (Sum.inr 3857, -2160), (Sum.inr 3875, -2160), (Sum.inr 3876, -2160), (Sum.inr 3902, -2160), (Sum.inr 3974, -4320), (Sum.inr 4046, -2160), (Sum.inr 5128, 8640), (Sum.inr 5129, 8640), (Sum.inr 5138, 8640), (Sum.inr 5145, 8640), (Sum.inr 5251, 8640), (Sum.inr 5377, 8640), (Sum.inr 5379, 8640), (Sum.inr 5419, 8640), (Sum.inr 5421, 8640), (Sum.inr 5429, 8640), (Sum.inr 5430, 8640), (Sum.inr 5480, 8640)]

def numericRow917 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 2, 30), (Sum.inl 12, -40), (Sum.inl 4, 80), (Sum.inl 1, -210), (Sum.inr 3516, 2160), (Sum.inr 3517, 2160), (Sum.inr 3519, 2160), (Sum.inr 3521, 2160), (Sum.inr 3539, 2160), (Sum.inr 3544, 2160), (Sum.inr 3562, 2160), (Sum.inr 3605, 2160), (Sum.inr 3797, 2160), (Sum.inr 3832, 2160), (Sum.inr 3835, 2160), (Sum.inr 3836, 2160), (Sum.inr 3842, 2160), (Sum.inr 3843, 4320), (Sum.inr 3848, 2160), (Sum.inr 3857, 2160), (Sum.inr 3873, 2160), (Sum.inr 3874, 2160), (Sum.inr 3875, 2160), (Sum.inr 3974, 2160), (Sum.inr 3978, 2160)]

def numericRow918 : Integer.Sparse Master := [(Sum.inl 0, 1662), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -510), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -1920), (Sum.inl 24, 720), (Sum.inl 12, -720), (Sum.inl 4, -2160), (Sum.inl 27, 180), (Sum.inl 1, 2445), (Sum.inr 1987, -12960), (Sum.inr 1990, -12960), (Sum.inr 1996, -12960), (Sum.inr 1997, -12960), (Sum.inr 2000, -25920), (Sum.inr 2020, -12960), (Sum.inr 2051, -12960), (Sum.inr 2191, -12960), (Sum.inr 2202, -12960), (Sum.inr 2452, -12960), (Sum.inr 2459, -12960), (Sum.inr 2479, -12960), (Sum.inr 2722, -12960), (Sum.inr 3429, -12960), (Sum.inr 3433, -12960), (Sum.inr 3459, -12960), (Sum.inr 3533, -12960), (Sum.inr 3678, -12960), (Sum.inr 3681, -25920), (Sum.inr 3683, -25920), (Sum.inr 3689, -12960), (Sum.inr 3690, -12960), (Sum.inr 3703, -12960), (Sum.inr 3744, -12960), (Sum.inr 3746, -25920), (Sum.inr 3757, -12960), (Sum.inr 3758, -12960), (Sum.inr 3764, -12960), (Sum.inr 3837, -25920), (Sum.inr 3838, -25920), (Sum.inr 3843, -25920), (Sum.inr 3845, -25920), (Sum.inr 3896, -12960), (Sum.inr 3901, -25920), (Sum.inr 3902, -12960), (Sum.inr 3903, -12960), (Sum.inr 3974, -25920), (Sum.inr 4046, -12960)]

def numericRow919 : Integer.Sparse Master := [(Sum.inl 0, -993), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 2, 360), (Sum.inl 7, 240), (Sum.inl 8, 240), (Sum.inl 3, 1440), (Sum.inl 24, -720), (Sum.inl 12, 480), (Sum.inl 4, 1440), (Sum.inl 27, -180), (Sum.inl 1, -1200), (Sum.inr 1987, 12960), (Sum.inr 1990, 12960), (Sum.inr 2000, 12960), (Sum.inr 2020, 12960), (Sum.inr 2191, 12960), (Sum.inr 2452, 12960), (Sum.inr 2459, 12960), (Sum.inr 2479, 12960), (Sum.inr 2722, 12960), (Sum.inr 3678, 12960), (Sum.inr 3681, 12960), (Sum.inr 3683, 12960), (Sum.inr 3689, 12960), (Sum.inr 3690, 12960), (Sum.inr 3746, 12960), (Sum.inr 3758, 12960), (Sum.inr 3837, 12960), (Sum.inr 3838, 12960), (Sum.inr 3843, 12960), (Sum.inr 3845, 12960), (Sum.inr 3901, 12960), (Sum.inr 3902, 12960), (Sum.inr 3974, 12960)]

def numericRow920 : Integer.Sparse Master := [(Sum.inl 0, 150), (Sum.inl 2, 75), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -255), (Sum.inr 2553, -4320), (Sum.inr 2739, -4320), (Sum.inr 3514, -4320), (Sum.inr 3534, -4320), (Sum.inr 3719, -4320), (Sum.inr 3781, -4320), (Sum.inr 3782, -4320), (Sum.inr 3794, -4320), (Sum.inr 3795, -4320), (Sum.inr 3796, -4320), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 4047, -4320), (Sum.inr 5138, 17280), (Sum.inr 5160, 17280), (Sum.inr 5379, 17280), (Sum.inr 5381, 17280), (Sum.inr 5382, 17280), (Sum.inr 5425, 51840), (Sum.inr 5426, 17280), (Sum.inr 5430, 17280), (Sum.inr 5445, 17280)]

def numericRow921 : Integer.Sparse Master := [(Sum.inl 0, -328), (Sum.inl 2, -100), (Sum.inl 3, 320), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 340), (Sum.inr 3514, 8640), (Sum.inr 3517, 8640), (Sum.inr 3534, 8640), (Sum.inr 3558, 8640), (Sum.inr 3794, 8640), (Sum.inr 3795, 8640), (Sum.inr 3796, 8640), (Sum.inr 3832, 8640), (Sum.inr 3834, 8640), (Sum.inr 3837, 8640), (Sum.inr 3839, 8640), (Sum.inr 3840, 8640), (Sum.inr 3841, 8640), (Sum.inr 3845, 8640), (Sum.inr 3866, 8640), (Sum.inr 3871, 8640), (Sum.inr 3872, 8640), (Sum.inr 3876, 8640), (Sum.inr 3880, 8640)]

def numericRow922 : Integer.Sparse Master := [(Sum.inl 0, 23), (Sum.inl 1, 25), (Sum.inr 3607, -1440), (Sum.inr 3608, -360), (Sum.inr 3616, -720), (Sum.inr 3627, -720), (Sum.inr 4042, -1440), (Sum.inr 4043, -360), (Sum.inr 4045, -720), (Sum.inr 4047, -1440)]

def numericRow923 : Integer.Sparse Master := [(Sum.inl 0, 113), (Sum.inl 4, -80), (Sum.inl 1, -105), (Sum.inr 3607, -4320), (Sum.inr 3613, -4320), (Sum.inr 3614, -2160), (Sum.inr 3615, -2160), (Sum.inr 3616, -2160), (Sum.inr 3632, -2160), (Sum.inr 3892, -4320), (Sum.inr 3894, -2160), (Sum.inr 3896, -4320), (Sum.inr 3898, -4320), (Sum.inr 3903, -4320), (Sum.inr 3913, -2160), (Sum.inr 4010, -4320)]

def numericRow924 : Integer.Sparse Master := [(Sum.inl 0, 83), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 80), (Sum.inl 4, 320), (Sum.inl 1, -150), (Sum.inr 2884, -4320), (Sum.inr 2931, -4320), (Sum.inr 3612, -4320), (Sum.inr 3621, -4320), (Sum.inr 3690, -4320), (Sum.inr 3694, -4320), (Sum.inr 3764, -4320), (Sum.inr 3773, -4320), (Sum.inr 3885, -8640), (Sum.inr 3910, -4320), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3957, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3974, -8640), (Sum.inr 3983, -8640), (Sum.inr 4010, -4320), (Sum.inr 5145, 17280), (Sum.inr 5147, 17280), (Sum.inr 5164, 17280), (Sum.inr 5185, 17280), (Sum.inr 5189, 17280), (Sum.inr 5266, 17280), (Sum.inr 5282, 17280), (Sum.inr 5445, 17280), (Sum.inr 5446, 17280), (Sum.inr 5463, 17280), (Sum.inr 5470, 17280)]

def numericRow925 : Integer.Sparse Master := [(Sum.inl 0, -91), (Sum.inl 2, 35), (Sum.inl 3, -400), (Sum.inl 12, -240), (Sum.inl 25, 240), (Sum.inl 4, -320), (Sum.inl 1, 50), (Sum.inr 3529, 4320), (Sum.inr 3530, 4320), (Sum.inr 3535, 4320), (Sum.inr 3542, 4320), (Sum.inr 3562, 4320), (Sum.inr 3565, 4320), (Sum.inr 3580, 4320), (Sum.inr 3612, 4320), (Sum.inr 3621, 4320), (Sum.inr 3764, 4320), (Sum.inr 3773, 4320), (Sum.inr 3952, 4320), (Sum.inr 3955, 4320), (Sum.inr 3957, 4320), (Sum.inr 3959, 4320), (Sum.inr 3960, 4320), (Sum.inr 3961, 8640), (Sum.inr 3974, 4320), (Sum.inr 3983, 4320), (Sum.inr 4024, 4320)]

def numericRow926 : Integer.Sparse Master := [(Sum.inl 0, 571), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, 10), (Sum.inr 2383, -4320), (Sum.inr 2385, -4320), (Sum.inr 2388, -4320), (Sum.inr 2398, -4320), (Sum.inr 2399, -4320), (Sum.inr 2400, -4320), (Sum.inr 2404, -8640), (Sum.inr 2462, -4320), (Sum.inr 2467, -4320), (Sum.inr 2512, -4320), (Sum.inr 2723, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -4320), (Sum.inr 3341, -4320), (Sum.inr 3344, -4320), (Sum.inr 3352, -4320), (Sum.inr 3353, -4320), (Sum.inr 3354, -4320), (Sum.inr 3357, -8640), (Sum.inr 3436, -4320), (Sum.inr 3471, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3548, -4320), (Sum.inr 3683, -4320), (Sum.inr 3705, -4320), (Sum.inr 3746, -4320), (Sum.inr 3767, -4320), (Sum.inr 3845, -8640), (Sum.inr 3942, -8640), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3957, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3963, -8640), (Sum.inr 3974, -8640), (Sum.inr 4010, -4320), (Sum.inr 4047, -4320)]

def numericRow927 : Integer.Sparse Master := [(Sum.inl 0, -343), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 50), (Sum.inr 2383, 4320), (Sum.inr 2385, 4320), (Sum.inr 2388, 4320), (Sum.inr 2404, 4320), (Sum.inr 2462, 4320), (Sum.inr 2467, 4320), (Sum.inr 2512, 4320), (Sum.inr 2723, 4320), (Sum.inr 2743, 4320), (Sum.inr 3341, 4320), (Sum.inr 3344, 4320), (Sum.inr 3357, 4320), (Sum.inr 3534, 4320), (Sum.inr 3683, 4320), (Sum.inr 3705, 4320), (Sum.inr 3845, 4320), (Sum.inr 3942, 4320), (Sum.inr 3945, 4320), (Sum.inr 3957, 4320), (Sum.inr 3958, 4320), (Sum.inr 3961, 4320), (Sum.inr 3963, 4320), (Sum.inr 3974, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow928 : Integer.Sparse Master := [(Sum.inl 0, 30), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 4, -16), (Sum.inl 1, -29), (Sum.inr 2881, -864), (Sum.inr 3624, -864), (Sum.inr 3703, -864), (Sum.inr 3705, -864), (Sum.inr 3706, -864), (Sum.inr 3758, -864), (Sum.inr 3767, -864), (Sum.inr 3771, -864), (Sum.inr 3781, -864), (Sum.inr 3794, -864), (Sum.inr 3845, -1728), (Sum.inr 3850, -1728), (Sum.inr 3857, -864), (Sum.inr 3876, -864), (Sum.inr 3903, -864), (Sum.inr 3913, -864), (Sum.inr 3958, -864), (Sum.inr 3961, -864), (Sum.inr 3963, -1728), (Sum.inr 4047, -864), (Sum.inr 5197, 3456), (Sum.inr 5198, 3456), (Sum.inr 5199, 3456), (Sum.inr 5299, 3456), (Sum.inr 5421, 3456), (Sum.inr 5429, 3456), (Sum.inr 5430, 3456), (Sum.inr 5436, 3456), (Sum.inr 5446, 6912)]

def numericRow929 : Integer.Sparse Master := [(Sum.inl 0, -194), (Sum.inl 2, -100), (Sum.inl 3, -320), (Sum.inl 12, -80), (Sum.inl 25, 240), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, 270), (Sum.inr 3569, 4320), (Sum.inr 3570, 4320), (Sum.inr 3573, 4320), (Sum.inr 3578, 4320), (Sum.inr 3624, 4320), (Sum.inr 3758, 4320), (Sum.inr 3767, 4320), (Sum.inr 3771, 4320), (Sum.inr 3794, 4320), (Sum.inr 3845, 4320), (Sum.inr 3873, 4320), (Sum.inr 3877, 4320), (Sum.inr 3884, 4320), (Sum.inr 3954, 4320), (Sum.inr 3958, 4320), (Sum.inr 3959, 4320), (Sum.inr 3963, 4320), (Sum.inr 3972, 4320)]

def numericRow930 : Integer.Sparse Master := [(Sum.inl 0, 41), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 70), (Sum.inr 2480, -2160), (Sum.inr 2485, -2160), (Sum.inr 2489, -2160), (Sum.inr 2723, -2160), (Sum.inr 2924, -2160), (Sum.inr 2931, -2160), (Sum.inr 2954, -2160), (Sum.inr 3077, -2160), (Sum.inr 3467, -2160), (Sum.inr 3481, -2160), (Sum.inr 3482, -2160), (Sum.inr 3544, -2160), (Sum.inr 3605, -2160), (Sum.inr 3606, -2160), (Sum.inr 3612, -2160), (Sum.inr 3625, -2160), (Sum.inr 3690, -2160), (Sum.inr 3694, -2160), (Sum.inr 3764, -2160), (Sum.inr 3773, -2160), (Sum.inr 3779, -2160), (Sum.inr 3787, -2160), (Sum.inr 3790, -2160), (Sum.inr 3797, -2160), (Sum.inr 3800, -2160), (Sum.inr 3804, -2160), (Sum.inr 3805, -2160), (Sum.inr 3815, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3902, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 3974, -4320), (Sum.inr 3983, -4320), (Sum.inr 4010, -2160), (Sum.inr 4091, 8640)]

def numericRow931 : Integer.Sparse Master := [(Sum.inl 0, 99), (Sum.inl 2, 50), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -145), (Sum.inr 2508, -2160), (Sum.inr 2512, -2160), (Sum.inr 2515, -2160), (Sum.inr 2739, -2160), (Sum.inr 3460, -2160), (Sum.inr 3471, -2160), (Sum.inr 3479, -2160), (Sum.inr 3534, -2160), (Sum.inr 3703, -2160), (Sum.inr 3705, -2160), (Sum.inr 3706, -2160), (Sum.inr 3758, -2160), (Sum.inr 3767, -2160), (Sum.inr 3771, -2160), (Sum.inr 3781, -2160), (Sum.inr 3782, -2160), (Sum.inr 3794, -2160), (Sum.inr 3796, -2160), (Sum.inr 3800, -2160), (Sum.inr 3801, -2160), (Sum.inr 3805, -2160), (Sum.inr 3809, -4320), (Sum.inr 3812, -2160), (Sum.inr 3813, -4320), (Sum.inr 3814, -4320), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3903, -4320), (Sum.inr 3906, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 4047, -2160), (Sum.inr 4092, 8640)]

def numericRow932 : Integer.Sparse Master := [(Sum.inl 0, 24), (Sum.inl 2, 10), (Sum.inl 3, -40), (Sum.inl 12, -40), (Sum.inl 1, 10), (Sum.inr 2561, -1080), (Sum.inr 2743, -1080), (Sum.inr 2881, -1080), (Sum.inr 3522, -1080), (Sum.inr 3548, -1080), (Sum.inr 3624, -1080), (Sum.inr 3689, -1080), (Sum.inr 3693, -1080), (Sum.inr 3757, -1080), (Sum.inr 3770, -1080), (Sum.inr 3781, -1080), (Sum.inr 3794, -1080), (Sum.inr 3838, -1080), (Sum.inr 3843, -1080), (Sum.inr 3845, -2160), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3907, -1080), (Sum.inr 3958, -1080), (Sum.inr 3961, -1080), (Sum.inr 4047, -1080), (Sum.inr 5139, 4320), (Sum.inr 5164, 4320), (Sum.inr 5187, 4320), (Sum.inr 5188, 4320), (Sum.inr 5267, 4320), (Sum.inr 5379, 4320), (Sum.inr 5385, 4320), (Sum.inr 5414, 4320), (Sum.inr 5425, 4320), (Sum.inr 5436, 4320), (Sum.inr 5446, 4320)]

def numericRow933 : Integer.Sparse Master := [(Sum.inl 0, -232), (Sum.inl 2, -90), (Sum.inl 3, -160), (Sum.inl 12, 160), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, 70), (Sum.inr 3522, 8640), (Sum.inr 3523, 8640), (Sum.inr 3537, 8640), (Sum.inr 3538, 8640), (Sum.inr 3541, 8640), (Sum.inr 3548, 8640), (Sum.inr 3565, 8640), (Sum.inr 3624, 8640), (Sum.inr 3757, 8640), (Sum.inr 3770, 8640), (Sum.inr 3794, 8640), (Sum.inr 3832, 8640), (Sum.inr 3838, 8640), (Sum.inr 3839, 8640), (Sum.inr 3845, 8640), (Sum.inr 3868, 8640), (Sum.inr 3869, 8640), (Sum.inr 3876, 8640), (Sum.inr 3877, 8640), (Sum.inr 3884, 8640), (Sum.inr 3958, 8640)]

def numericRow934 : Integer.Sparse Master := [(Sum.inl 0, 215), (Sum.inl 2, 20), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 240), (Sum.inl 1, 5), (Sum.inr 2000, -4320), (Sum.inr 2003, -4320), (Sum.inr 2006, -4320), (Sum.inr 2054, -4320), (Sum.inr 2206, -4320), (Sum.inr 2382, -4320), (Sum.inr 2388, -4320), (Sum.inr 2400, -4320), (Sum.inr 2722, -4320), (Sum.inr 3340, -4320), (Sum.inr 3344, -4320), (Sum.inr 3354, -4320), (Sum.inr 3533, -4320), (Sum.inr 3683, -4320), (Sum.inr 3705, -4320), (Sum.inr 3746, -4320), (Sum.inr 3767, -4320), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320), (Sum.inr 3957, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320)]

def numericRow935 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 2889, -2160), (Sum.inr 3631, -2160), (Sum.inr 3705, -4320), (Sum.inr 3767, -4320), (Sum.inr 3886, -2160), (Sum.inr 3913, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 5199, 17280), (Sum.inr 5201, 4320), (Sum.inr 5300, 8640), (Sum.inr 5446, 17280)]

def numericRow936 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, -10), (Sum.inl 3, 80), (Sum.inl 25, -120), (Sum.inl 4, 80), (Sum.inl 1, 5), (Sum.inr 3578, 4320), (Sum.inr 3579, 1080), (Sum.inr 3584, 2160), (Sum.inr 3631, 2160), (Sum.inr 3767, 4320), (Sum.inr 3958, 4320), (Sum.inr 3959, 4320)]

def numericRow937 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 4, -80), (Sum.inl 1, 105), (Sum.inr 2404, -4320), (Sum.inr 2407, -1080), (Sum.inr 2410, -2160), (Sum.inr 2743, -2160), (Sum.inr 3357, -4320), (Sum.inr 3360, -1080), (Sum.inr 3548, -2160), (Sum.inr 3942, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320)]

def numericRow938 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 2765, -2160), (Sum.inr 3582, -2160), (Sum.inr 3850, -8640), (Sum.inr 3913, -2160), (Sum.inr 3963, -2160), (Sum.inr 5198, 17280), (Sum.inr 5201, 4320), (Sum.inr 5206, 8640), (Sum.inr 5233, 17280), (Sum.inr 5235, 4320), (Sum.inr 5300, 8640), (Sum.inr 5420, 8640), (Sum.inr 5446, 17280)]

def numericRow939 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -40), (Sum.inl 3, 320), (Sum.inl 4, 320), (Sum.inl 1, 130), (Sum.inl 31, -480), (Sum.inr 2678, 17280), (Sum.inr 2680, 4320), (Sum.inr 2687, 8640), (Sum.inr 2774, 8640), (Sum.inr 3570, 17280), (Sum.inr 3579, 4320), (Sum.inr 3582, 8640), (Sum.inr 3850, 17280), (Sum.inr 3870, 8640), (Sum.inr 3881, 17280)]

def numericRow940 : Integer.Sparse Master := [(Sum.inl 0, 198), (Sum.inl 2, 30), (Sum.inl 3, -480), (Sum.inl 23, 720), (Sum.inl 12, -480), (Sum.inl 27, 180), (Sum.inl 1, 1020), (Sum.inr 2101, -25920), (Sum.inr 2103, -6480), (Sum.inr 2115, -12960), (Sum.inr 2276, -12960), (Sum.inr 3732, -25920), (Sum.inr 3784, -12960), (Sum.inr 3811, -25920), (Sum.inr 3885, -25920), (Sum.inr 3893, -6480), (Sum.inr 3907, -12960)]

def numericRow941 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -85), (Sum.inr 2590, -4320), (Sum.inr 2722, -4320), (Sum.inr 2765, -4320), (Sum.inr 3533, -4320), (Sum.inr 3564, -4320), (Sum.inr 3582, -4320), (Sum.inr 3732, -4320), (Sum.inr 3786, -4320), (Sum.inr 3799, -4320), (Sum.inr 3811, -4320), (Sum.inr 3837, -8640), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3886, -8640), (Sum.inr 3903, -4320), (Sum.inr 3913, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 5144, 17280), (Sum.inr 5147, 17280), (Sum.inr 5151, 17280), (Sum.inr 5184, 17280), (Sum.inr 5188, 17280), (Sum.inr 5198, 17280), (Sum.inr 5231, 17280), (Sum.inr 5232, 17280), (Sum.inr 5233, 17280), (Sum.inr 5299, 17280), (Sum.inr 5381, 17280), (Sum.inr 5420, 17280), (Sum.inr 5429, 17280), (Sum.inr 5430, 17280), (Sum.inr 5436, 17280), (Sum.inr 5446, 17280)]

def numericRow942 : Integer.Sparse Master := [(Sum.inl 0, -230), (Sum.inl 2, -100), (Sum.inl 1, 210), (Sum.inl 31, 480), (Sum.inr 2676, 8640), (Sum.inr 2677, 8640), (Sum.inr 2678, 8640), (Sum.inr 2681, 8640), (Sum.inr 2773, 8640), (Sum.inr 3524, 8640), (Sum.inr 3530, 8640), (Sum.inr 3533, 8640), (Sum.inr 3538, 8640), (Sum.inr 3557, 8640), (Sum.inr 3564, 8640), (Sum.inr 3570, 8640), (Sum.inr 3582, 8640), (Sum.inr 3799, 8640), (Sum.inr 3811, 8640), (Sum.inr 3834, 8640), (Sum.inr 3837, 8640), (Sum.inr 3846, 8640), (Sum.inr 3850, 8640), (Sum.inr 3854, 8640), (Sum.inr 3870, 8640), (Sum.inr 3871, 8640), (Sum.inr 3876, 8640), (Sum.inr 3881, 8640), (Sum.inr 3886, 8640)]

def numericRow943 : Integer.Sparse Master := [(Sum.inl 0, 501), (Sum.inl 5, 60), (Sum.inl 7, 240), (Sum.inl 3, 1440), (Sum.inl 23, -720), (Sum.inl 12, 960), (Sum.inl 4, 720), (Sum.inl 27, -180), (Sum.inl 1, -645), (Sum.inr 2016, -12960), (Sum.inr 2018, -12960), (Sum.inr 2028, -12960), (Sum.inr 2048, -12960), (Sum.inr 2075, -12960), (Sum.inr 2082, -12960), (Sum.inr 2106, -12960), (Sum.inr 2215, -12960), (Sum.inr 2242, -12960), (Sum.inr 3687, -12960), (Sum.inr 3693, -12960), (Sum.inr 3702, -12960), (Sum.inr 3719, -12960), (Sum.inr 3749, -12960), (Sum.inr 3770, -12960), (Sum.inr 3786, -12960), (Sum.inr 3795, -12960), (Sum.inr 3799, -12960), (Sum.inr 3849, -12960), (Sum.inr 3850, -12960), (Sum.inr 3857, -12960), (Sum.inr 3875, -12960), (Sum.inr 3876, -12960), (Sum.inr 3891, -12960), (Sum.inr 3906, -12960), (Sum.inr 3910, -12960)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow944 : Integer.Sparse Master := [(Sum.inl 0, 48), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 2553, -4320), (Sum.inr 2722, -4320), (Sum.inr 3514, -4320), (Sum.inr 3533, -4320), (Sum.inr 3719, -4320), (Sum.inr 3795, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3850, -8640), (Sum.inr 3903, -4320), (Sum.inr 5129, 17280), (Sum.inr 5144, 17280), (Sum.inr 5376, 8640), (Sum.inr 5381, 17280), (Sum.inr 5420, 8640), (Sum.inr 5425, 17280), (Sum.inr 5430, 17280)]

def numericRow945 : Integer.Sparse Master := [(Sum.inl 0, -48), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 35), (Sum.inr 3514, 4320), (Sum.inr 3516, 4320), (Sum.inr 3533, 4320), (Sum.inr 3557, 4320), (Sum.inr 3795, 4320), (Sum.inr 3833, 2160), (Sum.inr 3834, 4320), (Sum.inr 3838, 4320), (Sum.inr 3840, 4320), (Sum.inr 3850, 4320), (Sum.inr 3870, 2160), (Sum.inr 3871, 4320)]

def numericRow946 : Integer.Sparse Master := [(Sum.inl 0, 117), (Sum.inl 5, -12), (Sum.inl 6, 3), (Sum.inl 2, -42), (Sum.inl 7, -96), (Sum.inl 3, -480), (Sum.inl 23, 144), (Sum.inl 12, -288), (Sum.inl 4, -288), (Sum.inl 27, 36), (Sum.inl 1, 366), (Sum.inr 1986, -2592), (Sum.inr 1990, -5184), (Sum.inr 1997, -5184), (Sum.inr 2019, -5184), (Sum.inr 2190, -5184), (Sum.inr 3678, -2592), (Sum.inr 3681, -5184), (Sum.inr 3689, -5184), (Sum.inr 3744, -2592), (Sum.inr 3757, -5184), (Sum.inr 3837, -5184), (Sum.inr 3838, -5184), (Sum.inr 3843, -5184), (Sum.inr 3895, -2592), (Sum.inr 3901, -5184)]

def numericRow947 : Integer.Sparse Master := [(Sum.inl 0, 2), (Sum.inl 1, 10), (Sum.inr 3603, -180), (Sum.inr 3608, -45), (Sum.inr 3614, -90), (Sum.inr 3891, -180), (Sum.inr 3893, -45), (Sum.inr 3895, -90), (Sum.inr 3902, -180), (Sum.inr 3907, -90)]

def numericRow948 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 2479, -4320), (Sum.inr 2482, -4320), (Sum.inr 2488, -4320), (Sum.inr 2553, -4320), (Sum.inr 2561, -4320), (Sum.inr 2590, -4320), (Sum.inr 2722, -4320), (Sum.inr 3459, -4320), (Sum.inr 3468, -4320), (Sum.inr 3478, -4320), (Sum.inr 3514, -4320), (Sum.inr 3522, -4320), (Sum.inr 3533, -4320), (Sum.inr 3564, -4320), (Sum.inr 3689, -4320), (Sum.inr 3693, -4320), (Sum.inr 3719, -4320), (Sum.inr 3732, -4320), (Sum.inr 3757, -4320), (Sum.inr 3770, -4320), (Sum.inr 3786, -4320), (Sum.inr 3795, -4320), (Sum.inr 3799, -4320), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3811, -4320), (Sum.inr 3813, -4320), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320), (Sum.inr 4092, 17280)]

def numericRow949 : Integer.Sparse Master := [(Sum.inl 0, -61), (Sum.inl 1, -35), (Sum.inr 4080, 1440), (Sum.inr 4081, 360), (Sum.inr 4082, 720), (Sum.inr 4084, 720), (Sum.inr 4088, 1440), (Sum.inr 4089, 360), (Sum.inr 4090, 720), (Sum.inr 4091, 1440), (Sum.inr 4092, 2160)]

def numericRow950 : Integer.Sparse Master := [(Sum.inl 0, 613), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 12, -400), (Sum.inl 1, 2910), (Sum.inr 2954, -8640), (Sum.inr 3603, -4320), (Sum.inr 3606, -8640), (Sum.inr 3623, -4320), (Sum.inr 3731, -4320), (Sum.inr 3732, -8640), (Sum.inr 3789, -8640), (Sum.inr 3810, -8640), (Sum.inr 3811, -8640), (Sum.inr 3814, -17280), (Sum.inr 3867, -4320), (Sum.inr 3885, -8640), (Sum.inr 3891, -4320), (Sum.inr 3895, -4320), (Sum.inr 3899, -8640), (Sum.inr 3902, -17280), (Sum.inr 3907, -8640)]

def numericRow951 : Integer.Sparse Master := [(Sum.inl 0, 773), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, 20), (Sum.inl 7, -320), (Sum.inl 8, -160), (Sum.inl 3, -320), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, 240), (Sum.inl 4, 160), (Sum.inl 27, 180), (Sum.inl 1, -1080), (Sum.inr 2924, -8640), (Sum.inr 3602, -4320), (Sum.inr 3605, -8640), (Sum.inr 3622, -4320), (Sum.inr 3719, -8640), (Sum.inr 3721, -4320), (Sum.inr 3782, -8640), (Sum.inr 3795, -8640), (Sum.inr 3796, -8640), (Sum.inr 3801, -8640), (Sum.inr 3812, -8640), (Sum.inr 3836, -4320), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3890, -4320), (Sum.inr 3900, -4320), (Sum.inr 3901, -4320), (Sum.inr 3903, -8640), (Sum.inr 3906, -8640), (Sum.inr 3910, -4320), (Sum.inr 3964, -4320)]

def numericRow952 : Integer.Sparse Master := [(Sum.inl 0, 914), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -215), (Sum.inl 7, -320), (Sum.inl 8, -160), (Sum.inl 3, -1360), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, -400), (Sum.inl 4, -1440), (Sum.inl 27, 180), (Sum.inl 1, 1340), (Sum.inr 2019, -4320), (Sum.inr 2020, -8640), (Sum.inr 2051, -4320), (Sum.inr 2190, -4320), (Sum.inr 2191, -4320), (Sum.inr 2202, -8640), (Sum.inr 2243, -8640), (Sum.inr 3689, -4320), (Sum.inr 3690, -8640), (Sum.inr 3703, -4320), (Sum.inr 3757, -4320), (Sum.inr 3758, -4320), (Sum.inr 3764, -8640), (Sum.inr 3837, -17280), (Sum.inr 3838, -17280), (Sum.inr 3843, -17280), (Sum.inr 3895, -4320), (Sum.inr 3896, -8640), (Sum.inr 3901, -12960), (Sum.inr 3902, -4320), (Sum.inr 3903, -8640), (Sum.inr 4046, -4320)]

def numericRow953 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -40), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 125), (Sum.inr 2721, -2160), (Sum.inr 3532, -2160), (Sum.inr 3800, -1080), (Sum.inr 3801, -1080), (Sum.inr 3805, -1080), (Sum.inr 3812, -1080), (Sum.inr 3849, -2160), (Sum.inr 3875, -2160), (Sum.inr 3899, -2160), (Sum.inr 3901, -2160), (Sum.inr 3902, -1080), (Sum.inr 3909, -1080), (Sum.inr 3910, -1080), (Sum.inr 3974, -4320), (Sum.inr 4025, -1080), (Sum.inr 4046, -1080), (Sum.inr 5251, 4320), (Sum.inr 5281, 4320), (Sum.inr 5425, 8640), (Sum.inr 5430, 8640), (Sum.inr 5445, 8640)]

def numericRow954 : Integer.Sparse Master := [(Sum.inl 0, 73), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 1, 310), (Sum.inr 2908, -4320), (Sum.inr 3053, -1440), (Sum.inr 3600, -4320), (Sum.inr 3619, -1440), (Sum.inr 3713, -4320), (Sum.inr 3731, -1440), (Sum.inr 3814, -8640), (Sum.inr 3867, -1440), (Sum.inr 3902, -4320)]

def numericRow955 : Integer.Sparse Master := [(Sum.inl 0, 29), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, 90), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3900, -4320), (Sum.inr 3901, -4320), (Sum.inr 3909, -2880), (Sum.inr 3964, -4320), (Sum.inr 4025, -2880), (Sum.inr 4815, 17280), (Sum.inr 4830, 5760), (Sum.inr 4885, 5760), (Sum.inr 5251, 17280), (Sum.inr 5277, 5760), (Sum.inr 5359, 17280), (Sum.inr 5425, 34560)]

def numericRow956 : Integer.Sparse Master := [(Sum.inl 0, 56), (Sum.inl 2, 5), (Sum.inl 1, -55), (Sum.inr 2105, -360), (Sum.inr 2106, -360), (Sum.inr 2107, -720), (Sum.inr 2241, -360), (Sum.inr 2242, -360), (Sum.inr 2245, -360), (Sum.inr 2260, -720), (Sum.inr 2277, -360), (Sum.inr 3786, -360), (Sum.inr 3787, -720), (Sum.inr 3799, -360), (Sum.inr 3801, -360), (Sum.inr 3804, -720), (Sum.inr 3812, -360), (Sum.inr 3849, -720), (Sum.inr 3850, -1440), (Sum.inr 3857, -720), (Sum.inr 3875, -720), (Sum.inr 3876, -720), (Sum.inr 3890, -360), (Sum.inr 3891, -360), (Sum.inr 3892, -720), (Sum.inr 3906, -720), (Sum.inr 3910, -360), (Sum.inr 3913, -720)]

def numericRow957 : Integer.Sparse Master := [(Sum.inl 0, 65), (Sum.inl 2, -35), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 40), (Sum.inr 2764, -4320), (Sum.inr 3053, -2160), (Sum.inr 3581, -4320), (Sum.inr 3619, -2160), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3885, -8640), (Sum.inr 3901, -2160), (Sum.inr 3902, -2160), (Sum.inr 3909, -2160), (Sum.inr 3910, -4320), (Sum.inr 3957, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4025, -2160), (Sum.inr 5265, 8640), (Sum.inr 5266, 17280), (Sum.inr 5270, 8640), (Sum.inr 5281, 8640), (Sum.inr 5282, 8640), (Sum.inr 5429, 8640), (Sum.inr 5445, 17280), (Sum.inr 5446, 17280)]

def numericRow958 : Integer.Sparse Master := [(Sum.inl 0, 223), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 240), (Sum.inl 4, 320), (Sum.inl 1, -450), (Sum.inr 2536, -4320), (Sum.inr 2589, -1440), (Sum.inr 2671, -1440), (Sum.inr 2853, -4320), (Sum.inr 2880, -1440), (Sum.inr 3370, -4320), (Sum.inr 3390, -1440), (Sum.inr 3563, -1440), (Sum.inr 3617, -1440), (Sum.inr 3620, -4320), (Sum.inr 3776, -4320), (Sum.inr 3778, -4320), (Sum.inr 3809, -8640), (Sum.inr 3813, -8640), (Sum.inr 3909, -1440), (Sum.inr 3910, -4320), (Sum.inr 4010, -4320), (Sum.inr 4025, -1440)]

def numericRow959 : Integer.Sparse Master := [(Sum.inl 0, -52), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, 125), (Sum.inr 2853, 2160), (Sum.inr 2880, 720), (Sum.inr 3370, 2160), (Sum.inr 3390, 720), (Sum.inr 3563, 720), (Sum.inr 3778, 2160), (Sum.inr 3809, 4320), (Sum.inr 4010, 2160), (Sum.inr 4025, 720)]

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

def numericRow96 : Integer.Sparse Master := [(Sum.inr 2290, 3), (Sum.inr 2294, 1), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

def numericRow97 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 160), (Sum.inl 1, 130), (Sum.inr 828, -2160), (Sum.inr 832, -720), (Sum.inr 857, -2160), (Sum.inr 860, -1440), (Sum.inr 862, -720), (Sum.inr 1190, -2160), (Sum.inr 1297, -720), (Sum.inr 1926, -4320), (Sum.inr 1948, -4320), (Sum.inr 1951, -4320), (Sum.inr 1952, -2160), (Sum.inr 2112, -2160), (Sum.inr 2279, -4320), (Sum.inr 2281, -720), (Sum.inr 2287, -2160), (Sum.inr 2289, -720), (Sum.inr 2294, -720), (Sum.inr 3054, -2160), (Sum.inr 3626, -2160), (Sum.inr 3633, -720)]

def numericRow98 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -70), (Sum.inr 828, 2160), (Sum.inr 832, 720), (Sum.inr 860, 720), (Sum.inr 1190, 2160), (Sum.inr 1297, 720), (Sum.inr 1926, 4320), (Sum.inr 1951, 2160), (Sum.inr 2112, 2160), (Sum.inr 2279, 2160), (Sum.inr 2294, 720), (Sum.inr 3054, 2160)]

def numericRow99 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 2), (Sum.inr 1091, -144), (Sum.inr 1756, -144), (Sum.inr 2062, -432), (Sum.inr 2230, -432), (Sum.inr 2266, -432), (Sum.inr 2278, -432), (Sum.inr 3633, -144), (Sum.inr 4476, 1728), (Sum.inr 4478, 1728), (Sum.inr 4481, 576), (Sum.inr 4508, 576), (Sum.inr 4817, 3456), (Sum.inr 4881, 1728), (Sum.inr 5276, 1728), (Sum.inr 5311, 576)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow960 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 3721, -4320), (Sum.inr 3731, -1440), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3836, -4320), (Sum.inr 3867, -1440), (Sum.inr 3899, -2880), (Sum.inr 3900, -4320), (Sum.inr 3964, -4320), (Sum.inr 4046, -4320), (Sum.inr 4851, 17280), (Sum.inr 4863, 5760), (Sum.inr 4885, 5760), (Sum.inr 5429, 17280), (Sum.inr 5430, 34560)]

def numericRow961 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -10), (Sum.inr 3053, -1440), (Sum.inr 3619, -1440), (Sum.inr 3899, -2880), (Sum.inr 3901, -4320), (Sum.inr 3910, -4320), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 5085, 17280), (Sum.inr 5097, 5760), (Sum.inr 5277, 5760), (Sum.inr 5281, 17280), (Sum.inr 5359, 17280), (Sum.inr 5445, 34560)]

def numericRow962 : Integer.Sparse Master := [(Sum.inl 0, -63), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, 10), (Sum.inr 3058, 1440), (Sum.inr 3059, 1440), (Sum.inr 3074, 4320), (Sum.inr 3461, 4320), (Sum.inr 3619, 1440), (Sum.inr 3759, 4320), (Sum.inr 3899, 1440), (Sum.inr 3952, 4320), (Sum.inr 4024, 8640)]

def numericRow963 : Integer.Sparse Master := [(Sum.inl 0, 118), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, -150), (Sum.inr 2589, -720), (Sum.inr 2590, -1440), (Sum.inr 2764, -720), (Sum.inr 3563, -720), (Sum.inr 3564, -1440), (Sum.inr 3581, -720), (Sum.inr 3613, -720), (Sum.inr 3787, -1440), (Sum.inr 3790, -1440), (Sum.inr 3804, -1440), (Sum.inr 3809, -1440), (Sum.inr 3813, -1440), (Sum.inr 3815, -1440), (Sum.inr 3896, -720), (Sum.inr 3898, -720), (Sum.inr 3909, -720), (Sum.inr 3910, -720), (Sum.inr 3913, -1440), (Sum.inr 4010, -2160), (Sum.inr 4025, -720)]

def numericRow964 : Integer.Sparse Master := [(Sum.inl 0, 751), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, 80), (Sum.inl 4, -320), (Sum.inl 1, 50), (Sum.inr 2508, -4320), (Sum.inr 2509, -4320), (Sum.inr 2512, -8640), (Sum.inr 2703, -4320), (Sum.inr 2704, -4320), (Sum.inr 2705, -4320), (Sum.inr 2739, -8640), (Sum.inr 3460, -4320), (Sum.inr 3471, -8640), (Sum.inr 3496, -4320), (Sum.inr 3498, -4320), (Sum.inr 3534, -8640), (Sum.inr 3623, -4320), (Sum.inr 3703, -4320), (Sum.inr 3705, -8640), (Sum.inr 3758, -4320), (Sum.inr 3767, -8640), (Sum.inr 3902, -4320), (Sum.inr 3945, -8640), (Sum.inr 3952, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 4046, -4320), (Sum.inr 4047, -8640)]

def numericRow965 : Integer.Sparse Master := [(Sum.inl 0, 8), (Sum.inl 2, -5), (Sum.inl 1, 15), (Sum.inr 3787, -360), (Sum.inr 3800, -360), (Sum.inr 3804, -360), (Sum.inr 3805, -360), (Sum.inr 3838, -360), (Sum.inr 3843, -360), (Sum.inr 3857, -360), (Sum.inr 3876, -360), (Sum.inr 3974, -720), (Sum.inr 3983, -1440), (Sum.inr 4010, -360), (Sum.inr 4046, -360), (Sum.inr 5069, 1440), (Sum.inr 5071, 1440), (Sum.inr 5074, 1440), (Sum.inr 5092, 1440), (Sum.inr 5132, 1440), (Sum.inr 5138, 1440), (Sum.inr 5160, 1440), (Sum.inr 5255, 1440), (Sum.inr 5289, 1440), (Sum.inr 5350, 1440), (Sum.inr 5353, 1440), (Sum.inr 5362, 1440), (Sum.inr 5419, 1440), (Sum.inr 5421, 1440), (Sum.inr 5430, 2880), (Sum.inr 5461, 1440), (Sum.inr 5470, 1440), (Sum.inr 5480, 1440)]

def numericRow966 : Integer.Sparse Master := [(Sum.inl 0, -292), (Sum.inl 2, 300), (Sum.inl 3, 640), (Sum.inl 12, 160), (Sum.inl 4, 480), (Sum.inl 1, -880), (Sum.inl 31, -480), (Sum.inr 2550, 8640), (Sum.inr 2551, 8640), (Sum.inr 2557, 8640), (Sum.inr 2587, 8640), (Sum.inr 2718, 8640), (Sum.inr 3442, 8640), (Sum.inr 3445, 8640), (Sum.inr 3463, 8640), (Sum.inr 3572, 8640), (Sum.inr 3748, 8640), (Sum.inr 3750, 8640), (Sum.inr 3761, 8640), (Sum.inr 3804, 8640), (Sum.inr 3805, 8640), (Sum.inr 3848, 8640), (Sum.inr 3871, 8640), (Sum.inr 3922, 8640), (Sum.inr 3927, 8640), (Sum.inr 3946, 8640), (Sum.inr 3955, 8640), (Sum.inr 3978, 8640), (Sum.inr 3983, 8640)]

def numericRow967 : Integer.Sparse Master := [(Sum.inl 0, -156), (Sum.inl 5, 48), (Sum.inl 6, -6), (Sum.inl 2, 150), (Sum.inl 7, 96), (Sum.inl 35, 96), (Sum.inl 3, 864), (Sum.inl 13, 192), (Sum.inl 24, -288), (Sum.inl 12, 384), (Sum.inl 56, -288), (Sum.inl 26, 96), (Sum.inl 4, 576), (Sum.inl 27, -72), (Sum.inl 1, -504), (Sum.inr 2476, 5184), (Sum.inr 2478, 5184), (Sum.inr 2481, 5184), (Sum.inr 2501, 5184), (Sum.inr 2763, 5184), (Sum.inr 3499, 5184), (Sum.inr 3503, 5184), (Sum.inr 3517, 5184), (Sum.inr 3558, 5184), (Sum.inr 3688, 5184), (Sum.inr 3691, 5184), (Sum.inr 3700, 5184), (Sum.inr 3842, 5184), (Sum.inr 3843, 5184), (Sum.inr 3848, 5184), (Sum.inr 3857, 5184), (Sum.inr 3873, 5184), (Sum.inr 3947, 5184), (Sum.inr 3972, 5184), (Sum.inr 3973, 5184), (Sum.inr 3974, 5184), (Sum.inr 3978, 5184), (Sum.inr 3983, 5184)]

def numericRow968 : Integer.Sparse Master := [(Sum.inl 0, 1007), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -110), (Sum.inl 7, -80), (Sum.inl 8, -400), (Sum.inl 3, -160), (Sum.inl 24, 240), (Sum.inl 12, -160), (Sum.inl 4, 160), (Sum.inl 27, 180), (Sum.inl 1, 340), (Sum.inl 30, 480), (Sum.inr 2553, -8640), (Sum.inr 2556, -4320), (Sum.inr 2721, -4320), (Sum.inr 3514, -8640), (Sum.inr 3521, -4320), (Sum.inr 3532, -4320), (Sum.inr 3602, -4320), (Sum.inr 3779, -8640), (Sum.inr 3781, -8640), (Sum.inr 3794, -8640), (Sum.inr 3797, -8640), (Sum.inr 3800, -8640), (Sum.inr 3805, -8640), (Sum.inr 3903, -8640), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3957, -8640), (Sum.inr 4041, -4320), (Sum.inr 4046, -8640), (Sum.inr 4047, -8640)]

def numericRow969 : Integer.Sparse Master := [(Sum.inl 0, 1049), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -100), (Sum.inl 7, -80), (Sum.inl 8, -400), (Sum.inl 3, -320), (Sum.inl 24, 240), (Sum.inl 12, -160), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, 620), (Sum.inl 30, 480), (Sum.inr 2479, -4320), (Sum.inr 2480, -8640), (Sum.inr 2508, -4320), (Sum.inr 3459, -4320), (Sum.inr 3460, -4320), (Sum.inr 3467, -8640), (Sum.inr 3622, -4320), (Sum.inr 3689, -4320), (Sum.inr 3690, -8640), (Sum.inr 3703, -4320), (Sum.inr 3757, -4320), (Sum.inr 3758, -4320), (Sum.inr 3764, -8640), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3896, -4320), (Sum.inr 3901, -4320), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 4045, -8640), (Sum.inr 4047, -8640)]

def numericRow970 : Integer.Sparse Master := [(Sum.inl 0, 2118), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -165), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -240), (Sum.inl 24, 720), (Sum.inl 12, -240), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, -1710), (Sum.inr 2477, -25920), (Sum.inr 2483, -12960), (Sum.inr 2503, -12960), (Sum.inr 2764, -12960), (Sum.inr 3444, -25920), (Sum.inr 3446, -12960), (Sum.inr 3477, -12960), (Sum.inr 3581, -12960), (Sum.inr 3687, -25920), (Sum.inr 3692, -12960), (Sum.inr 3701, -12960), (Sum.inr 3749, -25920), (Sum.inr 3751, -12960), (Sum.inr 3769, -12960), (Sum.inr 3782, -25920), (Sum.inr 3787, -25920), (Sum.inr 3796, -25920), (Sum.inr 3804, -25920), (Sum.inr 3849, -12960), (Sum.inr 3857, -25920), (Sum.inr 3875, -12960), (Sum.inr 3876, -25920), (Sum.inr 3896, -12960), (Sum.inr 3900, -12960), (Sum.inr 3901, -12960), (Sum.inr 3903, -25920), (Sum.inr 3910, -12960), (Sum.inr 3964, -12960), (Sum.inr 3983, -51840), (Sum.inr 4010, -12960)]

def numericRow971 : Integer.Sparse Master := [(Sum.inl 0, -1251), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 7, 240), (Sum.inl 8, 240), (Sum.inl 24, -720), (Sum.inl 27, -180), (Sum.inl 1, 1050), (Sum.inr 2477, 25920), (Sum.inr 2483, 12960), (Sum.inr 2503, 12960), (Sum.inr 2764, 12960), (Sum.inr 3687, 25920), (Sum.inr 3692, 12960), (Sum.inr 3701, 12960), (Sum.inr 3787, 25920), (Sum.inr 3796, 25920), (Sum.inr 3849, 12960), (Sum.inr 3876, 25920), (Sum.inr 3900, 12960), (Sum.inr 3901, 12960), (Sum.inr 3910, 12960), (Sum.inr 3983, 25920)]

def numericRow972 : Integer.Sparse Master := [(Sum.inl 0, 88), (Sum.inl 2, -60), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, 300), (Sum.inr 3787, -4320), (Sum.inr 3789, -2160), (Sum.inr 3804, -4320), (Sum.inr 3810, -2160), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3849, -2160), (Sum.inr 3875, -2160), (Sum.inr 3902, -2160), (Sum.inr 3957, -4320), (Sum.inr 3974, -8640), (Sum.inr 3983, -8640), (Sum.inr 4010, -2160), (Sum.inr 4046, -4320), (Sum.inr 5249, 8640), (Sum.inr 5251, 8640), (Sum.inr 5255, 17280), (Sum.inr 5281, 8640), (Sum.inr 5414, 8640), (Sum.inr 5429, 8640), (Sum.inr 5430, 17280), (Sum.inr 5470, 17280), (Sum.inr 5480, 17280)]

def numericRow973 : Integer.Sparse Master := [(Sum.inl 0, -206), (Sum.inl 2, 270), (Sum.inl 3, 1440), (Sum.inl 12, 240), (Sum.inl 26, 320), (Sum.inl 4, 960), (Sum.inl 1, -1260), (Sum.inl 31, -480), (Sum.inr 2708, 4320), (Sum.inr 2710, 4320), (Sum.inr 2718, 8640), (Sum.inr 2750, 4320), (Sum.inr 3804, 8640), (Sum.inr 3810, 4320), (Sum.inr 3849, 4320), (Sum.inr 3869, 4320), (Sum.inr 3871, 8640), (Sum.inr 3954, 4320), (Sum.inr 3955, 8640), (Sum.inr 3957, 4320), (Sum.inr 3978, 8640), (Sum.inr 3983, 8640)]

def numericRow974 : Integer.Sparse Master := [(Sum.inl 0, 131), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 80), (Sum.inl 4, 320), (Sum.inl 1, 90), (Sum.inr 2954, -4320), (Sum.inr 3606, -4320), (Sum.inr 3787, -4320), (Sum.inr 3790, -4320), (Sum.inr 3804, -4320), (Sum.inr 3815, -4320), (Sum.inr 3857, -8640), (Sum.inr 3876, -8640), (Sum.inr 3902, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 3974, -8640), (Sum.inr 3983, -17280), (Sum.inr 4010, -8640), (Sum.inr 5160, 17280), (Sum.inr 5161, 17280), (Sum.inr 5164, 17280), (Sum.inr 5255, 17280), (Sum.inr 5260, 17280), (Sum.inr 5269, 17280), (Sum.inr 5289, 34560), (Sum.inr 5430, 17280), (Sum.inr 5446, 17280), (Sum.inr 5461, 17280), (Sum.inr 5463, 17280), (Sum.inr 5470, 17280), (Sum.inr 5480, 34560)]

def numericRow975 : Integer.Sparse Master := [(Sum.inl 0, -166), (Sum.inl 2, 30), (Sum.inl 3, -640), (Sum.inl 12, -160), (Sum.inl 26, -160), (Sum.inl 4, -480), (Sum.inl 1, -20), (Sum.inr 2718, 4320), (Sum.inr 2719, 4320), (Sum.inr 2724, 4320), (Sum.inr 2736, 4320), (Sum.inr 2763, 4320), (Sum.inr 3558, 4320), (Sum.inr 3565, 4320), (Sum.inr 3572, 4320), (Sum.inr 3606, 4320), (Sum.inr 3804, 4320), (Sum.inr 3815, 4320), (Sum.inr 3857, 4320), (Sum.inr 3955, 4320), (Sum.inr 3959, 4320), (Sum.inr 3960, 4320), (Sum.inr 3961, 4320), (Sum.inr 3972, 4320), (Sum.inr 3973, 4320), (Sum.inr 3974, 4320), (Sum.inr 3978, 8640), (Sum.inr 3983, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow976 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 2, 7), (Sum.inl 3, -16), (Sum.inl 4, 32), (Sum.inl 1, -62), (Sum.inr 2503, -864), (Sum.inr 2504, -864), (Sum.inr 2505, -864), (Sum.inr 2515, -864), (Sum.inr 2782, -864), (Sum.inr 3446, -864), (Sum.inr 3448, -864), (Sum.inr 3479, -864), (Sum.inr 3583, -864), (Sum.inr 3701, -864), (Sum.inr 3702, -864), (Sum.inr 3706, -864), (Sum.inr 3751, -864), (Sum.inr 3771, -864), (Sum.inr 3857, -864), (Sum.inr 3876, -864), (Sum.inr 3900, -864), (Sum.inr 3903, -864), (Sum.inr 3913, -864), (Sum.inr 3964, -864), (Sum.inr 3983, -1728)]

def numericRow977 : Integer.Sparse Master := [(Sum.inl 0, 329), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -220), (Sum.inl 7, -80), (Sum.inl 8, -400), (Sum.inl 3, -320), (Sum.inl 24, 240), (Sum.inl 4, -160), (Sum.inl 27, 180), (Sum.inl 1, 260), (Sum.inl 30, 480), (Sum.inr 3602, -4320), (Sum.inr 3603, -4320), (Sum.inr 3607, -8640), (Sum.inr 3622, -4320), (Sum.inr 3896, -4320), (Sum.inr 3898, -4320), (Sum.inr 3903, -8640), (Sum.inr 4041, -4320), (Sum.inr 4042, -8640), (Sum.inr 4045, -8640), (Sum.inr 4046, -12960), (Sum.inr 4047, -8640)]

def numericRow978 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 2, -6), (Sum.inl 4, -16), (Sum.inl 1, 21), (Sum.inr 2458, -432), (Sum.inr 2459, -432), (Sum.inr 2462, -432), (Sum.inr 2508, -432), (Sum.inr 2739, -432), (Sum.inr 3429, -432), (Sum.inr 3436, -432), (Sum.inr 3460, -432), (Sum.inr 3534, -432), (Sum.inr 3681, -432), (Sum.inr 3683, -432), (Sum.inr 3703, -432), (Sum.inr 3746, -432), (Sum.inr 3758, -432), (Sum.inr 3838, -432), (Sum.inr 3843, -432), (Sum.inr 3942, -432), (Sum.inr 3958, -432), (Sum.inr 3961, -432), (Sum.inr 3974, -432), (Sum.inr 4010, -432), (Sum.inr 4046, -432)]

def numericRow979 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 80), (Sum.inr 3899, -720), (Sum.inr 3900, -1080), (Sum.inr 3901, -1080), (Sum.inr 3909, -720), (Sum.inr 3945, -1080), (Sum.inr 3952, -1080), (Sum.inr 3964, -1080), (Sum.inr 3974, -4320), (Sum.inr 4025, -720), (Sum.inr 4046, -1080), (Sum.inr 4091, 1440)]

def numericRow980 : Integer.Sparse Master := [(Sum.inl 0, 64), (Sum.inl 2, -60), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, 180), (Sum.inr 2880, -2160), (Sum.inr 3617, -2160), (Sum.inr 3690, -4320), (Sum.inr 3692, -2160), (Sum.inr 3764, -4320), (Sum.inr 3769, -2160), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3910, -2160), (Sum.inr 3957, -8640), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4046, -4320), (Sum.inr 5184, 8640), (Sum.inr 5185, 17280), (Sum.inr 5265, 8640), (Sum.inr 5414, 8640), (Sum.inr 5429, 25920), (Sum.inr 5470, 17280)]

def numericRow981 : Integer.Sparse Master := [(Sum.inl 0, -63), (Sum.inl 2, 105), (Sum.inl 3, 720), (Sum.inl 12, 280), (Sum.inl 25, -240), (Sum.inl 26, 160), (Sum.inl 4, 560), (Sum.inl 1, -460), (Sum.inr 3524, 2160), (Sum.inr 3526, 2160), (Sum.inr 3529, 4320), (Sum.inr 3617, 2160), (Sum.inr 3764, 4320), (Sum.inr 3769, 2160), (Sum.inr 3869, 2160), (Sum.inr 3874, 4320), (Sum.inr 3954, 2160), (Sum.inr 3955, 4320), (Sum.inr 3957, 4320), (Sum.inr 3961, 4320)]

def numericRow982 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 2, -11), (Sum.inl 3, -16), (Sum.inl 4, 32), (Sum.inl 1, -14), (Sum.inr 2382, -1728), (Sum.inr 2383, -864), (Sum.inr 2398, -864), (Sum.inr 2721, -864), (Sum.inr 3340, -1728), (Sum.inr 3341, -864), (Sum.inr 3352, -864), (Sum.inr 3532, -864), (Sum.inr 3781, -1728), (Sum.inr 3794, -1728), (Sum.inr 3845, -1728), (Sum.inr 3945, -864), (Sum.inr 3952, -864), (Sum.inr 3958, -1728), (Sum.inr 3961, -1728), (Sum.inr 4046, -864)]

def numericRow983 : Integer.Sparse Master := [(Sum.inl 0, 657), (Sum.inl 5, 60), (Sum.inl 2, 15), (Sum.inl 7, 240), (Sum.inl 3, -240), (Sum.inl 23, -720), (Sum.inl 12, -480), (Sum.inl 27, -180), (Sum.inl 1, 2970), (Sum.inr 2100, -12960), (Sum.inr 2101, -25920), (Sum.inr 2110, -12960), (Sum.inr 2275, -12960), (Sum.inr 3731, -12960), (Sum.inr 3732, -25920), (Sum.inr 3784, -25920), (Sum.inr 3789, -12960), (Sum.inr 3810, -12960), (Sum.inr 3811, -25920), (Sum.inr 3867, -12960), (Sum.inr 3885, -25920), (Sum.inr 3886, -25920), (Sum.inr 3891, -12960), (Sum.inr 3902, -12960), (Sum.inr 3907, -25920)]

def numericRow984 : Integer.Sparse Master := [(Sum.inl 0, 107), (Sum.inl 2, -95), (Sum.inl 3, -400), (Sum.inl 12, -320), (Sum.inl 4, -160), (Sum.inl 1, 130), (Sum.inr 2721, -4320), (Sum.inr 3532, -4320), (Sum.inr 3787, -8640), (Sum.inr 3789, -4320), (Sum.inr 3804, -8640), (Sum.inr 3810, -4320), (Sum.inr 3857, -8640), (Sum.inr 3876, -8640), (Sum.inr 3885, -8640), (Sum.inr 3901, -8640), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 5185, 34560), (Sum.inr 5187, 17280), (Sum.inr 5197, 17280), (Sum.inr 5219, 17280), (Sum.inr 5220, 17280), (Sum.inr 5226, 34560), (Sum.inr 5281, 17280), (Sum.inr 5425, 34560), (Sum.inr 5430, 34560), (Sum.inr 5445, 34560)]

def numericRow985 : Integer.Sparse Master := [(Sum.inl 0, -109), (Sum.inl 2, 195), (Sum.inl 3, 1040), (Sum.inl 12, 320), (Sum.inl 26, 160), (Sum.inl 4, 640), (Sum.inl 1, -620), (Sum.inl 31, -480), (Sum.inr 2661, 4320), (Sum.inr 2662, 4320), (Sum.inr 2669, 8640), (Sum.inr 2750, 4320), (Sum.inr 3529, 8640), (Sum.inr 3532, 4320), (Sum.inr 3537, 4320), (Sum.inr 3569, 4320), (Sum.inr 3804, 8640), (Sum.inr 3810, 4320), (Sum.inr 3840, 8640), (Sum.inr 3848, 8640), (Sum.inr 3857, 8640), (Sum.inr 3880, 8640), (Sum.inr 3885, 4320)]

def numericRow986 : Integer.Sparse Master := [(Sum.inl 0, 1548), (Sum.inl 5, -240), (Sum.inl 6, 15), (Sum.inl 2, -195), (Sum.inl 7, -1200), (Sum.inl 3, -2640), (Sum.inl 23, 1440), (Sum.inl 24, 1440), (Sum.inl 12, -720), (Sum.inl 4, 480), (Sum.inl 27, 720), (Sum.inl 1, -1890), (Sum.inr 2016, -25920), (Sum.inr 2023, -12960), (Sum.inr 2046, -12960), (Sum.inr 2075, -25920), (Sum.inr 2077, -12960), (Sum.inr 2105, -12960), (Sum.inr 2214, -12960), (Sum.inr 2241, -12960), (Sum.inr 3687, -25920), (Sum.inr 3692, -12960), (Sum.inr 3701, -12960), (Sum.inr 3719, -25920), (Sum.inr 3721, -12960), (Sum.inr 3749, -25920), (Sum.inr 3751, -12960), (Sum.inr 3769, -12960), (Sum.inr 3786, -25920), (Sum.inr 3795, -25920), (Sum.inr 3799, -25920), (Sum.inr 3836, -12960), (Sum.inr 3849, -12960), (Sum.inr 3850, -51840), (Sum.inr 3857, -25920), (Sum.inr 3875, -12960), (Sum.inr 3876, -25920), (Sum.inr 3890, -12960), (Sum.inr 3897, -12960), (Sum.inr 3901, -12960), (Sum.inr 3906, -25920), (Sum.inr 3910, -25920)]

def numericRow987 : Integer.Sparse Master := [(Sum.inl 0, -269), (Sum.inl 5, 60), (Sum.inl 2, 25), (Sum.inl 7, 240), (Sum.inl 3, 560), (Sum.inl 23, -240), (Sum.inl 24, -480), (Sum.inl 12, 160), (Sum.inl 27, -180), (Sum.inl 1, 250), (Sum.inr 2075, 8640), (Sum.inr 2077, 4320), (Sum.inr 2105, 4320), (Sum.inr 2214, 4320), (Sum.inr 3719, 8640), (Sum.inr 3721, 4320), (Sum.inr 3749, 8640), (Sum.inr 3751, 4320), (Sum.inr 3769, 4320), (Sum.inr 3799, 8640), (Sum.inr 3850, 8640), (Sum.inr 3875, 4320), (Sum.inr 3876, 8640), (Sum.inr 3897, 4320), (Sum.inr 3906, 8640)]

def numericRow988 : Integer.Sparse Master := [(Sum.inl 0, 115), (Sum.inl 2, -75), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 30), (Sum.inr 2589, -4320), (Sum.inr 2764, -4320), (Sum.inr 3563, -4320), (Sum.inr 3581, -4320), (Sum.inr 3731, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3849, -8640), (Sum.inr 3867, -4320), (Sum.inr 3875, -8640), (Sum.inr 3885, -8640), (Sum.inr 3910, -8640), (Sum.inr 3957, -17280), (Sum.inr 4046, -4320), (Sum.inr 5145, 34560), (Sum.inr 5150, 17280), (Sum.inr 5243, 17280), (Sum.inr 5244, 17280), (Sum.inr 5265, 34560), (Sum.inr 5379, 34560), (Sum.inr 5421, 34560), (Sum.inr 5429, 51840)]

def numericRow989 : Integer.Sparse Master := [(Sum.inl 0, 267), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -170), (Sum.inl 7, -320), (Sum.inl 8, -160), (Sum.inl 3, -1120), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, -400), (Sum.inl 4, -160), (Sum.inl 27, 180), (Sum.inl 1, -100), (Sum.inr 3602, -4320), (Sum.inr 3607, -8640), (Sum.inr 3613, -4320), (Sum.inr 3890, -4320), (Sum.inr 3891, -4320), (Sum.inr 3892, -8640), (Sum.inr 3896, -8640), (Sum.inr 3897, -4320), (Sum.inr 3901, -8640), (Sum.inr 3903, -8640), (Sum.inr 3906, -8640), (Sum.inr 3910, -4320)]

def numericRow990 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 2556, -4320), (Sum.inr 2589, -1440), (Sum.inr 3521, -4320), (Sum.inr 3563, -1440), (Sum.inr 3721, -4320), (Sum.inr 3731, -1440), (Sum.inr 3836, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3849, -4320), (Sum.inr 3867, -1440), (Sum.inr 3875, -4320), (Sum.inr 3909, -1440), (Sum.inr 4025, -1440), (Sum.inr 4046, -4320), (Sum.inr 4091, 5760)]

def numericRow991 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 1, 5), (Sum.inr 4079, 60), (Sum.inr 4080, 180), (Sum.inr 4083, 60), (Sum.inr 4087, 60), (Sum.inr 4088, 180), (Sum.inr 4090, 180), (Sum.inr 4091, 300), (Sum.inr 4092, 360)]

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

def numericRow992 : Integer.Sparse Master := [(Sum.inl 0, 1101), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 7, -480), (Sum.inl 23, 720), (Sum.inl 12, 480), (Sum.inl 27, 180), (Sum.inl 1, 5820), (Sum.inr 3784, -51840), (Sum.inr 3789, -51840), (Sum.inr 3810, -51840), (Sum.inr 3885, -51840), (Sum.inr 3895, -12960), (Sum.inr 3902, -51840)]

def numericRow993 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 1, -5), (Sum.inr 4090, 360), (Sum.inr 4091, 480)]

def numericRow994 : Integer.Sparse Master := [(Sum.inr 617, 1), (Sum.inr 936, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

def numericRow995 : Integer.Sparse Master := [(Sum.inr 862, 1), (Sum.inr 1629, 3), (Sum.inr 1752, 1), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

def numericRow996 : Integer.Sparse Master := [(Sum.inr 1749, 3), (Sum.inr 1752, 2), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

def numericRow997 : Integer.Sparse Master := [(Sum.inr 587, 1), (Sum.inr 911, 2), (Sum.inr 951, 1), (Sum.inr 1027, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

def numericRow998 : Integer.Sparse Master := [(Sum.inr 849, 1), (Sum.inr 1615, 2), (Sum.inr 1749, 1), (Sum.inr 1752, 2), (Sum.inr 4072, -1)]

def numericRow999 : Integer.Sparse Master := [(Sum.inr 794, 2), (Sum.inr 797, 1), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 1716, 1), (Sum.inr 4069, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock10 : Integer.Sparse (Fin 2886) := [(320, -6062232000), (321, -21031476480), (322, -5851062720), (323, -2973138240), (324, -4842156000), (325, -1675752000), (326, -206942400), (327, -3645895920), (328, -3021984000), (329, -16230715200), (330, 2052249600), (331, 6508739520), (332, 7805568000), (333, -10718012160), (334, 6949261440), (335, 11544219520), (336, -7681584000), (337, 45371566120), (338, 10913104800), (339, -8143950720), (340, -24128404800), (341, -32308070400), (342, -2436820320), (343, 4891350000), (344, 3062000400), (345, 7681584000), (346, 968431200), (347, 41996073600), (348, 3382263360), (349, 14205906400), (350, 24906247200), (351, 21394965600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock11 : Integer.Sparse (Fin 2886) := [(352, 25944217680), (353, -4891350000), (354, -4593000600), (355, 34130795040), (356, 7681584000), (357, 72408693800), (358, 51916555200), (359, 12511067520), (360, -9829123200), (361, -40223205600), (362, -4096241280), (363, -4891350000), (364, -4593000600), (365, -655456000), (366, -7865472000), (367, -7681584000), (368, 984853440), (369, -32363434400), (370, 8357064000), (371, -31096581600), (372, 10438497600), (373, 4891350000), (374, 5817800760), (375, 689808000), (376, -2879009760), (377, 3021984000), (378, 3440836800), (379, 26916001920), (380, -8256782016), (381, -38337686400), (382, -85045968720), (383, -62829660000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock12 : Integer.Sparse (Fin 2886) := [(384, -4367116800), (385, -7681584000), (386, 13595421600), (387, -41996073600), (388, -3382263360), (389, 49787942400), (390, 62829660000), (391, 22394548800), (392, 7681584000), (393, -984853440), (394, 8297990400), (395, -8088133200), (396, -4263292800), (397, -3591436800), (398, -31722650400), (399, -3021984000), (400, -10020873120), (401, 17944001280), (402, -1539187200), (403, -24958425600), (404, -7805568000), (405, -6949261440), (406, 33191961600), (407, 72531276000), (408, -55627355000), (409, -19406008800), (410, -84224625600), (411, 4891350000), (412, 4593000600), (413, 5899104000), (414, 5839412600), (415, -5899104000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock13 : Integer.Sparse (Fin 2886) := [(416, 31096581600), (417, -4891350000), (418, -4593000600), (419, 2565312000), (420, 22659036000), (421, 3021984000), (422, -15448158720), (423, 4608692640), (424, 28903210080), (425, -30639798720), (426, 16865093280), (427, 364979040), (428, -6472454400), (429, -4157069760), (430, -10027419840), (431, -9536209920), (432, -12460468800), (433, 12702349440), (434, 48085286400), (435, -12705079680), (436, 9079309440), (437, -2969668800), (438, -12702349440), (439, -6052872960), (440, 6340708800), (441, -31525516800), (442, -11702125440), (443, 82138442400), (444, -11702125440), (445, 8919414720), (446, 8378760000), (447, -23681979360)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock14 : Integer.Sparse (Fin 2886) := [(448, -6166598400), (449, 27472187520), (450, -6062232000), (451, -2366887680), (452, -7602509760), (453, 6166598400), (454, -11702125440), (455, -59335206720), (456, -5277668160), (457, -35596375200), (458, 20905332480), (459, -10054512000), (460, -2973138240), (461, -1455396480), (462, 4922282880), (463, -778565760), (464, 3114263040), (465, -4922282880), (466, -21031476480), (467, 1455396480), (468, -606706560), (469, -4671394560), (470, 6062232000), (471, 21031476480), (472, -11702125440), (473, 2973138240), (474, -658082400), (475, 1213413120), (476, 10054512000), (477, 8919414720), (478, -11017584640), (479, -3178736640)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock15 : Integer.Sparse (Fin 2886) := [(480, 2366887680), (481, -14184489600), (482, 3912211200), (483, 28348864640), (484, 2943398400), (485, -20905332480), (486, -606706560), (487, 2969668800), (488, -8378760000), (489, 6052872960), (490, -10555336320), (491, 12705079680), (492, -8919414720), (493, -9079309440), (494, -4339159680), (495, -4783584000), (496, 6003054720), (497, -880757400), (498, 21394965600), (499, -4891350000), (500, -2449600320), (501, 1823596800), (502, -4842156000), (503, -21394965600), (504, 4891350000), (505, 3368200440), (506, 4088628400), (507, -11693349600), (508, 4891350000), (509, 3368200440), (510, 4752056000), (511, 14137403000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock16 : Integer.Sparse (Fin 2886) := [(512, -5899104000), (513, 31096581600), (514, -4891350000), (515, -4593000600), (516, 513062400), (517, 15986424960), (518, 4783584000), (519, 24893262720), (520, -8297990400), (521, -9701616000), (522, 22435393400), (523, 10342394400), (524, 21394965600), (525, -4891350000), (526, -4593000600), (527, -5899104000), (528, -14137403000), (529, 5899104000), (530, -31096581600), (531, 4891350000), (532, 4593000600), (533, -513062400), (534, -4531807200), (535, 19934159040), (536, -22430001600), (537, -14953334400), (538, 1099785600), (539, -1350411840), (540, -30273848640), (541, 10337482560), (542, 377769600), (543, 1350411840)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock17 : Integer.Sparse (Fin 2886) := [(544, 5297333760), (545, -84562560), (546, -8701539840), (547, -1872743040), (548, -2536649280), (549, -50415792000), (550, -3081579840), (551, 50415792000), (552, 13244495680), (553, -5277668160), (554, -1684920960), (555, 1684920960), (556, 372539520), (557, 1684920960), (558, -1872743040), (559, -745079040), (560, -1684920960), (561, 6383759040), (562, -10337482560), (563, -7602509760), (564, 9079309440), (565, -5277668160), (566, 372539520), (567, 84562560), (568, -6052872960), (569, -4900762080), (570, 5465156040), (571, 4836802720), (572, 25540245600), (573, 30498751440), (574, 824652960), (575, -22643952240)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock18 : Integer.Sparse (Fin 2886) := [(576, 8327170560), (577, -22889021040), (578, -2520544800), (579, -4157069760), (580, 800534400), (581, -70600320), (582, -11702125440), (583, -13595421600), (584, 5946276480), (585, -519274880), (586, -5851062720), (587, 22659036000), (588, -5946276480), (589, -1455396480), (590, 1455396480), (591, 519043840), (592, -5851062720), (593, 4531807200), (594, 5946276480), (595, 16294397760), (596, 10729172160), (597, -1904308800), (598, 70600320), (599, -5946276480), (600, 14588786880), (601, 460713600), (602, -460713600), (603, -1675376640), (604, 3350753280), (605, -1675376640), (606, -971081280), (607, 772712640)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock19 : Integer.Sparse (Fin 2886) := [(608, 9927207360), (609, 1524257280), (610, 9927207360), (611, 772712640), (612, -952660800), (613, -19854414720), (614, -1524257280), (615, -188943200), (616, 4161320640), (617, -15086390400), (618, 23154986880), (619, 2950909760), (620, -1020293280), (621, -4161320640), (622, -214004160), (623, 952660800), (624, 4864653120), (625, -3088286400), (626, 18756605760), (627, -23154986880), (628, -12712813440), (629, 3088286400), (630, 24091104960), (631, -11306956800), (632, 4204656000), (633, 4893592320), (634, 642406880), (635, -943747200), (636, -983184000), (637, 983184000), (638, 983184000), (639, 4511577600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock2 : Integer.Sparse (Fin 2886) := [(64, -2834735040), (65, 717984160), (66, -21141114240), (67, -6613813440), (68, -21991292160), (69, 522207360), (70, -8913645120), (71, 13312972800), (72, 8842310400), (73, -1957576320), (74, 1333725120), (75, 3083921280), (76, -10640588880), (77, -14963621760), (78, -3626979840), (79, 23045362560), (80, -7955241120), (81, 21563723520), (82, 2928539040), (83, -545198400), (84, 34097686560), (85, 19375987680), (86, -23647759680), (87, -12379132800), (88, -11714846400), (89, -11204730240), (90, 1379616000), (91, 11172102240), (92, -1541328000), (93, 15006748800), (94, 9445352256), (95, 33069067200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock20 : Integer.Sparse (Fin 2886) := [(640, -1966368000), (641, -1557131520), (642, 233002560), (643, -7007091840), (644, -233002560), (645, -4511577600), (646, -983184000), (647, 242702400), (648, -4496332800), (649, -15244800), (650, 21533016000), (651, -21533016000), (652, -242702400), (653, 4496332800), (654, 15244800), (655, 10259016000), (656, -9767424000), (657, 11667543040), (658, -9275832000), (659, 9767424000), (660, -2282120640), (661, 2282120640), (662, 9775883520), (663, 5844191040), (664, 12577524480), (665, 5844191040), (666, -19551767040), (667, -5844191040), (668, -12577524480), (669, 286883520), (670, -12577524480), (671, 239069600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock21 : Integer.Sparse (Fin 2886) := [(672, -6493545600), (673, -286883520), (674, -5194836480), (675, -5844191040), (676, -286883520), (677, -239069600), (678, 21428167680), (679, 5321594880), (680, 282042720), (681, -2632325760), (682, -25302504960), (683, 35004375360), (684, 5321594880), (685, -778348800), (686, -1363832640), (687, -1434417600), (688, 6530198400), (689, 9775883520), (690, -143441760), (691, 12577524480), (692, -143441760), (693, 430325280), (694, 525953120), (695, 11688382080), (696, 655456000), (697, -4511577600), (698, 143441760), (699, -24301392480), (700, -10643189760), (701, -13515732000), (702, 5264651520), (703, 50605009920)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock22 : Integer.Sparse (Fin 2886) := [(704, -63478552320), (705, -5321594880), (706, 778348800), (707, -5166365760), (708, 1290975840), (709, 12944257600), (710, -5321594880), (711, 4511577600), (712, -25363775600), (713, 3113416000), (714, -9795297600), (715, -63023193600), (716, 28415707200), (717, 4496332800), (718, 15244800), (719, -5321594880), (720, 2685520880), (721, 9080424000), (722, 5321594880), (723, -16939689600), (724, -4496332800), (725, 17511888960), (726, -5815324800), (727, -15244800), (728, -60162984000), (729, 60162984000), (730, -10259016000), (731, 9767424000), (732, 143441760), (733, 7776671360), (734, 778348800), (735, 1195348000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock23 : Integer.Sparse (Fin 2886) := [(736, -10360464480), (737, 7801056000), (738, -9767424000), (739, 12466367040), (740, 2810002560), (741, -965890800), (742, -9927207360), (743, -9927207360), (744, -1545425280), (745, 9927207360), (746, -573767040), (747, 9927207360), (748, 772712640), (749, 965890800), (750, 113365920), (751, -4161320640), (752, 15086390400), (753, -23154986880), (754, -4003565760), (755, 906927360), (756, 778565760), (757, -1398015360), (758, 6228526080), (759, -1165012800), (760, 4511577600), (761, 1966368000), (762, 2873224800), (763, 5321594880), (764, -2632325760), (765, -25302504960), (766, 28474176960), (767, 4788708000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock24 : Integer.Sparse (Fin 2886) := [(768, 5321594880), (769, -4511577600), (770, 20892408000), (771, -1966368000), (772, -932010240), (773, -4161320640), (774, 4838744640), (775, -4864653120), (776, -2276884800), (777, -13063399680), (778, 23154986880), (779, 15521053760), (780, -1203850560), (781, -11092952640), (782, 63023193600), (783, 17182392000), (784, -20368003200), (785, 1398015360), (786, -45598099200), (787, -4496332800), (788, -15244800), (789, 5321594880), (790, 14846243520), (791, -5321594880), (792, 16939689600), (793, 4496332800), (794, -24042087360), (795, -12345523200), (796, 15244800), (797, 22465026240), (798, 1327024320), (799, 4030504320)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock25 : Integer.Sparse (Fin 2886) := [(800, -20352852480), (801, 12345523200), (802, 11306956800), (803, -4204656000), (804, -9098248320), (805, -680195520), (806, 60162984000), (807, -11927064960), (808, -60162984000), (809, 7801056000), (810, -9767424000), (811, 957741600), (812, -778348800), (813, -1147534080), (814, -2873224800), (815, -7801056000), (816, 9767424000), (817, -519043840), (818, 4204656000), (819, -75577280), (820, 943747200), (821, -10184246400), (822, -2282120640), (823, -2810002560), (824, 5365171200), (825, 2276884800), (826, -12784148160), (827, 11306956800), (828, 21533016000), (829, -12345523200), (830, 24691046400), (831, -21533016000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock26 : Integer.Sparse (Fin 2886) := [(832, 130816320), (833, 15116823680), (834, -12345523200), (835, -11306956800), (836, -1488550080), (837, -106003785600), (838, 106003785600), (839, -5531680320), (840, -9503812800), (841, -20716922880), (842, -2832503040), (843, 11649499200), (844, 3594201600), (845, -28344173760), (846, -23457219840), (847, -1972067520), (848, 46731375360), (849, -88185976320), (850, -9764424000), (851, -23304249600), (852, -24632757120), (853, -8902558560), (854, -29171005440), (855, -33694815360), (856, 11704045440), (857, -8577817920), (858, 12928711680), (859, 17480376480), (860, -15921950400), (861, -626952960), (862, 2761647360), (863, 124757280960)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock27 : Integer.Sparse (Fin 2886) := [(864, 38659256640), (865, -39041011200), (866, -139338829440), (867, -15298080000), (868, -53502945600), (869, -11586662400), (870, -26782492800), (871, -841374720), (872, 33502659840), (873, 51263390400), (874, 5789256000), (875, -5331376320), (876, 19464549600), (877, -59197275840), (878, 15514438560), (879, -2761647360), (880, -4111730880), (881, 59045352000), (882, 28669344960), (883, -2238993600), (884, 24027390720), (885, 841374720), (886, -81169111680), (887, -15863424000), (888, 30703624320), (889, 13384772640), (890, -43329504960), (891, -697308960), (892, 51263390400), (893, 20184249600), (894, 16303636800), (895, 17888192640)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock28 : Integer.Sparse (Fin 2886) := [(896, 20355807360), (897, -26140056960), (898, 59646838080), (899, 3684537600), (900, 24438657600), (901, 90786548160), (902, 72717328320), (903, 12656995200), (904, -53105987520), (905, -24436592640), (906, -16494482880), (907, -4854971520), (908, 22442110560), (909, -44920608000), (910, -46013337600), (911, 37131510240), (912, -24425581920), (913, -30122788320), (914, -34914424320), (915, -15924055680), (916, 17303277120), (917, 84184678080), (918, -25105542720), (919, 10095405120), (920, -21429406080), (921, -26705880000), (922, -7207872000), (923, -2290443840), (924, 19270920960), (925, 15924055680), (926, -44733043200), (927, -20190810240)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock29 : Integer.Sparse (Fin 2886) := [(928, -36049392000), (929, -4079589120), (930, 184428679680), (931, -222970521600), (932, -20355807360), (933, -104945280), (934, -59045352000), (935, -29794296960), (936, 19140878400), (937, 7079086080), (938, 16494482880), (939, -64920779520), (940, 6370032960), (941, 15863424000), (942, -19381936320), (943, 11365163040), (944, -16491696480), (945, 19270920960), (946, 51401866080), (947, 18475167840), (948, 2659780800), (949, -216714240), (950, -5166429120), (951, 3284599680), (952, -4025032320), (953, -3347095680), (954, -3989436480), (955, 21910199040), (956, 75516028800), (957, 33619985280), (958, 28376352000), (959, 28803375360)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock3 : Integer.Sparse (Fin 2886) := [(96, -11656704000), (97, -1471699200), (98, 1793145600), (99, -17455823040), (100, -3591436800), (101, 1541328000), (102, 6923236320), (103, -39682880640), (104, -19316027520), (105, 49685040000), (106, 13312972800), (107, 2022739200), (108, -3936988800), (109, -1352247120), (110, -1686608640), (111, 3936988800), (112, -113365920), (113, 1686608640), (114, 453463680), (115, 1545425280), (116, -6315936000), (117, 11656704000), (118, 2834735040), (119, -513062400), (120, -680195520), (121, 9311471520), (122, 39682880640), (123, 10344026880), (124, 6105404800), (125, -13312972800), (126, 10105497600), (127, -2022739200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock30 : Integer.Sparse (Fin 2886) := [(960, 16533460800), (961, 16044998400), (962, -9284467680), (963, 10910926080), (964, 19835609280), (965, 11914051200), (966, -20923219680), (967, -2542207680), (968, 52549732800), (969, 951422400), (970, -22592992320), (971, -23117454720), (972, -71602124160), (973, -46537849920), (974, -85112192640), (975, -24438657600), (976, 34373554560), (977, 61001697600), (978, 57071091840), (979, 36849767040), (980, 50345853120), (981, -14412450240), (982, 35427759360), (983, -34668051360), (984, 2761647360), (985, -12025560000), (986, 2228996160), (987, 5315318400), (988, 43907532480), (989, 40694216640), (990, -34229623680), (991, -57840823680)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock31 : Integer.Sparse (Fin 2886) := [(992, -6245040000), (993, -21241960320), (994, -33279843360), (995, 36651522720), (996, -3277440480), (997, 33313173120), (998, -4504694400), (999, 15924055680), (1000, -17303277120), (1001, -46633697280), (1002, -15305165760), (1003, -15924055680), (1004, -51897707520), (1005, 10095405120), (1006, -27138769920), (1007, 26705880000), (1008, 7207872000), (1009, -4330238400), (1010, 50924900160), (1011, 20355807360), (1012, 891888000), (1013, 11949730560), (1014, 2484509760), (1015, -32966534400), (1016, -46581556800), (1017, 28382808960), (1018, -53860588800), (1019, 4330238400), (1020, -5789256000), (1021, -5990311680), (1022, 106116756960), (1023, 28717637280)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock32 : Integer.Sparse (Fin 2886) := [(1024, -50924900160), (1025, 30220117920), (1026, 1944152640), (1027, -19938131520), (1028, -3106893120), (1029, -18611928000), (1030, -2896158720), (1031, -16533460800), (1032, -73260070080), (1033, 20259264960), (1034, -39648541440), (1035, -12361694400), (1036, 4584015360), (1037, -15823549920), (1038, -30997950720), (1039, 43259212800), (1040, 7492012800), (1041, 46031237280), (1042, -30701108640), (1043, 211086720), (1044, 8197485120), (1045, -19938131520), (1046, -91803287040), (1047, -26223429120), (1048, 18260079360), (1049, -18570432000), (1050, 18614069760), (1051, -18489318240), (1052, 1473098400), (1053, -17255059200), (1054, 14178726720), (1055, -118420945920)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock33 : Integer.Sparse (Fin 2886) := [(1056, -56074103040), (1057, 39131352000), (1058, -4355479680), (1059, 31775260800), (1060, 24750694560), (1061, -61274348160), (1062, -45903946560), (1063, 22108464000), (1064, 46238529600), (1065, -23562930240), (1066, -12524753760), (1067, -12225940800), (1068, 4504694400), (1069, -10095405120), (1070, -16121574720), (1071, 10095405120), (1072, 63188161920), (1073, -50924900160), (1074, 47095621440), (1075, 27309787200), (1076, -10074168000), (1077, 25372248000), (1078, 39026473920), (1079, -12225940800), (1080, 50924900160), (1081, -28392524640), (1082, 19938131520), (1083, 15962798400), (1084, 39648541440), (1085, 26313788160), (1086, -18614069760), (1087, -22360001760)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock34 : Integer.Sparse (Fin 2886) := [(1088, -47238804480), (1089, 39376221600), (1090, 40618465440), (1091, 1679664960), (1092, -18611928000), (1093, -24355312320), (1094, -1930870080), (1095, 4742619840), (1096, 27842882880), (1097, -19243593600), (1098, -6689957760), (1099, -41668538880), (1100, -21260339520), (1101, -4572421440), (1102, 26705880000), (1103, 7207872000), (1104, -26705880000), (1105, -7207872000), (1106, 13825656000), (1107, 24529604160), (1108, 21275371200), (1109, 18611928000), (1110, 12182188800), (1111, 1930870080), (1112, -10012992000), (1113, 9714124800), (1114, 3043320000), (1115, -602036640), (1116, 7662680640), (1117, 12231642240), (1118, -8983886400), (1119, 44248805760)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock35 : Integer.Sparse (Fin 2886) := [(1120, -9410139840), (1121, -22619797440), (1122, -37160467200), (1123, -41039222400), (1124, -9714124800), (1125, 8983886400), (1126, -44251121280), (1127, 32398181760), (1128, 37160467200), (1129, 41036906880), (1130, -3043320000), (1131, 20813687520), (1132, -6731640000), (1133, -32827296960), (1134, 21079798560), (1135, -3096668160), (1136, -32100528000), (1137, 28835668800), (1138, -24524249760), (1139, 13071264960), (1140, -33681320640), (1141, 2919001920), (1142, -20960256960), (1143, 27444600000), (1144, 16110261120), (1145, 6236720640), (1146, 31687339200), (1147, 122837110080), (1148, -9576076800), (1149, -130091384000), (1150, 18828969360), (1151, -2489739840)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock36 : Integer.Sparse (Fin 2886) := [(1152, -69426360000), (1153, 99565244000), (1154, 102398444800), (1155, 78169707040), (1156, -17487314800), (1157, -1075968000), (1158, -11396067600), (1159, -3560809200), (1160, -31561775200), (1161, -6982212000), (1162, 11104874400), (1163, 3560809200), (1164, 291193200), (1165, -31687339200), (1166, -160946364480), (1167, 20693438400), (1168, 126898217120), (1169, -18828969360), (1170, 37891362240), (1171, 41215104000), (1172, -121005753600), (1173, 15908878400), (1174, -104300972640), (1175, 64664352000), (1176, 19120223520), (1177, 11396067600), (1178, 3560809200), (1179, 11800540800), (1180, 21440509600), (1181, 7362845120), (1182, -47177037200), (1183, -58083479520)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock37 : Integer.Sparse (Fin 2886) := [(1184, -21792797600), (1185, -32676890400), (1186, -11104874400), (1187, -3560809200), (1188, -291193200), (1189, 38109254400), (1190, 28211256000), (1191, 21440509600), (1192, -118307323200), (1193, 26131265600), (1194, 31561775200), (1195, 6982212000), (1196, -11104874400), (1197, -3560809200), (1198, -21440509600), (1199, -7362845120), (1200, 21792797600), (1201, 32676890400), (1202, 11104874400), (1203, 3560809200), (1204, -11117361600), (1205, -47177037200), (1206, -24430589280), (1207, -291193200), (1208, 47177037200), (1209, 54890312640), (1210, 291193200), (1211, -43347340800), (1212, 29740402080), (1213, -3951411840), (1214, -24973506720), (1215, -22104192000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock38 : Integer.Sparse (Fin 2886) := [(1216, 20210904000), (1217, -60504474240), (1218, -90704725440), (1219, 37611000000), (1220, -22127928000), (1221, 10987226880), (1222, -56876813760), (1223, 33608041920), (1224, -7891734240), (1225, 22104192000), (1226, 15341940000), (1227, 65343541440), (1228, -9891735360), (1229, -10987226880), (1230, 19265813760), (1231, 3561901440), (1232, -13716326400), (1233, -31734372480), (1234, 11830790400), (1235, 112785109280), (1236, -33383971440), (1237, 25763754240), (1238, 36762840000), (1239, -123451736000), (1240, -189998147200), (1241, -69810220960), (1242, 60239702800), (1243, 24022892160), (1244, 11396067600), (1245, 3560809200), (1246, 86879699200), (1247, 68743742400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock39 : Integer.Sparse (Fin 2886) := [(1248, -11104874400), (1249, -3560809200), (1250, -291193200), (1251, 91030713600), (1252, -49478184000), (1253, -88127299200), (1254, 54562934400), (1255, 30092011200), (1256, 58035288000), (1257, 49478184000), (1258, 24742564800), (1259, 13716326400), (1260, 1298386560), (1261, -33543998400), (1262, -115978276160), (1263, 33383971440), (1264, 9637868160), (1265, -16078464000), (1266, 121005753600), (1267, 78487319200), (1268, 42507384960), (1269, -43220870400), (1270, -44737755360), (1271, -11396067600), (1272, -3560809200), (1273, -91030713600), (1274, 110625926400), (1275, -23566032000), (1276, 49478184000), (1277, 88127299200), (1278, 34898174400), (1279, 64718544000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock4 : Integer.Sparse (Fin 2886) := [(128, -1527638400), (129, 867035520), (130, -9452638720), (131, 2943398400), (132, -6600101760), (133, -6036938560), (134, 545198400), (135, -5891803040), (136, -33069067200), (137, -49685040000), (138, -12000871440), (139, 12379132800), (140, 12066415040), (141, -8842310400), (142, -3429192960), (143, -4486000320), (144, -35552785920), (145, 197436160), (146, 3517361120), (147, -6600101760), (148, 14513679360), (149, 25793022400), (150, -17628934080), (151, -1539187200), (152, 1541328000), (153, 2565312000), (154, 735849600), (155, -1541328000), (156, 5052748800), (157, 513062400), (158, 75577280), (159, -10737091200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock40 : Integer.Sparse (Fin 2886) := [(1280, 90276033600), (1281, -58035288000), (1282, -52661520000), (1283, 11800540800), (1284, 2445982400), (1285, -40959046880), (1286, -17018832400), (1287, -40602700320), (1288, -22297619200), (1289, -37544311200), (1290, 11104874400), (1291, 3560809200), (1292, 291193200), (1293, 30435985920), (1294, -20684376000), (1295, 2445982400), (1296, 111510828000), (1297, 27302836000), (1298, -86879699200), (1299, -68743742400), (1300, 11104874400), (1301, 3560809200), (1302, -110625926400), (1303, -30092011200), (1304, -90276033600), (1305, -2445982400), (1306, 40959046880), (1307, 22297619200), (1308, 37544311200), (1309, -11104874400), (1310, -3560809200), (1311, 21713208000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock41 : Integer.Sparse (Fin 2886) := [(1312, -17018832400), (1313, 14328529440), (1314, 291193200), (1315, 23566032000), (1316, -58035288000), (1317, -49478184000), (1318, 58035288000), (1319, 52661520000), (1320, 17018832400), (1321, 37409533440), (1322, -291193200), (1323, 61018948800), (1324, 86787635040), (1325, 46598368320), (1326, -24973506720), (1327, 22104192000), (1328, 109088208000), (1329, 37691688960), (1330, -8201856960), (1331, 32595648000), (1332, 25460485440), (1333, -78060799680), (1334, 1506232320), (1335, -21544810560), (1336, -1362458880), (1337, 22670596800), (1338, 25670966400), (1339, 2266787520), (1340, -45977080320), (1341, 41107896000), (1342, 2266787520), (1343, -41107896000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock42 : Integer.Sparse (Fin 2886) := [(1344, -2970057600), (1345, -26715732480), (1346, -4533575040), (1347, 52311168000), (1348, -52311168000), (1349, -7891734240), (1350, -22104192000), (1351, 15341940000), (1352, -74367161280), (1353, -37363283520), (1354, -1506232320), (1355, 2970057600), (1356, -25064469120), (1357, 25436791680), (1358, 966442560), (1359, -28143720000), (1360, -105367920000), (1361, -25225598400), (1362, 71961876000), (1363, 120667120320), (1364, 55501712640), (1365, -40269264000), (1366, -33493728000), (1367, 16369293120), (1368, 50334995520), (1369, -26364576000), (1370, -11764436160), (1371, 6565147200), (1372, -3582112320), (1373, -36428678400), (1374, 61334378880), (1375, -7770451200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock43 : Integer.Sparse (Fin 2886) := [(1376, 24607056000), (1377, -91344896000), (1378, 40644088560), (1379, 37128933120), (1380, -8551584000), (1381, 116316597600), (1382, 13325332000), (1383, 65205118080), (1384, -39856968000), (1385, -54907276800), (1386, -11396067600), (1387, -3560809200), (1388, -24607056000), (1389, -5177069760), (1390, -36703621600), (1391, -36738299360), (1392, -20382734800), (1393, -47565599040), (1394, -11371866400), (1395, 7127592000), (1396, 11104874400), (1397, 3560809200), (1398, 291193200), (1399, 72370704000), (1400, 81295103040), (1401, 48699081600), (1402, -24607056000), (1403, 71909843360), (1404, -55199090640), (1405, 9746162880), (1406, 16078464000), (1407, -140203089600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock44 : Integer.Sparse (Fin 2886) := [(1408, -20121827200), (1409, -84460621920), (1410, 61165874400), (1411, 59801372160), (1412, 11396067600), (1413, 3560809200), (1414, 45515356800), (1415, 27656481600), (1416, 23566032000), (1417, 29820369600), (1418, 54562934400), (1419, 30092011200), (1420, 3183336000), (1421, 24607056000), (1422, 28451084160), (1423, 36703621600), (1424, 45680181440), (1425, 41826216400), (1426, 47400364800), (1427, 144359200), (1428, 1332079200), (1429, -11104874400), (1430, -3560809200), (1431, -291193200), (1432, 28143720000), (1433, 62555452800), (1434, 12534105600), (1435, -73767985920), (1436, -97679078400), (1437, -18806785920), (1438, 4357972800), (1439, -100576605120)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock45 : Integer.Sparse (Fin 2886) := [(1440, -51075779520), (1441, -35840326080), (1442, -35942025600), (1443, -99611985600), (1444, 11784321600), (1445, 13048718880), (1446, 14555002080), (1447, 23928148800), (1448, 24607056000), (1449, 40578692160), (1450, 19197336000), (1451, -10898468640), (1452, -17945004000), (1453, -35897460960), (1454, -45515356800), (1455, 34898174400), (1456, -24607056000), (1457, 6950538240), (1458, 4689156000), (1459, -50312723040), (1460, -24807384000), (1461, -46836888480), (1462, 12231642240), (1463, 33493728000), (1464, 35564084160), (1465, 26364576000), (1466, 3229858560), (1467, 30595320000), (1468, 4665144000), (1469, 42812467200), (1470, 35911291200), (1471, 33493728000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock46 : Integer.Sparse (Fin 2886) := [(1472, 84202680960), (1473, 46716867840), (1474, -6565147200), (1475, 3579796800), (1476, -43017496320), (1477, -7526880000), (1478, 23886492000), (1479, 6796495200), (1480, 19255503840), (1481, 17506285600), (1482, 47636768000), (1483, 11371866400), (1484, -7127592000), (1485, -11104874400), (1486, -3560809200), (1487, -27656481600), (1488, -30092011200), (1489, -41392777600), (1490, 4632541600), (1491, -144359200), (1492, -1332079200), (1493, 11104874400), (1494, 3560809200), (1495, -33493728000), (1496, -12576042240), (1497, -30595320000), (1498, -4667459520), (1499, 12691492800), (1500, 26364576000), (1501, 43992542400), (1502, -52712952000), (1503, -21308906400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock47 : Integer.Sparse (Fin 2886) := [(1504, -11280429120), (1505, 38327738800), (1506, 77076726240), (1507, -291193200), (1508, -23566032000), (1509, -3183336000), (1510, -17018832400), (1511, -6949810080), (1512, 291193200), (1513, -26364576000), (1514, -5035968480), (1515, 6731640000), (1516, 2212876800), (1517, -38890668960), (1518, -9290004480), (1519, 32100528000), (1520, -29404575360), (1521, 62360648640), (1522, -13995250560), (1523, 15206696640), (1524, 4231169280), (1525, 14870793600), (1526, 28580212800), (1527, 471075840), (1528, 27338481600), (1529, -17671608000), (1530, -106770856320), (1531, -75915910080), (1532, -48648709440), (1533, -129299112000), (1534, 5397932160), (1535, 123079896000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock48 : Integer.Sparse (Fin 2886) := [(1536, -840140160), (1537, -63071485440), (1538, 7230439680), (1539, 12493459200), (1540, -24973506720), (1541, -22104192000), (1542, -8201856960), (1543, -60036387840), (1544, 22800864960), (1545, -18961989120), (1546, -21544810560), (1547, 1362458880), (1548, 13514102400), (1549, -25670966400), (1550, 47794132800), (1551, -2266787520), (1552, -2484794880), (1553, -41107896000), (1554, -45977080320), (1555, 2266787520), (1556, 54185688000), (1557, -2970057600), (1558, -24973506720), (1559, 22104192000), (1560, -60504474240), (1561, 98417945280), (1562, -2661295680), (1563, 18961989120), (1564, 2970057600), (1565, 62675469120), (1566, 57263882880), (1567, -13077792000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock49 : Integer.Sparse (Fin 2886) := [(1568, -3096668160), (1569, -24524249760), (1570, -27254740800), (1571, -32184268800), (1572, -14870793600), (1573, -12493459200), (1574, -20960256960), (1575, -27915675840), (1576, 9764081280), (1577, -6390299520), (1578, 12237903360), (1579, -966442560), (1580, -21563601600), (1581, -40147420800), (1582, 144824639040), (1583, 49328320320), (1584, -67755787200), (1585, -20345959680), (1586, -29600006400), (1587, -28211256000), (1588, -2243173600), (1589, 59941831200), (1590, 15821971360), (1591, 90244812800), (1592, 79604035200), (1593, 11104874400), (1594, 3560809200), (1595, 2243173600), (1596, 18261313760), (1597, -121446125600), (1598, -83050905600), (1599, -11104874400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock5 : Integer.Sparse (Fin 2886) := [(160, 4627601280), (161, -1839624000), (162, 6600101760), (163, 8579179840), (164, 19375987680), (165, 6081626560), (166, -11714846400), (167, -1392067040), (168, 1121429520), (169, -2556859680), (170, -3692998080), (171, -2495842560), (172, -772712640), (173, 1352247120), (174, -2781372480), (175, -1990157760), (176, 4570859280), (177, 2300262080), (178, -2990666880), (179, 206942400), (180, -1656021360), (181, -4263292800), (182, -513062400), (183, 20407262400), (184, -4783584000), (185, -11433947040), (186, 19966740480), (187, 513062400), (188, -10614174720), (189, 4783584000), (190, -14975055360), (191, 6177366720)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock50 : Integer.Sparse (Fin 2886) := [(1600, -3560809200), (1601, 69175999680), (1602, -44642664000), (1603, 2243173600), (1604, -140745038400), (1605, 11793018560), (1606, -34926888800), (1607, -17842504800), (1608, -11104874400), (1609, -3560809200), (1610, -27656481600), (1611, -30092011200), (1612, -2243173600), (1613, 9353676160), (1614, 132673632800), (1615, 104070986400), (1616, 11104874400), (1617, 3560809200), (1618, 21563601600), (1619, 17699832000), (1620, -144826954560), (1621, -26340278400), (1622, 37160467200), (1623, -24276918720), (1624, -39575993280), (1625, 72853920000), (1626, 80803207200), (1627, -27614989920), (1628, -2243173600), (1629, -18261313760), (1630, 88281461600), (1631, 57501607200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock51 : Integer.Sparse (Fin 2886) := [(1632, 11104874400), (1633, 3560809200), (1634, 27656481600), (1635, 30092011200), (1636, 2243173600), (1637, -9353676160), (1638, -154826892800), (1639, -140283218400), (1640, -11104874400), (1641, -3560809200), (1642, 7662680640), (1643, 30595320000), (1644, 4664372160), (1645, 22447588800), (1646, 30595320000), (1647, 44618247360), (1648, -55317924000), (1649, -61761530400), (1650, 33164664000), (1651, 25549298400), (1652, 22153260000), (1653, 36212232000), (1654, -30595320000), (1655, -4666687680), (1656, 41525403840), (1657, 7131669120), (1658, -31065164640), (1659, -20695098240), (1660, -2869326720), (1661, -16331302080), (1662, -35264439360), (1663, 11728944960)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock52 : Integer.Sparse (Fin 2886) := [(1664, 5159059200), (1665, -13563699840), (1666, -43089621120), (1667, -34178477760), (1668, 53994753600), (1669, -5630924160), (1670, 18714173760), (1671, 73534622400), (1672, 15306086400), (1673, 6777233280), (1674, -32091895680), (1675, 24375447360), (1676, -24661774080), (1677, -8993124480), (1678, -5630924160), (1679, -47794132800), (1680, -2266787520), (1681, 2266787520), (1682, -13077792000), (1683, 12286451520), (1684, -21902857920), (1685, -37611000000), (1686, 11682981120), (1687, 13077792000), (1688, 3865770240), (1689, 18457999200), (1690, 20695098240), (1691, 36961007040), (1692, 22528468800), (1693, -11728944960), (1694, -17995943040), (1695, 10446238080)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock53 : Integer.Sparse (Fin 2886) := [(1696, -3865770240), (1697, -3223732800), (1698, 12618492000), (1699, -2352340800), (1700, 29232033200), (1701, 851860800), (1702, 291193200), (1703, -29232033200), (1704, -23250407520), (1705, -291193200), (1706, -34066862400), (1707, -7788551600), (1708, 12943412160), (1709, -291193200), (1710, -23566032000), (1711, -3183336000), (1712, 7788551600), (1713, 5169799200), (1714, 291193200), (1715, 3223732800), (1716, -14424601920), (1717, 36419203200), (1718, -21443481600), (1719, -20181606720), (1720, 29232033200), (1721, 20057240640), (1722, 291193200), (1723, 23566032000), (1724, 3183336000), (1725, -7788551600), (1726, -8362966080), (1727, -291193200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock54 : Integer.Sparse (Fin 2886) := [(1728, -602036640), (1729, 37530025920), (1730, -4526850240), (1731, -13666114560), (1732, 1759960320), (1733, 47007820800), (1734, -41642377920), (1735, 81664291200), (1736, -610496640), (1737, 3613479840), (1738, -80007093120), (1739, -10036861440), (1740, 23704545600), (1741, -23704545600), (1742, 36226100160), (1743, -36226100160), (1744, 4881795840), (1745, 29740402080), (1746, -1657198080), (1747, 13375184640), (1748, -4881795840), (1749, -21383216640), (1750, 13666114560), (1751, -1759960320), (1752, -2727826560), (1753, 9939297600), (1754, 10688469120), (1755, 1831777920), (1756, 30805021440), (1757, -1831777920), (1758, -29397516480), (1759, -577347840)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock55 : Integer.Sparse (Fin 2886) := [(1760, 60791849280), (1761, 1154695680), (1762, 30959360640), (1763, -1831777920), (1764, -577347840), (1765, -4359585600), (1766, 1831777920), (1767, -7542887040), (1768, -6917552640), (1769, 3478201920), (1770, 151724160), (1771, 23664430080), (1772, 37304058240), (1773, 151724160), (1774, 3478201920), (1775, 7542887040), (1776, -53169154560), (1777, -25170687360), (1778, -303448320), (1779, -25170687360), (1780, 6917552640), (1781, -6956403840), (1782, -1172142720), (1783, -20813333760), (1784, 13131941760), (1785, 45081736800), (1786, 15860171520), (1787, -12898039680), (1788, -8498807520), (1789, 29504724480), (1790, 13037316480), (1791, -10296464640)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock56 : Integer.Sparse (Fin 2886) := [(1792, -19041576000), (1793, 18466607040), (1794, -13131941760), (1795, -49561960800), (1796, 34778529600), (1797, 17459255520), (1798, -4480224000), (1799, -30968316480), (1800, -22351752960), (1801, -15860171520), (1802, -11202278400), (1803, -13532618880), (1804, -20109456000), (1805, 915603840), (1806, 1949826240), (1807, -5904316800), (1808, 4422816000), (1809, 47828960640), (1810, 37489950720), (1811, -5904316800), (1812, 1949826240), (1813, 20109456000), (1814, -47828960640), (1815, -18744975360), (1816, 11808633600), (1817, -18744975360), (1818, -6965038080), (1819, -2891059200), (1820, 14527101600), (1821, 7235763840), (1822, 1090258560), (1823, 26360455680)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock57 : Integer.Sparse (Fin 2886) := [(1824, 24067801440), (1825, 9468954720), (1826, -9264926880), (1827, 3846663360), (1828, 77009292000), (1829, -31227593760), (1830, -9468954720), (1831, -77009292000), (1832, 13532618880), (1833, 50291959680), (1834, -17272396800), (1835, -7210152000), (1836, 41929908480), (1837, -2211408000), (1838, -2211408000), (1839, 41929908480), (1840, -7210152000), (1841, -50291959680), (1842, -47828960640), (1843, -18744975360), (1844, -41929908480), (1845, -41929908480), (1846, -18744975360), (1847, 23321831040), (1848, 6705855360), (1849, 6705855360), (1850, -14527101600), (1851, -7235763840), (1852, -1090258560), (1853, -26360455680), (1854, -24067801440), (1855, 9468954720)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock58 : Integer.Sparse (Fin 2886) := [(1856, -22831165440), (1857, -13668665760), (1858, 32313669600), (1859, 15078927840), (1860, -35549871840), (1861, 20421514080), (1862, -7975556160), (1863, -9468954720), (1864, -32313669600), (1865, 47828960640), (1866, 18744975360), (1867, 18744975360), (1868, 3829473600), (1869, 10847290560), (1870, 3671820480), (1871, 23307218400), (1872, -152009150400), (1873, -59820541920), (1874, 119695480800), (1875, -13485216000), (1876, 46573672320), (1877, -33906730080), (1878, 48973251360), (1879, 74999858400), (1880, 13485216000), (1881, -42686188800), (1882, -17356602240), (1883, 8282807520), (1884, 79225920), (1885, 16069440000), (1886, 45201499680), (1887, 24044996160)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock59 : Integer.Sparse (Fin 2886) := [(1888, -16069440000), (1889, -18627731520), (1890, 18277105920), (1891, 8835269760), (1892, 64004486400), (1893, 18317710080), (1894, -1911841920), (1895, 18317710080), (1896, -17670539520), (1897, -64004486400), (1898, -18317710080), (1899, 1911841920), (1900, 1911841920), (1901, -18317710080), (1902, -64004486400), (1903, -18317710080), (1904, -18317710080), (1905, -5286291840), (1906, -38544670080), (1907, -29071918080), (1908, -118767916800), (1909, 13532618880), (1910, -30182503680), (1911, 16356792960), (1912, 5260325760), (1913, -36025591680), (1914, -2211408000), (1915, 8835269760), (1916, -1911841920), (1917, -2211408000), (1918, -36025591680), (1919, 5260325760)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock6 : Integer.Sparse (Fin 2886) := [(192, 6472454400), (193, 10729172160), (194, 10027419840), (195, -3178736640), (196, 12092544000), (197, -14184489600), (198, -16599544320), (199, 6052872960), (200, -1471699200), (201, 6346624320), (202, -6052872960), (203, 23375734560), (204, 115439281240), (205, 73742764800), (206, -394570560), (207, -59013377800), (208, -73742764800), (209, 8667519600), (210, 4891350000), (211, 4593000600), (212, -4891350000), (213, -4593000600), (214, -23375734560), (215, -107829550840), (216, -73742764800), (217, 394570560), (218, 31660828800), (219, 32308070400), (220, -11573959920), (221, -4891350000), (222, -4593000600), (223, 3563376000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock60 : Integer.Sparse (Fin 2886) := [(1920, 30182503680), (1921, 36025591680), (1922, 64004486400), (1923, 36635420160), (1924, 36025591680), (1925, -10307358720), (1926, -5764622400), (1927, -5764622400), (1928, -14527101600), (1929, -7235763840), (1930, -1090258560), (1931, -26360455680), (1932, -24067801440), (1933, -18937909440), (1934, 32096092320), (1935, 9822002400), (1936, -109322961600), (1937, 16148665920), (1938, 10572583680), (1939, 77089340160), (1940, 29071918080), (1941, 118767916800), (1942, -17240785920), (1943, -8881524000), (1944, -15952749600), (1945, -18937909440), (1946, 21359265600), (1947, 36002526720), (1948, 23979399840), (1949, -32227714560), (1950, -32583814560), (1951, 28257823200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock61 : Integer.Sparse (Fin 2886) := [(1952, 14650172640), (1953, 81065138400), (1954, 18915148800), (1955, 29083992000), (1956, -29083992000), (1957, 29071918080), (1958, 118767916800), (1959, -22846209600), (1960, 27796672800), (1961, -30472704000), (1962, -17303419200), (1963, -18915148800), (1964, -4055846400), (1965, -9114832320), (1966, 18800954880), (1967, 31148367840), (1968, -16069440000), (1969, 5635431360), (1970, -5635431360), (1971, -14826551040), (1972, -116690400), (1973, 16069440000), (1974, 40518361920), (1975, 17242670400), (1976, 34485340800), (1977, -7331790720), (1978, 7542887040), (1979, 6917552640), (1980, -3478201920), (1981, -151724160), (1982, -13532618880), (1983, 2211408000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock62 : Integer.Sparse (Fin 2886) := [(1984, 2211408000), (1985, -151724160), (1986, -3478201920), (1987, -7542887040), (1988, 5840294400), (1989, -12133370880), (1990, 151724160), (1991, 151724160), (1992, -12133370880), (1993, -6917552640), (1994, 3478201920), (1995, -6049434240), (1996, 504296640), (1997, 504296640), (1998, 3478201920), (1999, 1172142720), (2000, 20813333760), (2001, -13131941760), (2002, -45081736800), (2003, -15860171520), (2004, 14527101600), (2005, 7235763840), (2006, 1090258560), (2007, 26360455680), (2008, 24067801440), (2009, 35549871840), (2010, -20421514080), (2011, 7975556160), (2012, -5286291840), (2013, -38544670080), (2014, 17240785920), (2015, 8881524000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock63 : Integer.Sparse (Fin 2886) := [(2016, 15952749600), (2017, -5862948480), (2018, 447692640), (2019, -5840294400), (2020, 12133370880), (2021, 12133370880), (2022, 10296464640), (2023, 30322132800), (2024, 1175356800), (2025, 13131941760), (2026, 49561960800), (2027, 23623006080), (2028, 4018583520), (2029, -39832000320), (2030, -34826690400), (2031, 1672306560), (2032, 9276596160), (2033, 123751327200), (2034, 5855827200), (2035, 33906730080), (2036, 4287736800), (2037, -14428365600), (2038, -18915148800), (2039, -29083992000), (2040, 12073920), (2041, -118767916800), (2042, 30085022400), (2043, -27796672800), (2044, 98133722880), (2045, -68101300800), (2046, 13485216000), (2047, -3772083840)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock64 : Integer.Sparse (Fin 2886) := [(2048, 1681554240), (2049, -5375609280), (2050, 5429932800), (2051, 4480224000), (2052, 46742035200), (2053, 30968316480), (2054, 30573719040), (2055, 15860171520), (2056, 26471434560), (2057, 17820905760), (2058, -31227593760), (2059, -34466263200), (2060, -24044996160), (2061, 16069440000), (2062, -5635431360), (2063, -22541725440), (2064, 16611600000), (2065, 116690400), (2066, -16069440000), (2067, -11211492480), (2068, 11202278400), (2069, -21890630400), (2070, -18277105920), (2071, -17242670400), (2072, -34485340800), (2073, 7331790720), (2074, -11280556800), (2075, -45503496000), (2076, -12979031520), (2077, 4480224000), (2078, 54639324000), (2079, -123751327200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock65 : Integer.Sparse (Fin 2886) := [(2080, -43792033440), (2081, -28257823200), (2082, 42686188800), (2083, -48723109440), (2084, 64045454400), (2085, 4055846400), (2086, 4181394240), (2087, 4927916640), (2088, -4480224000), (2089, -46742035200), (2090, -27863929920), (2091, -18021080640), (2092, -5429932800), (2093, -63164736000), (2094, 5429932800), (2095, 34719423360), (2096, -6542266560), (2097, -9023861760), (2098, 5429932800), (2099, 14983576320), (2100, -5429932800), (2101, 28588357440), (2102, 173684799360), (2103, 198521277840), (2104, 84976313760), (2105, 22112948160), (2106, 218407535040), (2107, 36277422720), (2108, -4352643360), (2109, -6833967600), (2110, 52544808000), (2111, 332760998400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock66 : Integer.Sparse (Fin 2886) := [(2112, 131229672720), (2113, -9690454880), (2114, -26760117120), (2115, 18091419840), (2116, -57081145120), (2117, -6363334320), (2118, 16189117920), (2119, 99197019360), (2120, 40264353360), (2121, 81239126400), (2122, 20783692320), (2123, -15832544160), (2124, 20936366640), (2125, -59143728960), (2126, -29358881040), (2127, 81173468160), (2128, 74963023680), (2129, 82255072920), (2130, 2628710400), (2131, 37334957520), (2132, -31265090760), (2133, -47344442160), (2134, 10032668640), (2135, -40049530080), (2136, -59091869600), (2137, -22095397440), (2138, -16215945520), (2139, -61828894080), (2140, 186807476960), (2141, -19790860320), (2142, -224386793040), (2143, -106234789400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock67 : Integer.Sparse (Fin 2886) := [(2144, -38713886160), (2145, 51869179200), (2146, -51294132000), (2147, -261293431200), (2148, -179224764720), (2149, -61019927040), (2150, -28722546720), (2151, -257170321440), (2152, 26557454640), (2153, -71129433600), (2154, 41502743040), (2155, -70455217920), (2156, -181490878800), (2157, 498528600), (2158, -10195068000), (2159, -144585806880), (2160, -4411204680), (2161, 35352758640), (2162, -66991429440), (2163, -145433555520), (2164, -26688552960), (2165, -30261856320), (2166, -20113308480), (2167, 18952239360), (2168, 31531533120), (2169, 22459008000), (2170, -35781227520), (2171, 109742042880), (2172, -179535872640), (2173, 7047137280), (2174, -198362880), (2175, -1269676800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock68 : Integer.Sparse (Fin 2886) := [(2176, -5614752000), (2177, -11068343040), (2178, -244351925760), (2179, -19789087680), (2180, 41492083200), (2181, -79879749600), (2182, -5820135840), (2183, -108445633760), (2184, 32040920640), (2185, 3331916000), (2186, -34052750400), (2187, -202090914000), (2188, 27361002240), (2189, 27803192880), (2190, 131029924320), (2191, 95785122320), (2192, 86974335360), (2193, 30987058800), (2194, -5186510400), (2195, -5864927880), (2196, -10946874240), (2197, -70512808320), (2198, -35933301360), (2199, -8729926560), (2200, 2785553280), (2201, -64386633600), (2202, 15131114400), (2203, 28779193920), (2204, 12247949280), (2205, 2152584000), (2206, 30023799840), (2207, 28430653200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock69 : Integer.Sparse (Fin 2886) := [(2208, 2325747648), (2209, 10174585920), (2210, 14458983120), (2211, 6983544192), (2212, 41118433920), (2213, 105727698240), (2214, 127482366800), (2215, 94717871040), (2216, -59917721280), (2217, 90265586880), (2218, 15186376800), (2219, 13468067520), (2220, 13111545984), (2221, -75491113920), (2222, 141650632560), (2223, 17611916400), (2224, 127434411360), (2225, 40687487520), (2226, 37452674880), (2227, 90834899520), (2228, -30881651760), (2229, 16489344000), (2230, 248886167040), (2231, -34073200800), (2232, 82874491680), (2233, -20093569560), (2234, -22251735600), (2235, 71848187280), (2236, 140375734080), (2237, 31275884160), (2238, -15890849280), (2239, 13876855680)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock7 : Integer.Sparse (Fin 2886) := [(224, 39552482400), (225, -14861740000), (226, 41434694400), (227, 18209881120), (228, 4891350000), (229, 5817800760), (230, 15152615600), (231, 41434694400), (232, 4891350000), (233, 3368200440), (234, -27352549000), (235, 13247688000), (236, -41434694400), (237, -4891350000), (238, -4593000600), (239, 18041921120), (240, -10516170720), (241, -5851062720), (242, -6062232000), (243, -3563376000), (244, -11702125440), (245, 5946276480), (246, 5177428000), (247, 6703008000), (248, 5946276480), (249, 42004716480), (250, 7373970720), (251, 6062232000), (252, 21755694240), (253, -5851062720), (254, -5946276480), (255, -17437040160)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock70 : Integer.Sparse (Fin 2886) := [(2240, 387034596480), (2241, -317340480), (2242, 65403264000), (2243, -14236499520), (2244, -22459008000), (2245, 31022502720), (2246, -34636753920), (2247, 65283607200), (2248, -7593210720), (2249, -20547720000), (2250, -77691031680), (2251, -53975601840), (2252, -81358596480), (2253, -26794424880), (2254, 9476558400), (2255, -17825395200), (2256, -46727562960), (2257, -3888915600), (2258, -14076578880), (2259, -23975871120), (2260, -41492083200), (2261, -29704458240), (2262, -646280640), (2263, -25185862720), (2264, -4758454560), (2265, -3924651520), (2266, -3210480000), (2267, -48398638560), (2268, 37284743040), (2269, -1027497360), (2270, 20981767680), (2271, 18184504880)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock71 : Integer.Sparse (Fin 2886) := [(2272, 12093438960), (2273, -2346018240), (2274, -90318763200), (2275, -2917087344), (2276, -56027260920), (2277, -69533421440), (2278, -25204183200), (2279, -229294560), (2280, 26555973120), (2281, 3168586560), (2282, -32912653520), (2283, 18985004304), (2284, 36446353920), (2285, -19642180080), (2286, -128076984960), (2287, 9755589600), (2288, -126326566320), (2289, -21978605760), (2290, 59460313280), (2291, 61205507520), (2292, 36587845440), (2293, -2541376080), (2294, 18377043840), (2295, 34751568000), (2296, -17877500160), (2297, 14621172480), (2298, -45802977600), (2299, 15506176320), (2300, 53361129600), (2301, 60118089920), (2302, 45650111040), (2303, 14396377440)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock72 : Integer.Sparse (Fin 2886) := [(2304, -40972413840), (2305, -77676135840), (2306, 36844286400), (2307, 25195671720), (2308, -12603127200), (2309, 7954347360), (2310, 11445253440), (2311, 23602894080), (2312, -19191440400), (2313, 116784693840), (2314, 34694184720), (2315, 55110368040), (2316, -1135962080), (2317, -2048698800), (2318, -16433028000), (2319, -10159945920), (2320, 28138372240), (2321, 28477512240), (2322, -11229504000), (2323, 19651632000), (2324, -20746041600), (2325, 28493753680), (2326, 24670783920), (2327, 36305572800), (2328, 2446403760), (2329, 2199785280), (2330, 65612752640), (2331, 13749933600), (2332, 63950874000), (2333, 68274009600), (2334, -27617621760), (2335, 10138864800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock73 : Integer.Sparse (Fin 2886) := [(2336, 27036763920), (2337, -121147853760), (2338, -31378885680), (2339, -16312046640), (2340, 68642441640), (2341, -42708115440), (2342, 14341033920), (2343, -47280171000), (2344, -3525346560), (2345, 20512214240), (2346, 10132584400), (2347, -4546412160), (2348, 13639726320), (2349, -2610481920), (2350, -67065433960), (2351, 49078791360), (2352, 7161813520), (2353, 4332624480), (2354, 126626353200), (2355, 179046816960), (2356, 709566437880), (2357, -29606574240), (2358, 94694929440), (2359, -118232166400), (2360, 70240364800), (2361, 17100179040), (2362, -82568679560), (2363, 17250203520), (2364, 90512788240), (2365, 284801434440), (2366, -39662974560), (2367, 8053488080)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock74 : Integer.Sparse (Fin 2886) := [(2368, -65205723240), (2369, -49374989440), (2370, 22604714640), (2371, -144898064640), (2372, -246620576520), (2373, 120897845280), (2374, -77627280960), (2375, -201403157520), (2376, -56208224160), (2377, -156245208240), (2378, -33567760200), (2379, -10938011520), (2380, 10255934320), (2381, 48045374040), (2382, -34148752320), (2383, -45145603680), (2384, -232946023840), (2385, 40053479760), (2386, 2851571760), (2387, -6312192000), (2388, 149837521040), (2389, -16009994800), (2390, -35794478480), (2391, -166129114320), (2392, 18535552720), (2393, 118855596480), (2394, 7836927760), (2395, 57340892880), (2396, 29474272080), (2397, -2890879280), (2398, -111359264160), (2399, 97266550160)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock75 : Integer.Sparse (Fin 2886) := [(2400, -49540614480), (2401, 19060092560), (2402, -241843442320), (2403, -124444539240), (2404, 134291832480), (2405, 62008066480), (2406, 15404358800), (2407, -10586607200), (2408, 22573682640), (2409, -19248180720), (2410, -92871236160), (2411, -204446844240), (2412, 277437109200), (2413, -90645302880), (2414, -13262269160), (2415, 4553906000), (2416, -256088763600), (2417, -49077475480), (2418, -32732670720), (2419, 166076389760), (2420, -17377408080), (2421, -61944523920), (2422, -144865072880), (2423, -159417459120), (2424, -78861139280), (2425, 171064210560), (2426, 163572001920), (2427, 26302040160), (2428, 40561427520), (2429, 53989962240), (2430, 114245799840), (2431, 59984395200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock76 : Integer.Sparse (Fin 2886) := [(2432, -74677500000), (2433, 39902572800), (2434, 277266644640), (2435, 145494670080), (2436, -104137225920), (2437, 4560264960), (2438, -143659440000), (2439, 7336967200), (2440, -170220652800), (2441, 24549885760), (2442, -173815992000), (2443, -68900767200), (2444, 5158261120), (2445, 128688370560), (2446, 142548077280), (2447, -251085086160), (2448, 75397542720), (2449, -213667645200), (2450, -92685692160), (2451, 88699461120), (2452, 11700642624), (2453, 26420478720), (2454, 36378677920), (2455, 19932687520), (2456, -50386334880), (2457, -170767914240), (2458, -9318353280), (2459, -11069268480), (2460, 32751053760), (2461, -138298757760), (2462, -41795249280), (2463, 156207899520)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock77 : Integer.Sparse (Fin 2886) := [(2464, 59625673920), (2465, 80569291200), (2466, 90415507200), (2467, -222656215200), (2468, -35817134400), (2469, -37074625440), (2470, -73256630440), (2471, -15029351280), (2472, -28075223520), (2473, 6312192000), (2474, -333860876800), (2475, 39902572800), (2476, -1174422320), (2477, 171721161200), (2478, 71754163680), (2479, 96987695040), (2480, -31543610640), (2481, 40201116000), (2482, 251942575840), (2483, 101673310000), (2484, 90525826320), (2485, -20456109360), (2486, 6909342320), (2487, 56990279280), (2488, -25002267840), (2489, -22594677120), (2490, -222331042080), (2491, 17151888960), (2492, -96987695040), (2493, 57327463280), (2494, -4970178000), (2495, 1800137360)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock78 : Integer.Sparse (Fin 2886) := [(2496, 133109377360), (2497, 2581495960), (2498, 173815992000), (2499, 63243540000), (2500, 31159570480), (2501, 5916834080), (2502, 63279700800), (2503, -65633791200), (2504, 22988392800), (2505, 2014495680), (2506, 61881626560), (2507, -29434869600), (2508, -3120878880), (2509, -149969145600), (2510, -14079306480), (2511, -88321265280), (2512, 8725170240), (2513, -102848410080), (2514, -416271120), (2515, 97890662400), (2516, 20479536000), (2517, 23608051200), (2518, 73703074320), (2519, -15470073480), (2520, 12391456080), (2521, -28844880000), (2522, -65612324040), (2523, -28582650720), (2524, 44975981600), (2525, -158264635200), (2526, 172581972960), (2527, -151040588880)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock79 : Integer.Sparse (Fin 2886) := [(2528, -64673782080), (2529, 31184084640), (2530, 52916319280), (2531, -55902749040), (2532, 22565850336), (2533, -40363279680), (2534, -82919052640), (2535, -55872858880), (2536, 118038269760), (2537, 72946361760), (2538, 76682450400), (2539, 176570546880), (2540, 4171087840), (2541, 84249384000), (2542, -18685629280), (2543, -17400605280), (2544, -118378819600), (2545, 74745834480), (2546, 10849510160), (2547, 93928209840), (2548, 167739810240), (2549, 40021870200), (2550, 248493837600), (2551, 35303490240), (2552, 97921657320), (2553, 56559228480), (2554, 134217930960), (2555, 1828358280), (2556, 39516772800), (2557, 4773588640), (2558, -100814408880), (2559, 73844861120)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock8 : Integer.Sparse (Fin 2886) := [(256, -3563376000), (257, -6703008000), (258, -4318654080), (259, -5946276480), (260, -4206891360), (261, -20247005320), (262, -10913104800), (263, 4761687360), (264, 17523425800), (265, 10913104800), (266, 1342258080), (267, -4891350000), (268, -4593000600), (269, 4891350000), (270, 4593000600), (271, 983184000), (272, -983184000), (273, -3130436800), (274, 10341905320), (275, 10913104800), (276, -4761687360), (277, -39193252800), (278, -22606454400), (279, -10229534400), (280, 4891350000), (281, 6124000800), (282, -983184000), (283, 9831840000), (284, 29155563400), (285, -8357064000), (286, 31096581600), (287, 19727107800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock80 : Integer.Sparse (Fin 2886) := [(2560, 31541459520), (2561, -44657792160), (2562, -49852232640), (2563, 10651267200), (2564, 122991876480), (2565, -70259291520), (2566, 148491963360), (2567, 31886642880), (2568, 23979208800), (2569, -26523501600), (2570, 44837716800), (2571, -79936891680), (2572, 103267498800), (2573, -220655614320), (2574, -75840805840), (2575, -114367811520), (2576, 78936544320), (2577, -65159040000), (2578, -4824040720), (2579, -33392949200), (2580, 32205942360), (2581, -19207074240), (2582, -9298233920), (2583, 35162608800), (2584, 36502799040), (2585, 98777203200), (2586, 107266045360), (2587, 72601052160), (2588, -27682830720), (2589, 20597398080), (2590, 28063444320), (2591, 19866199680)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock81 : Integer.Sparse (Fin 2886) := [(2592, 19706327616), (2593, -23608051200), (2594, 45458951520), (2595, 21803022720), (2596, 27397679520), (2597, -120295503360), (2598, -249815111640), (2599, -146618106000), (2600, -1583273280), (2601, -97221541440), (2602, -112133076480), (2603, -57918681480), (2604, -30136375440), (2605, 111263016744), (2606, -77090685120), (2607, -55422491760), (2608, -58291364928), (2609, -154533336000), (2610, 11023403520), (2611, 45165883200), (2612, 97278520320), (2613, 22389196080), (2614, 243375339360), (2615, 1965872184), (2616, 108902126400), (2617, -84480861360), (2618, 65159040000), (2619, 51191942400), (2620, 21474181440), (2621, -93282494400), (2622, -48167756160), (2623, -59653416480)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock82 : Integer.Sparse (Fin 2886) := [(2624, -145887997200), (2625, -846506880), (2626, -48604387680), (2627, -29289765120), (2628, -67829291760), (2629, 88892606880), (2630, -38744668320), (2631, 8541086400), (2632, 124850719680), (2633, 68215020240), (2634, -52044372480), (2635, 33301422000), (2636, -70282894080), (2637, 15724160040), (2638, -34643013720), (2639, -13199134080), (2640, 206772988320), (2641, -38735335280), (2642, -152669552880), (2643, -33321692640), (2644, 23524214800), (2645, -16741642320), (2646, -59248431360), (2647, -43730807040), (2648, -41524809400), (2649, -54920555760), (2650, 4696238880), (2651, 154383516080), (2652, 47107195560), (2653, 19207074240), (2654, 60804089920), (2655, 86048565120)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock83 : Integer.Sparse (Fin 2886) := [(2656, 8689273200), (2657, 116686987200), (2658, 46987459440), (2659, -9428064960), (2660, 39641370240), (2661, 8356094400), (2662, 25571060400), (2663, 6448516320), (2664, 85165226856), (2665, -83506716880), (2666, -4466670560), (2667, -28301606400), (2668, -54421667240), (2669, 65164959920), (2670, -5759404800), (2671, 24440506640), (2672, 75158508480), (2673, -7644434160), (2674, 37314069920), (2675, 4912046640), (2676, 249303360), (2677, 31168829520), (2678, 54421821120), (2679, 57815945440), (2680, -6115859880), (2681, -2349687640), (2682, -28910416160), (2683, -111901383360), (2684, 23588739440), (2685, -29135184640), (2686, 85300658880), (2687, -7881846960)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock84 : Integer.Sparse (Fin 2886) := [(2688, 120925828800), (2689, 34333871040), (2690, 295124194240), (2691, 18758213000), (2692, 16155720480), (2693, -25307791360), (2694, -67165112880), (2695, -2034772080), (2696, 17682887520), (2697, 55271146720), (2698, 48308224200), (2699, -24528769920), (2700, -17029644480), (2701, 15275984160), (2702, 78108851520), (2703, -17194545400), (2704, -50478153360), (2705, 25338206080), (2706, -212802172000), (2707, -57578695560), (2708, 19207074240), (2709, -13314241320), (2710, -8039874240), (2711, -32556736560), (2712, -135136641600), (2713, -13241985360), (2714, -66152373120), (2715, -21855207840), (2716, 58899945120), (2717, 2985990720), (2718, -63013829520), (2719, -84110226760)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock85 : Integer.Sparse (Fin 2886) := [(2720, -123152322240), (2721, 61981314480), (2722, -48784844320), (2723, 2248083000), (2724, 59248431360), (2725, 617189760), (2726, 13467990040), (2727, 102678513360), (2728, 41470746960), (2729, 19791401920), (2730, -96553292760), (2731, -19207074240), (2732, 39601068160), (2733, 83076659520), (2734, -17253001680), (2735, 11730552000), (2736, -50180808480), (2737, -79464541920), (2738, -44732773560), (2739, -53078305800), (2740, -18203620320), (2741, -9899351640), (2742, 8815051200), (2743, -33818861040), (2744, 1090620480), (2745, -13949930640), (2746, 307527960), (2747, 33430043680), (2748, 42334134120), (2749, 21662031480), (2750, 4532419840), (2751, 17425550160)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock86 : Integer.Sparse (Fin 2886) := [(2752, -4749425680), (2753, 30723827920), (2754, 11529636880), (2755, -40891467760), (2756, -24878305840), (2757, 12932955920), (2758, -3537700800), (2759, -24240774400), (2760, 15773304000), (2761, 20010395440), (2762, -30400177280), (2763, -32053738400), (2764, -39808563600), (2765, -11048475840), (2766, -42685139784), (2767, -4183807880), (2768, -3263229280), (2769, 28301606400), (2770, 52615829600), (2771, -10038288560), (2772, 5759404800), (2773, 12229556240), (2774, -30751249440), (2775, -12420556560), (2776, 34567384320), (2777, -4411061760), (2778, -37829664000), (2779, -1563432960), (2780, 37829664000), (2781, 5614752000), (2782, -14164588800), (2783, 15559531200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock87 : Integer.Sparse (Fin 2886) := [(2784, 10373020800), (2785, 5614752000), (2786, 5186510400), (2787, 128192524800), (2788, -42336357120), (2789, -32626140000), (2790, 122293680000), (2791, 56715248160), (2792, -6462957600), (2793, -122293680000), (2794, -74677500000), (2795, -19842213120), (2796, -13875116800), (2797, -38761696800), (2798, -7336967200), (2799, 506570400), (2800, 41709844800), (2801, -49533427200), (2802, -81289584000), (2803, -56475672000), (2804, 626512320), (2805, 56475672000), (2806, 66389719680), (2807, 81289584000), (2808, 86075299200), (2809, -9717393600), (2810, -15789352800), (2811, -76405896000), (2812, -56050135200), (2813, 76405896000), (2814, 41641183200), (2815, 33408700800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock88 : Integer.Sparse (Fin 2886) := [(2816, -48344200800), (2817, 17229204000), (2818, -27995450400), (2819, 140987363520), (2820, 50555669760), (2821, 192202411200), (2822, 1255236480), (2823, -47324040000), (2824, 191985931200), (2825, -22754900160), (2826, -12673492800), (2827, -78356439360), (2828, -296620039680), (2829, 56788848000), (2830, -64948270080), (2831, 34650547200), (2832, 37859232000), (2833, -47324040000), (2834, 100765398400), (2835, -42474746880), (2836, -63619065120), (2837, -41004096000), (2838, 56475672000), (2839, -118195249920), (2840, 50555669760), (2841, 84811104000), (2842, -56475672000), (2843, -14366992320), (2844, 41004096000), (2845, 3537700800), (2846, 19033325280), (2847, -16509386400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock89 : Integer.Sparse (Fin 2886) := [(2848, 198699576000), (2849, 146133607680), (2850, -35628653280), (2851, -198699576000), (2852, 27259584000), (2853, 11397799200), (2854, -11136233600), (2855, 15069535200), (2856, -18178405600), (2857, 46994318640), (2858, 28414555200), (2859, 6419160960), (2860, 37829664000), (2861, -26084940672), (2862, -49229709120), (2863, -56475672000), (2864, 6893352000), (2865, 56475672000), (2866, -28414555200), (2867, -6106736640), (2868, -37829664000), (2869, -16844256000), (2870, 2393825280), (2871, 10373020800), (2872, -37829664000), (2873, -157695480000), (2874, 157695480000), (2875, -7631160000), (2876, 37829664000), (2877, -31119062400), (2878, -5614752000), (2879, -7075401600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock9 : Integer.Sparse (Fin 2886) := [(288, -4891350000), (289, -6736400880), (290, 14068899600), (291, 11693349600), (292, -4891350000), (293, -4593000600), (294, -6882288000), (295, -30098402800), (296, 7373880000), (297, -31096581600), (298, 4891350000), (299, 5817800760), (300, 14476542480), (301, -14809605760), (302, 31525516800), (303, -5851062720), (304, 6062232000), (305, -96702295200), (306, -11702125440), (307, 50415792000), (308, 30096136800), (309, 1675752000), (310, 2973138240), (311, 1455396480), (312, -4922282880), (313, 1455396480), (314, 1557131520), (315, -10881866880), (316, 4922282880), (317, 21031476480), (318, -2910792960), (319, 13477086080)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock90 : Integer.Sparse (Fin 2886) := [(2880, 7075401600), (2881, 8422128000), (2882, -10373020800), (2883, -1439851200), (2884, 1439851200), (2885, 15559531200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode1 : Integer.Sparse (Fin 2886) := keyPolynomialBlock3 ++ keyPolynomialBlock4

def keyPolynomialNode2 : Integer.Sparse (Fin 2886) := keyPolynomialBlock2 ++ keyPolynomialNode1

def keyPolynomialNode4 : Integer.Sparse (Fin 2886) := keyPolynomialBlock6 ++ keyPolynomialBlock7

def keyPolynomialNode5 : Integer.Sparse (Fin 2886) := keyPolynomialBlock5 ++ keyPolynomialNode4

def keyPolynomialNode6 : Integer.Sparse (Fin 2886) := keyPolynomialBlock9 ++ keyPolynomialBlock10

def keyPolynomialNode7 : Integer.Sparse (Fin 2886) := keyPolynomialBlock8 ++ keyPolynomialNode6

def keyPolynomialNode8 : Integer.Sparse (Fin 2886) := keyPolynomialNode5 ++ keyPolynomialNode7

def keyPolynomialNode10 : Integer.Sparse (Fin 2886) := keyPolynomialBlock11 ++ keyPolynomialBlock12

def keyPolynomialNode11 : Integer.Sparse (Fin 2886) := keyPolynomialBlock14 ++ keyPolynomialBlock15

def keyPolynomialNode12 : Integer.Sparse (Fin 2886) := keyPolynomialBlock13 ++ keyPolynomialNode11

def keyPolynomialNode13 : Integer.Sparse (Fin 2886) := keyPolynomialNode10 ++ keyPolynomialNode12

def keyPolynomialNode14 : Integer.Sparse (Fin 2886) := keyPolynomialBlock17 ++ keyPolynomialBlock18

def keyPolynomialNode15 : Integer.Sparse (Fin 2886) := keyPolynomialBlock16 ++ keyPolynomialNode14

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode16 : Integer.Sparse (Fin 2886) := keyPolynomialBlock20 ++ keyPolynomialBlock21

def keyPolynomialNode17 : Integer.Sparse (Fin 2886) := keyPolynomialBlock19 ++ keyPolynomialNode16

def keyPolynomialNode18 : Integer.Sparse (Fin 2886) := keyPolynomialNode15 ++ keyPolynomialNode17

def keyPolynomialNode19 : Integer.Sparse (Fin 2886) := keyPolynomialNode13 ++ keyPolynomialNode18

def keyPolynomialNode21 : Integer.Sparse (Fin 2886) := keyPolynomialBlock22 ++ keyPolynomialBlock23

def keyPolynomialNode22 : Integer.Sparse (Fin 2886) := keyPolynomialBlock25 ++ keyPolynomialBlock26

def keyPolynomialNode23 : Integer.Sparse (Fin 2886) := keyPolynomialBlock24 ++ keyPolynomialNode22

def keyPolynomialNode24 : Integer.Sparse (Fin 2886) := keyPolynomialNode21 ++ keyPolynomialNode23

def keyPolynomialNode25 : Integer.Sparse (Fin 2886) := keyPolynomialBlock28 ++ keyPolynomialBlock29

def keyPolynomialNode26 : Integer.Sparse (Fin 2886) := keyPolynomialBlock27 ++ keyPolynomialNode25

def keyPolynomialNode27 : Integer.Sparse (Fin 2886) := keyPolynomialBlock31 ++ keyPolynomialBlock32

def keyPolynomialNode28 : Integer.Sparse (Fin 2886) := keyPolynomialBlock30 ++ keyPolynomialNode27

def keyPolynomialNode29 : Integer.Sparse (Fin 2886) := keyPolynomialNode26 ++ keyPolynomialNode28

def keyPolynomialNode30 : Integer.Sparse (Fin 2886) := keyPolynomialNode24 ++ keyPolynomialNode29

def keyPolynomialNode31 : Integer.Sparse (Fin 2886) := keyPolynomialBlock34 ++ keyPolynomialBlock35

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode32 : Integer.Sparse (Fin 2886) := keyPolynomialBlock33 ++ keyPolynomialNode31

def keyPolynomialNode33 : Integer.Sparse (Fin 2886) := keyPolynomialBlock37 ++ keyPolynomialBlock38

def keyPolynomialNode34 : Integer.Sparse (Fin 2886) := keyPolynomialBlock36 ++ keyPolynomialNode33

def keyPolynomialNode35 : Integer.Sparse (Fin 2886) := keyPolynomialNode32 ++ keyPolynomialNode34

def keyPolynomialNode36 : Integer.Sparse (Fin 2886) := keyPolynomialBlock40 ++ keyPolynomialBlock41

def keyPolynomialNode37 : Integer.Sparse (Fin 2886) := keyPolynomialBlock39 ++ keyPolynomialNode36

def keyPolynomialNode38 : Integer.Sparse (Fin 2886) := keyPolynomialBlock43 ++ keyPolynomialBlock44

def keyPolynomialNode39 : Integer.Sparse (Fin 2886) := keyPolynomialBlock42 ++ keyPolynomialNode38

def keyPolynomialNode40 : Integer.Sparse (Fin 2886) := keyPolynomialNode37 ++ keyPolynomialNode39

def keyPolynomialNode41 : Integer.Sparse (Fin 2886) := keyPolynomialNode35 ++ keyPolynomialNode40

def keyPolynomialNode42 : Integer.Sparse (Fin 2886) := keyPolynomialNode30 ++ keyPolynomialNode41

def keyPolynomialNode44 : Integer.Sparse (Fin 2886) := keyPolynomialBlock45 ++ keyPolynomialBlock46

def keyPolynomialNode45 : Integer.Sparse (Fin 2886) := keyPolynomialBlock48 ++ keyPolynomialBlock49

def keyPolynomialNode46 : Integer.Sparse (Fin 2886) := keyPolynomialBlock47 ++ keyPolynomialNode45

def keyPolynomialNode47 : Integer.Sparse (Fin 2886) := keyPolynomialNode44 ++ keyPolynomialNode46

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode48 : Integer.Sparse (Fin 2886) := keyPolynomialBlock51 ++ keyPolynomialBlock52

def keyPolynomialNode49 : Integer.Sparse (Fin 2886) := keyPolynomialBlock50 ++ keyPolynomialNode48

def keyPolynomialNode50 : Integer.Sparse (Fin 2886) := keyPolynomialBlock54 ++ keyPolynomialBlock55

def keyPolynomialNode51 : Integer.Sparse (Fin 2886) := keyPolynomialBlock53 ++ keyPolynomialNode50

def keyPolynomialNode52 : Integer.Sparse (Fin 2886) := keyPolynomialNode49 ++ keyPolynomialNode51

def keyPolynomialNode53 : Integer.Sparse (Fin 2886) := keyPolynomialNode47 ++ keyPolynomialNode52

def keyPolynomialNode54 : Integer.Sparse (Fin 2886) := keyPolynomialBlock57 ++ keyPolynomialBlock58

def keyPolynomialNode55 : Integer.Sparse (Fin 2886) := keyPolynomialBlock56 ++ keyPolynomialNode54

def keyPolynomialNode56 : Integer.Sparse (Fin 2886) := keyPolynomialBlock60 ++ keyPolynomialBlock61

def keyPolynomialNode57 : Integer.Sparse (Fin 2886) := keyPolynomialBlock59 ++ keyPolynomialNode56

def keyPolynomialNode58 : Integer.Sparse (Fin 2886) := keyPolynomialNode55 ++ keyPolynomialNode57

def keyPolynomialNode59 : Integer.Sparse (Fin 2886) := keyPolynomialBlock63 ++ keyPolynomialBlock64

def keyPolynomialNode60 : Integer.Sparse (Fin 2886) := keyPolynomialBlock62 ++ keyPolynomialNode59

def keyPolynomialNode61 : Integer.Sparse (Fin 2886) := keyPolynomialBlock66 ++ keyPolynomialBlock67

def keyPolynomialNode62 : Integer.Sparse (Fin 2886) := keyPolynomialBlock65 ++ keyPolynomialNode61

def keyPolynomialNode63 : Integer.Sparse (Fin 2886) := keyPolynomialNode60 ++ keyPolynomialNode62

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode64 : Integer.Sparse (Fin 2886) := keyPolynomialNode58 ++ keyPolynomialNode63

def keyPolynomialNode65 : Integer.Sparse (Fin 2886) := keyPolynomialNode53 ++ keyPolynomialNode64

def keyPolynomialNode66 : Integer.Sparse (Fin 2886) := keyPolynomialBlock68 ++ keyPolynomialBlock69

def keyPolynomialNode67 : Integer.Sparse (Fin 2886) := keyPolynomialBlock71 ++ keyPolynomialBlock72

def keyPolynomialNode68 : Integer.Sparse (Fin 2886) := keyPolynomialBlock70 ++ keyPolynomialNode67

def keyPolynomialNode69 : Integer.Sparse (Fin 2886) := keyPolynomialNode66 ++ keyPolynomialNode68

def keyPolynomialNode70 : Integer.Sparse (Fin 2886) := keyPolynomialBlock74 ++ keyPolynomialBlock75

def keyPolynomialNode71 : Integer.Sparse (Fin 2886) := keyPolynomialBlock73 ++ keyPolynomialNode70

def keyPolynomialNode72 : Integer.Sparse (Fin 2886) := keyPolynomialBlock77 ++ keyPolynomialBlock78

def keyPolynomialNode73 : Integer.Sparse (Fin 2886) := keyPolynomialBlock76 ++ keyPolynomialNode72

def keyPolynomialNode74 : Integer.Sparse (Fin 2886) := keyPolynomialNode71 ++ keyPolynomialNode73

def keyPolynomialNode75 : Integer.Sparse (Fin 2886) := keyPolynomialNode69 ++ keyPolynomialNode74

def keyPolynomialNode76 : Integer.Sparse (Fin 2886) := keyPolynomialBlock80 ++ keyPolynomialBlock81

def keyPolynomialNode77 : Integer.Sparse (Fin 2886) := keyPolynomialBlock79 ++ keyPolynomialNode76

def keyPolynomialNode78 : Integer.Sparse (Fin 2886) := keyPolynomialBlock83 ++ keyPolynomialBlock84

def keyPolynomialNode79 : Integer.Sparse (Fin 2886) := keyPolynomialBlock82 ++ keyPolynomialNode78

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode80 : Integer.Sparse (Fin 2886) := keyPolynomialNode77 ++ keyPolynomialNode79

def keyPolynomialNode81 : Integer.Sparse (Fin 2886) := keyPolynomialBlock86 ++ keyPolynomialBlock87

def keyPolynomialNode82 : Integer.Sparse (Fin 2886) := keyPolynomialBlock85 ++ keyPolynomialNode81

def keyPolynomialNode83 : Integer.Sparse (Fin 2886) := keyPolynomialBlock89 ++ keyPolynomialBlock90

def keyPolynomialNode84 : Integer.Sparse (Fin 2886) := keyPolynomialBlock88 ++ keyPolynomialNode83

def keyPolynomialNode85 : Integer.Sparse (Fin 2886) := keyPolynomialNode82 ++ keyPolynomialNode84

def keyPolynomialNode86 : Integer.Sparse (Fin 2886) := keyPolynomialNode80 ++ keyPolynomialNode85

def keyPolynomialNode87 : Integer.Sparse (Fin 2886) := keyPolynomialNode75 ++ keyPolynomialNode86

def keyPolynomialNode88 : Integer.Sparse (Fin 2886) := keyPolynomialNode65 ++ keyPolynomialNode87

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge0 : Integer.Sparse Master := [(Sum.inl 0, 4526895990700081152000), (Sum.inl 1, -5071151322752901120000), (Sum.inl 2, -2721276660264099840000)]

def reducedMerge1 : Integer.Sparse Master := [(Sum.inl 0, 7090058769856634880000), (Sum.inl 1, -1575929351175782400000), (Sum.inl 2, -391128679212687360000)]

def reducedMerge10 : Integer.Sparse Master := [(Sum.inl 0, 74539561980764160000), (Sum.inl 1, 220021514702438400000), (Sum.inl 2, 192916489793126400000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 697067250492211200000), (Sum.inl 6, 46175033821593600000), (Sum.inl 7, -2313481462264627200000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 314971557743001600000), (Sum.inl 35, -1469293651987660800000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 54165832919654400000), (Sum.inl 69, -2532563430830899200000), (Sum.inl 70, -2220010509975552000000), (Sum.inl 71, -1469293651987660800000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -844187810276966400000), (Sum.inl 495, -312552920855347200000)]

def reducedMerge11 : Integer.Sparse Master := [(Sum.inl 0, 1812226203531878400000), (Sum.inl 1, 687401943666278400000), (Sum.inl 2, 215629048780185600000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 505272307934822400000), (Sum.inl 6, 96647387126169600000), (Sum.inl 7, -2071214166402662400000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 153460027168358400000), (Sum.inl 35, -1348160004056678400000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 61736685915340800000), (Sum.inl 69, -2128784604394291200000), (Sum.inl 70, -1856609566182604800000), (Sum.inl 71, -1146270590838374400000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -763432044989644800000), (Sum.inl 495, -312552920855347200000)]

def reducedMerge12 : Integer.Sparse Master := [(Sum.inl 0, 21520222987994357760000), (Sum.inl 1, 1427842769251368960000), (Sum.inl 2, 1803838724431994880000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 505272307934822400000), (Sum.inl 6, 96647387126169600000), (Sum.inl 7, -2071214166402662400000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 153460027168358400000), (Sum.inl 35, -1348160004056678400000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 61736685915340800000), (Sum.inl 69, -2128784604394291200000), (Sum.inl 70, -1856609566182604800000), (Sum.inl 71, -1146270590838374400000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -763432044989644800000), (Sum.inl 495, -312552920855347200000)]

def reducedMerge13 : Integer.Sparse Master := [(Sum.inl 0, -26025529345966080000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -184117085481369600000), (Sum.inl 5, 329165055855820800000), (Sum.inl 6, -94750365214310400000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, 502053651283968000000), (Sum.inl 58, -71062773910732800000), (Sum.inl 69, -625105841710694400000), (Sum.inl 70, -312552920855347200000), (Sum.inl 71, -937658762566041600000), (Sum.inl 256, 937658762566041600000), (Sum.inl 495, -379001460857241600000)]

def reducedMerge14 : Integer.Sparse Master := [(Sum.inl 0, -78138230213836800000), (Sum.inl 1, -70447468312166400000), (Sum.inl 2, -172273289829580800000), (Sum.inl 5, 423915421070131200000), (Sum.inl 6, -165813139125043200000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, 691554381712588800000), (Sum.inl 35, -379001460857241600000), (Sum.inl 58, -94750365214310400000), (Sum.inl 69, -814606572139315200000), (Sum.inl 70, -502053651283968000000), (Sum.inl 71, -937658762566041600000), (Sum.inl 256, 937658762566041600000), (Sum.inl 257, -379001460857241600000), (Sum.inl 495, -758002921714483200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge100 : Integer.Sparse Master := [(Sum.inl 0, 79107855734476800000), (Sum.inl 1, -941751999149875200000), (Sum.inl 2, -773884849257676800000), (Sum.inl 3, 292079170407628800000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 2413119435090739200000), (Sum.inl 6, 136981552948531200000), (Sum.inl 7, -885563875123200000000), (Sum.inl 8, -944130279717273600000), (Sum.inl 9, 94366339006464000000), (Sum.inl 26, 980452619196825600000), (Sum.inl 35, 1190799237287116800000), (Sum.inl 52, -838720913109811200000), (Sum.inl 67, 1839637567556812800000), (Sum.inl 69, 269070204882124800000), (Sum.inl 71, 207147341669990400000), (Sum.inl 81, -4874829493395456000000), (Sum.inl 257, -98752190526259200000)]

def reducedMerge101 : Integer.Sparse Master := [(Sum.inl 0, 171055250282004480000), (Sum.inl 1, -354269147207270400000), (Sum.inl 2, 37032071447347200000), (Sum.inl 5, -74064142894694400000), (Sum.inl 6, 48912652331827200000), (Sum.inl 8, -782602437309235200000), (Sum.inl 67, -296256571578777600000)]

def reducedMerge102 : Integer.Sparse Master := [(Sum.inl 0, 163547035437219840000), (Sum.inl 1, -340064416419840000000), (Sum.inl 2, 37032071447347200000), (Sum.inl 5, -74064142894694400000), (Sum.inl 6, 51956523214848000000), (Sum.inl 7, -16233978042777600000), (Sum.inl 8, -815070393394790400000), (Sum.inl 67, -296256571578777600000)]

def reducedMerge103 : Integer.Sparse Master := [(Sum.inl 0, -229065794665021440000), (Sum.inl 1, -321554933438054400000), (Sum.inl 5, -864028542866227200000), (Sum.inl 7, -1205710727793868800000), (Sum.inl 8, -2250403443671040000000)]

def reducedMerge104 : Integer.Sparse Master := [(Sum.inl 0, 93221495780474880000), (Sum.inl 1, 866600898508800000000), (Sum.inl 3, -121133647930982400000), (Sum.inl 5, 1743296267678515200000), (Sum.inl 6, 410587890267340800000), (Sum.inl 7, -161511530574643200000), (Sum.inl 9, 10094470660915200000), (Sum.inl 13, -40377882643660800000), (Sum.inl 26, -161511530574643200000), (Sum.inl 34, -40377882643660800000), (Sum.inl 35, -323023061149286400000), (Sum.inl 67, -80755765287321600000), (Sum.inl 68, -30283411982745600000), (Sum.inl 69, -40377882643660800000), (Sum.inl 70, -121133647930982400000), (Sum.inl 124, 121133647930982400000), (Sum.inl 196, 121133647930982400000), (Sum.inl 197, 242267295861964800000), (Sum.inl 257, -40377882643660800000), (Sum.inl 266, 121133647930982400000)]

def reducedMerge105 : Integer.Sparse Master := [(Sum.inl 0, -135844298884546560000), (Sum.inl 1, 545045965070745600000), (Sum.inl 3, -121133647930982400000), (Sum.inl 5, 879267724812288000000), (Sum.inl 6, 410587890267340800000), (Sum.inl 7, -1367222258368512000000), (Sum.inl 8, -2250403443671040000000), (Sum.inl 9, 10094470660915200000), (Sum.inl 13, -40377882643660800000), (Sum.inl 26, -161511530574643200000), (Sum.inl 34, -40377882643660800000), (Sum.inl 35, -323023061149286400000), (Sum.inl 67, -80755765287321600000), (Sum.inl 68, -30283411982745600000), (Sum.inl 69, -40377882643660800000), (Sum.inl 70, -121133647930982400000), (Sum.inl 124, 121133647930982400000), (Sum.inl 196, 121133647930982400000), (Sum.inl 197, 242267295861964800000), (Sum.inl 257, -40377882643660800000), (Sum.inl 266, 121133647930982400000)]

def reducedMerge106 : Integer.Sparse Master := [(Sum.inl 0, 27702736552673280000), (Sum.inl 1, 204981548650905600000), (Sum.inl 2, 37032071447347200000), (Sum.inl 3, -121133647930982400000), (Sum.inl 5, 805203581917593600000), (Sum.inl 6, 462544413482188800000), (Sum.inl 7, -1383456236411289600000), (Sum.inl 8, -3065473837065830400000), (Sum.inl 9, 10094470660915200000), (Sum.inl 13, -40377882643660800000), (Sum.inl 26, -161511530574643200000), (Sum.inl 34, -40377882643660800000), (Sum.inl 35, -323023061149286400000), (Sum.inl 67, -377012336866099200000), (Sum.inl 68, -30283411982745600000), (Sum.inl 69, -40377882643660800000), (Sum.inl 70, -121133647930982400000), (Sum.inl 124, 121133647930982400000), (Sum.inl 196, 121133647930982400000), (Sum.inl 197, 242267295861964800000), (Sum.inl 257, -40377882643660800000), (Sum.inl 266, 121133647930982400000)]

def reducedMerge107 : Integer.Sparse Master := [(Sum.inl 0, 110263890710937600000), (Sum.inl 1, -36543092679475200000), (Sum.inl 2, 21015991406592000000), (Sum.inl 3, -2012524139682201600000), (Sum.inl 5, 408715668445593600000), (Sum.inl 6, -74693300174438400000), (Sum.inl 7, -1614159872085196800000), (Sum.inl 9, 99591066899251200000), (Sum.inl 13, -1215795604488192000000), (Sum.inl 23, 124216810183065600000), (Sum.inl 26, -796728535194009600000), (Sum.inl 27, -15527101272883200000), (Sum.inl 34, -398364267597004800000), (Sum.inl 35, -2410888407279206400000), (Sum.inl 52, -796728535194009600000), (Sum.inl 54, 124216810183065600000), (Sum.inl 55, 62108405091532800000), (Sum.inl 60, -398364267597004800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, -398364267597004800000), (Sum.inl 68, -329827403243520000000), (Sum.inl 69, -398364267597004800000), (Sum.inl 70, -796728535194009600000), (Sum.inl 124, 62108405091532800000), (Sum.inl 125, 2576510820856627200000), (Sum.inl 126, 1195092802791014400000), (Sum.inl 196, 124216810183065600000), (Sum.inl 197, 1257201207882547200000), (Sum.inl 257, -398364267597004800000), (Sum.inl 260, 1195092802791014400000), (Sum.inl 264, 124216810183065600000), (Sum.inl 266, 62108405091532800000), (Sum.inl 268, 1195092802791014400000)]

def reducedMerge108 : Integer.Sparse Master := [(Sum.inl 0, -189469462876323840000), (Sum.inl 1, 103099025536819200000), (Sum.inl 2, 97735816365465600000), (Sum.inl 3, 1214138068048281600000), (Sum.inl 5, -628521870709555200000), (Sum.inl 6, 75883629253017600000), (Sum.inl 7, 1214138068048281600000), (Sum.inl 9, -151767258506035200000), (Sum.inl 13, 2428276136096563200000), (Sum.inl 23, -257434040224972800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 27, 128717020112486400000), (Sum.inl 32, 607069034024140800000), (Sum.inl 35, 2428276136096563200000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, 1214138068048281600000), (Sum.inl 54, -3899848244369817600000), (Sum.inl 55, -257434040224972800000), (Sum.inl 56, -257434040224972800000), (Sum.inl 60, 1214138068048281600000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 68, 584018795630592000000), (Sum.inl 69, 607069034024140800000), (Sum.inl 70, 607069034024140800000), (Sum.inl 124, -257434040224972800000), (Sum.inl 125, -3899848244369817600000), (Sum.inl 126, -257434040224972800000), (Sum.inl 196, -257434040224972800000), (Sum.inl 197, -514868080449945600000), (Sum.inl 257, 607069034024140800000), (Sum.inl 260, -3642414204144844800000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5463621306217267200000), (Sum.inl 266, -257434040224972800000), (Sum.inl 268, -257434040224972800000)]

def reducedMerge109 : Integer.Sparse Master := [(Sum.inl 0, -79205572165386240000), (Sum.inl 1, 66555932857344000000), (Sum.inl 2, 118751807772057600000), (Sum.inl 3, -798386071633920000000), (Sum.inl 5, -219806202263961600000), (Sum.inl 6, 1190329078579200000), (Sum.inl 7, -400021804036915200000), (Sum.inl 9, -52176191606784000000), (Sum.inl 13, 1212480531608371200000), (Sum.inl 23, -133217230041907200000), (Sum.inl 24, -257434040224972800000), (Sum.inl 26, -796728535194009600000), (Sum.inl 27, 113189918839603200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 34, -398364267597004800000), (Sum.inl 35, 17387728817356800000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, 417409532854272000000), (Sum.inl 54, -3775631434186752000000), (Sum.inl 55, -195325635133440000000), (Sum.inl 56, -257434040224972800000), (Sum.inl 60, 815773800451276800000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, -398364267597004800000), (Sum.inl 68, 254191392387072000000), (Sum.inl 69, 208704766427136000000), (Sum.inl 70, -189659501169868800000), (Sum.inl 124, -195325635133440000000), (Sum.inl 125, -1323337423513190400000), (Sum.inl 126, 937658762566041600000), (Sum.inl 196, -133217230041907200000), (Sum.inl 197, 742333127432601600000), (Sum.inl 257, 208704766427136000000), (Sum.inl 260, -2447321401353830400000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5339404496034201600000), (Sum.inl 266, -195325635133440000000), (Sum.inl 268, 937658762566041600000)]

def reducedMerge110 : Integer.Sparse Master := [(Sum.inl 0, -61969221091491840000), (Sum.inl 1, -184144864090521600000), (Sum.inl 2, -226027494553190400000), (Sum.inl 68, -401945212492185600000), (Sum.inl 124, -602597718864691200000), (Sum.inl 125, 1406488143849062400000), (Sum.inl 126, 1406488143849062400000), (Sum.inl 196, -602597718864691200000), (Sum.inl 197, 803890424984371200000), (Sum.inl 266, -602597718864691200000), (Sum.inl 268, 1406488143849062400000)]

def reducedMerge111 : Integer.Sparse Master := [(Sum.inl 0, 163464586476871680000), (Sum.inl 1, -165983003543347200000), (Sum.inl 2, 89468009771212800000), (Sum.inl 3, -1226164863909888000000), (Sum.inl 5, -408721621303296000000), (Sum.inl 6, 25545101331456000000), (Sum.inl 7, -408721621303296000000), (Sum.inl 9, -102180405325824000000), (Sum.inl 12, -408721621303296000000), (Sum.inl 13, -408721621303296000000), (Sum.inl 23, 1226164863909888000000), (Sum.inl 26, -817443242606592000000), (Sum.inl 27, 919623647932416000000), (Sum.inl 35, -1226164863909888000000), (Sum.inl 54, 1226164863909888000000), (Sum.inl 55, 2452329727819776000000), (Sum.inl 68, 1609221073659494400000), (Sum.inl 70, -408721621303296000000), (Sum.inl 125, 2146269752731238400000), (Sum.inl 196, 1226164863909888000000), (Sum.inl 197, 2452329727819776000000), (Sum.inl 264, -306059975088537600000)]

def reducedMerge112 : Integer.Sparse Master := [(Sum.inl 0, 101495365385379840000), (Sum.inl 1, -350127867633868800000), (Sum.inl 2, -136559484781977600000), (Sum.inl 3, -1226164863909888000000), (Sum.inl 5, -408721621303296000000), (Sum.inl 6, 25545101331456000000), (Sum.inl 7, -408721621303296000000), (Sum.inl 9, -102180405325824000000), (Sum.inl 12, -408721621303296000000), (Sum.inl 13, -408721621303296000000), (Sum.inl 23, 1226164863909888000000), (Sum.inl 26, -817443242606592000000), (Sum.inl 27, 919623647932416000000), (Sum.inl 35, -1226164863909888000000), (Sum.inl 54, 1226164863909888000000), (Sum.inl 55, 2452329727819776000000), (Sum.inl 68, 1207275861167308800000), (Sum.inl 70, -408721621303296000000), (Sum.inl 124, -602597718864691200000), (Sum.inl 125, 3552757896580300800000), (Sum.inl 126, 1406488143849062400000), (Sum.inl 196, 623567145045196800000), (Sum.inl 197, 3256220152804147200000), (Sum.inl 264, -306059975088537600000), (Sum.inl 266, -602597718864691200000), (Sum.inl 268, 1406488143849062400000)]

def reducedMerge113 : Integer.Sparse Master := [(Sum.inl 0, 22289793219993600000), (Sum.inl 1, -283571934776524800000), (Sum.inl 2, -17807677009920000000), (Sum.inl 3, -2024550935543808000000), (Sum.inl 5, -628527823567257600000), (Sum.inl 6, 26735430410035200000), (Sum.inl 7, -808743425340211200000), (Sum.inl 9, -154356596932608000000), (Sum.inl 12, -408721621303296000000), (Sum.inl 13, 803758910305075200000), (Sum.inl 23, 1092947633867980800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 26, -1614171777800601600000), (Sum.inl 27, 1032813566772019200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 34, -398364267597004800000), (Sum.inl 35, -1208777135092531200000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, 417409532854272000000), (Sum.inl 54, -2549466570276864000000), (Sum.inl 55, 2257004092686336000000), (Sum.inl 56, -257434040224972800000), (Sum.inl 60, 815773800451276800000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, -398364267597004800000), (Sum.inl 68, 1461467253554380800000), (Sum.inl 69, 208704766427136000000), (Sum.inl 70, -598381122473164800000), (Sum.inl 124, -797923353998131200000), (Sum.inl 125, 2229420473067110400000), (Sum.inl 126, 2344146906415104000000), (Sum.inl 196, 490349915003289600000), (Sum.inl 197, 3998553280236748800000), (Sum.inl 257, 208704766427136000000), (Sum.inl 260, -2447321401353830400000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5645464471122739200000), (Sum.inl 266, -797923353998131200000), (Sum.inl 268, 2344146906415104000000)]

def reducedMerge114 : Integer.Sparse Master := [(Sum.inl 0, 49992529772666880000), (Sum.inl 1, -78590386125619200000), (Sum.inl 2, 19224394437427200000), (Sum.inl 3, -2145684583474790400000), (Sum.inl 5, 176675758350336000000), (Sum.inl 6, 489279843892224000000), (Sum.inl 7, -2192199661751500800000), (Sum.inl 8, -3065473837065830400000), (Sum.inl 9, -144262126271692800000), (Sum.inl 12, -408721621303296000000), (Sum.inl 13, 763381027661414400000), (Sum.inl 23, 1092947633867980800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 26, -1775683308375244800000), (Sum.inl 27, 1032813566772019200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 34, -438742150240665600000), (Sum.inl 35, -1531800196241817600000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, 417409532854272000000), (Sum.inl 54, -2549466570276864000000), (Sum.inl 55, 2257004092686336000000), (Sum.inl 56, -257434040224972800000), (Sum.inl 60, 815773800451276800000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, -775376604463104000000), (Sum.inl 68, 1431183841571635200000), (Sum.inl 69, 168326883783475200000), (Sum.inl 70, -719514770404147200000), (Sum.inl 124, -676789706067148800000), (Sum.inl 125, 2229420473067110400000), (Sum.inl 126, 2344146906415104000000), (Sum.inl 196, 611483562934272000000), (Sum.inl 197, 4240820576098713600000), (Sum.inl 257, 168326883783475200000), (Sum.inl 260, -2447321401353830400000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5645464471122739200000), (Sum.inl 266, -676789706067148800000), (Sum.inl 268, 2344146906415104000000)]

def reducedMerge115 : Integer.Sparse Master := [(Sum.inl 0, 129100385507143680000), (Sum.inl 1, -1020342385275494400000), (Sum.inl 2, -754660454820249600000), (Sum.inl 3, -1853605413067161600000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 2589795193441075200000), (Sum.inl 6, 626261396840755200000), (Sum.inl 7, -3077763536874700800000), (Sum.inl 8, -4009604116783104000000), (Sum.inl 9, -49895787265228800000), (Sum.inl 12, -408721621303296000000), (Sum.inl 13, 763381027661414400000), (Sum.inl 23, 1092947633867980800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 26, -795230689178419200000), (Sum.inl 27, 1032813566772019200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 34, -438742150240665600000), (Sum.inl 35, -341000958954700800000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, -421311380255539200000), (Sum.inl 54, -2549466570276864000000), (Sum.inl 55, 2257004092686336000000), (Sum.inl 56, -257434040224972800000), (Sum.inl 60, 815773800451276800000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, 1064260963093708800000), (Sum.inl 68, 1431183841571635200000), (Sum.inl 69, 437397088665600000000), (Sum.inl 70, -719514770404147200000), (Sum.inl 71, 207147341669990400000), (Sum.inl 81, -4874829493395456000000), (Sum.inl 124, -676789706067148800000), (Sum.inl 125, 2229420473067110400000), (Sum.inl 126, 2344146906415104000000), (Sum.inl 196, 611483562934272000000), (Sum.inl 197, 4240820576098713600000), (Sum.inl 257, 69574693257216000000), (Sum.inl 260, -2447321401353830400000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5645464471122739200000), (Sum.inl 266, -676789706067148800000), (Sum.inl 268, 2344146906415104000000)]

def reducedMerge116 : Integer.Sparse Master := [(Sum.inl 0, 59872085026467840000), (Sum.inl 1, -2495445254578483200000), (Sum.inl 2, -1363385440398643200000), (Sum.inl 3, -203613601598668800000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 3755587804880486400000), (Sum.inl 6, 684424480694169600000), (Sum.inl 7, 1552674610800230400000), (Sum.inl 8, -3166314502437273600000), (Sum.inl 9, -300767084048793600000), (Sum.inl 12, -498088061485056000000), (Sum.inl 13, 817700385993523200000), (Sum.inl 23, 1092947633867980800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 26, -277086262866739200000), (Sum.inl 27, 1032813566772019200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 34, -438742150240665600000), (Sum.inl 35, 3364178571539251200000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, -2082762802313625600000), (Sum.inl 54, -2549466570276864000000), (Sum.inl 55, 2257004092686336000000), (Sum.inl 56, -257434040224972800000), (Sum.inl 58, -31814174291558400000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 1131543237604147200000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, 2277103264579584000000), (Sum.inl 68, 1431183841571635200000), (Sum.inl 69, 2769187459394764800000), (Sum.inl 70, 1879492275943833600000), (Sum.inl 71, 1269163316581171200000), (Sum.inl 81, -6499772657860608000000), (Sum.inl 124, -676789706067148800000), (Sum.inl 125, 2229420473067110400000), (Sum.inl 126, 2344146906415104000000), (Sum.inl 128, 716680257011712000000), (Sum.inl 196, 611483562934272000000), (Sum.inl 197, 4240820576098713600000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, 764272568431411200000), (Sum.inl 260, -2447321401353830400000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5645464471122739200000), (Sum.inl 266, -676789706067148800000), (Sum.inl 268, 2344146906415104000000), (Sum.inl 495, -541647721488384000000)]

def reducedMerge117 : Integer.Sparse Master := [(Sum.inl 0, 21483538927652229120000), (Sum.inl 1, -247749570652631040000), (Sum.inl 2, -50146919582699520000), (Sum.inl 3, 2353870197168537600000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 4034757944177049600000), (Sum.inl 6, 634035773610086400000), (Sum.inl 7, 2428745876766720000000), (Sum.inl 8, -4709307760032153600000), (Sum.inl 9, 623655511957094400000), (Sum.inl 12, -498088061485056000000), (Sum.inl 13, 5398095709981900800000), (Sum.inl 23, 1092947633867980800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 26, -277086262866739200000), (Sum.inl 27, 1032813566772019200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 34, -438742150240665600000), (Sum.inl 35, 13100944972824576000000), (Sum.inl 51, -257434040224972800000), (Sum.inl 52, 7656533580216729600000), (Sum.inl 54, -2630008233345024000000), (Sum.inl 55, 2257004092686336000000), (Sum.inl 56, -257434040224972800000), (Sum.inl 58, -151417574100172800000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 7687417449096806400000), (Sum.inl 61, -257434040224972800000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 65, 62108405091532800000), (Sum.inl 67, 2277103264579584000000), (Sum.inl 68, 1431183841571635200000), (Sum.inl 69, 5357675998479974400000), (Sum.inl 70, 3727340071664025600000), (Sum.inl 71, 1132407313293312000000), (Sum.inl 81, -6499772657860608000000), (Sum.inl 124, -676789706067148800000), (Sum.inl 125, 2229420473067110400000), (Sum.inl 126, 2344146906415104000000), (Sum.inl 128, 4213980361388851200000), (Sum.inl 196, 611483562934272000000), (Sum.inl 197, 4240820576098713600000), (Sum.inl 256, -413201857388544000000), (Sum.inl 257, 2885252692112179200000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -6575848624196812800000), (Sum.inl 263, 514868080449945600000), (Sum.inl 264, -5645464471122739200000), (Sum.inl 266, -676789706067148800000), (Sum.inl 268, 2344146906415104000000), (Sum.inl 495, 2533028548003430400000)]

def reducedMerge118 : Integer.Sparse Master := [(Sum.inl 0, -25950200822784000000), (Sum.inl 1, 350783845171200000), (Sum.inl 2, -108257264523878400000), (Sum.inl 3, 104844789891072000000), (Sum.inl 4, 41937915956428800000), (Sum.inl 5, 347995533312000000), (Sum.inl 6, -2621119747276800000), (Sum.inl 7, 41937915956428800000), (Sum.inl 9, -7689361475174400000), (Sum.inl 13, -30757445900697600000), (Sum.inl 24, -125813747869286400000), (Sum.inl 26, 41937915956428800000), (Sum.inl 27, -47180155450982400000), (Sum.inl 35, -40545933823180800000), (Sum.inl 55, -62906873934643200000), (Sum.inl 56, -125813747869286400000), (Sum.inl 68, -39838789509120000000), (Sum.inl 70, -30757445900697600000), (Sum.inl 125, -62906873934643200000), (Sum.inl 196, 155179211636736000000), (Sum.inl 197, -251627495738572800000)]

def reducedMerge119 : Integer.Sparse Master := [(Sum.inl 0, 6471264238387200000), (Sum.inl 1, -10456371175219200000), (Sum.inl 2, -140678729585049600000), (Sum.inl 3, -240984170761420800000), (Sum.inl 4, 41937915956428800000), (Sum.inl 5, -172566484792934400000), (Sum.inl 6, 29800345313894400000), (Sum.inl 7, 41937915956428800000), (Sum.inl 9, -50917981556736000000), (Sum.inl 13, -376586406553190400000), (Sum.inl 24, -125813747869286400000), (Sum.inl 26, 41937915956428800000), (Sum.inl 27, 341877425283072000000), (Sum.inl 33, 518743440978739200000), (Sum.inl 35, -40545933823180800000), (Sum.inl 52, -345828960652492800000), (Sum.inl 55, 974580008022835200000), (Sum.inl 56, -125813747869286400000), (Sum.inl 64, 1037486881957478400000), (Sum.inl 68, 608590511714304000000), (Sum.inl 70, -30757445900697600000), (Sum.inl 125, 974580008022835200000), (Sum.inl 196, 155179211636736000000), (Sum.inl 197, 267115945240166400000), (Sum.inl 260, 518743440978739200000), (Sum.inl 263, -1037486881957478400000)]

def reducedMerge120 : Integer.Sparse Master := [(Sum.inl 0, 29159605252915200000), (Sum.inl 1, -74981066917478400000), (Sum.inl 2, -28115125368422400000), (Sum.inl 3, 16656430281523200000), (Sum.inl 5, 49989022226841600000), (Sum.inl 6, -11456228664115200000), (Sum.inl 7, 16656430281523200000), (Sum.inl 9, 24994511113420800000), (Sum.inl 13, 83321614172160000000), (Sum.inl 26, 16656430281523200000), (Sum.inl 35, 33312860563046400000), (Sum.inl 52, 83321614172160000000), (Sum.inl 64, -249964842516480000000), (Sum.inl 68, -74983533340262400000), (Sum.inl 70, 16656430281523200000), (Sum.inl 125, -249964842516480000000), (Sum.inl 197, -49969290844569600000), (Sum.inl 260, -249964842516480000000)]

def reducedMerge121 : Integer.Sparse Master := [(Sum.inl 0, -134520836902502400000), (Sum.inl 1, 358777087699968000000), (Sum.inl 2, 305166234394828800000), (Sum.inl 5, 14983330295808000000), (Sum.inl 13, 59933321183232000000), (Sum.inl 27, 257055009568358400000), (Sum.inl 35, 59933321183232000000), (Sum.inl 55, 1208020001823129600000), (Sum.inl 63, -179799963549696000000), (Sum.inl 68, 514110019136716800000), (Sum.inl 125, 1208020001823129600000), (Sum.inl 196, -179799963549696000000), (Sum.inl 197, 1208020001823129600000), (Sum.inl 264, -179799963549696000000)]

def reducedMerge122 : Integer.Sparse Master := [(Sum.inl 0, -105361231649587200000), (Sum.inl 1, 283796020782489600000), (Sum.inl 2, 277051109026406400000), (Sum.inl 3, 16656430281523200000), (Sum.inl 5, 64972352522649600000), (Sum.inl 6, -11456228664115200000), (Sum.inl 7, 16656430281523200000), (Sum.inl 9, 24994511113420800000), (Sum.inl 13, 143254935355392000000), (Sum.inl 26, 16656430281523200000), (Sum.inl 27, 257055009568358400000), (Sum.inl 35, 93246181746278400000), (Sum.inl 52, 83321614172160000000), (Sum.inl 55, 1208020001823129600000), (Sum.inl 63, -179799963549696000000), (Sum.inl 64, -249964842516480000000), (Sum.inl 68, 439126485796454400000), (Sum.inl 70, 16656430281523200000), (Sum.inl 125, 958055159306649600000), (Sum.inl 196, -179799963549696000000), (Sum.inl 197, 1158050710978560000000), (Sum.inl 260, -249964842516480000000), (Sum.inl 264, -179799963549696000000)]

def reducedMerge123 : Integer.Sparse Master := [(Sum.inl 0, -98889967411200000000), (Sum.inl 1, 273339649607270400000), (Sum.inl 2, 136372379441356800000), (Sum.inl 3, -224327740479897600000), (Sum.inl 4, 41937915956428800000), (Sum.inl 5, -107594132270284800000), (Sum.inl 6, 18344116649779200000), (Sum.inl 7, 58594346237952000000), (Sum.inl 9, -25923470443315200000), (Sum.inl 13, -233331471197798400000), (Sum.inl 24, -125813747869286400000), (Sum.inl 26, 58594346237952000000), (Sum.inl 27, 598932434851430400000), (Sum.inl 33, 518743440978739200000), (Sum.inl 35, 52700247923097600000), (Sum.inl 52, -262507346480332800000), (Sum.inl 55, 2182600009845964800000), (Sum.inl 56, -125813747869286400000), (Sum.inl 63, -179799963549696000000), (Sum.inl 64, 787522039440998400000), (Sum.inl 68, 1047716997510758400000), (Sum.inl 70, -14101015619174400000), (Sum.inl 125, 1932635167329484800000), (Sum.inl 196, -24620751912960000000), (Sum.inl 197, 1425166656218726400000), (Sum.inl 260, 268778598462259200000), (Sum.inl 263, -1037486881957478400000), (Sum.inl 264, -179799963549696000000)]

def reducedMerge124 : Integer.Sparse Master := [(Sum.inl 0, -54375962735001600000), (Sum.inl 1, -389762768631398400000), (Sum.inl 2, -83311460034969600000), (Sum.inl 3, 688658985300787200000), (Sum.inl 5, 172164746325196800000), (Sum.inl 6, -17632111601664000000), (Sum.inl 7, 282113785626624000000), (Sum.inl 9, 18324839883571200000), (Sum.inl 12, 406545199674163200000), (Sum.inl 13, 479844559208448000000), (Sum.inl 23, -1219635599022489600000), (Sum.inl 27, -304908899755622400000), (Sum.inl 35, 282113785626624000000), (Sum.inl 54, -1219635599022489600000), (Sum.inl 68, -461519719324876800000), (Sum.inl 70, 73299359534284800000), (Sum.inl 125, -1032988477951180800000), (Sum.inl 196, -813090399348326400000)]

def reducedMerge125 : Integer.Sparse Master := [(Sum.inl 0, 363948951164682240000), (Sum.inl 1, 485434079391744000000), (Sum.inl 2, -723957245138534400000), (Sum.inl 5, 397191320528486400000), (Sum.inl 6, -46950263945625600000), (Sum.inl 9, 93900527891251200000), (Sum.inl 23, -2512683176951808000000), (Sum.inl 27, -628170794237952000000), (Sum.inl 54, -3639489511646822400000), (Sum.inl 62, -1126806334695014400000), (Sum.inl 68, -1538043172149657600000), (Sum.inl 125, -2512683176951808000000), (Sum.inl 196, -2512683176951808000000), (Sum.inl 260, -1126806334695014400000), (Sum.inl 264, -1126806334695014400000)]

def reducedMerge126 : Integer.Sparse Master := [(Sum.inl 0, 309572988429680640000), (Sum.inl 1, 95671310760345600000), (Sum.inl 2, -807268705173504000000), (Sum.inl 3, 688658985300787200000), (Sum.inl 5, 569356066853683200000), (Sum.inl 6, -64582375547289600000), (Sum.inl 7, 282113785626624000000), (Sum.inl 9, 112225367774822400000), (Sum.inl 12, 406545199674163200000), (Sum.inl 13, 479844559208448000000), (Sum.inl 23, -3732318775974297600000), (Sum.inl 27, -933079693993574400000), (Sum.inl 35, 282113785626624000000), (Sum.inl 54, -4859125110669312000000), (Sum.inl 62, -1126806334695014400000), (Sum.inl 68, -1999562891474534400000), (Sum.inl 70, 73299359534284800000), (Sum.inl 125, -3545671654902988800000), (Sum.inl 196, -3325773576300134400000), (Sum.inl 260, -1126806334695014400000), (Sum.inl 264, -1126806334695014400000)]

def reducedMerge127 : Integer.Sparse Master := [(Sum.inl 0, -23508031544524800000), (Sum.inl 1, 97012026832896000000), (Sum.inl 2, 55942137022464000000), (Sum.inl 5, -24074982715392000000), (Sum.inl 24, -118977977696256000000), (Sum.inl 27, 72224948146176000000), (Sum.inl 56, -118977977696256000000), (Sum.inl 68, 144449896292352000000), (Sum.inl 197, -237955955392512000000), (Sum.inl 263, -815755540561920000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge128 : Integer.Sparse Master := [(Sum.inl 0, -114282888596029440000), (Sum.inl 1, -120252608269516800000), (Sum.inl 2, -184704298942464000000), (Sum.inl 68, -506962752307200000000), (Sum.inl 196, -996623958461644800000), (Sum.inl 197, -1031227050767155200000)]

def reducedMerge129 : Integer.Sparse Master := [(Sum.inl 0, -137790920140554240000), (Sum.inl 1, -23240581436620800000), (Sum.inl 2, -128762161920000000000), (Sum.inl 5, -24074982715392000000), (Sum.inl 24, -118977977696256000000), (Sum.inl 27, 72224948146176000000), (Sum.inl 56, -118977977696256000000), (Sum.inl 68, -362512856014848000000), (Sum.inl 196, -996623958461644800000), (Sum.inl 197, -1269183006159667200000), (Sum.inl 263, -815755540561920000000)]

def reducedMerge130 : Integer.Sparse Master := [(Sum.inl 0, 171782068289126400000), (Sum.inl 1, 72430729323724800000), (Sum.inl 2, -936030867093504000000), (Sum.inl 3, 688658985300787200000), (Sum.inl 5, 545281084138291200000), (Sum.inl 6, -64582375547289600000), (Sum.inl 7, 282113785626624000000), (Sum.inl 9, 112225367774822400000), (Sum.inl 12, 406545199674163200000), (Sum.inl 13, 479844559208448000000), (Sum.inl 23, -3732318775974297600000), (Sum.inl 24, -118977977696256000000), (Sum.inl 27, -860854745847398400000), (Sum.inl 35, 282113785626624000000), (Sum.inl 54, -4859125110669312000000), (Sum.inl 56, -118977977696256000000), (Sum.inl 62, -1126806334695014400000), (Sum.inl 68, -2362075747489382400000), (Sum.inl 70, 73299359534284800000), (Sum.inl 125, -3545671654902988800000), (Sum.inl 196, -4322397534761779200000), (Sum.inl 197, -1269183006159667200000), (Sum.inl 260, -1126806334695014400000), (Sum.inl 263, -815755540561920000000), (Sum.inl 264, -1126806334695014400000)]

def reducedMerge131 : Integer.Sparse Master := [(Sum.inl 0, 72892100877926400000), (Sum.inl 1, 345770378930995200000), (Sum.inl 2, -799658487652147200000), (Sum.inl 3, 464331244820889600000), (Sum.inl 4, 41937915956428800000), (Sum.inl 5, 437686951868006400000), (Sum.inl 6, -46238258897510400000), (Sum.inl 7, 340708131864576000000), (Sum.inl 9, 86301897331507200000), (Sum.inl 12, 406545199674163200000), (Sum.inl 13, 246513088010649600000), (Sum.inl 23, -3732318775974297600000), (Sum.inl 24, -244791725565542400000), (Sum.inl 26, 58594346237952000000), (Sum.inl 27, -261922310995968000000), (Sum.inl 33, 518743440978739200000), (Sum.inl 35, 334814033549721600000), (Sum.inl 52, -262507346480332800000), (Sum.inl 54, -4859125110669312000000), (Sum.inl 55, 2182600009845964800000), (Sum.inl 56, -244791725565542400000), (Sum.inl 62, -1126806334695014400000), (Sum.inl 63, -179799963549696000000), (Sum.inl 64, 787522039440998400000), (Sum.inl 68, -1314358749978624000000), (Sum.inl 70, 59198343915110400000), (Sum.inl 125, -1613036487573504000000), (Sum.inl 196, -4347018286674739200000), (Sum.inl 197, 155983650059059200000), (Sum.inl 260, -858027736232755200000), (Sum.inl 263, -1853242422519398400000), (Sum.inl 264, -1306606298244710400000)]

def reducedMerge132 : Integer.Sparse Master := [(Sum.inl 0, -25929898191912960000), (Sum.inl 1, -178573189939200000), (Sum.inl 2, -98614200442060800000), (Sum.inl 3, 88133262232780800000), (Sum.inl 5, 44066631116390400000), (Sum.inl 6, -5508328889548800000), (Sum.inl 9, 7344438519398400000), (Sum.inl 13, 29377754077593600000), (Sum.inl 26, 176266524465561600000), (Sum.inl 27, -66099946674585600000), (Sum.inl 34, 88133262232780800000), (Sum.inl 35, 88133262232780800000), (Sum.inl 54, -264399786698342400000), (Sum.inl 65, -264399786698342400000), (Sum.inl 67, 88133262232780800000), (Sum.inl 68, -204929985783398400000), (Sum.inl 257, 29377754077593600000), (Sum.inl 264, -555320156435251200000), (Sum.inl 266, -264399786698342400000)]

def reducedMerge133 : Integer.Sparse Master := [(Sum.inl 0, -184125046592471040000), (Sum.inl 1, -593410379692032000000), (Sum.inl 2, 99129735058636800000), (Sum.inl 3, 88133262232780800000), (Sum.inl 5, 44066631116390400000), (Sum.inl 6, -5508328889548800000), (Sum.inl 9, 7344438519398400000), (Sum.inl 13, 29377754077593600000), (Sum.inl 26, 176266524465561600000), (Sum.inl 27, -66099946674585600000), (Sum.inl 34, 88133262232780800000), (Sum.inl 35, 88133262232780800000), (Sum.inl 54, -264399786698342400000), (Sum.inl 65, -264399786698342400000), (Sum.inl 67, 88133262232780800000), (Sum.inl 68, -995905727786188800000), (Sum.inl 125, -3163902968011161600000), (Sum.inl 257, 29377754077593600000), (Sum.inl 264, -555320156435251200000), (Sum.inl 266, -264399786698342400000)]

def reducedMerge134 : Integer.Sparse Master := [(Sum.inl 0, 152080119637770240000), (Sum.inl 1, 284330255273164800000), (Sum.inl 2, 240985507437158400000), (Sum.inl 3, -2304019796262912000000), (Sum.inl 5, -849318546559795200000), (Sum.inl 6, 104328708690124800000), (Sum.inl 9, -136656798747033600000), (Sum.inl 12, -1152009898131456000000), (Sum.inl 13, -3456029694394368000000), (Sum.inl 26, -1093254389976268800000), (Sum.inl 27, 1296011135397888000000), (Sum.inl 32, -576004949065728000000), (Sum.inl 34, -1122632144053862400000), (Sum.inl 35, -1669259339041996800000), (Sum.inl 54, 1728014847197184000000), (Sum.inl 55, 3456029694394368000000), (Sum.inl 60, -1152009898131456000000), (Sum.inl 61, 3456029694394368000000), (Sum.inl 65, 1728014847197184000000), (Sum.inl 67, -517249440910540800000), (Sum.inl 68, 2137985243438284800000), (Sum.inl 257, -546627194988134400000), (Sum.inl 264, 1728014847197184000000), (Sum.inl 266, 3367896432161587200000), (Sum.inl 268, 3456029694394368000000)]

def reducedMerge135 : Integer.Sparse Master := [(Sum.inl 0, 268498978857123840000), (Sum.inl 1, -358318371730636800000), (Sum.inl 2, -358318371730636800000), (Sum.inl 3, 691205938878873600000), (Sum.inl 5, 410950757493964800000), (Sum.inl 6, -86400742359859200000), (Sum.inl 9, 172801484719718400000), (Sum.inl 13, 691205938878873600000), (Sum.inl 26, 691205938878873600000), (Sum.inl 27, -196043364163584000000), (Sum.inl 34, 691205938878873600000), (Sum.inl 35, 1382411877757747200000), (Sum.inl 54, -784173456654336000000), (Sum.inl 60, 691205938878873600000), (Sum.inl 65, -784173456654336000000), (Sum.inl 67, 691205938878873600000), (Sum.inl 68, -910491182486323200000), (Sum.inl 257, 691205938878873600000), (Sum.inl 264, -784173456654336000000), (Sum.inl 266, -784173456654336000000), (Sum.inl 268, -2073617816636620800000)]

def reducedMerge136 : Integer.Sparse Master := [(Sum.inl 0, 420579098494894080000), (Sum.inl 1, -73988116457472000000), (Sum.inl 2, -117332864293478400000), (Sum.inl 3, -1612813857384038400000), (Sum.inl 5, -438367789065830400000), (Sum.inl 6, 17927966330265600000), (Sum.inl 9, 36144685972684800000), (Sum.inl 12, -1152009898131456000000), (Sum.inl 13, -2764823755515494400000), (Sum.inl 26, -402048451097395200000), (Sum.inl 27, 1099967771234304000000), (Sum.inl 32, -576004949065728000000), (Sum.inl 34, -431426205174988800000), (Sum.inl 35, -286847461284249600000), (Sum.inl 54, 943841390542848000000), (Sum.inl 55, 3456029694394368000000), (Sum.inl 60, -460803959252582400000), (Sum.inl 61, 3456029694394368000000), (Sum.inl 65, 943841390542848000000), (Sum.inl 67, 173956497968332800000), (Sum.inl 68, 1227494060951961600000), (Sum.inl 257, 144578743890739200000), (Sum.inl 264, 943841390542848000000), (Sum.inl 266, 2583722975507251200000), (Sum.inl 268, 1382411877757747200000)]

def reducedMerge137 : Integer.Sparse Master := [(Sum.inl 0, 236454051902423040000), (Sum.inl 1, -667398496149504000000), (Sum.inl 2, -18203129234841600000), (Sum.inl 3, -1524680595151257600000), (Sum.inl 5, -394301157949440000000), (Sum.inl 6, 12419637440716800000), (Sum.inl 9, 43489124492083200000), (Sum.inl 12, -1152009898131456000000), (Sum.inl 13, -2735446001437900800000), (Sum.inl 26, -225781926631833600000), (Sum.inl 27, 1033867824559718400000), (Sum.inl 32, -576004949065728000000), (Sum.inl 34, -343292942942208000000), (Sum.inl 35, -198714199051468800000), (Sum.inl 54, 679441603844505600000), (Sum.inl 55, 3456029694394368000000), (Sum.inl 60, -460803959252582400000), (Sum.inl 61, 3456029694394368000000), (Sum.inl 65, 679441603844505600000), (Sum.inl 67, 262089760201113600000), (Sum.inl 68, 231588333165772800000), (Sum.inl 125, -3163902968011161600000), (Sum.inl 257, 173956497968332800000), (Sum.inl 264, 388521234107596800000), (Sum.inl 266, 2319323188808908800000), (Sum.inl 268, 1382411877757747200000)]

def reducedMerge138 : Integer.Sparse Master := [(Sum.inl 0, -192693142250864640000), (Sum.inl 1, 84026643215155200000), (Sum.inl 2, 158556889851494400000), (Sum.inl 5, -177549683009126400000), (Sum.inl 6, 1187049572352000000), (Sum.inl 9, -2374099144704000000), (Sum.inl 13, -18992793157632000000), (Sum.inl 27, 518404454159155200000), (Sum.inl 32, -9496396578816000000), (Sum.inl 35, -18992793157632000000), (Sum.inl 55, 2073617816636620800000), (Sum.inl 60, -18992793157632000000), (Sum.inl 61, 2073617816636620800000), (Sum.inl 68, 1043931205752422400000), (Sum.inl 257, -9496396578816000000), (Sum.inl 264, 28489189736448000000), (Sum.inl 266, 2073617816636620800000), (Sum.inl 268, 2073617816636620800000)]

def reducedMerge139 : Integer.Sparse Master := [(Sum.inl 0, -249616275525550080000), (Sum.inl 1, 228037286331187200000), (Sum.inl 2, 300037904964403200000), (Sum.inl 68, -1320081996260966400000), (Sum.inl 266, -1824298290649497600000), (Sum.inl 268, -3456029694394368000000)]

def reducedMerge140 : Integer.Sparse Master := [(Sum.inl 0, -442309417776414720000), (Sum.inl 1, 312063929546342400000), (Sum.inl 2, 458594794815897600000), (Sum.inl 5, -177549683009126400000), (Sum.inl 6, 1187049572352000000), (Sum.inl 9, -2374099144704000000), (Sum.inl 13, -18992793157632000000), (Sum.inl 27, 518404454159155200000), (Sum.inl 32, -9496396578816000000), (Sum.inl 35, -18992793157632000000), (Sum.inl 55, 2073617816636620800000), (Sum.inl 60, -18992793157632000000), (Sum.inl 61, 2073617816636620800000), (Sum.inl 68, -276150790508544000000), (Sum.inl 257, -9496396578816000000), (Sum.inl 264, 28489189736448000000), (Sum.inl 266, 249319525987123200000), (Sum.inl 268, -1382411877757747200000)]

def reducedMerge141 : Integer.Sparse Master := [(Sum.inl 0, -130859540969472000000), (Sum.inl 1, 204243509256192000000), (Sum.inl 2, 13476419131392000000), (Sum.inl 3, 1652154789003264000000), (Sum.inl 5, 18206714953728000000), (Sum.inl 6, 177290670993408000000), (Sum.inl 7, 394831982297088000000), (Sum.inl 9, 157165350838272000000), (Sum.inl 12, 431245412204544000000), (Sum.inl 13, 3790175135072256000000), (Sum.inl 32, 646868118306816000000), (Sum.inl 35, 1867777495105536000000), (Sum.inl 52, 1652154789003264000000), (Sum.inl 54, -646868118306816000000), (Sum.inl 58, -25814918578176000000), (Sum.inl 60, 1078113530511360000000), (Sum.inl 62, -1293736236613632000000), (Sum.inl 68, -309779022938112000000), (Sum.inl 69, 197415991148544000000), (Sum.inl 70, 197415991148544000000), (Sum.inl 125, -592247973445632000000), (Sum.inl 128, 431245412204544000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 260, -646868118306816000000), (Sum.inl 264, -646868118306816000000), (Sum.inl 495, 215622706102272000000)]

def reducedMerge142 : Integer.Sparse Master := [(Sum.inl 0, 130042774613606400000), (Sum.inl 1, -25775842498560000000), (Sum.inl 2, -19790670477312000000), (Sum.inl 3, -441775950594048000000), (Sum.inl 5, 427490743357440000000), (Sum.inl 6, 13805498456064000000), (Sum.inl 7, -331331962945536000000), (Sum.inl 8, -590841861636096000000), (Sum.inl 9, -153695637430272000000), (Sum.inl 12, -110443987648512000000), (Sum.inl 13, -441775950594048000000), (Sum.inl 23, 331331962945536000000), (Sum.inl 24, 590841861636096000000), (Sum.inl 27, 230543456145408000000), (Sum.inl 35, -441775950594048000000), (Sum.inl 52, -220887975297024000000), (Sum.inl 54, 662663925891072000000), (Sum.inl 56, 1181683723272192000000), (Sum.inl 68, 461086912290816000000), (Sum.inl 69, -110443987648512000000), (Sum.inl 70, -110443987648512000000), (Sum.inl 71, -393894574424064000000), (Sum.inl 125, 331331962945536000000), (Sum.inl 196, 331331962945536000000), (Sum.inl 197, 1181683723272192000000)]

def reducedMerge143 : Integer.Sparse Master := [(Sum.inl 0, -816766355865600000), (Sum.inl 1, 178467666757632000000), (Sum.inl 2, -6314251345920000000), (Sum.inl 3, 1210378838409216000000), (Sum.inl 5, 445697458311168000000), (Sum.inl 6, 191096169449472000000), (Sum.inl 7, 63500019351552000000), (Sum.inl 8, -590841861636096000000), (Sum.inl 9, 3469713408000000000), (Sum.inl 12, 320801424556032000000), (Sum.inl 13, 3348399184478208000000), (Sum.inl 23, 331331962945536000000), (Sum.inl 24, 590841861636096000000), (Sum.inl 27, 230543456145408000000), (Sum.inl 32, 646868118306816000000), (Sum.inl 35, 1426001544511488000000), (Sum.inl 52, 1431266813706240000000), (Sum.inl 54, 15795807584256000000), (Sum.inl 56, 1181683723272192000000), (Sum.inl 58, -25814918578176000000), (Sum.inl 60, 1078113530511360000000), (Sum.inl 62, -1293736236613632000000), (Sum.inl 68, 151307889352704000000), (Sum.inl 69, 86972003500032000000), (Sum.inl 70, 86972003500032000000), (Sum.inl 71, -393894574424064000000), (Sum.inl 125, -260916010500096000000), (Sum.inl 128, 431245412204544000000), (Sum.inl 196, 331331962945536000000), (Sum.inl 197, 1181683723272192000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 260, -646868118306816000000), (Sum.inl 264, -646868118306816000000), (Sum.inl 495, 215622706102272000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1000 : Integer.Sparse Master := [(Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000), (Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000)]

def reducedMerge1002 : Integer.Sparse Master := [(Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000)]

def reducedMerge1003 : Integer.Sparse Master := [(Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000)]

def reducedMerge1004 : Integer.Sparse Master := [(Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000)]

def reducedMerge1005 : Integer.Sparse Master := [(Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000)]

def reducedMerge1006 : Integer.Sparse Master := [(Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000)]

def reducedMerge1007 : Integer.Sparse Master := [(Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000)]

def reducedMerge1008 : Integer.Sparse Master := [(Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000)]

def reducedMerge1009 : Integer.Sparse Master := [(Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000)]

def reducedMerge1010 : Integer.Sparse Master := [(Sum.inr 2710, 3772583761333911552000)]

def reducedMerge1011 : Integer.Sparse Master := [(Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000)]

def reducedMerge1012 : Integer.Sparse Master := [(Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000)]

def reducedMerge1013 : Integer.Sparse Master := [(Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000), (Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000)]

def reducedMerge1014 : Integer.Sparse Master := [(Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000), (Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000), (Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000)]

def reducedMerge1015 : Integer.Sparse Master := [(Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000), (Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000), (Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000), (Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000), (Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000)]

def reducedMerge1016 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000), (Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000), (Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000), (Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000), (Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000), (Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000), (Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000)]

def reducedMerge1017 : Integer.Sparse Master := [(Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000)]

def reducedMerge1018 : Integer.Sparse Master := [(Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000)]

def reducedMerge1019 : Integer.Sparse Master := [(Sum.inr 2721, -19158304125686906880000)]

def reducedMerge1020 : Integer.Sparse Master := [(Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000)]

def reducedMerge1021 : Integer.Sparse Master := [(Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000)]

def reducedMerge1022 : Integer.Sparse Master := [(Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000)]

def reducedMerge1023 : Integer.Sparse Master := [(Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1024 : Integer.Sparse Master := [(Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000)]

def reducedMerge1025 : Integer.Sparse Master := [(Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000)]

def reducedMerge1026 : Integer.Sparse Master := [(Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000)]

def reducedMerge1027 : Integer.Sparse Master := [(Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000)]

def reducedMerge1028 : Integer.Sparse Master := [(Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000)]

def reducedMerge1029 : Integer.Sparse Master := [(Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000)]

def reducedMerge1030 : Integer.Sparse Master := [(Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000), (Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000)]

def reducedMerge1031 : Integer.Sparse Master := [(Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000)]

def reducedMerge1032 : Integer.Sparse Master := [(Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000)]

def reducedMerge1033 : Integer.Sparse Master := [(Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000)]

def reducedMerge1035 : Integer.Sparse Master := [(Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000)]

def reducedMerge1036 : Integer.Sparse Master := [(Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000)]

def reducedMerge1037 : Integer.Sparse Master := [(Sum.inr 2743, 11054987203142615040000)]

def reducedMerge1038 : Integer.Sparse Master := [(Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000)]

def reducedMerge1039 : Integer.Sparse Master := [(Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000)]

def reducedMerge1040 : Integer.Sparse Master := [(Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000)]

def reducedMerge1041 : Integer.Sparse Master := [(Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000)]

def reducedMerge1042 : Integer.Sparse Master := [(Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000)]

def reducedMerge1043 : Integer.Sparse Master := [(Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000)]

def reducedMerge1044 : Integer.Sparse Master := [(Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000), (Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000)]

def reducedMerge1045 : Integer.Sparse Master := [(Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000), (Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000), (Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000), (Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000)]

def reducedMerge1046 : Integer.Sparse Master := [(Sum.inl 0, 2171091313262592000), (Sum.inl 1, -6633890123857920000), (Sum.inl 2, -3015404601753600000), (Sum.inl 3, 19298589451223040000), (Sum.inl 12, 9649294725611520000), (Sum.inl 13, 9649294725611520000), (Sum.inr 2754, -4946831880077574144000)]

def reducedMerge1047 : Integer.Sparse Master := [(Sum.inl 0, 2171091313262592000), (Sum.inl 1, -6633890123857920000), (Sum.inl 2, -3015404601753600000), (Sum.inl 3, 19298589451223040000), (Sum.inl 12, 9649294725611520000), (Sum.inl 13, 9649294725611520000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000)]

def reducedMerge1048 : Integer.Sparse Master := [(Sum.inl 0, -4906555875577036800), (Sum.inl 1, 5257024152403968000), (Sum.inl 2, -26285120762019840000), (Sum.inl 13, 28037462146154496000), (Sum.inr 2758, -8092322011089469440000)]

def reducedMerge1049 : Integer.Sparse Master := [(Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000)]

def reducedMerge1050 : Integer.Sparse Master := [(Sum.inl 0, -4906555875577036800), (Sum.inl 1, 5257024152403968000), (Sum.inl 2, -26285120762019840000), (Sum.inl 13, 28037462146154496000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000)]

def reducedMerge1051 : Integer.Sparse Master := [(Sum.inl 0, -2735464562314444800), (Sum.inl 1, -1376865971453952000), (Sum.inl 2, -29300525363773440000), (Sum.inl 3, 19298589451223040000), (Sum.inl 12, 9649294725611520000), (Sum.inl 13, 37686756871766016000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000)]

def reducedMerge1052 : Integer.Sparse Master := [(Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000)]

def reducedMerge1053 : Integer.Sparse Master := [(Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000)]

def reducedMerge1054 : Integer.Sparse Master := [(Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000)]

def reducedMerge1055 : Integer.Sparse Master := [(Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1056 : Integer.Sparse Master := [(Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000)]

def reducedMerge1057 : Integer.Sparse Master := [(Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000)]

def reducedMerge1058 : Integer.Sparse Master := [(Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000)]

def reducedMerge1059 : Integer.Sparse Master := [(Sum.inl 0, -2735464562314444800), (Sum.inl 1, -1376865971453952000), (Sum.inl 2, -29300525363773440000), (Sum.inl 3, 19298589451223040000), (Sum.inl 12, 9649294725611520000), (Sum.inl 13, 37686756871766016000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000), (Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000)]

def reducedMerge1060 : Integer.Sparse Master := [(Sum.inl 0, 18893574671066726400), (Sum.inl 1, 60115919407939584000), (Sum.inl 2, -17175976973697024000), (Sum.inl 3, -137407815789576192000), (Sum.inl 12, -137407815789576192000), (Sum.inl 13, -137407815789576192000), (Sum.inr 2777, -4714450911702024192000)]

def reducedMerge1061 : Integer.Sparse Master := [(Sum.inl 0, 20327853461465088000), (Sum.inl 1, 75762597121376256000), (Sum.inl 2, -15220142259517440000), (Sum.inl 3, -106114460362702848000), (Sum.inl 12, -106114460362702848000), (Sum.inl 13, -116545578838327296000), (Sum.inr 2777, -4714450911702024192000)]

def reducedMerge1062 : Integer.Sparse Master := [(Sum.inl 0, 6751740971424153600), (Sum.inl 1, 25319028642840576000), (Sum.inl 2, 25319028642840576000), (Sum.inl 13, 135034819428483072000), (Sum.inr 2779, 1029413887898812416000)]

def reducedMerge1063 : Integer.Sparse Master := [(Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000)]

def reducedMerge1064 : Integer.Sparse Master := [(Sum.inl 0, 6751740971424153600), (Sum.inl 1, 25319028642840576000), (Sum.inl 2, 25319028642840576000), (Sum.inl 13, 135034819428483072000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000)]

def reducedMerge1065 : Integer.Sparse Master := [(Sum.inl 0, 27079594432889241600), (Sum.inl 1, 101081625764216832000), (Sum.inl 2, 10098886383323136000), (Sum.inl 3, -106114460362702848000), (Sum.inl 12, -106114460362702848000), (Sum.inl 13, 18489240590155776000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000)]

def reducedMerge1066 : Integer.Sparse Master := [(Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000)]

def reducedMerge1067 : Integer.Sparse Master := [(Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000)]

def reducedMerge1068 : Integer.Sparse Master := [(Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000)]

def reducedMerge1069 : Integer.Sparse Master := [(Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000)]

def reducedMerge1070 : Integer.Sparse Master := [(Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1071 : Integer.Sparse Master := [(Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1072 : Integer.Sparse Master := [(Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1073 : Integer.Sparse Master := [(Sum.inl 0, 27079594432889241600), (Sum.inl 1, 101081625764216832000), (Sum.inl 2, 10098886383323136000), (Sum.inl 3, -106114460362702848000), (Sum.inl 12, -106114460362702848000), (Sum.inl 13, 18489240590155776000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000), (Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1074 : Integer.Sparse Master := [(Sum.inl 0, 24344129870574796800), (Sum.inl 1, 99704759792762880000), (Sum.inl 2, -19201638980450304000), (Sum.inl 3, -86815870911479808000), (Sum.inl 12, -96465165637091328000), (Sum.inl 13, 56175997461921792000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000), (Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000), (Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1075 : Integer.Sparse Master := [(Sum.inl 0, 24344129870574796800), (Sum.inl 1, 99704759792762880000), (Sum.inl 2, -19201638980450304000), (Sum.inl 3, -86815870911479808000), (Sum.inl 12, -96465165637091328000), (Sum.inl 13, 56175997461921792000), (Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000), (Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000), (Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000), (Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000), (Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000), (Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1076 : Integer.Sparse Master := [(Sum.inl 0, 24344129870574796800), (Sum.inl 1, 99704759792762880000), (Sum.inl 2, -19201638980450304000), (Sum.inl 3, -86815870911479808000), (Sum.inl 12, -96465165637091328000), (Sum.inl 13, 56175997461921792000), (Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000), (Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000), (Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000), (Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000), (Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000), (Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000), (Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000), (Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000), (Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000), (Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000), (Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000), (Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000), (Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000)]

def reducedMerge1077 : Integer.Sparse Master := [(Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000)]

def reducedMerge1078 : Integer.Sparse Master := [(Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000)]

def reducedMerge1079 : Integer.Sparse Master := [(Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000)]

def reducedMerge1080 : Integer.Sparse Master := [(Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000)]

def reducedMerge1081 : Integer.Sparse Master := [(Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000)]

def reducedMerge1082 : Integer.Sparse Master := [(Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000)]

def reducedMerge1083 : Integer.Sparse Master := [(Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000)]

def reducedMerge1084 : Integer.Sparse Master := [(Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000)]

def reducedMerge1085 : Integer.Sparse Master := [(Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000)]

def reducedMerge1086 : Integer.Sparse Master := [(Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000)]

def reducedMerge1087 : Integer.Sparse Master := [(Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1088 : Integer.Sparse Master := [(Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000)]

def reducedMerge1089 : Integer.Sparse Master := [(Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000)]

def reducedMerge1090 : Integer.Sparse Master := [(Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000), (Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000)]

def reducedMerge1091 : Integer.Sparse Master := [(Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000)]

def reducedMerge1092 : Integer.Sparse Master := [(Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000)]

def reducedMerge1093 : Integer.Sparse Master := [(Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000)]

def reducedMerge1094 : Integer.Sparse Master := [(Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000)]

def reducedMerge1095 : Integer.Sparse Master := [(Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000)]

def reducedMerge1096 : Integer.Sparse Master := [(Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000)]

def reducedMerge1097 : Integer.Sparse Master := [(Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000)]

def reducedMerge1098 : Integer.Sparse Master := [(Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000)]

def reducedMerge1099 : Integer.Sparse Master := [(Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000)]

def reducedMerge1100 : Integer.Sparse Master := [(Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000)]

def reducedMerge1101 : Integer.Sparse Master := [(Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000)]

def reducedMerge1102 : Integer.Sparse Master := [(Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000)]

def reducedMerge1103 : Integer.Sparse Master := [(Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000)]

def reducedMerge1104 : Integer.Sparse Master := [(Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000), (Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000)]

def reducedMerge1105 : Integer.Sparse Master := [(Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000), (Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000), (Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000), (Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000)]

def reducedMerge1106 : Integer.Sparse Master := [(Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000)]

def reducedMerge1107 : Integer.Sparse Master := [(Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000)]

def reducedMerge1108 : Integer.Sparse Master := [(Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000)]

def reducedMerge1109 : Integer.Sparse Master := [(Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000)]

def reducedMerge1110 : Integer.Sparse Master := [(Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000)]

def reducedMerge1111 : Integer.Sparse Master := [(Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000)]

def reducedMerge1112 : Integer.Sparse Master := [(Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000)]

def reducedMerge1113 : Integer.Sparse Master := [(Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000)]

def reducedMerge1114 : Integer.Sparse Master := [(Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000)]

def reducedMerge1115 : Integer.Sparse Master := [(Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000)]

def reducedMerge1116 : Integer.Sparse Master := [(Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000)]

def reducedMerge1117 : Integer.Sparse Master := [(Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000)]

def reducedMerge1118 : Integer.Sparse Master := [(Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000)]

def reducedMerge1119 : Integer.Sparse Master := [(Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000), (Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1120 : Integer.Sparse Master := [(Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000)]

def reducedMerge1121 : Integer.Sparse Master := [(Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000)]

def reducedMerge1122 : Integer.Sparse Master := [(Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000)]

def reducedMerge1123 : Integer.Sparse Master := [(Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000)]

def reducedMerge1124 : Integer.Sparse Master := [(Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000)]

def reducedMerge1125 : Integer.Sparse Master := [(Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000)]

def reducedMerge1126 : Integer.Sparse Master := [(Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000)]

def reducedMerge1127 : Integer.Sparse Master := [(Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000)]

def reducedMerge1128 : Integer.Sparse Master := [(Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000)]

def reducedMerge1129 : Integer.Sparse Master := [(Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000)]

def reducedMerge1130 : Integer.Sparse Master := [(Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000)]

def reducedMerge1131 : Integer.Sparse Master := [(Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000)]

def reducedMerge1132 : Integer.Sparse Master := [(Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000)]

def reducedMerge1133 : Integer.Sparse Master := [(Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000), (Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000)]

def reducedMerge1134 : Integer.Sparse Master := [(Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000), (Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000), (Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000), (Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000)]

def reducedMerge1135 : Integer.Sparse Master := [(Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000), (Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000), (Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000), (Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000), (Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000), (Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000), (Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000), (Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000)]

def reducedMerge1136 : Integer.Sparse Master := [(Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000)]

def reducedMerge1137 : Integer.Sparse Master := [(Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000)]

def reducedMerge1138 : Integer.Sparse Master := [(Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000)]

def reducedMerge1139 : Integer.Sparse Master := [(Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000)]

def reducedMerge1140 : Integer.Sparse Master := [(Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000)]

def reducedMerge1141 : Integer.Sparse Master := [(Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000)]

def reducedMerge1142 : Integer.Sparse Master := [(Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000)]

def reducedMerge1143 : Integer.Sparse Master := [(Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000)]

def reducedMerge1144 : Integer.Sparse Master := [(Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000)]

def reducedMerge1145 : Integer.Sparse Master := [(Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000)]

def reducedMerge1146 : Integer.Sparse Master := [(Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000)]

def reducedMerge1147 : Integer.Sparse Master := [(Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000)]

def reducedMerge1148 : Integer.Sparse Master := [(Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000)]

def reducedMerge1149 : Integer.Sparse Master := [(Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000), (Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000)]

def reducedMerge1150 : Integer.Sparse Master := [(Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000)]

def reducedMerge1151 : Integer.Sparse Master := [(Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1152 : Integer.Sparse Master := [(Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000)]

def reducedMerge1153 : Integer.Sparse Master := [(Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000)]

def reducedMerge1154 : Integer.Sparse Master := [(Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000)]

def reducedMerge1155 : Integer.Sparse Master := [(Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000)]

def reducedMerge1156 : Integer.Sparse Master := [(Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000)]

def reducedMerge1157 : Integer.Sparse Master := [(Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000)]

def reducedMerge1158 : Integer.Sparse Master := [(Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000)]

def reducedMerge1159 : Integer.Sparse Master := [(Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000)]

def reducedMerge1160 : Integer.Sparse Master := [(Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000)]

def reducedMerge1161 : Integer.Sparse Master := [(Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000)]

def reducedMerge1162 : Integer.Sparse Master := [(Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000)]

def reducedMerge1163 : Integer.Sparse Master := [(Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000), (Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000)]

def reducedMerge1164 : Integer.Sparse Master := [(Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000), (Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000), (Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000), (Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000)]

def reducedMerge1165 : Integer.Sparse Master := [(Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000)]

def reducedMerge1166 : Integer.Sparse Master := [(Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000)]

def reducedMerge1167 : Integer.Sparse Master := [(Sum.inr 3064, 7350751094580117504000)]

def reducedMerge1168 : Integer.Sparse Master := [(Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000)]

def reducedMerge1169 : Integer.Sparse Master := [(Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000)]

def reducedMerge1170 : Integer.Sparse Master := [(Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000)]

def reducedMerge1171 : Integer.Sparse Master := [(Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000)]

def reducedMerge1172 : Integer.Sparse Master := [(Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000)]

def reducedMerge1173 : Integer.Sparse Master := [(Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000)]

def reducedMerge1174 : Integer.Sparse Master := [(Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000)]

def reducedMerge1175 : Integer.Sparse Master := [(Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000)]

def reducedMerge1176 : Integer.Sparse Master := [(Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000)]

def reducedMerge1177 : Integer.Sparse Master := [(Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000)]

def reducedMerge1178 : Integer.Sparse Master := [(Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000), (Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000)]

def reducedMerge1179 : Integer.Sparse Master := [(Sum.inr 3086, -22351245374360125440000)]

def reducedMerge1180 : Integer.Sparse Master := [(Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000)]

def reducedMerge1181 : Integer.Sparse Master := [(Sum.inl 0, 24522720570025574400), (Sum.inl 1, 187522985425305600000), (Sum.inl 2, -24728881977999360000), (Sum.inl 3, -326619013934481408000), (Sum.inl 4, -141157642588913664000), (Sum.inl 26, -141157642588913664000)]

def reducedMerge1182 : Integer.Sparse Master := [(Sum.inl 0, 44591733363179520000), (Sum.inl 1, -45903254932684800000), (Sum.inl 2, -59018470627737600000), (Sum.inl 3, 104921725560422400000), (Sum.inl 26, 104921725560422400000), (Sum.inr 3092, -3891082594516992000000)]

def reducedMerge1183 : Integer.Sparse Master := [(Sum.inl 0, 69114453933205094400), (Sum.inl 1, 141619730492620800000), (Sum.inl 2, -83747352605736960000), (Sum.inl 3, -221697288374059008000), (Sum.inl 4, -141157642588913664000), (Sum.inl 26, -36235917028491264000), (Sum.inr 3092, -3891082594516992000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1184 : Integer.Sparse Master := [(Sum.inl 0, 69114453933205094400), (Sum.inl 1, 141619730492620800000), (Sum.inl 2, -83747352605736960000), (Sum.inl 3, -221697288374059008000), (Sum.inl 4, -141157642588913664000), (Sum.inl 26, -36235917028491264000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000)]

def reducedMerge1185 : Integer.Sparse Master := [(Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000)]

def reducedMerge1186 : Integer.Sparse Master := [(Sum.inl 0, 46025869562988134400), (Sum.inl 2, 54792701860700160000), (Sum.inl 3, 526009937862721536000), (Sum.inl 4, 350673291908481024000), (Sum.inl 26, 350673291908481024000), (Sum.inr 3098, 34405213211462467584000)]

def reducedMerge1187 : Integer.Sparse Master := [(Sum.inl 0, 46025869562988134400), (Sum.inl 2, 54792701860700160000), (Sum.inl 3, 526009937862721536000), (Sum.inl 4, 350673291908481024000), (Sum.inl 26, 350673291908481024000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000)]

def reducedMerge1188 : Integer.Sparse Master := [(Sum.inl 0, 17735212037033164800), (Sum.inl 1, -31670021494702080000), (Sum.inl 2, -19002012896821248000), (Sum.inl 3, -101344068783046656000), (Sum.inl 26, -101344068783046656000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1189 : Integer.Sparse Master := [(Sum.inl 0, -97383925744422912000), (Sum.inl 1, 62593054054207488000), (Sum.inl 2, -67850808205049856000), (Sum.inl 3, -291135276929581056000), (Sum.inl 4, -185031726683553792000), (Sum.inl 26, -185031726683553792000)]

def reducedMerge1190 : Integer.Sparse Master := [(Sum.inl 0, -79648713707389747200), (Sum.inl 1, 30923032559505408000), (Sum.inl 2, -86852821101871104000), (Sum.inl 3, -392479345712627712000), (Sum.inl 4, -185031726683553792000), (Sum.inl 26, -286375795466600448000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1191 : Integer.Sparse Master := [(Sum.inl 0, -33622844144401612800), (Sum.inl 1, 30923032559505408000), (Sum.inl 2, -32060119241170944000), (Sum.inl 3, 133530592150093824000), (Sum.inl 4, 165641565224927232000), (Sum.inl 26, 64297496441880576000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1192 : Integer.Sparse Master := [(Sum.inl 0, 35491609788803481600), (Sum.inl 1, 172542763052126208000), (Sum.inl 2, -115807471846907904000), (Sum.inl 3, -88166696223965184000), (Sum.inl 4, 24483922636013568000), (Sum.inl 26, 28061579413389312000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1193 : Integer.Sparse Master := [(Sum.inl 0, 35491609788803481600), (Sum.inl 1, 172542763052126208000), (Sum.inl 2, -115807471846907904000), (Sum.inl 3, -88166696223965184000), (Sum.inl 4, 24483922636013568000), (Sum.inl 26, 28061579413389312000), (Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000), (Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1194 : Integer.Sparse Master := [(Sum.inl 0, 35491609788803481600), (Sum.inl 1, 172542763052126208000), (Sum.inl 2, -115807471846907904000), (Sum.inl 3, -88166696223965184000), (Sum.inl 4, 24483922636013568000), (Sum.inl 26, 28061579413389312000), (Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000), (Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000), (Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000), (Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000), (Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000), (Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1195 : Integer.Sparse Master := [(Sum.inl 0, 35491609788803481600), (Sum.inl 1, 172542763052126208000), (Sum.inl 2, -115807471846907904000), (Sum.inl 3, -88166696223965184000), (Sum.inl 4, 24483922636013568000), (Sum.inl 26, 28061579413389312000), (Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000), (Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000), (Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000), (Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000), (Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000), (Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000), (Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000), (Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000), (Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000), (Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000), (Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000), (Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000), (Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000), (Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000)]

set_option maxHeartbeats 1000000 in
def reducedMerge1196 : Integer.Sparse Master := [(Sum.inl 0, 59835739659378278400), (Sum.inl 1, 272247522844889088000), (Sum.inl 2, -135009110827358208000), (Sum.inl 3, -174982567135444992000), (Sum.inl 4, 24483922636013568000), (Sum.inl 12, -96465165637091328000), (Sum.inl 13, 56175997461921792000), (Sum.inl 26, 28061579413389312000), (Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000), (Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000), (Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000), (Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000), (Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000), (Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000), (Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000), (Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000), (Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000), (Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000), (Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000), (Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000), (Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000), (Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000), (Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000), (Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000), (Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000), (Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000), (Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000), (Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000), (Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000), (Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000), (Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000), (Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000), (Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000), (Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000), (Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000), (Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000), (Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000)]

def reducedMerge1197 : Integer.Sparse Master := [(Sum.inl 0, -32828912319445401600), (Sum.inl 1, 25917562357456896000), (Sum.inl 2, 34556749809942528000), (Sum.inl 26, 138226999239770112000)]

def reducedMerge1198 : Integer.Sparse Master := [(Sum.inl 0, -32828912319445401600), (Sum.inl 1, 25917562357456896000), (Sum.inl 2, 34556749809942528000), (Sum.inl 26, 138226999239770112000)]

def reducedMerge1199 : Integer.Sparse Master := [(Sum.inr 3118, 6748651458342420480000)]

def reducedMerge1200 : Integer.Sparse Master := [(Sum.inl 0, -80161205828426956800), (Sum.inl 1, 67509917725114368000), (Sum.inl 2, -84226612142002176000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 435228483673718784000)]

def reducedMerge1201 : Integer.Sparse Master := [(Sum.inl 0, -80161205828426956800), (Sum.inl 1, 67509917725114368000), (Sum.inl 2, -84226612142002176000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 435228483673718784000), (Sum.inr 3118, 6748651458342420480000)]

def reducedMerge1202 : Integer.Sparse Master := [(Sum.inl 0, -112990118147872358400), (Sum.inl 1, 93427480082571264000), (Sum.inl 2, -49669862332059648000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000)]

def reducedMerge1203 : Integer.Sparse Master := [(Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000)]

def reducedMerge1204 : Integer.Sparse Master := [(Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000)]

def reducedMerge1205 : Integer.Sparse Master := [(Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000)]

def reducedMerge1206 : Integer.Sparse Master := [(Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000)]

def reducedMerge1207 : Integer.Sparse Master := [(Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000)]

def reducedMerge1208 : Integer.Sparse Master := [(Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000)]

def reducedMerge1209 : Integer.Sparse Master := [(Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000)]

def reducedMerge1210 : Integer.Sparse Master := [(Sum.inl 0, -112990118147872358400), (Sum.inl 1, 93427480082571264000), (Sum.inl 2, -49669862332059648000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000)]

def reducedMerge1211 : Integer.Sparse Master := [(Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000)]

def reducedMerge1212 : Integer.Sparse Master := [(Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000)]

def reducedMerge1213 : Integer.Sparse Master := [(Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000)]

def reducedMerge1214 : Integer.Sparse Master := [(Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000)]

def reducedMerge1215 : Integer.Sparse Master := [(Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1216 : Integer.Sparse Master := [(Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000)]

def reducedMerge1217 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000)]

def reducedMerge1218 : Integer.Sparse Master := [(Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000)]

def reducedMerge1219 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000)]

def reducedMerge1220 : Integer.Sparse Master := [(Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000)]

def reducedMerge1221 : Integer.Sparse Master := [(Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def reducedMerge1222 : Integer.Sparse Master := [(Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def reducedMerge1223 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def reducedMerge1224 : Integer.Sparse Master := [(Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def reducedMerge1225 : Integer.Sparse Master := [(Sum.inl 0, -112990118147872358400), (Sum.inl 1, 93427480082571264000), (Sum.inl 2, -49669862332059648000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def reducedMerge1226 : Integer.Sparse Master := [(Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000)]

def reducedMerge1227 : Integer.Sparse Master := [(Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000)]

def reducedMerge1228 : Integer.Sparse Master := [(Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000)]

def reducedMerge1229 : Integer.Sparse Master := [(Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000)]

def reducedMerge1230 : Integer.Sparse Master := [(Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000)]

def reducedMerge1231 : Integer.Sparse Master := [(Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000)]

def reducedMerge1232 : Integer.Sparse Master := [(Sum.inl 0, -24418675486369382400), (Sum.inl 1, 23479495659970560000), (Sum.inl 2, -4695899131994112000), (Sum.inl 3, -150268772223811584000), (Sum.inl 12, -75134386111905792000), (Sum.inl 13, -225403158335717376000), (Sum.inr 3222, -12438782405973245952000)]

def reducedMerge1233 : Integer.Sparse Master := [(Sum.inl 0, -30165864245998387200), (Sum.inl 1, -1651933730635776000), (Sum.inl 2, 77408247828086784000), (Sum.inl 3, 63794790818906112000), (Sum.inl 12, 121362273116356608000), (Sum.inl 13, 306519337051619328000)]

def reducedMerge1234 : Integer.Sparse Master := [(Sum.inl 0, -54584539732367769600), (Sum.inl 1, 21827561929334784000), (Sum.inl 2, 72712348696092672000), (Sum.inl 3, -86473981404905472000), (Sum.inl 12, 46227887004450816000), (Sum.inl 13, 81116178715901952000), (Sum.inr 3222, -12438782405973245952000)]

def reducedMerge1235 : Integer.Sparse Master := [(Sum.inl 0, 50231062632709324800), (Sum.inl 1, 246165671522340864000), (Sum.inl 2, 73434334061297664000), (Sum.inl 3, -293737336245190656000), (Sum.inl 12, -86783652574101504000), (Sum.inl 13, -293737336245190656000)]

def reducedMerge1236 : Integer.Sparse Master := []

def reducedMerge1237 : Integer.Sparse Master := [(Sum.inl 0, 50231062632709324800), (Sum.inl 1, 246165671522340864000), (Sum.inl 2, 73434334061297664000), (Sum.inl 3, -293737336245190656000), (Sum.inl 12, -86783652574101504000), (Sum.inl 13, -293737336245190656000)]

def reducedMerge1238 : Integer.Sparse Master := [(Sum.inl 0, -4353477099658444800), (Sum.inl 1, 267993233451675648000), (Sum.inl 2, 146146682757390336000), (Sum.inl 3, -380211317650096128000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inr 3222, -12438782405973245952000)]

def reducedMerge1239 : Integer.Sparse Master := [(Sum.inl 0, -4353477099658444800), (Sum.inl 1, 267993233451675648000), (Sum.inl 2, 146146682757390336000), (Sum.inl 3, -380211317650096128000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000)]

def reducedMerge1240 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000)]

def reducedMerge1241 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000)]

def reducedMerge1242 : Integer.Sparse Master := [(Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000)]

def reducedMerge1243 : Integer.Sparse Master := [(Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000)]

def reducedMerge1244 : Integer.Sparse Master := [(Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000)]

def reducedMerge1245 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000)]

def reducedMerge1246 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000)]

def reducedMerge1247 : Integer.Sparse Master := [(Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1248 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000)]

def reducedMerge1249 : Integer.Sparse Master := [(Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000)]

def reducedMerge1250 : Integer.Sparse Master := [(Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def reducedMerge1251 : Integer.Sparse Master := [(Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def reducedMerge1252 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def reducedMerge1253 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def reducedMerge1254 : Integer.Sparse Master := [(Sum.inl 0, -4353477099658444800), (Sum.inl 1, 267993233451675648000), (Sum.inl 2, 146146682757390336000), (Sum.inl 3, -380211317650096128000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def reducedMerge1255 : Integer.Sparse Master := [(Sum.inl 0, -117343595247530803200), (Sum.inl 1, 361420713534246912000), (Sum.inl 2, 96476820425330688000), (Sum.inl 3, 96957509274501120000), (Sum.inl 4, 477168826924597248000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def reducedMerge1256 : Integer.Sparse Master := [(Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000)]

def reducedMerge1257 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000)]

def reducedMerge1258 : Integer.Sparse Master := [(Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000)]

def reducedMerge1259 : Integer.Sparse Master := [(Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000)]

def reducedMerge1260 : Integer.Sparse Master := [(Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000)]

def reducedMerge1261 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000)]

def reducedMerge1262 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000)]

def reducedMerge1263 : Integer.Sparse Master := [(Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000)]

def reducedMerge1264 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000)]

def reducedMerge1265 : Integer.Sparse Master := [(Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000)]

def reducedMerge1266 : Integer.Sparse Master := [(Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def reducedMerge1267 : Integer.Sparse Master := [(Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def reducedMerge1268 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def reducedMerge1269 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def reducedMerge1270 : Integer.Sparse Master := [(Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000)]

def reducedMerge1271 : Integer.Sparse Master := [(Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000)]

def reducedMerge1272 : Integer.Sparse Master := [(Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000)]

def reducedMerge1273 : Integer.Sparse Master := [(Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000)]

def reducedMerge1274 : Integer.Sparse Master := [(Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000)]

def reducedMerge1275 : Integer.Sparse Master := [(Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000)]

def reducedMerge1276 : Integer.Sparse Master := [(Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000)]

def reducedMerge1277 : Integer.Sparse Master := [(Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000)]

def reducedMerge1278 : Integer.Sparse Master := [(Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000)]

def reducedMerge1279 : Integer.Sparse Master := [(Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1280 : Integer.Sparse Master := [(Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000)]

def reducedMerge1281 : Integer.Sparse Master := [(Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000)]

def reducedMerge1282 : Integer.Sparse Master := [(Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000)]

def reducedMerge1283 : Integer.Sparse Master := [(Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000)]

def reducedMerge1284 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000)]

def reducedMerge1285 : Integer.Sparse Master := [(Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000)]

def reducedMerge1286 : Integer.Sparse Master := [(Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000)]

def reducedMerge1287 : Integer.Sparse Master := [(Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000)]

def reducedMerge1288 : Integer.Sparse Master := [(Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000)]

def reducedMerge1289 : Integer.Sparse Master := [(Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000)]

def reducedMerge1290 : Integer.Sparse Master := [(Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000)]

def reducedMerge1291 : Integer.Sparse Master := [(Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000)]

def reducedMerge1292 : Integer.Sparse Master := [(Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000)]

def reducedMerge1293 : Integer.Sparse Master := [(Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000)]

def reducedMerge1294 : Integer.Sparse Master := [(Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000)]

def reducedMerge1295 : Integer.Sparse Master := [(Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000)]

def reducedMerge1296 : Integer.Sparse Master := [(Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000)]

def reducedMerge1297 : Integer.Sparse Master := [(Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000)]

def reducedMerge1298 : Integer.Sparse Master := [(Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000)]

def reducedMerge1299 : Integer.Sparse Master := [(Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000)]

def reducedMerge1300 : Integer.Sparse Master := [(Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000)]

def reducedMerge1301 : Integer.Sparse Master := [(Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000)]

def reducedMerge1302 : Integer.Sparse Master := [(Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000)]

def reducedMerge1303 : Integer.Sparse Master := [(Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000)]

def reducedMerge1304 : Integer.Sparse Master := [(Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000)]

def reducedMerge1305 : Integer.Sparse Master := [(Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000)]

def reducedMerge1306 : Integer.Sparse Master := [(Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000)]

def reducedMerge1307 : Integer.Sparse Master := [(Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000)]

def reducedMerge1308 : Integer.Sparse Master := [(Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000)]

def reducedMerge1309 : Integer.Sparse Master := [(Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def reducedMerge1310 : Integer.Sparse Master := [(Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def reducedMerge1311 : Integer.Sparse Master := [(Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1312 : Integer.Sparse Master := [(Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def reducedMerge1313 : Integer.Sparse Master := [(Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def reducedMerge1314 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000), (Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def reducedMerge1315 : Integer.Sparse Master := [(Sum.inl 0, -117343595247530803200), (Sum.inl 1, 361420713534246912000), (Sum.inl 2, 96476820425330688000), (Sum.inl 3, 96957509274501120000), (Sum.inl 4, 477168826924597248000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000), (Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000), (Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def reducedMerge1316 : Integer.Sparse Master := [(Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000)]

def reducedMerge1317 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000)]

def reducedMerge1318 : Integer.Sparse Master := [(Sum.inr 3524, -1072771597873446912000)]

def reducedMerge1319 : Integer.Sparse Master := [(Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000)]

def reducedMerge1320 : Integer.Sparse Master := [(Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000)]

def reducedMerge1321 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000)]

def reducedMerge1322 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000)]

def reducedMerge1323 : Integer.Sparse Master := [(Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000)]

def reducedMerge1324 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000)]

def reducedMerge1325 : Integer.Sparse Master := [(Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000)]

def reducedMerge1326 : Integer.Sparse Master := [(Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def reducedMerge1327 : Integer.Sparse Master := [(Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def reducedMerge1328 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def reducedMerge1329 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def reducedMerge1330 : Integer.Sparse Master := [(Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000)]

def reducedMerge1331 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000)]

def reducedMerge1332 : Integer.Sparse Master := [(Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000)]

def reducedMerge1333 : Integer.Sparse Master := [(Sum.inr 3548, -1028860950356951040000)]

def reducedMerge1334 : Integer.Sparse Master := [(Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000)]

def reducedMerge1335 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000)]

def reducedMerge1336 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000)]

def reducedMerge1337 : Integer.Sparse Master := [(Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000)]

def reducedMerge1338 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000)]

def reducedMerge1339 : Integer.Sparse Master := [(Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000)]

def reducedMerge1340 : Integer.Sparse Master := [(Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def reducedMerge1341 : Integer.Sparse Master := [(Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def reducedMerge1342 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def reducedMerge1343 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1344 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def reducedMerge1345 : Integer.Sparse Master := [(Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000)]

def reducedMerge1346 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000)]

def reducedMerge1347 : Integer.Sparse Master := [(Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000)]

def reducedMerge1348 : Integer.Sparse Master := [(Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000)]

def reducedMerge1349 : Integer.Sparse Master := [(Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000)]

def reducedMerge1350 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000)]

def reducedMerge1351 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000)]

def reducedMerge1352 : Integer.Sparse Master := [(Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000)]

def reducedMerge1353 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000)]

def reducedMerge1354 : Integer.Sparse Master := [(Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000)]

def reducedMerge1355 : Integer.Sparse Master := [(Sum.inr 3584, 29008204646800490496000)]

def reducedMerge1356 : Integer.Sparse Master := [(Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000)]

def reducedMerge1357 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000)]

def reducedMerge1358 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000)]

def reducedMerge1359 : Integer.Sparse Master := [(Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000)]

def reducedMerge1360 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000)]

def reducedMerge1361 : Integer.Sparse Master := [(Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000)]

def reducedMerge1362 : Integer.Sparse Master := [(Sum.inr 3627, 7417776676181114880000)]

def reducedMerge1363 : Integer.Sparse Master := [(Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000)]

def reducedMerge1364 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000)]

def reducedMerge1365 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000)]

def reducedMerge1366 : Integer.Sparse Master := [(Sum.inr 3633, 17665403553650442240000)]

def reducedMerge1367 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000)]

def reducedMerge1368 : Integer.Sparse Master := [(Sum.inr 3670, -3558260895488409600000)]

def reducedMerge1369 : Integer.Sparse Master := [(Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def reducedMerge1370 : Integer.Sparse Master := [(Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def reducedMerge1371 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def reducedMerge1372 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def reducedMerge1373 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def reducedMerge1374 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000), (Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def reducedMerge1375 : Integer.Sparse Master := [(Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1376 : Integer.Sparse Master := [(Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000)]

def reducedMerge1377 : Integer.Sparse Master := [(Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000)]

def reducedMerge1378 : Integer.Sparse Master := [(Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000)]

def reducedMerge1379 : Integer.Sparse Master := [(Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000)]

def reducedMerge1380 : Integer.Sparse Master := [(Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000), (Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000)]

def reducedMerge1381 : Integer.Sparse Master := [(Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000)]

def reducedMerge1382 : Integer.Sparse Master := [(Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000)]

def reducedMerge1383 : Integer.Sparse Master := [(Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000)]

def reducedMerge1384 : Integer.Sparse Master := [(Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000)]

def reducedMerge1385 : Integer.Sparse Master := [(Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000)]

def reducedMerge1386 : Integer.Sparse Master := [(Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000)]

def reducedMerge1387 : Integer.Sparse Master := [(Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000), (Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000)]

def reducedMerge1388 : Integer.Sparse Master := [(Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000), (Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000), (Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000), (Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000)]

def reducedMerge1389 : Integer.Sparse Master := [(Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000)]

def reducedMerge1390 : Integer.Sparse Master := [(Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000)]

def reducedMerge1391 : Integer.Sparse Master := [(Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000)]

def reducedMerge1392 : Integer.Sparse Master := [(Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000)]

def reducedMerge1393 : Integer.Sparse Master := [(Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000)]

def reducedMerge1394 : Integer.Sparse Master := [(Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000), (Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000)]

def reducedMerge1395 : Integer.Sparse Master := [(Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000)]

def reducedMerge1396 : Integer.Sparse Master := [(Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000)]

def reducedMerge1397 : Integer.Sparse Master := [(Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000)]

def reducedMerge1398 : Integer.Sparse Master := [(Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000)]

def reducedMerge1399 : Integer.Sparse Master := [(Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000)]

def reducedMerge1400 : Integer.Sparse Master := [(Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000)]

def reducedMerge1401 : Integer.Sparse Master := [(Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000), (Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000)]

def reducedMerge1402 : Integer.Sparse Master := [(Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000), (Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000), (Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000), (Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000)]

def reducedMerge1403 : Integer.Sparse Master := [(Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000), (Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000), (Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000), (Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000), (Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000), (Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000), (Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000), (Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000)]

def reducedMerge1404 : Integer.Sparse Master := [(Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000)]

def reducedMerge1405 : Integer.Sparse Master := [(Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000)]

def reducedMerge1406 : Integer.Sparse Master := [(Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000)]

def reducedMerge1407 : Integer.Sparse Master := [(Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1408 : Integer.Sparse Master := [(Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000)]

def reducedMerge1409 : Integer.Sparse Master := [(Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000), (Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000)]

def reducedMerge1410 : Integer.Sparse Master := [(Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000)]

def reducedMerge1411 : Integer.Sparse Master := [(Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000)]

def reducedMerge1412 : Integer.Sparse Master := [(Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000)]

def reducedMerge1413 : Integer.Sparse Master := [(Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000)]

def reducedMerge1414 : Integer.Sparse Master := [(Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000)]

def reducedMerge1415 : Integer.Sparse Master := [(Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000)]

def reducedMerge1416 : Integer.Sparse Master := [(Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000), (Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000)]

def reducedMerge1417 : Integer.Sparse Master := [(Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000), (Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000), (Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000), (Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000)]

def reducedMerge1418 : Integer.Sparse Master := [(Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000)]

def reducedMerge1419 : Integer.Sparse Master := [(Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000)]

def reducedMerge1420 : Integer.Sparse Master := [(Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000)]

def reducedMerge1421 : Integer.Sparse Master := []

def reducedMerge1422 : Integer.Sparse Master := [(Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000)]

def reducedMerge1423 : Integer.Sparse Master := [(Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000), (Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000)]

def reducedMerge1424 : Integer.Sparse Master := [(Sum.inr 3809, -28544727109663457280000)]

def reducedMerge1425 : Integer.Sparse Master := [(Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000)]

def reducedMerge1426 : Integer.Sparse Master := [(Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000)]

def reducedMerge1427 : Integer.Sparse Master := [(Sum.inr 3814, -18142276456326758400000)]

def reducedMerge1428 : Integer.Sparse Master := [(Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1429 : Integer.Sparse Master := [(Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1430 : Integer.Sparse Master := [(Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000), (Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1431 : Integer.Sparse Master := [(Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000), (Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000), (Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000), (Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1432 : Integer.Sparse Master := [(Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000), (Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000), (Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000), (Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000), (Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000), (Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000), (Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000), (Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1433 : Integer.Sparse Master := [(Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000), (Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000), (Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000), (Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000), (Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000), (Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000), (Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000), (Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000), (Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000), (Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000), (Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000), (Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000), (Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000), (Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000), (Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000), (Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1434 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000), (Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000), (Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000), (Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000), (Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000), (Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000), (Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000), (Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000), (Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000), (Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000), (Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000), (Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000), (Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000), (Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000), (Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000), (Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000), (Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000), (Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

set_option maxHeartbeats 1000000 in
def reducedMerge1435 : Integer.Sparse Master := [(Sum.inl 0, -117343595247530803200), (Sum.inl 1, 361420713534246912000), (Sum.inl 2, 96476820425330688000), (Sum.inl 3, 96957509274501120000), (Sum.inl 4, 477168826924597248000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000), (Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000), (Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000), (Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000), (Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000), (Sum.inr 3673, -2089015568665804800000), (Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000), (Sum.inr 3685, -669848715789926400000), (Sum.inr 3689, 5058598529834680320000), (Sum.inr 3690, -2714220736148275200000), (Sum.inr 3692, -5214891424162775040000), (Sum.inr 3693, -1773350590788403200000), (Sum.inr 3694, -5315776700851814400000), (Sum.inr 3698, 3611345102733312000000), (Sum.inr 3699, 3293229788164915200000), (Sum.inr 3703, -6378432071205519360000), (Sum.inr 3705, 8915230341595791360000), (Sum.inr 3706, -10603132867144581120000), (Sum.inr 3708, 23153419811192832000000), (Sum.inr 3709, 7818430382751744000000), (Sum.inr 3710, 3622287461825249280000), (Sum.inr 3715, 11249654248211742720000), (Sum.inr 3719, 7397988905631744000000), (Sum.inr 3720, 6831804330736680960000), (Sum.inr 3721, 12949195045327994880000), (Sum.inr 3722, -26217469888567050240000), (Sum.inr 3723, 3090408338022727680000), (Sum.inr 3724, -12931866039110860800000), (Sum.inr 3730, 498588466060984320000), (Sum.inr 3731, -4479366205522575360000), (Sum.inr 3732, -15823981309321543680000), (Sum.inr 3733, 1301788622079590400000), (Sum.inr 3755, 885060905467576320000), (Sum.inr 3759, -2229127337632333824000), (Sum.inr 3760, 7779502517921906688000), (Sum.inr 3761, -2581778767834054656000), (Sum.inr 3762, -3482485535088967680000), (Sum.inr 3763, 722635406229897216000), (Sum.inr 3768, -629877478875660288000), (Sum.inr 3772, -1457354951397015552000), (Sum.inr 3779, -23279727428871782400000), (Sum.inr 3780, 4493455024472064000000), (Sum.inr 3781, 1745085365617950720000), (Sum.inr 3782, -4452974806184755200000), (Sum.inr 3783, 1278536233166438400000), (Sum.inr 3786, 5625894605263994880000), (Sum.inr 3787, -16392111811529932800000), (Sum.inr 3788, 2738043209843343360000), (Sum.inr 3789, 1441864010724802560000), (Sum.inr 3800, 26650108359770112000000), (Sum.inr 3801, -13178290840890900480000), (Sum.inr 3802, -5516271414691430400000), (Sum.inr 3803, -6944207726412988416000), (Sum.inr 3805, 5260225873509089280000), (Sum.inr 3809, -28544727109663457280000), (Sum.inr 3812, 10099373456256860160000), (Sum.inr 3813, -31930167407745761280000), (Sum.inr 3814, -18142276456326758400000), (Sum.inr 3819, 2089015568665804800000)]

def reducedMerge1436part0 : Integer.Sparse Master := [(Sum.inl 0, -57507855588152524800), (Sum.inl 1, 633668236379136000000), (Sum.inl 2, -38532290402027520000), (Sum.inl 3, -78025057860943872000), (Sum.inl 4, 501652749560610816000), (Sum.inl 12, -137020931206742016000), (Sum.inl 13, -156445160067366912000), (Sum.inl 26, 601517062326878208000), (Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000), (Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000), (Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000), (Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000), (Sum.inr 2683, -2711614482074566656000), (Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000), (Sum.inr 2690, -2124806707563724800000), (Sum.inr 2697, 665857147118026752000), (Sum.inr 2698, -3210049119603916800000), (Sum.inr 2700, -450757951040323584000), (Sum.inr 2702, -423147689038577664000), (Sum.inr 2706, 4172340565215019008000), (Sum.inr 2707, -847409560407244800000), (Sum.inr 2708, 2180351629537837056000)]

def reducedMerge1436part1 : Integer.Sparse Master := [(Sum.inr 2710, 3772583761333911552000), (Sum.inr 2712, 669848715789926400000), (Sum.inr 2714, -18738707098219315200000), (Sum.inr 2716, 178978720009420800000), (Sum.inr 2718, 2657205919166496768000), (Sum.inr 2719, 189716558307655680000), (Sum.inr 2721, -19158304125686906880000), (Sum.inr 2722, -53630193427477954560000), (Sum.inr 2723, -6132895964194406400000), (Sum.inr 2724, 151499143634485248000), (Sum.inr 2726, -21951447043276800000), (Sum.inr 2728, -4207603471599403008000), (Sum.inr 2729, 160580769836433408000), (Sum.inr 2730, -5448613796115775488000), (Sum.inr 2731, 1891520709844598784000), (Sum.inr 2732, -3902216098532032512000), (Sum.inr 2734, 6171454343172980736000), (Sum.inr 2735, 3357311730124455936000), (Sum.inr 2736, 4773540463463890944000), (Sum.inr 2737, -189385081118392320000), (Sum.inr 2738, 4201772064568049664000), (Sum.inr 2739, 863627382126673920000), (Sum.inr 2740, -636663027329925120000), (Sum.inr 2743, 11054987203142615040000), (Sum.inr 2744, -22996102308321558528000), (Sum.inr 2745, -5202654127895347200000), (Sum.inr 2746, 5202654127895347200000), (Sum.inr 2747, -1346211378226003968000), (Sum.inr 2748, -3407495751248117760000), (Sum.inr 2750, 27983833967776038912000), (Sum.inr 2751, -28257993540927553536000), (Sum.inr 2754, -4946831880077574144000), (Sum.inr 2758, -8092322011089469440000), (Sum.inr 2759, -7444916811245813760000), (Sum.inr 2760, -416428679821787136000), (Sum.inr 2761, -1016042941450027008000), (Sum.inr 2763, -21955095856769531904000), (Sum.inr 2764, -23846279734862807040000), (Sum.inr 2765, 9533108969263595520000), (Sum.inr 2769, -22778979783065468928000), (Sum.inr 2771, -1080639818309173248000), (Sum.inr 2773, -7680684652994691072000), (Sum.inr 2774, 4689897337119375360000), (Sum.inr 2777, -4714450911702024192000), (Sum.inr 2779, 1029413887898812416000), (Sum.inr 2780, -218973289450438656000), (Sum.inr 2781, -9759313319373176832000), (Sum.inr 2782, -28741157247379046400000), (Sum.inr 2783, -12330745384768634880000), (Sum.inr 2789, -13743886838351265792000), (Sum.inr 2797, 10817029381629542400000), (Sum.inr 2798, -6752922376232632320000), (Sum.inr 2800, -3995973679581757440000), (Sum.inr 2801, -1340821167243264000000), (Sum.inr 2802, 4806257162718412800000), (Sum.inr 2803, 7655273626113146880000), (Sum.inr 2806, 416003421044736000000), (Sum.inr 2807, 9566869889386414080000), (Sum.inr 2809, -1653558743737958400000), (Sum.inr 2810, -2050187137963130880000), (Sum.inr 2811, -3435263414499409920000), (Sum.inr 2812, 7633541508433182720000), (Sum.inr 2813, -590178927323381760000), (Sum.inr 2814, -4479366205522575360000)]

def reducedMerge1436part2 : Integer.Sparse Master := [(Sum.inr 2815, 5011857085783080960000), (Sum.inr 2816, 999901708930252800000), (Sum.inr 2817, -7972461087479562240000), (Sum.inr 2818, -5777870711254548480000), (Sum.inr 2819, 8961285504761856000000), (Sum.inr 2820, 1274912738715893760000), (Sum.inr 2821, -2262212174315520000000), (Sum.inr 2824, -11618393320164556800000), (Sum.inr 2826, -10406241466564608000000), (Sum.inr 2827, 6238836832370688000000), (Sum.inr 2846, 2089015568665804800000), (Sum.inr 2847, 5660818630174310400000), (Sum.inr 2848, -5194848837860720640000), (Sum.inr 2861, -3445367674768588800000), (Sum.inr 2862, -3526248379837317120000), (Sum.inr 2864, 1340821167243264000000), (Sum.inr 2865, -21284105174522265600000), (Sum.inr 2867, -6729430235975516160000), (Sum.inr 2868, 3526248379837317120000), (Sum.inr 2878, 9976743826758696960000), (Sum.inr 2879, -416003421044736000000), (Sum.inr 2880, -1781271279310602240000), (Sum.inr 2881, 3469795674486865920000), (Sum.inr 2882, -9976743826758696960000), (Sum.inr 2884, 9212700734303109120000), (Sum.inr 2885, -3934716707045376000000), (Sum.inr 2886, 3435263414499409920000), (Sum.inr 2888, 8305600448385515520000), (Sum.inr 2889, 2724268260332666880000), (Sum.inr 2890, 1355923199361024000000), (Sum.inr 2892, 6564939594419404800000), (Sum.inr 2893, -1057001205647278080000), (Sum.inr 2895, -5105263763930480640000), (Sum.inr 2896, 3946875325262069760000), (Sum.inr 2898, -5660818630174310400000), (Sum.inr 2899, -9762840630358179840000), (Sum.inr 2900, 16607243005555507200000), (Sum.inr 2902, 13705060285808640000000), (Sum.inr 2916, -2757638739876249600000), (Sum.inr 2923, -359649951169904640000), (Sum.inr 2924, 19302033754623836160000), (Sum.inr 2925, 6891745041155358720000), (Sum.inr 2928, 20635690283060428800000), (Sum.inr 2930, 6436794359666442240000), (Sum.inr 2931, 829623023566848000000), (Sum.inr 2933, -16476867997522329600000), (Sum.inr 2942, -8398043666546688000000), (Sum.inr 2951, 33959038618062028800000), (Sum.inr 2952, -571357054756454400000), (Sum.inr 2954, -8958732411045150720000), (Sum.inr 2955, -39828535728449126400000), (Sum.inr 2964, -12088519805730816000000), (Sum.inr 2967, -15967457567244288000000), (Sum.inr 2979, -421979070165811200000), (Sum.inr 2981, 669848715789926400000), (Sum.inr 2984, 15200456282416742400000), (Sum.inr 3016, -4525925648641818624000), (Sum.inr 3023, -5814069266409062400000), (Sum.inr 3024, 1699294017721466880000), (Sum.inr 3025, -3657804786659229696000), (Sum.inr 3029, -12883500708986880000000), (Sum.inr 3030, -4222719607976755200000), (Sum.inr 3031, 4597326756229939200000), (Sum.inr 3032, 2216831132152627200000)]

def reducedMerge1436part3 : Integer.Sparse Master := [(Sum.inr 3033, -4250125755517501440000), (Sum.inr 3036, 3735836684119572480000), (Sum.inr 3037, -12943331682486976512000), (Sum.inr 3038, 14492549870804533248000), (Sum.inr 3039, 9313996009718808576000), (Sum.inr 3040, 919241958555648000000), (Sum.inr 3043, -2589617639009157120000), (Sum.inr 3044, -16300334708112752640000), (Sum.inr 3045, 4564186441588408320000), (Sum.inr 3046, 3365072991753338880000), (Sum.inr 3050, -4404201698619555840000), (Sum.inr 3051, 3906032471591878656000), (Sum.inr 3052, 7967955760767959040000), (Sum.inr 3053, -4769146164905902080000), (Sum.inr 3054, -6384294458848051200000), (Sum.inr 3055, 16753008632221532160000), (Sum.inr 3056, -4052239562185113600000), (Sum.inr 3058, 259351328607436800000), (Sum.inr 3059, -1852188959337873408000), (Sum.inr 3062, -4597326756229939200000), (Sum.inr 3064, 7350751094580117504000), (Sum.inr 3066, -5639933671031439360000), (Sum.inr 3068, -8048462097973248000000), (Sum.inr 3069, 1668709084299264000000), (Sum.inr 3073, 4020809998518190080000), (Sum.inr 3074, 15546685904170057728000), (Sum.inr 3075, -1716666600863563776000), (Sum.inr 3077, -16333431861191639040000), (Sum.inr 3078, 18561918376033320960000), (Sum.inr 3079, -12298111992747786240000), (Sum.inr 3083, -1415934024744960000000), (Sum.inr 3084, -50941984034146222080000), (Sum.inr 3086, -22351245374360125440000), (Sum.inr 3092, -3891082594516992000000), (Sum.inr 3096, -10769461456860610560000), (Sum.inr 3097, 23327342262493839360000), (Sum.inr 3098, 34405213211462467584000), (Sum.inr 3108, 12622627890148147200000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000)]

def reducedMerge1436part4 : Integer.Sparse Master := [(Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000), (Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000), (Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000)]

def reducedMerge1436part5 : Integer.Sparse Master := [(Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000), (Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000), (Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000)]

def reducedMerge1436 : Integer.Sparse Master := ((reducedMerge1436part0 ++ (reducedMerge1436part1 ++ reducedMerge1436part2)) ++ ((reducedMerge1436part3 ++ reducedMerge1436part4) ++ (reducedMerge1436part5 ++ reducedMerge1436part6)))

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1915 : Integer.Sparse Master := ((reducedMerge1915part0 ++ (reducedMerge1915part1 ++ reducedMerge1915part2)) ++ ((reducedMerge1915part3 ++ reducedMerge1915part4) ++ (reducedMerge1915part5 ++ reducedMerge1915part6)))

def reducedMerge1916 : Integer.Sparse Master := (((reducedMerge1916part0 ++ (reducedMerge1916part1 ++ reducedMerge1916part2)) ++ ((reducedMerge1916part3 ++ reducedMerge1916part4) ++ (reducedMerge1916part5 ++ reducedMerge1916part6))) ++ ((reducedMerge1916part7 ++ (reducedMerge1916part8 ++ reducedMerge1916part9)) ++ ((reducedMerge1916part10 ++ reducedMerge1916part11) ++ (reducedMerge1916part12 ++ reducedMerge1916part13))))

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


