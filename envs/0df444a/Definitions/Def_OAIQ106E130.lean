-- Prove2me | Definitions.Def_OAIQ106E130
-- name    : OAIQ106E130
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:17:59.238789+00:00
-- url     : https://prove2.me/theorems/f4b94f73-dea2-4134-99ab-91b8f87fd68e
-- title:
--   Definitions bundle OAIQ106E130 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5990 declarations of OpenAI's Lean: 5990 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk0`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk1`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk10`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk11`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk12`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk13`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk14`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk15`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk16`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk17`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk18`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk19`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk2`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk20`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk21`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk22`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk23`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk24`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk25`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk26`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk27`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk28`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk29`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk3`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk30`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk31`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk32`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk33`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk34`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk35`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk36`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk37`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk38`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk39`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk4`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk40`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk41`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk42`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk43`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunk44` and 5950 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedTargets_KeyTable`, `MutuallyUnbiased_MixedTargets_Keys0`, `MutuallyUnbiased_MixedTargets_Keys1`, `MutuallyUnbiased_MixedTargets_Keys10`, `MutuallyUnbiased_MixedTargets_Keys11`, `MutuallyUnbiased_MixedTargets_Keys12`, `MutuallyUnbiased_MixedTargets_Keys13`, `MutuallyUnbiased_MixedTargets_Keys14`, `MutuallyUnbiased_MixedTargets_Keys15`, `MutuallyUnbiased_MixedTargets_Keys16`, `MutuallyUnbiased_MixedTargets_Keys17`, `MutuallyUnbiased_MixedTargets_Keys18`, `MutuallyUnbiased_MixedTargets_Keys19`, `MutuallyUnbiased_MixedTargets_Keys2`, `MutuallyUnbiased_MixedTargets_Keys20`, `MutuallyUnbiased_MixedTargets_Keys21`, `MutuallyUnbiased_MixedTargets_Keys22`, `MutuallyUnbiased_MixedTargets_Keys23`, `MutuallyUnbiased_MixedTargets_Keys24`, `MutuallyUnbiased_MixedTargets_Keys25`, `MutuallyUnbiased_MixedTargets_Keys26`, `MutuallyUnbiased_MixedTargets_Keys27`, `MutuallyUnbiased_MixedTargets_Keys28`, `MutuallyUnbiased_MixedTargets_Keys29`, `MutuallyUnbiased_MixedTargets_Keys3`, `MutuallyUnbiased_MixedTargets_Keys30`, `MutuallyUnbiased_MixedTargets_Keys31`, `MutuallyUnbiased_MixedTargets_Keys32`, `MutuallyUnbiased_MixedTargets_Keys33`, `MutuallyUnbiased_MixedTargets_Keys34`, `MutuallyUnbiased_MixedTargets_Keys35`, `MutuallyUnbiased_MixedTargets_Keys36`, `MutuallyUnbiased_MixedTargets_Keys37`, `MutuallyUnbiased_MixedTargets_Keys38`, `MutuallyUnbiased_MixedTargets_Keys39`, `MutuallyUnbiased_MixedTargets_Keys4`, `MutuallyUnbiased_MixedTargets_Keys40`, `MutuallyUnbiased_MixedTargets_Keys41`, `MutuallyUnbiased_MixedTargets_Keys42`, `MutuallyUnbiased_MixedTargets_Keys43`, `MutuallyUnbiased_MixedTargets_Keys44`, `MutuallyUnbiased_MixedTargets_Keys45`, `MutuallyUnbiased_MixedTargets_Keys46`, `MutuallyUnbiased_MixedTargets_Keys47`, `MutuallyUnbiased_MixedTargets_Keys48`, `MutuallyUnbiased_MixedTargets_Keys49`, `MutuallyUnbiased_MixedTargets_Keys5`, `MutuallyUnbiased_MixedTargets_Keys50`, `MutuallyUnbiased_MixedTargets_Keys51`, `MutuallyUnbiased_MixedTargets_Keys52`, `MutuallyUnbiased_MixedTargets_Keys53`, `MutuallyUnbiased_MixedTargets_Keys54`, `MutuallyUnbiased_MixedTargets_Keys55`, `MutuallyUnbiased_MixedTargets_Keys56`, `MutuallyUnbiased_MixedTargets_Keys57`, `MutuallyUnbiased_MixedTargets_Keys58`, `MutuallyUnbiased_MixedTargets_Keys59`, `MutuallyUnbiased_MixedTargets_Keys6`, `MutuallyUnbiased_MixedTargets_Keys60`, `MutuallyUnbiased_MixedTargets_Keys61`, `MutuallyUnbiased_MixedTargets_Keys62`, `MutuallyUnbiased_MixedTargets_Keys63`, `MutuallyUnbiased_MixedTargets_Keys64`, `MutuallyUnbiased_MixedTargets_Keys65`, `MutuallyUnbiased_MixedTargets_Keys66`, `MutuallyUnbiased_MixedTargets_Keys67`, `MutuallyUnbiased_MixedTargets_Keys68`, `MutuallyUnbiased_MixedTargets_Keys69`, `MutuallyUnbiased_MixedTargets_Keys7`, `MutuallyUnbiased_MixedTargets_Keys70`, `MutuallyUnbiased_MixedTargets_Keys71`, `MutuallyUnbiased_MixedTargets_Keys72`, `MutuallyUnbiased_MixedTargets_Keys73`, `MutuallyUnbiased_MixedTargets_Keys74`, `MutuallyUnbiased_MixedTargets_Keys75`, `MutuallyUnbiased_MixedTargets_Keys76`, `MutuallyUnbiased_MixedTargets_Keys77`, `MutuallyUnbiased_MixedTargets_Keys78`, `MutuallyUnbiased_MixedTargets_Keys79`, `MutuallyUnbiased_MixedTargets_Keys8`, `MutuallyUnbiased_MixedTargets_Keys80`, `MutuallyUnbiased_MixedTargets_Keys81`, `MutuallyUnbiased_MixedTargets_Keys82`, `MutuallyUnbiased_MixedTargets_Keys83`, `MutuallyUnbiased_MixedTargets_Keys84`, `MutuallyUnbiased_MixedTargets_Keys85`, `MutuallyUnbiased_MixedTargets_Keys86`, `MutuallyUnbiased_MixedTargets_Keys87`, `MutuallyUnbiased_MixedTargets_Keys88`, `MutuallyUnbiased_MixedTargets_Keys89`, `MutuallyUnbiased_MixedTargets_Keys9`, `MutuallyUnbiased_MixedTargets_Keys90`, `MutuallyUnbiased_MixedTargets_OriginalBlock0`, `MutuallyUnbiased_MixedTargets_OriginalBlock1`, `MutuallyUnbiased_MixedTargets_OriginalBlock10`, `MutuallyUnbiased_MixedTargets_OriginalBlock11`, `MutuallyUnbiased_MixedTargets_OriginalBlock12`, `MutuallyUnbiased_MixedTargets_OriginalBlock13`, `MutuallyUnbiased_MixedTargets_OriginalBlock14`, `MutuallyUnbiased_MixedTargets_OriginalBlock15`, `MutuallyUnbiased_MixedTargets_OriginalBlock16`, `MutuallyUnbiased_MixedTargets_OriginalBlock17`, `MutuallyUnbiased_MixedTargets_OriginalBlock18`, `MutuallyUnbiased_MixedTargets_OriginalBlock19`, `MutuallyUnbiased_MixedTargets_OriginalBlock2`, `MutuallyUnbiased_MixedTargets_OriginalBlock20`, `MutuallyUnbiased_MixedTargets_OriginalBlock21`, `MutuallyUnbiased_MixedTargets_OriginalBlock22`, `MutuallyUnbiased_MixedTargets_OriginalBlock23`, `MutuallyUnbiased_MixedTargets_OriginalBlock24`, `MutuallyUnbiased_MixedTargets_OriginalBlock25`, `MutuallyUnbiased_MixedTargets_OriginalBlock26`, `MutuallyUnbiased_MixedTargets_OriginalBlock27`, `MutuallyUnbiased_MixedTargets_OriginalBlock28`, `MutuallyUnbiased_MixedTargets_OriginalBlock29`, `MutuallyUnbiased_MixedTargets_OriginalBlock3`, `MutuallyUnbiased_MixedTargets_OriginalBlock30`, `MutuallyUnbiased_MixedTargets_OriginalBlock31`, `MutuallyUnbiased_MixedTargets_OriginalBlock32`, `MutuallyUnbiased_MixedTargets_OriginalBlock33`, `MutuallyUnbiased_MixedTargets_OriginalBlock34`, `MutuallyUnbiased_MixedTargets_OriginalBlock35`, `MutuallyUnbiased_MixedTargets_OriginalBlock36`, `MutuallyUnbiased_MixedTargets_OriginalBlock37`, `MutuallyUnbiased_MixedTargets_OriginalBlock38`, `MutuallyUnbiased_MixedTargets_OriginalBlock39`, `MutuallyUnbiased_MixedTargets_OriginalBlock4`, `MutuallyUnbiased_MixedTargets_OriginalBlock40`, `MutuallyUnbiased_MixedTargets_OriginalBlock41`, `MutuallyUnbiased_MixedTargets_OriginalBlock42`, `MutuallyUnbiased_MixedTargets_OriginalBlock43`, `MutuallyUnbiased_MixedTargets_OriginalBlock44`, `MutuallyUnbiased_MixedTargets_OriginalBlock45`, `MutuallyUnbiased_MixedTargets_OriginalBlock46`, `MutuallyUnbiased_MixedTargets_OriginalBlock47`, `MutuallyUnbiased_MixedTargets_OriginalBlock48`, `MutuallyUnbiased_MixedTargets_OriginalBlock49`, `MutuallyUnbiased_MixedTargets_OriginalBlock5`, `MutuallyUnbiased_MixedTargets_OriginalBlock50`, `MutuallyUnbiased_MixedTargets_OriginalBlock51`, `MutuallyUnbiased_MixedTargets_OriginalBlock52`, `MutuallyUnbiased_MixedTargets_OriginalBlock53`, `MutuallyUnbiased_MixedTargets_OriginalBlock54`, `MutuallyUnbiased_MixedTargets_OriginalBlock55`, `MutuallyUnbiased_MixedTargets_OriginalBlock56`, `MutuallyUnbiased_MixedTargets_OriginalBlock57`, `MutuallyUnbiased_MixedTargets_OriginalBlock58`, `MutuallyUnbiased_MixedTargets_OriginalBlock59`, `MutuallyUnbiased_MixedTargets_OriginalBlock6`, `MutuallyUnbiased_MixedTargets_OriginalBlock60`, `MutuallyUnbiased_MixedTargets_OriginalBlock61`, `MutuallyUnbiased_MixedTargets_OriginalBlock62`, `MutuallyUnbiased_MixedTargets_OriginalBlock63`, `MutuallyUnbiased_MixedTargets_OriginalBlock64`, `MutuallyUnbiased_MixedTargets_OriginalBlock65`, `MutuallyUnbiased_MixedTargets_OriginalBlock66`, `MutuallyUnbiased_MixedTargets_OriginalBlock67`, `MutuallyUnbiased_MixedTargets_OriginalBlock68`, `MutuallyUnbiased_MixedTargets_OriginalBlock69`, `MutuallyUnbiased_MixedTargets_OriginalBlock7`, `MutuallyUnbiased_MixedTargets_OriginalBlock70`, `MutuallyUnbiased_MixedTargets_OriginalBlock71`, `MutuallyUnbiased_MixedTargets_OriginalBlock72`, `MutuallyUnbiased_MixedTargets_OriginalBlock73`, `MutuallyUnbiased_MixedTargets_OriginalBlock74`, `MutuallyUnbiased_MixedTargets_OriginalBlock75`, `MutuallyUnbiased_MixedTargets_OriginalBlock76`, `MutuallyUnbiased_MixedTargets_OriginalBlock77`, `MutuallyUnbiased_MixedTargets_OriginalBlock78`, `MutuallyUnbiased_MixedTargets_OriginalBlock79`, `MutuallyUnbiased_MixedTargets_OriginalBlock8`, `MutuallyUnbiased_MixedTargets_OriginalBlock80`, `MutuallyUnbiased_MixedTargets_OriginalBlock81`, `MutuallyUnbiased_MixedTargets_OriginalBlock82`, `MutuallyUnbiased_MixedTargets_OriginalBlock83`, `MutuallyUnbiased_MixedTargets_OriginalBlock84`, `MutuallyUnbiased_MixedTargets_OriginalBlock85`, `MutuallyUnbiased_MixedTargets_OriginalBlock86`, `MutuallyUnbiased_MixedTargets_OriginalBlock87`, `MutuallyUnbiased_MixedTargets_OriginalBlock88`, `MutuallyUnbiased_MixedTargets_OriginalBlock89`, `MutuallyUnbiased_MixedTargets_OriginalBlock9`, `MutuallyUnbiased_MixedTargets_OriginalBlock90`, `MutuallyUnbiased_MixedTargets_ReductionData0`, `MutuallyUnbiased_MixedTargets_ReductionData1`, `MutuallyUnbiased_MixedTargets_ReductionData10`, `MutuallyUnbiased_MixedTargets_ReductionData11`, `MutuallyUnbiased_MixedTargets_ReductionData12`, `MutuallyUnbiased_MixedTargets_ReductionData13`, `MutuallyUnbiased_MixedTargets_ReductionData14`, `MutuallyUnbiased_MixedTargets_ReductionData15`, `MutuallyUnbiased_MixedTargets_ReductionData2`, `MutuallyUnbiased_MixedTargets_ReductionData29`, `MutuallyUnbiased_MixedTargets_ReductionData3`, `MutuallyUnbiased_MixedTargets_ReductionData30`, `MutuallyUnbiased_MixedTargets_ReductionData31`, `MutuallyUnbiased_MixedTargets_ReductionData32`, `MutuallyUnbiased_MixedTargets_ReductionData33`, `MutuallyUnbiased_MixedTargets_ReductionData34`, `MutuallyUnbiased_MixedTargets_ReductionData35`, `MutuallyUnbiased_MixedTargets_ReductionData36`, `MutuallyUnbiased_MixedTargets_ReductionData37`, `MutuallyUnbiased_MixedTargets_ReductionData38`, `MutuallyUnbiased_MixedTargets_ReductionData39`, `MutuallyUnbiased_MixedTargets_ReductionData4`, `MutuallyUnbiased_MixedTargets_ReductionData40`, `MutuallyUnbiased_MixedTargets_ReductionData41`, `MutuallyUnbiased_MixedTargets_ReductionData42`, `MutuallyUnbiased_MixedTargets_ReductionData43`, `MutuallyUnbiased_MixedTargets_ReductionData44`, `MutuallyUnbiased_MixedTargets_ReductionData45`, `MutuallyUnbiased_MixedTargets_ReductionData46`, `MutuallyUnbiased_MixedTargets_ReductionData47`, `MutuallyUnbiased_MixedTargets_ReductionData48`, `MutuallyUnbiased_MixedTargets_ReductionData49`, `MutuallyUnbiased_MixedTargets_ReductionData5`, `MutuallyUnbiased_MixedTargets_ReductionData50`, `MutuallyUnbiased_MixedTargets_ReductionData51`, `MutuallyUnbiased_MixedTargets_ReductionData52`, `MutuallyUnbiased_MixedTargets_ReductionData53`, `MutuallyUnbiased_MixedTargets_ReductionData54`, `MutuallyUnbiased_MixedTargets_ReductionData55`, `MutuallyUnbiased_MixedTargets_ReductionData56`, `MutuallyUnbiased_MixedTargets_ReductionData57`, `MutuallyUnbiased_MixedTargets_ReductionData58`, `MutuallyUnbiased_MixedTargets_ReductionData59`, `MutuallyUnbiased_MixedTargets_ReductionData6`, `MutuallyUnbiased_MixedTargets_ReductionData7`, `MutuallyUnbiased_MixedTargets_ReductionData8`, `MutuallyUnbiased_MixedTargets_ReductionData9`, `MutuallyUnbiased_MixedTargets_ReductionMergeData0`, `MutuallyUnbiased_MixedTargets_ReductionMergeData1`, `MutuallyUnbiased_MixedTargets_ReductionMergeData10`, `MutuallyUnbiased_MixedTargets_ReductionMergeData11`, `MutuallyUnbiased_MixedTargets_ReductionMergeData12`, `MutuallyUnbiased_MixedTargets_ReductionMergeData13`, `MutuallyUnbiased_MixedTargets_ReductionMergeData14`, `MutuallyUnbiased_MixedTargets_ReductionMergeData15`, `MutuallyUnbiased_MixedTargets_ReductionMergeData2`, `MutuallyUnbiased_MixedTargets_ReductionMergeData29`, `MutuallyUnbiased_MixedTargets_ReductionMergeData3`, `MutuallyUnbiased_MixedTargets_ReductionMergeData30`, `MutuallyUnbiased_MixedTargets_ReductionMergeData31`, `MutuallyUnbiased_MixedTargets_ReductionMergeData32`, `MutuallyUnbiased_MixedTargets_ReductionMergeData33`, `MutuallyUnbiased_MixedTargets_ReductionMergeData34`, `MutuallyUnbiased_MixedTargets_ReductionMergeData35`, `MutuallyUnbiased_MixedTargets_ReductionMergeData36`, `MutuallyUnbiased_MixedTargets_ReductionMergeData37`, `MutuallyUnbiased_MixedTargets_ReductionMergeData38`, `MutuallyUnbiased_MixedTargets_ReductionMergeData39`, `MutuallyUnbiased_MixedTargets_ReductionMergeData4`, `MutuallyUnbiased_MixedTargets_ReductionMergeData40`, `MutuallyUnbiased_MixedTargets_ReductionMergeData41`, `MutuallyUnbiased_MixedTargets_ReductionMergeData42`, `MutuallyUnbiased_MixedTargets_ReductionMergeData43`, `MutuallyUnbiased_MixedTargets_ReductionMergeData44`, `MutuallyUnbiased_MixedTargets_ReductionMergeData45`, `MutuallyUnbiased_MixedTargets_ReductionMergeData46`, `MutuallyUnbiased_MixedTargets_ReductionMergeData47`, `MutuallyUnbiased_MixedTargets_ReductionMergeData48`, `MutuallyUnbiased_MixedTargets_ReductionMergeData49`, `MutuallyUnbiased_MixedTargets_ReductionMergeData5`, `MutuallyUnbiased_MixedTargets_ReductionMergeData50`, `MutuallyUnbiased_MixedTargets_ReductionMergeData51`, `MutuallyUnbiased_MixedTargets_ReductionMergeData52`, `MutuallyUnbiased_MixedTargets_ReductionMergeData53`, `MutuallyUnbiased_MixedTargets_ReductionMergeData54`, `MutuallyUnbiased_MixedTargets_ReductionMergeData55`, `MutuallyUnbiased_MixedTargets_ReductionMergeData56`, `MutuallyUnbiased_MixedTargets_ReductionMergeData57`, `MutuallyUnbiased_MixedTargets_ReductionMergeData58`, `MutuallyUnbiased_MixedTargets_ReductionMergeData59`, `MutuallyUnbiased_MixedTargets_ReductionMergeData6`, `MutuallyUnbiased_MixedTargets_ReductionMergeData7`, `MutuallyUnbiased_MixedTargets_ReductionMergeData8`, `MutuallyUnbiased_MixedTargets_ReductionMergeData9`.
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E105` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E136`; the statements `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1675_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`; the proofs of `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1675_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e` and `OAI.MUB6.family_size_le_five_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E105

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow0 : Integer.Sparse OriginalKey := [(Sum.inl 2, 5)]

def keyMomentRow1 : Integer.Sparse OriginalKey := [(Sum.inl 1, 5)]

def keyMomentRow2 : Integer.Sparse OriginalKey := [(Sum.inl 272, 5)]

def keyMomentRow3 : Integer.Sparse OriginalKey := [(Sum.inl 270, 5)]

def keyMomentRow4 : Integer.Sparse OriginalKey := [(Sum.inl 266, 5)]

def keyMomentRow5 : Integer.Sparse OriginalKey := [(Sum.inl 267, 5)]

def keyMomentRow6 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow7 : Integer.Sparse OriginalKey := [(Sum.inl 269, 5)]

def keyMomentRow8 : Integer.Sparse OriginalKey := [(Sum.inl 267, 5)]

def keyMomentRow9 : Integer.Sparse OriginalKey := [(Sum.inl 0, 5)]

def keyMomentRow10 : Integer.Sparse OriginalKey := [(Sum.inl 261, 5)]

def keyMomentRow11 : Integer.Sparse OriginalKey := [(Sum.inl 265, 5)]

def keyMomentRow12 : Integer.Sparse OriginalKey := [(Sum.inl 261, 5)]

def keyMomentRow13 : Integer.Sparse OriginalKey := [(Sum.inl 259, 5)]

def keyMomentRow14 : Integer.Sparse OriginalKey := [(Sum.inr 0, 5)]

def keyMomentRow15 : Integer.Sparse OriginalKey := [(Sum.inl 388, 5)]

def keyMomentRow16 : Integer.Sparse OriginalKey := [(Sum.inl 389, 5)]

def keyMomentRow17 : Integer.Sparse OriginalKey := [(Sum.inl 391, 5)]

def keyMomentRow18 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow19 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow20 : Integer.Sparse OriginalKey := [(Sum.inl 386, 5)]

def keyMomentRow21 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow22 : Integer.Sparse OriginalKey := [(Sum.inl 375, 5)]

def keyMomentRow23 : Integer.Sparse OriginalKey := [(Sum.inl 382, 5)]

def keyMomentRow24 : Integer.Sparse OriginalKey := [(Sum.inl 415, 5)]

def keyMomentRow25 : Integer.Sparse OriginalKey := [(Sum.inl 419, 5)]

def keyMomentRow26 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow27 : Integer.Sparse OriginalKey := [(Sum.inl 421, 5)]

def keyMomentRow28 : Integer.Sparse OriginalKey := [(Sum.inl 402, 5)]

def keyMomentRow29 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow30 : Integer.Sparse OriginalKey := [(Sum.inl 391, 5)]

def keyMomentRow31 : Integer.Sparse OriginalKey := [(Sum.inl 406, 5)]

def keyMomentChunk0 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow0, keyMomentRow1, keyMomentRow2, keyMomentRow3, keyMomentRow4, keyMomentRow5, keyMomentRow6, keyMomentRow7, keyMomentRow8, keyMomentRow9, keyMomentRow10, keyMomentRow11, keyMomentRow12, keyMomentRow13, keyMomentRow14, keyMomentRow15, keyMomentRow16, keyMomentRow17, keyMomentRow18, keyMomentRow19, keyMomentRow20, keyMomentRow21, keyMomentRow22, keyMomentRow23, keyMomentRow24, keyMomentRow25, keyMomentRow26, keyMomentRow27, keyMomentRow28, keyMomentRow29, keyMomentRow30, keyMomentRow31]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow32 : Integer.Sparse OriginalKey := [(Sum.inl 414, 5)]

def keyMomentRow33 : Integer.Sparse OriginalKey := [(Sum.inl 400, 5)]

def keyMomentRow34 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow35 : Integer.Sparse OriginalKey := [(Sum.inl 270, 5)]

def keyMomentRow36 : Integer.Sparse OriginalKey := [(Sum.inl 391, 5)]

def keyMomentRow37 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow38 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow39 : Integer.Sparse OriginalKey := [(Sum.inl 408, 5)]

def keyMomentRow40 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow41 : Integer.Sparse OriginalKey := [(Sum.inl 381, 5)]

def keyMomentRow42 : Integer.Sparse OriginalKey := [(Sum.inl 364, 5)]

def keyMomentRow43 : Integer.Sparse OriginalKey := [(Sum.inl 393, 5)]

def keyMomentRow44 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow45 : Integer.Sparse OriginalKey := [(Sum.inl 380, 5)]

def keyMomentRow46 : Integer.Sparse OriginalKey := [(Sum.inl 363, 5)]

def keyMomentRow47 : Integer.Sparse OriginalKey := [(Sum.inl 386, 5)]

def keyMomentRow48 : Integer.Sparse OriginalKey := [(Sum.inl 397, 5)]

def keyMomentRow49 : Integer.Sparse OriginalKey := [(Sum.inl 393, 5)]

def keyMomentRow50 : Integer.Sparse OriginalKey := [(Sum.inl 357, 5)]

def keyMomentRow51 : Integer.Sparse OriginalKey := [(Sum.inl 392, 5)]

def keyMomentRow52 : Integer.Sparse OriginalKey := [(Sum.inl 394, 5)]

def keyMomentRow53 : Integer.Sparse OriginalKey := [(Sum.inl 406, 5)]

def keyMomentRow54 : Integer.Sparse OriginalKey := [(Sum.inl 404, 5)]

def keyMomentRow55 : Integer.Sparse OriginalKey := [(Sum.inl 342, 5)]

def keyMomentRow56 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow57 : Integer.Sparse OriginalKey := [(Sum.inl 324, 5)]

def keyMomentRow58 : Integer.Sparse OriginalKey := [(Sum.inl 399, 5)]

def keyMomentRow59 : Integer.Sparse OriginalKey := [(Sum.inl 400, 5)]

def keyMomentRow60 : Integer.Sparse OriginalKey := [(Sum.inl 403, 5)]

def keyMomentRow61 : Integer.Sparse OriginalKey := [(Sum.inl 376, 5)]

def keyMomentRow62 : Integer.Sparse OriginalKey := [(Sum.inl 359, 5)]

def keyMomentRow63 : Integer.Sparse OriginalKey := [(Sum.inl 421, 5)]

def keyMomentChunk1 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow32, keyMomentRow33, keyMomentRow34, keyMomentRow35, keyMomentRow36, keyMomentRow37, keyMomentRow38, keyMomentRow39, keyMomentRow40, keyMomentRow41, keyMomentRow42, keyMomentRow43, keyMomentRow44, keyMomentRow45, keyMomentRow46, keyMomentRow47, keyMomentRow48, keyMomentRow49, keyMomentRow50, keyMomentRow51, keyMomentRow52, keyMomentRow53, keyMomentRow54, keyMomentRow55, keyMomentRow56, keyMomentRow57, keyMomentRow58, keyMomentRow59, keyMomentRow60, keyMomentRow61, keyMomentRow62, keyMomentRow63]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow320 : Integer.Sparse OriginalKey := [(Sum.inl 415, 5)]

def keyMomentRow321 : Integer.Sparse OriginalKey := [(Sum.inl 416, 5)]

def keyMomentRow322 : Integer.Sparse OriginalKey := [(Sum.inl 152, 5)]

def keyMomentRow323 : Integer.Sparse OriginalKey := [(Sum.inl 414, 5)]

def keyMomentRow324 : Integer.Sparse OriginalKey := [(Sum.inl 402, 5)]

def keyMomentRow325 : Integer.Sparse OriginalKey := [(Sum.inl 247, 5)]

def keyMomentRow326 : Integer.Sparse OriginalKey := [(Sum.inl 270, 5)]

def keyMomentRow327 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow328 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow329 : Integer.Sparse OriginalKey := [(Sum.inl 366, 5)]

def keyMomentRow330 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow331 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow332 : Integer.Sparse OriginalKey := [(Sum.inl 365, 5)]

def keyMomentRow333 : Integer.Sparse OriginalKey := [(Sum.inl 364, 5)]

def keyMomentRow334 : Integer.Sparse OriginalKey := [(Sum.inl 363, 5)]

def keyMomentRow335 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow336 : Integer.Sparse OriginalKey := [(Sum.inl 383, 5)]

def keyMomentRow337 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow338 : Integer.Sparse OriginalKey := [(Sum.inl 498, 5)]

def keyMomentRow339 : Integer.Sparse OriginalKey := [(Sum.inl 365, 5)]

def keyMomentRow340 : Integer.Sparse OriginalKey := [(Sum.inl 480, 5)]

def keyMomentRow341 : Integer.Sparse OriginalKey := [(Sum.inl 475, 5)]

def keyMomentRow342 : Integer.Sparse OriginalKey := [(Sum.inl 443, 5)]

def keyMomentRow343 : Integer.Sparse OriginalKey := [(Sum.inl 497, 5)]

def keyMomentRow344 : Integer.Sparse OriginalKey := [(Sum.inl 499, 5)]

def keyMomentRow345 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow346 : Integer.Sparse OriginalKey := [(Sum.inl 503, 5)]

def keyMomentRow347 : Integer.Sparse OriginalKey := [(Sum.inl 501, 5)]

def keyMomentRow348 : Integer.Sparse OriginalKey := [(Sum.inl 354, 5)]

def keyMomentRow349 : Integer.Sparse OriginalKey := [(Sum.inl 491, 5)]

def keyMomentRow350 : Integer.Sparse OriginalKey := [(Sum.inl 487, 5)]

def keyMomentRow351 : Integer.Sparse OriginalKey := [(Sum.inl 348, 5)]

def keyMomentChunk10 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow320, keyMomentRow321, keyMomentRow322, keyMomentRow323, keyMomentRow324, keyMomentRow325, keyMomentRow326, keyMomentRow327, keyMomentRow328, keyMomentRow329, keyMomentRow330, keyMomentRow331, keyMomentRow332, keyMomentRow333, keyMomentRow334, keyMomentRow335, keyMomentRow336, keyMomentRow337, keyMomentRow338, keyMomentRow339, keyMomentRow340, keyMomentRow341, keyMomentRow342, keyMomentRow343, keyMomentRow344, keyMomentRow345, keyMomentRow346, keyMomentRow347, keyMomentRow348, keyMomentRow349, keyMomentRow350, keyMomentRow351]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow352 : Integer.Sparse OriginalKey := [(Sum.inl 346, 5)]

def keyMomentRow353 : Integer.Sparse OriginalKey := [(Sum.inl 476, 5)]

def keyMomentRow354 : Integer.Sparse OriginalKey := [(Sum.inl 484, 5)]

def keyMomentRow355 : Integer.Sparse OriginalKey := [(Sum.inl 269, 5)]

def keyMomentRow356 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow357 : Integer.Sparse OriginalKey := [(Sum.inl 468, 5)]

def keyMomentRow358 : Integer.Sparse OriginalKey := [(Sum.inl 491, 5)]

def keyMomentRow359 : Integer.Sparse OriginalKey := [(Sum.inl 364, 5)]

def keyMomentRow360 : Integer.Sparse OriginalKey := [(Sum.inl 481, 5)]

def keyMomentRow361 : Integer.Sparse OriginalKey := [(Sum.inl 443, 5)]

def keyMomentRow362 : Integer.Sparse OriginalKey := [(Sum.inl 440, 5)]

def keyMomentRow363 : Integer.Sparse OriginalKey := [(Sum.inl 480, 5)]

def keyMomentRow364 : Integer.Sparse OriginalKey := [(Sum.inl 492, 5)]

def keyMomentRow365 : Integer.Sparse OriginalKey := [(Sum.inl 489, 5)]

def keyMomentRow366 : Integer.Sparse OriginalKey := [(Sum.inl 478, 5)]

def keyMomentRow367 : Integer.Sparse OriginalKey := [(Sum.inl 391, 5)]

def keyMomentRow368 : Integer.Sparse OriginalKey := [(Sum.inl 148, 5)]

def keyMomentRow369 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow370 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow371 : Integer.Sparse OriginalKey := [(Sum.inl 145, 5)]

def keyMomentRow372 : Integer.Sparse OriginalKey := [(Sum.inl 139, 5)]

def keyMomentRow373 : Integer.Sparse OriginalKey := [(Sum.inl 322, 5)]

def keyMomentRow374 : Integer.Sparse OriginalKey := [(Sum.inl 373, 5)]

def keyMomentRow375 : Integer.Sparse OriginalKey := [(Sum.inl 264, 5)]

def keyMomentRow376 : Integer.Sparse OriginalKey := [(Sum.inl 263, 5)]

def keyMomentRow377 : Integer.Sparse OriginalKey := [(Sum.inl 246, 5)]

def keyMomentRow378 : Integer.Sparse OriginalKey := [(Sum.inl 177, 5)]

def keyMomentRow379 : Integer.Sparse OriginalKey := [(Sum.inl 238, 5)]

def keyMomentRow380 : Integer.Sparse OriginalKey := [(Sum.inl 165, 5)]

def keyMomentRow381 : Integer.Sparse OriginalKey := [(Sum.inl 263, 5)]

def keyMomentRow382 : Integer.Sparse OriginalKey := [(Sum.inl 463, 5)]

def keyMomentRow383 : Integer.Sparse OriginalKey := [(Sum.inl 458, 5)]

def keyMomentChunk11 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow352, keyMomentRow353, keyMomentRow354, keyMomentRow355, keyMomentRow356, keyMomentRow357, keyMomentRow358, keyMomentRow359, keyMomentRow360, keyMomentRow361, keyMomentRow362, keyMomentRow363, keyMomentRow364, keyMomentRow365, keyMomentRow366, keyMomentRow367, keyMomentRow368, keyMomentRow369, keyMomentRow370, keyMomentRow371, keyMomentRow372, keyMomentRow373, keyMomentRow374, keyMomentRow375, keyMomentRow376, keyMomentRow377, keyMomentRow378, keyMomentRow379, keyMomentRow380, keyMomentRow381, keyMomentRow382, keyMomentRow383]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow384 : Integer.Sparse OriginalKey := [(Sum.inl 356, 5)]

def keyMomentRow385 : Integer.Sparse OriginalKey := [(Sum.inl 398, 5)]

def keyMomentRow386 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow387 : Integer.Sparse OriginalKey := [(Sum.inl 446, 5)]

def keyMomentRow388 : Integer.Sparse OriginalKey := [(Sum.inl 288, 5)]

def keyMomentRow389 : Integer.Sparse OriginalKey := [(Sum.inl 434, 5)]

def keyMomentRow390 : Integer.Sparse OriginalKey := [(Sum.inl 280, 5)]

def keyMomentRow391 : Integer.Sparse OriginalKey := [(Sum.inl 278, 5)]

def keyMomentRow392 : Integer.Sparse OriginalKey := [(Sum.inl 313, 5)]

def keyMomentRow393 : Integer.Sparse OriginalKey := [(Sum.inl 123, 5)]

def keyMomentRow394 : Integer.Sparse OriginalKey := [(Sum.inr 6, 5)]

def keyMomentRow395 : Integer.Sparse OriginalKey := [(Sum.inl 114, 5)]

def keyMomentRow396 : Integer.Sparse OriginalKey := [(Sum.inl 29, 5)]

def keyMomentRow397 : Integer.Sparse OriginalKey := [(Sum.inl 101, 5)]

def keyMomentRow398 : Integer.Sparse OriginalKey := [(Sum.inl 142, 5)]

def keyMomentRow399 : Integer.Sparse OriginalKey := [(Sum.inl 27, 5)]

def keyMomentRow400 : Integer.Sparse OriginalKey := [(Sum.inl 12, 5)]

def keyMomentRow401 : Integer.Sparse OriginalKey := [(Sum.inl 10, 5)]

def keyMomentRow402 : Integer.Sparse OriginalKey := [(Sum.inl 229, 5)]

def keyMomentRow403 : Integer.Sparse OriginalKey := [(Sum.inl 240, 5)]

def keyMomentRow404 : Integer.Sparse OriginalKey := [(Sum.inl 184, 5)]

def keyMomentRow405 : Integer.Sparse OriginalKey := [(Sum.inl 167, 5)]

def keyMomentRow406 : Integer.Sparse OriginalKey := [(Sum.inl 434, 5)]

def keyMomentRow407 : Integer.Sparse OriginalKey := [(Sum.inl 427, 5)]

def keyMomentRow408 : Integer.Sparse OriginalKey := [(Sum.inl 435, 5)]

def keyMomentRow409 : Integer.Sparse OriginalKey := [(Sum.inl 432, 5)]

def keyMomentRow410 : Integer.Sparse OriginalKey := [(Sum.inl 282, 5)]

def keyMomentRow411 : Integer.Sparse OriginalKey := [(Sum.inl 426, 5)]

def keyMomentRow412 : Integer.Sparse OriginalKey := [(Sum.inl 428, 5)]

def keyMomentRow413 : Integer.Sparse OriginalKey := [(Sum.inl 429, 5)]

def keyMomentRow414 : Integer.Sparse OriginalKey := [(Sum.inl 309, 5)]

def keyMomentRow415 : Integer.Sparse OriginalKey := [(Sum.inl 325, 5)]

def keyMomentChunk12 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow384, keyMomentRow385, keyMomentRow386, keyMomentRow387, keyMomentRow388, keyMomentRow389, keyMomentRow390, keyMomentRow391, keyMomentRow392, keyMomentRow393, keyMomentRow394, keyMomentRow395, keyMomentRow396, keyMomentRow397, keyMomentRow398, keyMomentRow399, keyMomentRow400, keyMomentRow401, keyMomentRow402, keyMomentRow403, keyMomentRow404, keyMomentRow405, keyMomentRow406, keyMomentRow407, keyMomentRow408, keyMomentRow409, keyMomentRow410, keyMomentRow411, keyMomentRow412, keyMomentRow413, keyMomentRow414, keyMomentRow415]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow416 : Integer.Sparse OriginalKey := [(Sum.inl 130, 5)]

def keyMomentRow417 : Integer.Sparse OriginalKey := [(Sum.inl 296, 5)]

def keyMomentRow418 : Integer.Sparse OriginalKey := [(Sum.inl 300, 5)]

def keyMomentRow419 : Integer.Sparse OriginalKey := [(Sum.inl 103, 5)]

def keyMomentRow420 : Integer.Sparse OriginalKey := [(Sum.inl 149, 5)]

def keyMomentRow421 : Integer.Sparse OriginalKey := [(Sum.inl 36, 5)]

def keyMomentRow422 : Integer.Sparse OriginalKey := [(Sum.inl 15, 5)]

def keyMomentRow423 : Integer.Sparse OriginalKey := [(Sum.inl 168, 5)]

def keyMomentRow424 : Integer.Sparse OriginalKey := [(Sum.inl 278, 5)]

def keyMomentRow425 : Integer.Sparse OriginalKey := [(Sum.inl 279, 5)]

def keyMomentRow426 : Integer.Sparse OriginalKey := [(Sum.inl 116, 5)]

def keyMomentRow427 : Integer.Sparse OriginalKey := [(Sum.inl 17, 5)]

def keyMomentRow428 : Integer.Sparse OriginalKey := [(Sum.inl 270, 5)]

def keyMomentRow429 : Integer.Sparse OriginalKey := [(Sum.inl 269, 5)]

def keyMomentRow430 : Integer.Sparse OriginalKey := [(Sum.inl 251, 5)]

def keyMomentRow431 : Integer.Sparse OriginalKey := [(Sum.inl 185, 5)]

def keyMomentRow432 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow433 : Integer.Sparse OriginalKey := [(Sum.inl 248, 5)]

def keyMomentRow434 : Integer.Sparse OriginalKey := [(Sum.inl 182, 5)]

def keyMomentRow435 : Integer.Sparse OriginalKey := [(Sum.inl 235, 5)]

def keyMomentRow436 : Integer.Sparse OriginalKey := [(Sum.inl 261, 5)]

def keyMomentRow437 : Integer.Sparse OriginalKey := [(Sum.inl 173, 5)]

def keyMomentRow438 : Integer.Sparse OriginalKey := [(Sum.inl 179, 5)]

def keyMomentRow439 : Integer.Sparse OriginalKey := [(Sum.inl 223, 5)]

def keyMomentRow440 : Integer.Sparse OriginalKey := [(Sum.inl 209, 5)]

def keyMomentRow441 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow442 : Integer.Sparse OriginalKey := [(Sum.inl 468, 5)]

def keyMomentRow443 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow444 : Integer.Sparse OriginalKey := [(Sum.inl 439, 5)]

def keyMomentRow445 : Integer.Sparse OriginalKey := [(Sum.inl 455, 5)]

def keyMomentRow446 : Integer.Sparse OriginalKey := [(Sum.inl 171, 5)]

def keyMomentRow447 : Integer.Sparse OriginalKey := [(Sum.inl 507, 5)]

def keyMomentChunk13 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow416, keyMomentRow417, keyMomentRow418, keyMomentRow419, keyMomentRow420, keyMomentRow421, keyMomentRow422, keyMomentRow423, keyMomentRow424, keyMomentRow425, keyMomentRow426, keyMomentRow427, keyMomentRow428, keyMomentRow429, keyMomentRow430, keyMomentRow431, keyMomentRow432, keyMomentRow433, keyMomentRow434, keyMomentRow435, keyMomentRow436, keyMomentRow437, keyMomentRow438, keyMomentRow439, keyMomentRow440, keyMomentRow441, keyMomentRow442, keyMomentRow443, keyMomentRow444, keyMomentRow445, keyMomentRow446, keyMomentRow447]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow448 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow449 : Integer.Sparse OriginalKey := [(Sum.inl 451, 5)]

def keyMomentRow450 : Integer.Sparse OriginalKey := [(Sum.inl 369, 5)]

def keyMomentRow451 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow452 : Integer.Sparse OriginalKey := [(Sum.inl 505, 5)]

def keyMomentRow453 : Integer.Sparse OriginalKey := [(Sum.inl 449, 5)]

def keyMomentRow454 : Integer.Sparse OriginalKey := [(Sum.inl 286, 5)]

def keyMomentRow455 : Integer.Sparse OriginalKey := [(Sum.inl 438, 5)]

def keyMomentRow456 : Integer.Sparse OriginalKey := [(Sum.inl 490, 5)]

def keyMomentRow457 : Integer.Sparse OriginalKey := [(Sum.inl 432, 5)]

def keyMomentRow458 : Integer.Sparse OriginalKey := [(Sum.inl 449, 5)]

def keyMomentRow459 : Integer.Sparse OriginalKey := [(Sum.inl 178, 5)]

def keyMomentRow460 : Integer.Sparse OriginalKey := [(Sum.inl 424, 5)]

def keyMomentRow461 : Integer.Sparse OriginalKey := [(Sum.inl 492, 5)]

def keyMomentRow462 : Integer.Sparse OriginalKey := [(Sum.inl 179, 5)]

def keyMomentRow463 : Integer.Sparse OriginalKey := [(Sum.inl 505, 5)]

def keyMomentRow464 : Integer.Sparse OriginalKey := [(Sum.inl 449, 5)]

def keyMomentRow465 : Integer.Sparse OriginalKey := [(Sum.inl 180, 5)]

def keyMomentRow466 : Integer.Sparse OriginalKey := [(Sum.inl 471, 5)]

def keyMomentRow467 : Integer.Sparse OriginalKey := [(Sum.inl 317, 5)]

def keyMomentRow468 : Integer.Sparse OriginalKey := [(Sum.inl 448, 5)]

def keyMomentRow469 : Integer.Sparse OriginalKey := [(Sum.inl 343, 5)]

def keyMomentRow470 : Integer.Sparse OriginalKey := [(Sum.inl 316, 5)]

def keyMomentRow471 : Integer.Sparse OriginalKey := [(Sum.inl 335, 5)]

def keyMomentRow472 : Integer.Sparse OriginalKey := [(Sum.inl 127, 5)]

def keyMomentRow473 : Integer.Sparse OriginalKey := [(Sum.inl 314, 5)]

def keyMomentRow474 : Integer.Sparse OriginalKey := [(Sum.inl 306, 5)]

def keyMomentRow475 : Integer.Sparse OriginalKey := [(Sum.inl 450, 5)]

def keyMomentRow476 : Integer.Sparse OriginalKey := [(Sum.inl 175, 5)]

def keyMomentRow477 : Integer.Sparse OriginalKey := [(Sum.inl 295, 5)]

def keyMomentRow478 : Integer.Sparse OriginalKey := [(Sum.inl 160, 5)]

def keyMomentRow479 : Integer.Sparse OriginalKey := [(Sum.inl 38, 5)]

def keyMomentChunk14 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow448, keyMomentRow449, keyMomentRow450, keyMomentRow451, keyMomentRow452, keyMomentRow453, keyMomentRow454, keyMomentRow455, keyMomentRow456, keyMomentRow457, keyMomentRow458, keyMomentRow459, keyMomentRow460, keyMomentRow461, keyMomentRow462, keyMomentRow463, keyMomentRow464, keyMomentRow465, keyMomentRow466, keyMomentRow467, keyMomentRow468, keyMomentRow469, keyMomentRow470, keyMomentRow471, keyMomentRow472, keyMomentRow473, keyMomentRow474, keyMomentRow475, keyMomentRow476, keyMomentRow477, keyMomentRow478, keyMomentRow479]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow480 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow481 : Integer.Sparse OriginalKey := [(Sum.inl 33, 5)]

def keyMomentRow482 : Integer.Sparse OriginalKey := [(Sum.inl 111, 5)]

def keyMomentRow483 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow484 : Integer.Sparse OriginalKey := [(Sum.inl 98, 5)]

def keyMomentRow485 : Integer.Sparse OriginalKey := [(Sum.inl 343, 5)]

def keyMomentRow486 : Integer.Sparse OriginalKey := [(Sum.inl 452, 5)]

def keyMomentRow487 : Integer.Sparse OriginalKey := [(Sum.inl 71, 5)]

def keyMomentRow488 : Integer.Sparse OriginalKey := [(Sum.inl 186, 5)]

def keyMomentRow489 : Integer.Sparse OriginalKey := [(Sum.inl 95, 5)]

def keyMomentRow490 : Integer.Sparse OriginalKey := [(Sum.inl 339, 5)]

def keyMomentRow491 : Integer.Sparse OriginalKey := [(Sum.inl 68, 5)]

def keyMomentRow492 : Integer.Sparse OriginalKey := [(Sum.inl 275, 5)]

def keyMomentRow493 : Integer.Sparse OriginalKey := [(Sum.inl 65, 5)]

def keyMomentRow494 : Integer.Sparse OriginalKey := [(Sum.inl 406, 5)]

def keyMomentRow495 : Integer.Sparse OriginalKey := [(Sum.inl 354, 5)]

def keyMomentRow496 : Integer.Sparse OriginalKey := [(Sum.inl 328, 5)]

def keyMomentRow497 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow498 : Integer.Sparse OriginalKey := [(Sum.inl 348, 5)]

def keyMomentRow499 : Integer.Sparse OriginalKey := [(Sum.inl 347, 5)]

def keyMomentRow500 : Integer.Sparse OriginalKey := [(Sum.inl 394, 5)]

def keyMomentRow501 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow502 : Integer.Sparse OriginalKey := [(Sum.inl 402, 5)]

def keyMomentRow503 : Integer.Sparse OriginalKey := [(Sum.inl 350, 5)]

def keyMomentRow504 : Integer.Sparse OriginalKey := [(Sum.inl 349, 5)]

def keyMomentRow505 : Integer.Sparse OriginalKey := [(Sum.inl 395, 5)]

def keyMomentRow506 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow507 : Integer.Sparse OriginalKey := [(Sum.inl 346, 5)]

def keyMomentRow508 : Integer.Sparse OriginalKey := [(Sum.inl 345, 5)]

def keyMomentRow509 : Integer.Sparse OriginalKey := [(Sum.inl 373, 5)]

def keyMomentRow510 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow511 : Integer.Sparse OriginalKey := [(Sum.inl 385, 5)]

def keyMomentChunk15 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow480, keyMomentRow481, keyMomentRow482, keyMomentRow483, keyMomentRow484, keyMomentRow485, keyMomentRow486, keyMomentRow487, keyMomentRow488, keyMomentRow489, keyMomentRow490, keyMomentRow491, keyMomentRow492, keyMomentRow493, keyMomentRow494, keyMomentRow495, keyMomentRow496, keyMomentRow497, keyMomentRow498, keyMomentRow499, keyMomentRow500, keyMomentRow501, keyMomentRow502, keyMomentRow503, keyMomentRow504, keyMomentRow505, keyMomentRow506, keyMomentRow507, keyMomentRow508, keyMomentRow509, keyMomentRow510, keyMomentRow511]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow512 : Integer.Sparse OriginalKey := [(Sum.inl 379, 5)]

def keyMomentRow513 : Integer.Sparse OriginalKey := [(Sum.inl 147, 5)]

def keyMomentRow514 : Integer.Sparse OriginalKey := [(Sum.inl 323, 5)]

def keyMomentRow515 : Integer.Sparse OriginalKey := [(Sum.inl 374, 5)]

def keyMomentRow516 : Integer.Sparse OriginalKey := [(Sum.inr 1, 5)]

def keyMomentRow517 : Integer.Sparse OriginalKey := [(Sum.inl 239, 5)]

def keyMomentRow518 : Integer.Sparse OriginalKey := [(Sum.inl 176, 5)]

def keyMomentRow519 : Integer.Sparse OriginalKey := [(Sum.inl 164, 5)]

def keyMomentRow520 : Integer.Sparse OriginalKey := [(Sum.inr 6, 5)]

def keyMomentRow521 : Integer.Sparse OriginalKey := [(Sum.inl 297, 5)]

def keyMomentRow522 : Integer.Sparse OriginalKey := [(Sum.inl 309, 5)]

def keyMomentRow523 : Integer.Sparse OriginalKey := [(Sum.inl 306, 5)]

def keyMomentRow524 : Integer.Sparse OriginalKey := [(Sum.inl 281, 5)]

def keyMomentRow525 : Integer.Sparse OriginalKey := [(Sum.inl 298, 5)]

def keyMomentRow526 : Integer.Sparse OriginalKey := [(Sum.inl 300, 5)]

def keyMomentRow527 : Integer.Sparse OriginalKey := [(Sum.inl 301, 5)]

def keyMomentRow528 : Integer.Sparse OriginalKey := [(Sum.inl 308, 5)]

def keyMomentRow529 : Integer.Sparse OriginalKey := [(Sum.inl 303, 5)]

def keyMomentRow530 : Integer.Sparse OriginalKey := [(Sum.inl 122, 5)]

def keyMomentRow531 : Integer.Sparse OriginalKey := [(Sum.inl 292, 5)]

def keyMomentRow532 : Integer.Sparse OriginalKey := [(Sum.inl 299, 5)]

def keyMomentRow533 : Integer.Sparse OriginalKey := [(Sum.inr 2, 5)]

def keyMomentRow534 : Integer.Sparse OriginalKey := [(Sum.inl 146, 5)]

def keyMomentRow535 : Integer.Sparse OriginalKey := [(Sum.inl 11, 5)]

def keyMomentRow536 : Integer.Sparse OriginalKey := [(Sum.inl 169, 5)]

def keyMomentRow537 : Integer.Sparse OriginalKey := [(Sum.inl 18, 5)]

def keyMomentRow538 : Integer.Sparse OriginalKey := [(Sum.inl 270, 5)]

def keyMomentRow539 : Integer.Sparse OriginalKey := [(Sum.inl 249, 5)]

def keyMomentRow540 : Integer.Sparse OriginalKey := [(Sum.inl 187, 5)]

def keyMomentRow541 : Integer.Sparse OriginalKey := [(Sum.inl 236, 5)]

def keyMomentRow542 : Integer.Sparse OriginalKey := [(Sum.inl 262, 5)]

def keyMomentRow543 : Integer.Sparse OriginalKey := [(Sum.inl 180, 5)]

def keyMomentChunk16 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow512, keyMomentRow513, keyMomentRow514, keyMomentRow515, keyMomentRow516, keyMomentRow517, keyMomentRow518, keyMomentRow519, keyMomentRow520, keyMomentRow521, keyMomentRow522, keyMomentRow523, keyMomentRow524, keyMomentRow525, keyMomentRow526, keyMomentRow527, keyMomentRow528, keyMomentRow529, keyMomentRow530, keyMomentRow531, keyMomentRow532, keyMomentRow533, keyMomentRow534, keyMomentRow535, keyMomentRow536, keyMomentRow537, keyMomentRow538, keyMomentRow539, keyMomentRow540, keyMomentRow541, keyMomentRow542, keyMomentRow543]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow544 : Integer.Sparse OriginalKey := [(Sum.inl 224, 5)]

def keyMomentRow545 : Integer.Sparse OriginalKey := [(Sum.inl 211, 5)]

def keyMomentRow546 : Integer.Sparse OriginalKey := [(Sum.inl 207, 5)]

def keyMomentRow547 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow548 : Integer.Sparse OriginalKey := [(Sum.inl 286, 5)]

def keyMomentRow549 : Integer.Sparse OriginalKey := [(Sum.inl 353, 5)]

def keyMomentRow550 : Integer.Sparse OriginalKey := [(Sum.inl 290, 5)]

def keyMomentRow551 : Integer.Sparse OriginalKey := [(Sum.inl 355, 5)]

def keyMomentRow552 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow553 : Integer.Sparse OriginalKey := [(Sum.inl 339, 5)]

def keyMomentRow554 : Integer.Sparse OriginalKey := [(Sum.inl 351, 5)]

def keyMomentRow555 : Integer.Sparse OriginalKey := [(Sum.inl 352, 5)]

def keyMomentRow556 : Integer.Sparse OriginalKey := [(Sum.inl 334, 5)]

def keyMomentRow557 : Integer.Sparse OriginalKey := [(Sum.inl 283, 5)]

def keyMomentRow558 : Integer.Sparse OriginalKey := [(Sum.inl 133, 5)]

def keyMomentRow559 : Integer.Sparse OriginalKey := [(Sum.inl 336, 5)]

def keyMomentRow560 : Integer.Sparse OriginalKey := [(Sum.inl 287, 5)]

def keyMomentRow561 : Integer.Sparse OriginalKey := [(Sum.inl 40, 5)]

def keyMomentRow562 : Integer.Sparse OriginalKey := [(Sum.inl 112, 5)]

def keyMomentRow563 : Integer.Sparse OriginalKey := [(Sum.inl 407, 5)]

def keyMomentRow564 : Integer.Sparse OriginalKey := [(Sum.inl 96, 5)]

def keyMomentRow565 : Integer.Sparse OriginalKey := [(Sum.inl 341, 5)]

def keyMomentRow566 : Integer.Sparse OriginalKey := [(Sum.inl 344, 5)]

def keyMomentRow567 : Integer.Sparse OriginalKey := [(Sum.inl 72, 5)]

def keyMomentRow568 : Integer.Sparse OriginalKey := [(Sum.inl 66, 5)]

def keyMomentRow569 : Integer.Sparse OriginalKey := [(Sum.inl 148, 5)]

def keyMomentRow570 : Integer.Sparse OriginalKey := [(Sum.inl 145, 5)]

def keyMomentRow571 : Integer.Sparse OriginalKey := [(Sum.inl 147, 5)]

def keyMomentRow572 : Integer.Sparse OriginalKey := [(Sum.inl 139, 5)]

def keyMomentRow573 : Integer.Sparse OriginalKey := [(Sum.inl 140, 5)]

def keyMomentRow574 : Integer.Sparse OriginalKey := [(Sum.inl 117, 5)]

def keyMomentRow575 : Integer.Sparse OriginalKey := [(Sum.inl 114, 5)]

def keyMomentChunk17 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow544, keyMomentRow545, keyMomentRow546, keyMomentRow547, keyMomentRow548, keyMomentRow549, keyMomentRow550, keyMomentRow551, keyMomentRow552, keyMomentRow553, keyMomentRow554, keyMomentRow555, keyMomentRow556, keyMomentRow557, keyMomentRow558, keyMomentRow559, keyMomentRow560, keyMomentRow561, keyMomentRow562, keyMomentRow563, keyMomentRow564, keyMomentRow565, keyMomentRow566, keyMomentRow567, keyMomentRow568, keyMomentRow569, keyMomentRow570, keyMomentRow571, keyMomentRow572, keyMomentRow573, keyMomentRow574, keyMomentRow575]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow576 : Integer.Sparse OriginalKey := [(Sum.inl 116, 5)]

def keyMomentRow577 : Integer.Sparse OriginalKey := [(Sum.inl 115, 5)]

def keyMomentRow578 : Integer.Sparse OriginalKey := [(Sum.inl 13, 5)]

def keyMomentRow579 : Integer.Sparse OriginalKey := [(Sum.inl 131, 5)]

def keyMomentRow580 : Integer.Sparse OriginalKey := [(Sum.inl 143, 5)]

def keyMomentRow581 : Integer.Sparse OriginalKey := [(Sum.inl 119, 5)]

def keyMomentRow582 : Integer.Sparse OriginalKey := [(Sum.inl 127, 5)]

def keyMomentRow583 : Integer.Sparse OriginalKey := [(Sum.inl 142, 5)]

def keyMomentRow584 : Integer.Sparse OriginalKey := [(Sum.inl 118, 5)]

def keyMomentRow585 : Integer.Sparse OriginalKey := [(Sum.inl 160, 5)]

def keyMomentRow586 : Integer.Sparse OriginalKey := [(Sum.inl 133, 5)]

def keyMomentRow587 : Integer.Sparse OriginalKey := [(Sum.inl 149, 5)]

def keyMomentRow588 : Integer.Sparse OriginalKey := [(Sum.inl 124, 5)]

def keyMomentRow589 : Integer.Sparse OriginalKey := [(Sum.inl 125, 5)]

def keyMomentRow590 : Integer.Sparse OriginalKey := [(Sum.inl 126, 5)]

def keyMomentRow591 : Integer.Sparse OriginalKey := [(Sum.inl 158, 5)]

def keyMomentRow592 : Integer.Sparse OriginalKey := [(Sum.inl 129, 5)]

def keyMomentRow593 : Integer.Sparse OriginalKey := [(Sum.inl 146, 5)]

def keyMomentRow594 : Integer.Sparse OriginalKey := [(Sum.inl 121, 5)]

def keyMomentRow595 : Integer.Sparse OriginalKey := [(Sum.inl 162, 5)]

def keyMomentRow596 : Integer.Sparse OriginalKey := [(Sum.inl 35, 5)]

def keyMomentRow597 : Integer.Sparse OriginalKey := [(Sum.inl 100, 5)]

def keyMomentRow598 : Integer.Sparse OriginalKey := [(Sum.inl 70, 5)]

def keyMomentRow599 : Integer.Sparse OriginalKey := [(Sum.inl 132, 5)]

def keyMomentRow600 : Integer.Sparse OriginalKey := [(Sum.inl 38, 5)]

def keyMomentRow601 : Integer.Sparse OriginalKey := [(Sum.inl 33, 5)]

def keyMomentRow602 : Integer.Sparse OriginalKey := [(Sum.inl 40, 5)]

def keyMomentRow603 : Integer.Sparse OriginalKey := [(Sum.inl 22, 5)]

def keyMomentRow604 : Integer.Sparse OriginalKey := [(Sum.inl 26, 5)]

def keyMomentRow605 : Integer.Sparse OriginalKey := [(Sum.inl 34, 5)]

def keyMomentRow606 : Integer.Sparse OriginalKey := [(Sum.inl 42, 5)]

def keyMomentRow607 : Integer.Sparse OriginalKey := [(Sum.inl 397, 5)]

def keyMomentChunk18 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow576, keyMomentRow577, keyMomentRow578, keyMomentRow579, keyMomentRow580, keyMomentRow581, keyMomentRow582, keyMomentRow583, keyMomentRow584, keyMomentRow585, keyMomentRow586, keyMomentRow587, keyMomentRow588, keyMomentRow589, keyMomentRow590, keyMomentRow591, keyMomentRow592, keyMomentRow593, keyMomentRow594, keyMomentRow595, keyMomentRow596, keyMomentRow597, keyMomentRow598, keyMomentRow599, keyMomentRow600, keyMomentRow601, keyMomentRow602, keyMomentRow603, keyMomentRow604, keyMomentRow605, keyMomentRow606, keyMomentRow607]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow608 : Integer.Sparse OriginalKey := [(Sum.inl 395, 5)]

def keyMomentRow609 : Integer.Sparse OriginalKey := [(Sum.inl 394, 5)]

def keyMomentRow610 : Integer.Sparse OriginalKey := [(Sum.inl 358, 5)]

def keyMomentRow611 : Integer.Sparse OriginalKey := [(Sum.inl 357, 5)]

def keyMomentRow612 : Integer.Sparse OriginalKey := [(Sum.inl 400, 5)]

def keyMomentRow613 : Integer.Sparse OriginalKey := [(Sum.inl 362, 5)]

def keyMomentRow614 : Integer.Sparse OriginalKey := [(Sum.inl 359, 5)]

def keyMomentRow615 : Integer.Sparse OriginalKey := [(Sum.inl 404, 5)]

def keyMomentRow616 : Integer.Sparse OriginalKey := [(Sum.inl 401, 5)]

def keyMomentRow617 : Integer.Sparse OriginalKey := [(Sum.inl 361, 5)]

def keyMomentRow618 : Integer.Sparse OriginalKey := [(Sum.inl 378, 5)]

def keyMomentRow619 : Integer.Sparse OriginalKey := [(Sum.inl 403, 5)]

def keyMomentRow620 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow621 : Integer.Sparse OriginalKey := [(Sum.inl 360, 5)]

def keyMomentRow622 : Integer.Sparse OriginalKey := [(Sum.inl 376, 5)]

def keyMomentRow623 : Integer.Sparse OriginalKey := [(Sum.inl 367, 5)]

def keyMomentRow624 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow625 : Integer.Sparse OriginalKey := [(Sum.inl 414, 5)]

def keyMomentRow626 : Integer.Sparse OriginalKey := [(Sum.inl 369, 5)]

def keyMomentRow627 : Integer.Sparse OriginalKey := [(Sum.inl 390, 5)]

def keyMomentRow628 : Integer.Sparse OriginalKey := [(Sum.inl 416, 5)]

def keyMomentRow629 : Integer.Sparse OriginalKey := [(Sum.inl 368, 5)]

def keyMomentRow630 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow631 : Integer.Sparse OriginalKey := [(Sum.inl 371, 5)]

def keyMomentRow632 : Integer.Sparse OriginalKey := [(Sum.inl 415, 5)]

def keyMomentRow633 : Integer.Sparse OriginalKey := [(Sum.inl 316, 5)]

def keyMomentRow634 : Integer.Sparse OriginalKey := [(Sum.inl 388, 5)]

def keyMomentRow635 : Integer.Sparse OriginalKey := [(Sum.inl 113, 5)]

def keyMomentRow636 : Integer.Sparse OriginalKey := [(Sum.inr 4, 5)]

def keyMomentRow637 : Integer.Sparse OriginalKey := [(Sum.inl 489, 5)]

def keyMomentRow638 : Integer.Sparse OriginalKey := [(Sum.inl 521, 5)]

def keyMomentRow639 : Integer.Sparse OriginalKey := [(Sum.inl 518, 5)]

def keyMomentChunk19 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow608, keyMomentRow609, keyMomentRow610, keyMomentRow611, keyMomentRow612, keyMomentRow613, keyMomentRow614, keyMomentRow615, keyMomentRow616, keyMomentRow617, keyMomentRow618, keyMomentRow619, keyMomentRow620, keyMomentRow621, keyMomentRow622, keyMomentRow623, keyMomentRow624, keyMomentRow625, keyMomentRow626, keyMomentRow627, keyMomentRow628, keyMomentRow629, keyMomentRow630, keyMomentRow631, keyMomentRow632, keyMomentRow633, keyMomentRow634, keyMomentRow635, keyMomentRow636, keyMomentRow637, keyMomentRow638, keyMomentRow639]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow64 : Integer.Sparse OriginalKey := [(Sum.inl 159, 5)]

def keyMomentRow65 : Integer.Sparse OriginalKey := [(Sum.inl 388, 5)]

def keyMomentRow66 : Integer.Sparse OriginalKey := [(Sum.inl 148, 5)]

def keyMomentRow67 : Integer.Sparse OriginalKey := [(Sum.inl 342, 5)]

def keyMomentRow68 : Integer.Sparse OriginalKey := [(Sum.inl 406, 5)]

def keyMomentRow69 : Integer.Sparse OriginalKey := [(Sum.inl 413, 5)]

def keyMomentRow70 : Integer.Sparse OriginalKey := [(Sum.inl 416, 5)]

def keyMomentRow71 : Integer.Sparse OriginalKey := [(Sum.inl 340, 5)]

def keyMomentRow72 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow73 : Integer.Sparse OriginalKey := [(Sum.inl 328, 5)]

def keyMomentRow74 : Integer.Sparse OriginalKey := [(Sum.inl 367, 5)]

def keyMomentRow75 : Integer.Sparse OriginalKey := [(Sum.inl 271, 5)]

def keyMomentRow76 : Integer.Sparse OriginalKey := [(Sum.inl 264, 5)]

def keyMomentRow77 : Integer.Sparse OriginalKey := [(Sum.inl 250, 5)]

def keyMomentRow78 : Integer.Sparse OriginalKey := [(Sum.inl 188, 5)]

def keyMomentRow79 : Integer.Sparse OriginalKey := [(Sum.inl 228, 5)]

def keyMomentRow80 : Integer.Sparse OriginalKey := [(Sum.inl 225, 5)]

def keyMomentRow81 : Integer.Sparse OriginalKey := [(Sum.inl 181, 5)]

def keyMomentRow82 : Integer.Sparse OriginalKey := [(Sum.inl 170, 5)]

def keyMomentRow83 : Integer.Sparse OriginalKey := [(Sum.inl 194, 5)]

def keyMomentRow84 : Integer.Sparse OriginalKey := [(Sum.inl 225, 5)]

def keyMomentRow85 : Integer.Sparse OriginalKey := [(Sum.inl 258, 5)]

def keyMomentRow86 : Integer.Sparse OriginalKey := [(Sum.inl 166, 5)]

def keyMomentRow87 : Integer.Sparse OriginalKey := [(Sum.inl 208, 5)]

def keyMomentRow88 : Integer.Sparse OriginalKey := [(Sum.inl 218, 5)]

def keyMomentRow89 : Integer.Sparse OriginalKey := [(Sum.inl 166, 5)]

def keyMomentRow90 : Integer.Sparse OriginalKey := [(Sum.inl 264, 5)]

def keyMomentRow91 : Integer.Sparse OriginalKey := [(Sum.inl 263, 5)]

def keyMomentRow92 : Integer.Sparse OriginalKey := [(Sum.inl 246, 5)]

def keyMomentRow93 : Integer.Sparse OriginalKey := [(Sum.inl 193, 5)]

def keyMomentRow94 : Integer.Sparse OriginalKey := [(Sum.inl 165, 5)]

def keyMomentRow95 : Integer.Sparse OriginalKey := [(Sum.inl 191, 5)]

def keyMomentChunk2 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow64, keyMomentRow65, keyMomentRow66, keyMomentRow67, keyMomentRow68, keyMomentRow69, keyMomentRow70, keyMomentRow71, keyMomentRow72, keyMomentRow73, keyMomentRow74, keyMomentRow75, keyMomentRow76, keyMomentRow77, keyMomentRow78, keyMomentRow79, keyMomentRow80, keyMomentRow81, keyMomentRow82, keyMomentRow83, keyMomentRow84, keyMomentRow85, keyMomentRow86, keyMomentRow87, keyMomentRow88, keyMomentRow89, keyMomentRow90, keyMomentRow91, keyMomentRow92, keyMomentRow93, keyMomentRow94, keyMomentRow95]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow640 : Integer.Sparse OriginalKey := [(Sum.inl 479, 5)]

def keyMomentRow641 : Integer.Sparse OriginalKey := [(Sum.inr 5, 5)]

def keyMomentRow642 : Integer.Sparse OriginalKey := [(Sum.inl 528, 5)]

def keyMomentRow643 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow644 : Integer.Sparse OriginalKey := [(Sum.inl 502, 5)]

def keyMomentRow645 : Integer.Sparse OriginalKey := [(Sum.inl 514, 5)]

def keyMomentRow646 : Integer.Sparse OriginalKey := [(Sum.inl 483, 5)]

def keyMomentRow647 : Integer.Sparse OriginalKey := [(Sum.inl 438, 5)]

def keyMomentRow648 : Integer.Sparse OriginalKey := [(Sum.inl 514, 5)]

def keyMomentRow649 : Integer.Sparse OriginalKey := [(Sum.inl 436, 5)]

def keyMomentRow650 : Integer.Sparse OriginalKey := [(Sum.inl 530, 5)]

def keyMomentRow651 : Integer.Sparse OriginalKey := [(Sum.inl 503, 5)]

def keyMomentRow652 : Integer.Sparse OriginalKey := [(Sum.inl 355, 5)]

def keyMomentRow653 : Integer.Sparse OriginalKey := [(Sum.inl 516, 5)]

def keyMomentRow654 : Integer.Sparse OriginalKey := [(Sum.inl 437, 5)]

def keyMomentRow655 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow656 : Integer.Sparse OriginalKey := [(Sum.inl 310, 5)]

def keyMomentRow657 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow658 : Integer.Sparse OriginalKey := [(Sum.inl 390, 5)]

def keyMomentRow659 : Integer.Sparse OriginalKey := [(Sum.inl 312, 5)]

def keyMomentRow660 : Integer.Sparse OriginalKey := [(Sum.inl 111, 5)]

def keyMomentRow661 : Integer.Sparse OriginalKey := [(Sum.inl 112, 5)]

def keyMomentRow662 : Integer.Sparse OriginalKey := [(Sum.inl 0, 5)]

def keyMomentRow663 : Integer.Sparse OriginalKey := [(Sum.inl 3, 5)]

def keyMomentRow664 : Integer.Sparse OriginalKey := [(Sum.inl 411, 5)]

def keyMomentRow665 : Integer.Sparse OriginalKey := [(Sum.inl 492, 5)]

def keyMomentRow666 : Integer.Sparse OriginalKey := [(Sum.inl 265, 5)]

def keyMomentRow667 : Integer.Sparse OriginalKey := [(Sum.inl 464, 5)]

def keyMomentRow668 : Integer.Sparse OriginalKey := [(Sum.inl 382, 5)]

def keyMomentRow669 : Integer.Sparse OriginalKey := [(Sum.inr 7, 5)]

def keyMomentRow670 : Integer.Sparse OriginalKey := [(Sum.inl 386, 5)]

def keyMomentRow671 : Integer.Sparse OriginalKey := [(Sum.inl 488, 5)]

def keyMomentChunk20 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow640, keyMomentRow641, keyMomentRow642, keyMomentRow643, keyMomentRow644, keyMomentRow645, keyMomentRow646, keyMomentRow647, keyMomentRow648, keyMomentRow649, keyMomentRow650, keyMomentRow651, keyMomentRow652, keyMomentRow653, keyMomentRow654, keyMomentRow655, keyMomentRow656, keyMomentRow657, keyMomentRow658, keyMomentRow659, keyMomentRow660, keyMomentRow661, keyMomentRow662, keyMomentRow663, keyMomentRow664, keyMomentRow665, keyMomentRow666, keyMomentRow667, keyMomentRow668, keyMomentRow669, keyMomentRow670, keyMomentRow671]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow672 : Integer.Sparse OriginalKey := [(Sum.inl 373, 5)]

def keyMomentRow673 : Integer.Sparse OriginalKey := [(Sum.inl 494, 5)]

def keyMomentRow674 : Integer.Sparse OriginalKey := [(Sum.inl 373, 5)]

def keyMomentRow675 : Integer.Sparse OriginalKey := [(Sum.inl 374, 5)]

def keyMomentRow676 : Integer.Sparse OriginalKey := [(Sum.inr 7, 5)]

def keyMomentRow677 : Integer.Sparse OriginalKey := [(Sum.inl 488, 5)]

def keyMomentRow678 : Integer.Sparse OriginalKey := [(Sum.inl 5, 5)]

def keyMomentRow679 : Integer.Sparse OriginalKey := [(Sum.inl 529, 5)]

def keyMomentRow680 : Integer.Sparse OriginalKey := [(Sum.inl 505, 5)]

def keyMomentRow681 : Integer.Sparse OriginalKey := [(Sum.inl 262, 5)]

def keyMomentRow682 : Integer.Sparse OriginalKey := [(Sum.inl 416, 5)]

def keyMomentRow683 : Integer.Sparse OriginalKey := [(Sum.inl 7, 5)]

def keyMomentRow684 : Integer.Sparse OriginalKey := [(Sum.inl 504, 5)]

def keyMomentRow685 : Integer.Sparse OriginalKey := [(Sum.inl 397, 5)]

def keyMomentRow686 : Integer.Sparse OriginalKey := [(Sum.inl 532, 5)]

def keyMomentRow687 : Integer.Sparse OriginalKey := [(Sum.inl 494, 5)]

def keyMomentRow688 : Integer.Sparse OriginalKey := [(Sum.inl 531, 5)]

def keyMomentRow689 : Integer.Sparse OriginalKey := [(Sum.inl 259, 5)]

def keyMomentRow690 : Integer.Sparse OriginalKey := [(Sum.inl 520, 5)]

def keyMomentRow691 : Integer.Sparse OriginalKey := [(Sum.inl 327, 5)]

def keyMomentRow692 : Integer.Sparse OriginalKey := [(Sum.inl 376, 5)]

def keyMomentRow693 : Integer.Sparse OriginalKey := [(Sum.inl 479, 5)]

def keyMomentRow694 : Integer.Sparse OriginalKey := [(Sum.inl 378, 5)]

def keyMomentRow695 : Integer.Sparse OriginalKey := [(Sum.inl 319, 5)]

def keyMomentRow696 : Integer.Sparse OriginalKey := [(Sum.inl 489, 5)]

def keyMomentRow697 : Integer.Sparse OriginalKey := [(Sum.inl 479, 5)]

def keyMomentRow698 : Integer.Sparse OriginalKey := [(Sum.inl 520, 5)]

def keyMomentRow699 : Integer.Sparse OriginalKey := [(Sum.inl 506, 5)]

def keyMomentRow700 : Integer.Sparse OriginalKey := [(Sum.inl 526, 5)]

def keyMomentRow701 : Integer.Sparse OriginalKey := [(Sum.inl 490, 5)]

def keyMomentRow702 : Integer.Sparse OriginalKey := [(Sum.inl 224, 5)]

def keyMomentRow703 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentChunk21 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow672, keyMomentRow673, keyMomentRow674, keyMomentRow675, keyMomentRow676, keyMomentRow677, keyMomentRow678, keyMomentRow679, keyMomentRow680, keyMomentRow681, keyMomentRow682, keyMomentRow683, keyMomentRow684, keyMomentRow685, keyMomentRow686, keyMomentRow687, keyMomentRow688, keyMomentRow689, keyMomentRow690, keyMomentRow691, keyMomentRow692, keyMomentRow693, keyMomentRow694, keyMomentRow695, keyMomentRow696, keyMomentRow697, keyMomentRow698, keyMomentRow699, keyMomentRow700, keyMomentRow701, keyMomentRow702, keyMomentRow703]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow704 : Integer.Sparse OriginalKey := [(Sum.inl 532, 5)]

def keyMomentRow705 : Integer.Sparse OriginalKey := [(Sum.inl 488, 5)]

def keyMomentRow706 : Integer.Sparse OriginalKey := [(Sum.inl 326, 5)]

def keyMomentRow707 : Integer.Sparse OriginalKey := [(Sum.inl 533, 5)]

def keyMomentRow708 : Integer.Sparse OriginalKey := [(Sum.inl 479, 5)]

def keyMomentRow709 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow710 : Integer.Sparse OriginalKey := [(Sum.inl 403, 5)]

def keyMomentRow711 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow712 : Integer.Sparse OriginalKey := [(Sum.inl 526, 5)]

def keyMomentRow713 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow714 : Integer.Sparse OriginalKey := [(Sum.inl 520, 5)]

def keyMomentRow715 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow716 : Integer.Sparse OriginalKey := [(Sum.inl 432, 5)]

def keyMomentRow717 : Integer.Sparse OriginalKey := [(Sum.inl 483, 5)]

def keyMomentRow718 : Integer.Sparse OriginalKey := [(Sum.inl 429, 5)]

def keyMomentRow719 : Integer.Sparse OriginalKey := [(Sum.inl 489, 5)]

def keyMomentRow720 : Integer.Sparse OriginalKey := [(Sum.inl 526, 5)]

def keyMomentRow721 : Integer.Sparse OriginalKey := [(Sum.inl 520, 5)]

def keyMomentRow722 : Integer.Sparse OriginalKey := [(Sum.inl 404, 5)]

def keyMomentRow723 : Integer.Sparse OriginalKey := [(Sum.inl 149, 5)]

def keyMomentRow724 : Integer.Sparse OriginalKey := [(Sum.inl 390, 5)]

def keyMomentRow725 : Integer.Sparse OriginalKey := [(Sum.inl 527, 5)]

def keyMomentRow726 : Integer.Sparse OriginalKey := [(Sum.inl 521, 5)]

def keyMomentRow727 : Integer.Sparse OriginalKey := [(Sum.inl 325, 5)]

def keyMomentRow728 : Integer.Sparse OriginalKey := [(Sum.inl 402, 5)]

def keyMomentRow729 : Integer.Sparse OriginalKey := [(Sum.inl 306, 5)]

def keyMomentRow730 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow731 : Integer.Sparse OriginalKey := [(Sum.inl 301, 5)]

def keyMomentRow732 : Integer.Sparse OriginalKey := [(Sum.inl 376, 5)]

def keyMomentRow733 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow734 : Integer.Sparse OriginalKey := [(Sum.inl 305, 5)]

def keyMomentRow735 : Integer.Sparse OriginalKey := [(Sum.inl 378, 5)]

def keyMomentChunk22 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow704, keyMomentRow705, keyMomentRow706, keyMomentRow707, keyMomentRow708, keyMomentRow709, keyMomentRow710, keyMomentRow711, keyMomentRow712, keyMomentRow713, keyMomentRow714, keyMomentRow715, keyMomentRow716, keyMomentRow717, keyMomentRow718, keyMomentRow719, keyMomentRow720, keyMomentRow721, keyMomentRow722, keyMomentRow723, keyMomentRow724, keyMomentRow725, keyMomentRow726, keyMomentRow727, keyMomentRow728, keyMomentRow729, keyMomentRow730, keyMomentRow731, keyMomentRow732, keyMomentRow733, keyMomentRow734, keyMomentRow735]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow736 : Integer.Sparse OriginalKey := [(Sum.inl 407, 5)]

def keyMomentRow737 : Integer.Sparse OriginalKey := [(Sum.inl 379, 5)]

def keyMomentRow738 : Integer.Sparse OriginalKey := [(Sum.inl 303, 5)]

def keyMomentRow739 : Integer.Sparse OriginalKey := [(Sum.inl 98, 5)]

def keyMomentRow740 : Integer.Sparse OriginalKey := [(Sum.inl 100, 5)]

def keyMomentRow741 : Integer.Sparse OriginalKey := [(Sum.inl 257, 5)]

def keyMomentRow742 : Integer.Sparse OriginalKey := [(Sum.inl 242, 5)]

def keyMomentRow743 : Integer.Sparse OriginalKey := [(Sum.inl 21, 5)]

def keyMomentRow744 : Integer.Sparse OriginalKey := [(Sum.inl 8, 5)]

def keyMomentRow745 : Integer.Sparse OriginalKey := [(Sum.inl 172, 5)]

def keyMomentRow746 : Integer.Sparse OriginalKey := [(Sum.inl 321, 5)]

def keyMomentRow747 : Integer.Sparse OriginalKey := [(Sum.inl 24, 5)]

def keyMomentRow748 : Integer.Sparse OriginalKey := [(Sum.inl 163, 5)]

def keyMomentRow749 : Integer.Sparse OriginalKey := [(Sum.inl 9, 5)]

def keyMomentRow750 : Integer.Sparse OriginalKey := [(Sum.inl 260, 5)]

def keyMomentRow751 : Integer.Sparse OriginalKey := [(Sum.inl 243, 5)]

def keyMomentRow752 : Integer.Sparse OriginalKey := [(Sum.inl 171, 5)]

def keyMomentRow753 : Integer.Sparse OriginalKey := [(Sum.inl 232, 5)]

def keyMomentRow754 : Integer.Sparse OriginalKey := [(Sum.inl 259, 5)]

def keyMomentRow755 : Integer.Sparse OriginalKey := [(Sum.inl 220, 5)]

def keyMomentRow756 : Integer.Sparse OriginalKey := [(Sum.inl 505, 5)]

def keyMomentRow757 : Integer.Sparse OriginalKey := [(Sum.inl 502, 5)]

def keyMomentRow758 : Integer.Sparse OriginalKey := [(Sum.inl 449, 5)]

def keyMomentRow759 : Integer.Sparse OriginalKey := [(Sum.inl 448, 5)]

def keyMomentRow760 : Integer.Sparse OriginalKey := [(Sum.inl 436, 5)]

def keyMomentRow761 : Integer.Sparse OriginalKey := [(Sum.inl 429, 5)]

def keyMomentRow762 : Integer.Sparse OriginalKey := [(Sum.inl 504, 5)]

def keyMomentRow763 : Integer.Sparse OriginalKey := [(Sum.inl 525, 5)]

def keyMomentRow764 : Integer.Sparse OriginalKey := [(Sum.inl 207, 5)]

def keyMomentRow765 : Integer.Sparse OriginalKey := [(Sum.inl 371, 5)]

def keyMomentRow766 : Integer.Sparse OriginalKey := [(Sum.inl 531, 5)]

def keyMomentRow767 : Integer.Sparse OriginalKey := [(Sum.inl 339, 5)]

def keyMomentChunk23 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow736, keyMomentRow737, keyMomentRow738, keyMomentRow739, keyMomentRow740, keyMomentRow741, keyMomentRow742, keyMomentRow743, keyMomentRow744, keyMomentRow745, keyMomentRow746, keyMomentRow747, keyMomentRow748, keyMomentRow749, keyMomentRow750, keyMomentRow751, keyMomentRow752, keyMomentRow753, keyMomentRow754, keyMomentRow755, keyMomentRow756, keyMomentRow757, keyMomentRow758, keyMomentRow759, keyMomentRow760, keyMomentRow761, keyMomentRow762, keyMomentRow763, keyMomentRow764, keyMomentRow765, keyMomentRow766, keyMomentRow767]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow768 : Integer.Sparse OriginalKey := [(Sum.inl 334, 5)]

def keyMomentRow769 : Integer.Sparse OriginalKey := [(Sum.inl 310, 5)]

def keyMomentRow770 : Integer.Sparse OriginalKey := [(Sum.inl 520, 5)]

def keyMomentRow771 : Integer.Sparse OriginalKey := [(Sum.inl 301, 5)]

def keyMomentRow772 : Integer.Sparse OriginalKey := [(Sum.inl 155, 5)]

def keyMomentRow773 : Integer.Sparse OriginalKey := [(Sum.inl 22, 5)]

def keyMomentRow774 : Integer.Sparse OriginalKey := [(Sum.inl 91, 5)]

def keyMomentRow775 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow776 : Integer.Sparse OriginalKey := [(Sum.inl 245, 5)]

def keyMomentRow777 : Integer.Sparse OriginalKey := [(Sum.inl 178, 5)]

def keyMomentRow778 : Integer.Sparse OriginalKey := [(Sum.inl 234, 5)]

def keyMomentRow779 : Integer.Sparse OriginalKey := [(Sum.inl 260, 5)]

def keyMomentRow780 : Integer.Sparse OriginalKey := [(Sum.inl 174, 5)]

def keyMomentRow781 : Integer.Sparse OriginalKey := [(Sum.inl 221, 5)]

def keyMomentRow782 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow783 : Integer.Sparse OriginalKey := [(Sum.inl 424, 5)]

def keyMomentRow784 : Integer.Sparse OriginalKey := [(Sum.inl 503, 5)]

def keyMomentRow785 : Integer.Sparse OriginalKey := [(Sum.inl 450, 5)]

def keyMomentRow786 : Integer.Sparse OriginalKey := [(Sum.inl 289, 5)]

def keyMomentRow787 : Integer.Sparse OriginalKey := [(Sum.inl 437, 5)]

def keyMomentRow788 : Integer.Sparse OriginalKey := [(Sum.inl 423, 5)]

def keyMomentRow789 : Integer.Sparse OriginalKey := [(Sum.inl 472, 5)]

def keyMomentRow790 : Integer.Sparse OriginalKey := [(Sum.inl 520, 5)]

def keyMomentRow791 : Integer.Sparse OriginalKey := [(Sum.inl 336, 5)]

def keyMomentRow792 : Integer.Sparse OriginalKey := [(Sum.inl 124, 5)]

def keyMomentRow793 : Integer.Sparse OriginalKey := [(Sum.inl 312, 5)]

def keyMomentRow794 : Integer.Sparse OriginalKey := [(Sum.inl 521, 5)]

def keyMomentRow795 : Integer.Sparse OriginalKey := [(Sum.inl 517, 5)]

def keyMomentRow796 : Integer.Sparse OriginalKey := [(Sum.inl 293, 5)]

def keyMomentRow797 : Integer.Sparse OriginalKey := [(Sum.inl 157, 5)]

def keyMomentRow798 : Integer.Sparse OriginalKey := [(Sum.inl 30, 5)]

def keyMomentRow799 : Integer.Sparse OriginalKey := [(Sum.inl 26, 5)]

def keyMomentChunk24 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow768, keyMomentRow769, keyMomentRow770, keyMomentRow771, keyMomentRow772, keyMomentRow773, keyMomentRow774, keyMomentRow775, keyMomentRow776, keyMomentRow777, keyMomentRow778, keyMomentRow779, keyMomentRow780, keyMomentRow781, keyMomentRow782, keyMomentRow783, keyMomentRow784, keyMomentRow785, keyMomentRow786, keyMomentRow787, keyMomentRow788, keyMomentRow789, keyMomentRow790, keyMomentRow791, keyMomentRow792, keyMomentRow793, keyMomentRow794, keyMomentRow795, keyMomentRow796, keyMomentRow797, keyMomentRow798, keyMomentRow799]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow800 : Integer.Sparse OriginalKey := [(Sum.inl 93, 5)]

def keyMomentRow801 : Integer.Sparse OriginalKey := [(Sum.inl 509, 5)]

def keyMomentRow802 : Integer.Sparse OriginalKey := [(Sum.inl 63, 5)]

def keyMomentRow803 : Integer.Sparse OriginalKey := [(Sum.inl 247, 5)]

def keyMomentRow804 : Integer.Sparse OriginalKey := [(Sum.inl 175, 5)]

def keyMomentRow805 : Integer.Sparse OriginalKey := [(Sum.inl 222, 5)]

def keyMomentRow806 : Integer.Sparse OriginalKey := [(Sum.inl 332, 5)]

def keyMomentRow807 : Integer.Sparse OriginalKey := [(Sum.inl 343, 5)]

def keyMomentRow808 : Integer.Sparse OriginalKey := [(Sum.inl 285, 5)]

def keyMomentRow809 : Integer.Sparse OriginalKey := [(Sum.inl 325, 5)]

def keyMomentRow810 : Integer.Sparse OriginalKey := [(Sum.inl 293, 5)]

def keyMomentRow811 : Integer.Sparse OriginalKey := [(Sum.inl 339, 5)]

def keyMomentRow812 : Integer.Sparse OriginalKey := [(Sum.inl 294, 5)]

def keyMomentRow813 : Integer.Sparse OriginalKey := [(Sum.inl 321, 5)]

def keyMomentRow814 : Integer.Sparse OriginalKey := [(Sum.inl 341, 5)]

def keyMomentRow815 : Integer.Sparse OriginalKey := [(Sum.inl 303, 5)]

def keyMomentRow816 : Integer.Sparse OriginalKey := [(Sum.inl 291, 5)]

def keyMomentRow817 : Integer.Sparse OriginalKey := [(Sum.inl 158, 5)]

def keyMomentRow818 : Integer.Sparse OriginalKey := [(Sum.inl 28, 5)]

def keyMomentRow819 : Integer.Sparse OriginalKey := [(Sum.inl 94, 5)]

def keyMomentRow820 : Integer.Sparse OriginalKey := [(Sum.inl 71, 5)]

def keyMomentRow821 : Integer.Sparse OriginalKey := [(Sum.inl 68, 5)]

def keyMomentRow822 : Integer.Sparse OriginalKey := [(Sum.inl 72, 5)]

def keyMomentRow823 : Integer.Sparse OriginalKey := [(Sum.inl 70, 5)]

def keyMomentRow824 : Integer.Sparse OriginalKey := [(Sum.inl 252, 5)]

def keyMomentRow825 : Integer.Sparse OriginalKey := [(Sum.inl 183, 5)]

def keyMomentRow826 : Integer.Sparse OriginalKey := [(Sum.inl 227, 5)]

def keyMomentRow827 : Integer.Sparse OriginalKey := [(Sum.inl 210, 5)]

def keyMomentRow828 : Integer.Sparse OriginalKey := [(Sum.inl 452, 5)]

def keyMomentRow829 : Integer.Sparse OriginalKey := [(Sum.inl 508, 5)]

def keyMomentRow830 : Integer.Sparse OriginalKey := [(Sum.inl 509, 5)]

def keyMomentRow831 : Integer.Sparse OriginalKey := [(Sum.inl 161, 5)]

def keyMomentChunk25 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow800, keyMomentRow801, keyMomentRow802, keyMomentRow803, keyMomentRow804, keyMomentRow805, keyMomentRow806, keyMomentRow807, keyMomentRow808, keyMomentRow809, keyMomentRow810, keyMomentRow811, keyMomentRow812, keyMomentRow813, keyMomentRow814, keyMomentRow815, keyMomentRow816, keyMomentRow817, keyMomentRow818, keyMomentRow819, keyMomentRow820, keyMomentRow821, keyMomentRow822, keyMomentRow823, keyMomentRow824, keyMomentRow825, keyMomentRow826, keyMomentRow827, keyMomentRow828, keyMomentRow829, keyMomentRow830, keyMomentRow831]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow832 : Integer.Sparse OriginalKey := [(Sum.inl 34, 5)]

def keyMomentRow833 : Integer.Sparse OriginalKey := [(Sum.inl 99, 5)]

def keyMomentRow834 : Integer.Sparse OriginalKey := [(Sum.inl 510, 5)]

def keyMomentRow835 : Integer.Sparse OriginalKey := [(Sum.inl 69, 5)]

def keyMomentRow836 : Integer.Sparse OriginalKey := [(Sum.inl 186, 5)]

def keyMomentRow837 : Integer.Sparse OriginalKey := [(Sum.inl 275, 5)]

def keyMomentRow838 : Integer.Sparse OriginalKey := [(Sum.inl 277, 5)]

def keyMomentRow839 : Integer.Sparse OriginalKey := [(Sum.inl 39, 5)]

def keyMomentRow840 : Integer.Sparse OriginalKey := [(Sum.inl 4085, 5)]

def keyMomentRow841 : Integer.Sparse OriginalKey := [(Sum.inl 2268, 5)]

def keyMomentRow842 : Integer.Sparse OriginalKey := [(Sum.inl 2281, 5)]

def keyMomentRow843 : Integer.Sparse OriginalKey := [(Sum.inl 4084, 5)]

def keyMomentRow844 : Integer.Sparse OriginalKey := [(Sum.inl 2293, 5)]

def keyMomentRow845 : Integer.Sparse OriginalKey := [(Sum.inl 2294, 5)]

def keyMomentRow846 : Integer.Sparse OriginalKey := [(Sum.inl 2247, 5)]

def keyMomentRow847 : Integer.Sparse OriginalKey := [(Sum.inl 2264, 5)]

def keyMomentRow848 : Integer.Sparse OriginalKey := [(Sum.inl 2265, 5)]

def keyMomentRow849 : Integer.Sparse OriginalKey := [(Sum.inl 2266, 5)]

def keyMomentRow850 : Integer.Sparse OriginalKey := [(Sum.inl 2278, 5)]

def keyMomentRow851 : Integer.Sparse OriginalKey := [(Sum.inl 2279, 5)]

def keyMomentRow852 : Integer.Sparse OriginalKey := [(Sum.inl 2291, 5)]

def keyMomentRow853 : Integer.Sparse OriginalKey := [(Sum.inl 4083, 5)]

def keyMomentRow854 : Integer.Sparse OriginalKey := [(Sum.inl 2244, 5)]

def keyMomentRow855 : Integer.Sparse OriginalKey := [(Sum.inl 2245, 5)]

def keyMomentRow856 : Integer.Sparse OriginalKey := [(Sum.inl 2262, 5)]

def keyMomentRow857 : Integer.Sparse OriginalKey := [(Sum.inl 2263, 5)]

def keyMomentRow858 : Integer.Sparse OriginalKey := [(Sum.inl 2277, 5)]

def keyMomentRow859 : Integer.Sparse OriginalKey := [(Sum.inl 2243, 5)]

def keyMomentRow860 : Integer.Sparse OriginalKey := [(Sum.inl 2268, 5)]

def keyMomentRow861 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 5)]

def keyMomentRow862 : Integer.Sparse OriginalKey := [(Sum.inl 2740, 5)]

def keyMomentRow863 : Integer.Sparse OriginalKey := [(Sum.inl 2742, 5)]

def keyMomentChunk26 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow832, keyMomentRow833, keyMomentRow834, keyMomentRow835, keyMomentRow836, keyMomentRow837, keyMomentRow838, keyMomentRow839, keyMomentRow840, keyMomentRow841, keyMomentRow842, keyMomentRow843, keyMomentRow844, keyMomentRow845, keyMomentRow846, keyMomentRow847, keyMomentRow848, keyMomentRow849, keyMomentRow850, keyMomentRow851, keyMomentRow852, keyMomentRow853, keyMomentRow854, keyMomentRow855, keyMomentRow856, keyMomentRow857, keyMomentRow858, keyMomentRow859, keyMomentRow860, keyMomentRow861, keyMomentRow862, keyMomentRow863]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow864 : Integer.Sparse OriginalKey := [(Sum.inl 2743, 5)]

def keyMomentRow865 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 5)]

def keyMomentRow866 : Integer.Sparse OriginalKey := [(Sum.inl 2722, 5)]

def keyMomentRow867 : Integer.Sparse OriginalKey := [(Sum.inl 2723, 5)]

def keyMomentRow868 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 5)]

def keyMomentRow869 : Integer.Sparse OriginalKey := [(Sum.inl 2731, 5)]

def keyMomentRow870 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 5)]

def keyMomentRow871 : Integer.Sparse OriginalKey := [(Sum.inl 2738, 5)]

def keyMomentRow872 : Integer.Sparse OriginalKey := [(Sum.inl 2739, 5)]

def keyMomentRow873 : Integer.Sparse OriginalKey := [(Sum.inl 2741, 5)]

def keyMomentRow874 : Integer.Sparse OriginalKey := [(Sum.inl 2709, 5)]

def keyMomentRow875 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 5)]

def keyMomentRow876 : Integer.Sparse OriginalKey := [(Sum.inl 2720, 5)]

def keyMomentRow877 : Integer.Sparse OriginalKey := [(Sum.inl 2721, 5)]

def keyMomentRow878 : Integer.Sparse OriginalKey := [(Sum.inl 2730, 5)]

def keyMomentRow879 : Integer.Sparse OriginalKey := [(Sum.inl 2783, 5)]

def keyMomentRow880 : Integer.Sparse OriginalKey := [(Sum.inl 2789, 5)]

def keyMomentRow881 : Integer.Sparse OriginalKey := [(Sum.inl 2765, 5)]

def keyMomentRow882 : Integer.Sparse OriginalKey := [(Sum.inl 2769, 5)]

def keyMomentRow883 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 5)]

def keyMomentRow884 : Integer.Sparse OriginalKey := [(Sum.inl 2777, 5)]

def keyMomentRow885 : Integer.Sparse OriginalKey := [(Sum.inl 2781, 5)]

def keyMomentRow886 : Integer.Sparse OriginalKey := [(Sum.inl 2782, 5)]

def keyMomentRow887 : Integer.Sparse OriginalKey := [(Sum.inl 2751, 5)]

def keyMomentRow888 : Integer.Sparse OriginalKey := [(Sum.inl 2754, 5)]

def keyMomentRow889 : Integer.Sparse OriginalKey := [(Sum.inl 2763, 5)]

def keyMomentRow890 : Integer.Sparse OriginalKey := [(Sum.inl 2764, 5)]

def keyMomentRow891 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 5)]

def keyMomentRow892 : Integer.Sparse OriginalKey := [(Sum.inl 2750, 5)]

def keyMomentRow893 : Integer.Sparse OriginalKey := [(Sum.inl 2281, 5)]

def keyMomentRow894 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 5)]

def keyMomentRow895 : Integer.Sparse OriginalKey := [(Sum.inl 3046, 5)]

def keyMomentChunk27 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow864, keyMomentRow865, keyMomentRow866, keyMomentRow867, keyMomentRow868, keyMomentRow869, keyMomentRow870, keyMomentRow871, keyMomentRow872, keyMomentRow873, keyMomentRow874, keyMomentRow875, keyMomentRow876, keyMomentRow877, keyMomentRow878, keyMomentRow879, keyMomentRow880, keyMomentRow881, keyMomentRow882, keyMomentRow883, keyMomentRow884, keyMomentRow885, keyMomentRow886, keyMomentRow887, keyMomentRow888, keyMomentRow889, keyMomentRow890, keyMomentRow891, keyMomentRow892, keyMomentRow893, keyMomentRow894, keyMomentRow895]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow896 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 5)]

def keyMomentRow897 : Integer.Sparse OriginalKey := [(Sum.inl 3054, 5)]

def keyMomentRow898 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 5)]

def keyMomentRow899 : Integer.Sparse OriginalKey := [(Sum.inl 3056, 5)]

def keyMomentRow900 : Integer.Sparse OriginalKey := [(Sum.inl 3031, 5)]

def keyMomentRow901 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 5)]

def keyMomentRow902 : Integer.Sparse OriginalKey := [(Sum.inl 3039, 5)]

def keyMomentRow903 : Integer.Sparse OriginalKey := [(Sum.inl 3040, 5)]

def keyMomentRow904 : Integer.Sparse OriginalKey := [(Sum.inl 3044, 5)]

def keyMomentRow905 : Integer.Sparse OriginalKey := [(Sum.inl 3045, 5)]

def keyMomentRow906 : Integer.Sparse OriginalKey := [(Sum.inl 3050, 5)]

def keyMomentRow907 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 5)]

def keyMomentRow908 : Integer.Sparse OriginalKey := [(Sum.inl 3053, 5)]

def keyMomentRow909 : Integer.Sparse OriginalKey := [(Sum.inl 3029, 5)]

def keyMomentRow910 : Integer.Sparse OriginalKey := [(Sum.inl 3030, 5)]

def keyMomentRow911 : Integer.Sparse OriginalKey := [(Sum.inl 3036, 5)]

def keyMomentRow912 : Integer.Sparse OriginalKey := [(Sum.inl 3037, 5)]

def keyMomentRow913 : Integer.Sparse OriginalKey := [(Sum.inl 3043, 5)]

def keyMomentRow914 : Integer.Sparse OriginalKey := [(Sum.inl 2247, 5)]

def keyMomentRow915 : Integer.Sparse OriginalKey := [(Sum.inl 3075, 5)]

def keyMomentRow916 : Integer.Sparse OriginalKey := [(Sum.inl 3077, 5)]

def keyMomentRow917 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 5)]

def keyMomentRow918 : Integer.Sparse OriginalKey := [(Sum.inl 3079, 5)]

def keyMomentRow919 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 5)]

def keyMomentRow920 : Integer.Sparse OriginalKey := [(Sum.inl 3066, 5)]

def keyMomentRow921 : Integer.Sparse OriginalKey := [(Sum.inl 3068, 5)]

def keyMomentRow922 : Integer.Sparse OriginalKey := [(Sum.inl 3069, 5)]

def keyMomentRow923 : Integer.Sparse OriginalKey := [(Sum.inl 3073, 5)]

def keyMomentRow924 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 5)]

def keyMomentRow925 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 5)]

def keyMomentRow926 : Integer.Sparse OriginalKey := [(Sum.inl 2967, 5)]

def keyMomentRow927 : Integer.Sparse OriginalKey := [(Sum.inl 3086, 5)]

def keyMomentChunk28 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow896, keyMomentRow897, keyMomentRow898, keyMomentRow899, keyMomentRow900, keyMomentRow901, keyMomentRow902, keyMomentRow903, keyMomentRow904, keyMomentRow905, keyMomentRow906, keyMomentRow907, keyMomentRow908, keyMomentRow909, keyMomentRow910, keyMomentRow911, keyMomentRow912, keyMomentRow913, keyMomentRow914, keyMomentRow915, keyMomentRow916, keyMomentRow917, keyMomentRow918, keyMomentRow919, keyMomentRow920, keyMomentRow921, keyMomentRow922, keyMomentRow923, keyMomentRow924, keyMomentRow925, keyMomentRow926, keyMomentRow927]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow928 : Integer.Sparse OriginalKey := [(Sum.inl 2964, 5)]

def keyMomentRow929 : Integer.Sparse OriginalKey := [(Sum.inl 3096, 5)]

def keyMomentRow930 : Integer.Sparse OriginalKey := [(Sum.inl 3097, 5)]

def keyMomentRow931 : Integer.Sparse OriginalKey := [(Sum.inl 3084, 5)]

def keyMomentRow932 : Integer.Sparse OriginalKey := [(Sum.inl 2789, 5)]

def keyMomentRow933 : Integer.Sparse OriginalKey := [(Sum.inl 1310, 5)]

def keyMomentRow934 : Integer.Sparse OriginalKey := [(Sum.inl 2777, 5)]

def keyMomentRow935 : Integer.Sparse OriginalKey := [(Sum.inl 1306, 5)]

def keyMomentRow936 : Integer.Sparse OriginalKey := [(Sum.inl 2643, 5)]

def keyMomentRow937 : Integer.Sparse OriginalKey := [(Sum.inl 1273, 5)]

def keyMomentRow938 : Integer.Sparse OriginalKey := [(Sum.inl 2603, 5)]

def keyMomentRow939 : Integer.Sparse OriginalKey := [(Sum.inl 2769, 5)]

def keyMomentRow940 : Integer.Sparse OriginalKey := [(Sum.inl 3118, 5)]

def keyMomentRow941 : Integer.Sparse OriginalKey := [(Sum.inl 2641, 5)]

def keyMomentRow942 : Integer.Sparse OriginalKey := [(Sum.inl 1270, 5)]

def keyMomentRow943 : Integer.Sparse OriginalKey := [(Sum.inl 2600, 5)]

def keyMomentRow944 : Integer.Sparse OriginalKey := [(Sum.inl 2754, 5)]

def keyMomentRow945 : Integer.Sparse OriginalKey := [(Sum.inl 3108, 5)]

def keyMomentRow946 : Integer.Sparse OriginalKey := [(Sum.inl 2575, 5)]

def keyMomentRow947 : Integer.Sparse OriginalKey := [(Sum.inl 2573, 5)]

def keyMomentRow948 : Integer.Sparse OriginalKey := [(Sum.inl 2285, 5)]

def keyMomentRow949 : Integer.Sparse OriginalKey := [(Sum.inl 2136, 5)]

def keyMomentRow950 : Integer.Sparse OriginalKey := [(Sum.inl 1832, 5)]

def keyMomentRow951 : Integer.Sparse OriginalKey := [(Sum.inl 2255, 5)]

def keyMomentRow952 : Integer.Sparse OriginalKey := [(Sum.inl 2113, 5)]

def keyMomentRow953 : Integer.Sparse OriginalKey := [(Sum.inl 1820, 5)]

def keyMomentRow954 : Integer.Sparse OriginalKey := [(Sum.inl 1828, 5)]

def keyMomentRow955 : Integer.Sparse OriginalKey := [(Sum.inl 2037, 5)]

def keyMomentRow956 : Integer.Sparse OriginalKey := [(Sum.inl 2092, 5)]

def keyMomentRow957 : Integer.Sparse OriginalKey := [(Sum.inl 1813, 5)]

def keyMomentRow958 : Integer.Sparse OriginalKey := [(Sum.inl 1980, 5)]

def keyMomentRow959 : Integer.Sparse OriginalKey := [(Sum.inl 1797, 5)]

def keyMomentChunk29 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow928, keyMomentRow929, keyMomentRow930, keyMomentRow931, keyMomentRow932, keyMomentRow933, keyMomentRow934, keyMomentRow935, keyMomentRow936, keyMomentRow937, keyMomentRow938, keyMomentRow939, keyMomentRow940, keyMomentRow941, keyMomentRow942, keyMomentRow943, keyMomentRow944, keyMomentRow945, keyMomentRow946, keyMomentRow947, keyMomentRow948, keyMomentRow949, keyMomentRow950, keyMomentRow951, keyMomentRow952, keyMomentRow953, keyMomentRow954, keyMomentRow955, keyMomentRow956, keyMomentRow957, keyMomentRow958, keyMomentRow959]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow96 : Integer.Sparse OriginalKey := [(Sum.inl 256, 5)]

def keyMomentRow97 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow98 : Integer.Sparse OriginalKey := [(Sum.inl 251, 5)]

def keyMomentRow99 : Integer.Sparse OriginalKey := [(Sum.inl 196, 5)]

def keyMomentRow100 : Integer.Sparse OriginalKey := [(Sum.inl 229, 5)]

def keyMomentRow101 : Integer.Sparse OriginalKey := [(Sum.inl 214, 5)]

def keyMomentRow102 : Integer.Sparse OriginalKey := [(Sum.inl 168, 5)]

def keyMomentRow103 : Integer.Sparse OriginalKey := [(Sum.inl 195, 5)]

def keyMomentRow104 : Integer.Sparse OriginalKey := [(Sum.inl 240, 5)]

def keyMomentRow105 : Integer.Sparse OriginalKey := [(Sum.inl 248, 5)]

def keyMomentRow106 : Integer.Sparse OriginalKey := [(Sum.inl 213, 5)]

def keyMomentRow107 : Integer.Sparse OriginalKey := [(Sum.inl 167, 5)]

def keyMomentRow108 : Integer.Sparse OriginalKey := [(Sum.inl 253, 5)]

def keyMomentRow109 : Integer.Sparse OriginalKey := [(Sum.inl 257, 5)]

def keyMomentRow110 : Integer.Sparse OriginalKey := [(Sum.inl 189, 5)]

def keyMomentRow111 : Integer.Sparse OriginalKey := [(Sum.inl 254, 5)]

def keyMomentRow112 : Integer.Sparse OriginalKey := [(Sum.inl 260, 5)]

def keyMomentRow113 : Integer.Sparse OriginalKey := [(Sum.inl 190, 5)]

def keyMomentRow114 : Integer.Sparse OriginalKey := [(Sum.inl 220, 5)]

def keyMomentRow115 : Integer.Sparse OriginalKey := [(Sum.inl 163, 5)]

def keyMomentRow116 : Integer.Sparse OriginalKey := [(Sum.inl 259, 5)]

def keyMomentRow117 : Integer.Sparse OriginalKey := [(Sum.inl 255, 5)]

def keyMomentRow118 : Integer.Sparse OriginalKey := [(Sum.inl 134, 5)]

def keyMomentRow119 : Integer.Sparse OriginalKey := [(Sum.inr 1, 5)]

def keyMomentRow120 : Integer.Sparse OriginalKey := [(Sum.inl 222, 5)]

def keyMomentRow121 : Integer.Sparse OriginalKey := [(Sum.inl 117, 5)]

def keyMomentRow122 : Integer.Sparse OriginalKey := [(Sum.inl 192, 5)]

def keyMomentRow123 : Integer.Sparse OriginalKey := [(Sum.inl 239, 5)]

def keyMomentRow124 : Integer.Sparse OriginalKey := [(Sum.inl 260, 5)]

def keyMomentRow125 : Integer.Sparse OriginalKey := [(Sum.inl 212, 5)]

def keyMomentRow126 : Integer.Sparse OriginalKey := [(Sum.inl 221, 5)]

def keyMomentRow127 : Integer.Sparse OriginalKey := [(Sum.inl 164, 5)]

def keyMomentChunk3 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow96, keyMomentRow97, keyMomentRow98, keyMomentRow99, keyMomentRow100, keyMomentRow101, keyMomentRow102, keyMomentRow103, keyMomentRow104, keyMomentRow105, keyMomentRow106, keyMomentRow107, keyMomentRow108, keyMomentRow109, keyMomentRow110, keyMomentRow111, keyMomentRow112, keyMomentRow113, keyMomentRow114, keyMomentRow115, keyMomentRow116, keyMomentRow117, keyMomentRow118, keyMomentRow119, keyMomentRow120, keyMomentRow121, keyMomentRow122, keyMomentRow123, keyMomentRow124, keyMomentRow125, keyMomentRow126, keyMomentRow127]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow960 : Integer.Sparse OriginalKey := [(Sum.inl 1971, 5)]

def keyMomentRow961 : Integer.Sparse OriginalKey := [(Sum.inl 2026, 5)]

def keyMomentRow962 : Integer.Sparse OriginalKey := [(Sum.inl 2235, 5)]

def keyMomentRow963 : Integer.Sparse OriginalKey := [(Sum.inl 1976, 5)]

def keyMomentRow964 : Integer.Sparse OriginalKey := [(Sum.inl 1793, 5)]

def keyMomentRow965 : Integer.Sparse OriginalKey := [(Sum.inl 1965, 5)]

def keyMomentRow966 : Integer.Sparse OriginalKey := [(Sum.inl 2010, 5)]

def keyMomentRow967 : Integer.Sparse OriginalKey := [(Sum.inl 1957, 5)]

def keyMomentRow968 : Integer.Sparse OriginalKey := [(Sum.inl 2255, 5)]

def keyMomentRow969 : Integer.Sparse OriginalKey := [(Sum.inl 2716, 5)]

def keyMomentRow970 : Integer.Sparse OriginalKey := [(Sum.inl 3033, 5)]

def keyMomentRow971 : Integer.Sparse OriginalKey := [(Sum.inl 3156, 5)]

def keyMomentRow972 : Integer.Sparse OriginalKey := [(Sum.inl 3222, 5)]

def keyMomentRow973 : Integer.Sparse OriginalKey := [(Sum.inl 3180, 5)]

def keyMomentRow974 : Integer.Sparse OriginalKey := [(Sum.inl 3131, 5)]

def keyMomentRow975 : Integer.Sparse OriginalKey := [(Sum.inl 3062, 5)]

def keyMomentRow976 : Integer.Sparse OriginalKey := [(Sum.inl 3196, 5)]

def keyMomentRow977 : Integer.Sparse OriginalKey := [(Sum.inl 3202, 5)]

def keyMomentRow978 : Integer.Sparse OriginalKey := [(Sum.inl 3163, 5)]

def keyMomentRow979 : Integer.Sparse OriginalKey := [(Sum.inl 3136, 5)]

def keyMomentRow980 : Integer.Sparse OriginalKey := [(Sum.inl 3134, 5)]

def keyMomentRow981 : Integer.Sparse OriginalKey := [(Sum.inl 3127, 5)]

def keyMomentRow982 : Integer.Sparse OriginalKey := [(Sum.inl 3170, 5)]

def keyMomentRow983 : Integer.Sparse OriginalKey := [(Sum.inl 3221, 5)]

def keyMomentRow984 : Integer.Sparse OriginalKey := [(Sum.inl 3161, 5)]

def keyMomentRow985 : Integer.Sparse OriginalKey := [(Sum.inl 2821, 5)]

def keyMomentRow986 : Integer.Sparse OriginalKey := [(Sum.inl 3198, 5)]

def keyMomentRow987 : Integer.Sparse OriginalKey := [(Sum.inl 2816, 5)]

def keyMomentRow988 : Integer.Sparse OriginalKey := [(Sum.inl 3138, 5)]

def keyMomentRow989 : Integer.Sparse OriginalKey := [(Sum.inl 2803, 5)]

def keyMomentRow990 : Integer.Sparse OriginalKey := [(Sum.inl 3129, 5)]

def keyMomentRow991 : Integer.Sparse OriginalKey := [(Sum.inl 3174, 5)]

def keyMomentChunk30 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow960, keyMomentRow961, keyMomentRow962, keyMomentRow963, keyMomentRow964, keyMomentRow965, keyMomentRow966, keyMomentRow967, keyMomentRow968, keyMomentRow969, keyMomentRow970, keyMomentRow971, keyMomentRow972, keyMomentRow973, keyMomentRow974, keyMomentRow975, keyMomentRow976, keyMomentRow977, keyMomentRow978, keyMomentRow979, keyMomentRow980, keyMomentRow981, keyMomentRow982, keyMomentRow983, keyMomentRow984, keyMomentRow985, keyMomentRow986, keyMomentRow987, keyMomentRow988, keyMomentRow989, keyMomentRow990, keyMomentRow991]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow992 : Integer.Sparse OriginalKey := [(Sum.inl 3189, 5)]

def keyMomentRow993 : Integer.Sparse OriginalKey := [(Sum.inl 2800, 5)]

def keyMomentRow994 : Integer.Sparse OriginalKey := [(Sum.inl 3162, 5)]

def keyMomentRow995 : Integer.Sparse OriginalKey := [(Sum.inl 3199, 5)]

def keyMomentRow996 : Integer.Sparse OriginalKey := [(Sum.inl 3133, 5)]

def keyMomentRow997 : Integer.Sparse OriginalKey := [(Sum.inl 2235, 5)]

def keyMomentRow998 : Integer.Sparse OriginalKey := [(Sum.inl 2707, 5)]

def keyMomentRow999 : Integer.Sparse OriginalKey := [(Sum.inl 3155, 5)]

def keyMomentRow1000 : Integer.Sparse OriginalKey := [(Sum.inl 3221, 5)]

def keyMomentRow1001 : Integer.Sparse OriginalKey := [(Sum.inl 3179, 5)]

def keyMomentRow1002 : Integer.Sparse OriginalKey := [(Sum.inl 3130, 5)]

def keyMomentRow1003 : Integer.Sparse OriginalKey := [(Sum.inl 3158, 5)]

def keyMomentRow1004 : Integer.Sparse OriginalKey := [(Sum.inl 2899, 5)]

def keyMomentRow1005 : Integer.Sparse OriginalKey := [(Sum.inl 3197, 5)]

def keyMomentRow1006 : Integer.Sparse OriginalKey := [(Sum.inl 2895, 5)]

def keyMomentRow1007 : Integer.Sparse OriginalKey := [(Sum.inl 3137, 5)]

def keyMomentRow1008 : Integer.Sparse OriginalKey := [(Sum.inl 2890, 5)]

def keyMomentRow1009 : Integer.Sparse OriginalKey := [(Sum.inl 3128, 5)]

def keyMomentRow1010 : Integer.Sparse OriginalKey := [(Sum.inl 3172, 5)]

def keyMomentRow1011 : Integer.Sparse OriginalKey := [(Sum.inl 2520, 5)]

def keyMomentRow1012 : Integer.Sparse OriginalKey := [(Sum.inl 1146, 5)]

def keyMomentRow1013 : Integer.Sparse OriginalKey := [(Sum.inl 2497, 5)]

def keyMomentRow1014 : Integer.Sparse OriginalKey := [(Sum.inl 1137, 5)]

def keyMomentRow1015 : Integer.Sparse OriginalKey := [(Sum.inl 2443, 5)]

def keyMomentRow1016 : Integer.Sparse OriginalKey := [(Sum.inl 1121, 5)]

def keyMomentRow1017 : Integer.Sparse OriginalKey := [(Sum.inl 2435, 5)]

def keyMomentRow1018 : Integer.Sparse OriginalKey := [(Sum.inl 2486, 5)]

def keyMomentRow1019 : Integer.Sparse OriginalKey := [(Sum.inl 3132, 5)]

def keyMomentRow1020 : Integer.Sparse OriginalKey := [(Sum.inl 2440, 5)]

def keyMomentRow1021 : Integer.Sparse OriginalKey := [(Sum.inl 1116, 5)]

def keyMomentRow1022 : Integer.Sparse OriginalKey := [(Sum.inl 2430, 5)]

def keyMomentRow1023 : Integer.Sparse OriginalKey := [(Sum.inl 2471, 5)]

def keyMomentChunk31 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow992, keyMomentRow993, keyMomentRow994, keyMomentRow995, keyMomentRow996, keyMomentRow997, keyMomentRow998, keyMomentRow999, keyMomentRow1000, keyMomentRow1001, keyMomentRow1002, keyMomentRow1003, keyMomentRow1004, keyMomentRow1005, keyMomentRow1006, keyMomentRow1007, keyMomentRow1008, keyMomentRow1009, keyMomentRow1010, keyMomentRow1011, keyMomentRow1012, keyMomentRow1013, keyMomentRow1014, keyMomentRow1015, keyMomentRow1016, keyMomentRow1017, keyMomentRow1018, keyMomentRow1019, keyMomentRow1020, keyMomentRow1021, keyMomentRow1022, keyMomentRow1023]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1024 : Integer.Sparse OriginalKey := [(Sum.inl 3164, 5)]

def keyMomentRow1025 : Integer.Sparse OriginalKey := [(Sum.inl 2423, 5)]

def keyMomentRow1026 : Integer.Sparse OriginalKey := [(Sum.inl 621, 5)]

def keyMomentRow1027 : Integer.Sparse OriginalKey := [(Sum.inl 1061, 5)]

def keyMomentRow1028 : Integer.Sparse OriginalKey := [(Sum.inl 612, 5)]

def keyMomentRow1029 : Integer.Sparse OriginalKey := [(Sum.inl 954, 5)]

def keyMomentRow1030 : Integer.Sparse OriginalKey := [(Sum.inl 590, 5)]

def keyMomentRow1031 : Integer.Sparse OriginalKey := [(Sum.inl 940, 5)]

def keyMomentRow1032 : Integer.Sparse OriginalKey := [(Sum.inl 1047, 5)]

def keyMomentRow1033 : Integer.Sparse OriginalKey := [(Sum.inl 2346, 5)]

def keyMomentRow1034 : Integer.Sparse OriginalKey := [(Sum.inl 949, 5)]

def keyMomentRow1035 : Integer.Sparse OriginalKey := [(Sum.inl 585, 5)]

def keyMomentRow1036 : Integer.Sparse OriginalKey := [(Sum.inl 931, 5)]

def keyMomentRow1037 : Integer.Sparse OriginalKey := [(Sum.inl 1024, 5)]

def keyMomentRow1038 : Integer.Sparse OriginalKey := [(Sum.inl 2340, 5)]

def keyMomentRow1039 : Integer.Sparse OriginalKey := [(Sum.inl 914, 5)]

def keyMomentRow1040 : Integer.Sparse OriginalKey := [(Sum.inl 2327, 5)]

def keyMomentRow1041 : Integer.Sparse OriginalKey := [(Sum.inl 909, 5)]

def keyMomentRow1042 : Integer.Sparse OriginalKey := [(Sum.inl 2323, 5)]

def keyMomentRow1043 : Integer.Sparse OriginalKey := [(Sum.inl 1438, 5)]

def keyMomentRow1044 : Integer.Sparse OriginalKey := [(Sum.inl 1348, 5)]

def keyMomentRow1045 : Integer.Sparse OriginalKey := [(Sum.inl 1369, 5)]

def keyMomentRow1046 : Integer.Sparse OriginalKey := [(Sum.inl 1408, 5)]

def keyMomentRow1047 : Integer.Sparse OriginalKey := [(Sum.inl 1323, 5)]

def keyMomentRow1048 : Integer.Sparse OriginalKey := [(Sum.inl 1336, 5)]

def keyMomentRow1049 : Integer.Sparse OriginalKey := [(Sum.inl 1332, 5)]

def keyMomentRow1050 : Integer.Sparse OriginalKey := [(Sum.inl 1315, 5)]

def keyMomentRow1051 : Integer.Sparse OriginalKey := [(Sum.inl 1385, 5)]

def keyMomentRow1052 : Integer.Sparse OriginalKey := [(Sum.inl 1326, 5)]

def keyMomentRow1053 : Integer.Sparse OriginalKey := [(Sum.inl 1436, 5)]

def keyMomentRow1054 : Integer.Sparse OriginalKey := [(Sum.inl 1367, 5)]

def keyMomentRow1055 : Integer.Sparse OriginalKey := [(Sum.inl 1406, 5)]

def keyMomentChunk32 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1024, keyMomentRow1025, keyMomentRow1026, keyMomentRow1027, keyMomentRow1028, keyMomentRow1029, keyMomentRow1030, keyMomentRow1031, keyMomentRow1032, keyMomentRow1033, keyMomentRow1034, keyMomentRow1035, keyMomentRow1036, keyMomentRow1037, keyMomentRow1038, keyMomentRow1039, keyMomentRow1040, keyMomentRow1041, keyMomentRow1042, keyMomentRow1043, keyMomentRow1044, keyMomentRow1045, keyMomentRow1046, keyMomentRow1047, keyMomentRow1048, keyMomentRow1049, keyMomentRow1050, keyMomentRow1051, keyMomentRow1052, keyMomentRow1053, keyMomentRow1054, keyMomentRow1055]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1056 : Integer.Sparse OriginalKey := [(Sum.inl 1321, 5)]

def keyMomentRow1057 : Integer.Sparse OriginalKey := [(Sum.inl 1335, 5)]

def keyMomentRow1058 : Integer.Sparse OriginalKey := [(Sum.inl 1330, 5)]

def keyMomentRow1059 : Integer.Sparse OriginalKey := [(Sum.inl 1314, 5)]

def keyMomentRow1060 : Integer.Sparse OriginalKey := [(Sum.inl 1383, 5)]

def keyMomentRow1061 : Integer.Sparse OriginalKey := [(Sum.inl 1375, 5)]

def keyMomentRow1062 : Integer.Sparse OriginalKey := [(Sum.inl 1325, 5)]

def keyMomentRow1063 : Integer.Sparse OriginalKey := [(Sum.inl 1338, 5)]

def keyMomentRow1064 : Integer.Sparse OriginalKey := [(Sum.inl 1334, 5)]

def keyMomentRow1065 : Integer.Sparse OriginalKey := [(Sum.inl 1318, 5)]

def keyMomentRow1066 : Integer.Sparse OriginalKey := [(Sum.inl 1391, 5)]

def keyMomentRow1067 : Integer.Sparse OriginalKey := [(Sum.inl 1328, 5)]

def keyMomentRow1068 : Integer.Sparse OriginalKey := [(Sum.inl 1435, 5)]

def keyMomentRow1069 : Integer.Sparse OriginalKey := [(Sum.inl 1366, 5)]

def keyMomentRow1070 : Integer.Sparse OriginalKey := [(Sum.inl 1319, 5)]

def keyMomentRow1071 : Integer.Sparse OriginalKey := [(Sum.inl 1370, 5)]

def keyMomentRow1072 : Integer.Sparse OriginalKey := [(Sum.inl 1320, 5)]

def keyMomentRow1073 : Integer.Sparse OriginalKey := [(Sum.inl 1316, 5)]

def keyMomentRow1074 : Integer.Sparse OriginalKey := [(Sum.inl 1372, 5)]

def keyMomentRow1075 : Integer.Sparse OriginalKey := [(Sum.inl 1142, 5)]

def keyMomentRow1076 : Integer.Sparse OriginalKey := [(Sum.inl 1337, 5)]

def keyMomentRow1077 : Integer.Sparse OriginalKey := [(Sum.inl 1118, 5)]

def keyMomentRow1078 : Integer.Sparse OriginalKey := [(Sum.inl 1317, 5)]

def keyMomentRow1079 : Integer.Sparse OriginalKey := [(Sum.inl 1388, 5)]

def keyMomentRow1080 : Integer.Sparse OriginalKey := [(Sum.inl 1322, 5)]

def keyMomentRow1081 : Integer.Sparse OriginalKey := [(Sum.inl 1327, 5)]

def keyMomentRow1082 : Integer.Sparse OriginalKey := [(Sum.inl 1064, 5)]

def keyMomentRow1083 : Integer.Sparse OriginalKey := [(Sum.inl 617, 5)]

def keyMomentRow1084 : Integer.Sparse OriginalKey := [(Sum.inl 951, 5)]

def keyMomentRow1085 : Integer.Sparse OriginalKey := [(Sum.inl 587, 5)]

def keyMomentRow1086 : Integer.Sparse OriginalKey := [(Sum.inl 936, 5)]

def keyMomentRow1087 : Integer.Sparse OriginalKey := [(Sum.inl 1027, 5)]

def keyMomentChunk33 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1056, keyMomentRow1057, keyMomentRow1058, keyMomentRow1059, keyMomentRow1060, keyMomentRow1061, keyMomentRow1062, keyMomentRow1063, keyMomentRow1064, keyMomentRow1065, keyMomentRow1066, keyMomentRow1067, keyMomentRow1068, keyMomentRow1069, keyMomentRow1070, keyMomentRow1071, keyMomentRow1072, keyMomentRow1073, keyMomentRow1074, keyMomentRow1075, keyMomentRow1076, keyMomentRow1077, keyMomentRow1078, keyMomentRow1079, keyMomentRow1080, keyMomentRow1081, keyMomentRow1082, keyMomentRow1083, keyMomentRow1084, keyMomentRow1085, keyMomentRow1086, keyMomentRow1087]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1088 : Integer.Sparse OriginalKey := [(Sum.inl 1324, 5)]

def keyMomentRow1089 : Integer.Sparse OriginalKey := [(Sum.inl 911, 5)]

def keyMomentRow1090 : Integer.Sparse OriginalKey := [(Sum.inl 1333, 5)]

def keyMomentRow1091 : Integer.Sparse OriginalKey := [(Sum.inl 654, 5)]

def keyMomentRow1092 : Integer.Sparse OriginalKey := [(Sum.inl 639, 5)]

def keyMomentRow1093 : Integer.Sparse OriginalKey := [(Sum.inl 634, 5)]

def keyMomentRow1094 : Integer.Sparse OriginalKey := [(Sum.inl 624, 5)]

def keyMomentRow1095 : Integer.Sparse OriginalKey := [(Sum.inl 653, 5)]

def keyMomentRow1096 : Integer.Sparse OriginalKey := [(Sum.inl 638, 5)]

def keyMomentRow1097 : Integer.Sparse OriginalKey := [(Sum.inl 631, 5)]

def keyMomentRow1098 : Integer.Sparse OriginalKey := [(Sum.inl 623, 5)]

def keyMomentRow1099 : Integer.Sparse OriginalKey := [(Sum.inl 642, 5)]

def keyMomentRow1100 : Integer.Sparse OriginalKey := [(Sum.inl 636, 5)]

def keyMomentRow1101 : Integer.Sparse OriginalKey := [(Sum.inl 627, 5)]

def keyMomentRow1102 : Integer.Sparse OriginalKey := [(Sum.inl 637, 5)]

def keyMomentRow1103 : Integer.Sparse OriginalKey := [(Sum.inl 629, 5)]

def keyMomentRow1104 : Integer.Sparse OriginalKey := [(Sum.inl 640, 5)]

def keyMomentRow1105 : Integer.Sparse OriginalKey := [(Sum.inl 630, 5)]

def keyMomentRow1106 : Integer.Sparse OriginalKey := [(Sum.inl 641, 5)]

def keyMomentRow1107 : Integer.Sparse OriginalKey := [(Sum.inl 633, 5)]

def keyMomentRow1108 : Integer.Sparse OriginalKey := [(Sum.inl 626, 5)]

def keyMomentRow1109 : Integer.Sparse OriginalKey := [(Sum.inl 643, 5)]

def keyMomentRow1110 : Integer.Sparse OriginalKey := [(Sum.inl 591, 5)]

def keyMomentRow1111 : Integer.Sparse OriginalKey := [(Sum.inl 628, 5)]

def keyMomentRow1112 : Integer.Sparse OriginalKey := [(Sum.inl 635, 5)]

def keyMomentRow1113 : Integer.Sparse OriginalKey := [(Sum.inl 2740, 5)]

def keyMomentRow1114 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 5)]

def keyMomentRow1115 : Integer.Sparse OriginalKey := [(Sum.inl 3547, 5)]

def keyMomentRow1116 : Integer.Sparse OriginalKey := [(Sum.inl 3548, 5)]

def keyMomentRow1117 : Integer.Sparse OriginalKey := [(Sum.inl 3549, 5)]

def keyMomentRow1118 : Integer.Sparse OriginalKey := [(Sum.inl 3075, 5)]

def keyMomentRow1119 : Integer.Sparse OriginalKey := [(Sum.inl 3534, 5)]

def keyMomentChunk34 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1088, keyMomentRow1089, keyMomentRow1090, keyMomentRow1091, keyMomentRow1092, keyMomentRow1093, keyMomentRow1094, keyMomentRow1095, keyMomentRow1096, keyMomentRow1097, keyMomentRow1098, keyMomentRow1099, keyMomentRow1100, keyMomentRow1101, keyMomentRow1102, keyMomentRow1103, keyMomentRow1104, keyMomentRow1105, keyMomentRow1106, keyMomentRow1107, keyMomentRow1108, keyMomentRow1109, keyMomentRow1110, keyMomentRow1111, keyMomentRow1112, keyMomentRow1113, keyMomentRow1114, keyMomentRow1115, keyMomentRow1116, keyMomentRow1117, keyMomentRow1118, keyMomentRow1119]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1120 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 5)]

def keyMomentRow1121 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 5)]

def keyMomentRow1122 : Integer.Sparse OriginalKey := [(Sum.inl 3525, 5)]

def keyMomentRow1123 : Integer.Sparse OriginalKey := [(Sum.inl 3526, 5)]

def keyMomentRow1124 : Integer.Sparse OriginalKey := [(Sum.inl 2783, 5)]

def keyMomentRow1125 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 5)]

def keyMomentRow1126 : Integer.Sparse OriginalKey := [(Sum.inl 3583, 5)]

def keyMomentRow1127 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 5)]

def keyMomentRow1128 : Integer.Sparse OriginalKey := [(Sum.inl 3572, 5)]

def keyMomentRow1129 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 5)]

def keyMomentRow1130 : Integer.Sparse OriginalKey := [(Sum.inl 2789, 5)]

def keyMomentRow1131 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 5)]

def keyMomentRow1132 : Integer.Sparse OriginalKey := [(Sum.inl 3636, 5)]

def keyMomentRow1133 : Integer.Sparse OriginalKey := [(Sum.inl 3629, 5)]

def keyMomentRow1134 : Integer.Sparse OriginalKey := [(Sum.inl 3633, 5)]

def keyMomentRow1135 : Integer.Sparse OriginalKey := [(Sum.inl 2294, 5)]

def keyMomentRow1136 : Integer.Sparse OriginalKey := [(Sum.inl 3635, 5)]

def keyMomentRow1137 : Integer.Sparse OriginalKey := [(Sum.inl 3623, 5)]

def keyMomentRow1138 : Integer.Sparse OriginalKey := [(Sum.inl 3626, 5)]

def keyMomentRow1139 : Integer.Sparse OriginalKey := [(Sum.inl 3627, 5)]

def keyMomentRow1140 : Integer.Sparse OriginalKey := [(Sum.inl 3628, 5)]

def keyMomentRow1141 : Integer.Sparse OriginalKey := [(Sum.inl 3632, 5)]

def keyMomentRow1142 : Integer.Sparse OriginalKey := [(Sum.inl 3619, 5)]

def keyMomentRow1143 : Integer.Sparse OriginalKey := [(Sum.inl 3622, 5)]

def keyMomentRow1144 : Integer.Sparse OriginalKey := [(Sum.inl 3625, 5)]

def keyMomentRow1145 : Integer.Sparse OriginalKey := [(Sum.inl 3618, 5)]

def keyMomentRow1146 : Integer.Sparse OriginalKey := [(Sum.inl 4084, 5)]

def keyMomentRow1147 : Integer.Sparse OriginalKey := [(Sum.inl 2742, 5)]

def keyMomentRow1148 : Integer.Sparse OriginalKey := [(Sum.inl 3054, 5)]

def keyMomentRow1149 : Integer.Sparse OriginalKey := [(Sum.inl 4092, 5)]

def keyMomentRow1150 : Integer.Sparse OriginalKey := [(Sum.inl 3817, 5)]

def keyMomentRow1151 : Integer.Sparse OriginalKey := [(Sum.inl 3626, 5)]

def keyMomentChunk35 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1120, keyMomentRow1121, keyMomentRow1122, keyMomentRow1123, keyMomentRow1124, keyMomentRow1125, keyMomentRow1126, keyMomentRow1127, keyMomentRow1128, keyMomentRow1129, keyMomentRow1130, keyMomentRow1131, keyMomentRow1132, keyMomentRow1133, keyMomentRow1134, keyMomentRow1135, keyMomentRow1136, keyMomentRow1137, keyMomentRow1138, keyMomentRow1139, keyMomentRow1140, keyMomentRow1141, keyMomentRow1142, keyMomentRow1143, keyMomentRow1144, keyMomentRow1145, keyMomentRow1146, keyMomentRow1147, keyMomentRow1148, keyMomentRow1149, keyMomentRow1150, keyMomentRow1151]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1152 : Integer.Sparse OriginalKey := [(Sum.inl 3077, 5)]

def keyMomentRow1153 : Integer.Sparse OriginalKey := [(Sum.inl 3807, 5)]

def keyMomentRow1154 : Integer.Sparse OriginalKey := [(Sum.inl 3808, 5)]

def keyMomentRow1155 : Integer.Sparse OriginalKey := [(Sum.inl 3809, 5)]

def keyMomentRow1156 : Integer.Sparse OriginalKey := [(Sum.inl 3813, 5)]

def keyMomentRow1157 : Integer.Sparse OriginalKey := [(Sum.inl 3814, 5)]

def keyMomentRow1158 : Integer.Sparse OriginalKey := [(Sum.inl 3816, 5)]

def keyMomentRow1159 : Integer.Sparse OriginalKey := [(Sum.inl 4091, 5)]

def keyMomentRow1160 : Integer.Sparse OriginalKey := [(Sum.inl 3800, 5)]

def keyMomentRow1161 : Integer.Sparse OriginalKey := [(Sum.inl 3801, 5)]

def keyMomentRow1162 : Integer.Sparse OriginalKey := [(Sum.inl 3805, 5)]

def keyMomentRow1163 : Integer.Sparse OriginalKey := [(Sum.inl 3806, 5)]

def keyMomentRow1164 : Integer.Sparse OriginalKey := [(Sum.inl 3812, 5)]

def keyMomentRow1165 : Integer.Sparse OriginalKey := [(Sum.inl 2264, 5)]

def keyMomentRow1166 : Integer.Sparse OriginalKey := [(Sum.inl 2722, 5)]

def keyMomentRow1167 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 5)]

def keyMomentRow1168 : Integer.Sparse OriginalKey := [(Sum.inl 3807, 5)]

def keyMomentRow1169 : Integer.Sparse OriginalKey := [(Sum.inl 3845, 5)]

def keyMomentRow1170 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 5)]

def keyMomentRow1171 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 5)]

def keyMomentRow1172 : Integer.Sparse OriginalKey := [(Sum.inl 3837, 5)]

def keyMomentRow1173 : Integer.Sparse OriginalKey := [(Sum.inl 3838, 5)]

def keyMomentRow1174 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 5)]

def keyMomentRow1175 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 5)]

def keyMomentRow1176 : Integer.Sparse OriginalKey := [(Sum.inl 3841, 5)]

def keyMomentRow1177 : Integer.Sparse OriginalKey := [(Sum.inl 3843, 5)]

def keyMomentRow1178 : Integer.Sparse OriginalKey := [(Sum.inl 3844, 5)]

def keyMomentRow1179 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 5)]

def keyMomentRow1180 : Integer.Sparse OriginalKey := [(Sum.inl 3850, 5)]

def keyMomentRow1181 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 5)]

def keyMomentRow1182 : Integer.Sparse OriginalKey := [(Sum.inl 3854, 5)]

def keyMomentRow1183 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 5)]

def keyMomentChunk36 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1152, keyMomentRow1153, keyMomentRow1154, keyMomentRow1155, keyMomentRow1156, keyMomentRow1157, keyMomentRow1158, keyMomentRow1159, keyMomentRow1160, keyMomentRow1161, keyMomentRow1162, keyMomentRow1163, keyMomentRow1164, keyMomentRow1165, keyMomentRow1166, keyMomentRow1167, keyMomentRow1168, keyMomentRow1169, keyMomentRow1170, keyMomentRow1171, keyMomentRow1172, keyMomentRow1173, keyMomentRow1174, keyMomentRow1175, keyMomentRow1176, keyMomentRow1177, keyMomentRow1178, keyMomentRow1179, keyMomentRow1180, keyMomentRow1181, keyMomentRow1182, keyMomentRow1183]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1184 : Integer.Sparse OriginalKey := [(Sum.inl 3846, 5)]

def keyMomentRow1185 : Integer.Sparse OriginalKey := [(Sum.inl 3037, 5)]

def keyMomentRow1186 : Integer.Sparse OriginalKey := [(Sum.inl 3848, 5)]

def keyMomentRow1187 : Integer.Sparse OriginalKey := [(Sum.inl 3849, 5)]

def keyMomentRow1188 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 5)]

def keyMomentRow1189 : Integer.Sparse OriginalKey := [(Sum.inl 2765, 5)]

def keyMomentRow1190 : Integer.Sparse OriginalKey := [(Sum.inl 3086, 5)]

def keyMomentRow1191 : Integer.Sparse OriginalKey := [(Sum.inl 3850, 5)]

def keyMomentRow1192 : Integer.Sparse OriginalKey := [(Sum.inl 3876, 5)]

def keyMomentRow1193 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 5)]

def keyMomentRow1194 : Integer.Sparse OriginalKey := [(Sum.inl 3871, 5)]

def keyMomentRow1195 : Integer.Sparse OriginalKey := [(Sum.inl 3872, 5)]

def keyMomentRow1196 : Integer.Sparse OriginalKey := [(Sum.inl 3874, 5)]

def keyMomentRow1197 : Integer.Sparse OriginalKey := [(Sum.inl 3875, 5)]

def keyMomentRow1198 : Integer.Sparse OriginalKey := [(Sum.inl 3886, 5)]

def keyMomentRow1199 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 5)]

def keyMomentRow1200 : Integer.Sparse OriginalKey := [(Sum.inl 3881, 5)]

def keyMomentRow1201 : Integer.Sparse OriginalKey := [(Sum.inl 3039, 5)]

def keyMomentRow1202 : Integer.Sparse OriginalKey := [(Sum.inl 3884, 5)]

def keyMomentRow1203 : Integer.Sparse OriginalKey := [(Sum.inl 3885, 5)]

def keyMomentRow1204 : Integer.Sparse OriginalKey := [(Sum.inl 2777, 5)]

def keyMomentRow1205 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 5)]

def keyMomentRow1206 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 5)]

def keyMomentRow1207 : Integer.Sparse OriginalKey := [(Sum.inl 2730, 5)]

def keyMomentRow1208 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 5)]

def keyMomentRow1209 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 5)]

def keyMomentRow1210 : Integer.Sparse OriginalKey := [(Sum.inl 2731, 5)]

def keyMomentRow1211 : Integer.Sparse OriginalKey := [(Sum.inl 3629, 5)]

def keyMomentRow1212 : Integer.Sparse OriginalKey := [(Sum.inl 3905, 5)]

def keyMomentRow1213 : Integer.Sparse OriginalKey := [(Sum.inl 3907, 5)]

def keyMomentRow1214 : Integer.Sparse OriginalKey := [(Sum.inl 2279, 5)]

def keyMomentRow1215 : Integer.Sparse OriginalKey := [(Sum.inl 3632, 5)]

def keyMomentChunk37 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1184, keyMomentRow1185, keyMomentRow1186, keyMomentRow1187, keyMomentRow1188, keyMomentRow1189, keyMomentRow1190, keyMomentRow1191, keyMomentRow1192, keyMomentRow1193, keyMomentRow1194, keyMomentRow1195, keyMomentRow1196, keyMomentRow1197, keyMomentRow1198, keyMomentRow1199, keyMomentRow1200, keyMomentRow1201, keyMomentRow1202, keyMomentRow1203, keyMomentRow1204, keyMomentRow1205, keyMomentRow1206, keyMomentRow1207, keyMomentRow1208, keyMomentRow1209, keyMomentRow1210, keyMomentRow1211, keyMomentRow1212, keyMomentRow1213, keyMomentRow1214, keyMomentRow1215]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1216 : Integer.Sparse OriginalKey := [(Sum.inl 3908, 5)]

def keyMomentRow1217 : Integer.Sparse OriginalKey := [(Sum.inl 3814, 5)]

def keyMomentRow1218 : Integer.Sparse OriginalKey := [(Sum.inl 3903, 5)]

def keyMomentRow1219 : Integer.Sparse OriginalKey := [(Sum.inl 3904, 5)]

def keyMomentRow1220 : Integer.Sparse OriginalKey := [(Sum.inl 3906, 5)]

def keyMomentRow1221 : Integer.Sparse OriginalKey := [(Sum.inl 2277, 5)]

def keyMomentRow1222 : Integer.Sparse OriginalKey := [(Sum.inl 3901, 5)]

def keyMomentRow1223 : Integer.Sparse OriginalKey := [(Sum.inl 3812, 5)]

def keyMomentRow1224 : Integer.Sparse OriginalKey := [(Sum.inl 2281, 5)]

def keyMomentRow1225 : Integer.Sparse OriginalKey := [(Sum.inl 3633, 5)]

def keyMomentRow1226 : Integer.Sparse OriginalKey := [(Sum.inl 3054, 5)]

def keyMomentRow1227 : Integer.Sparse OriginalKey := [(Sum.inl 3913, 5)]

def keyMomentRow1228 : Integer.Sparse OriginalKey := [(Sum.inl 3907, 5)]

def keyMomentRow1229 : Integer.Sparse OriginalKey := [(Sum.inl 2278, 5)]

def keyMomentRow1230 : Integer.Sparse OriginalKey := [(Sum.inl 3910, 5)]

def keyMomentRow1231 : Integer.Sparse OriginalKey := [(Sum.inl 3813, 5)]

def keyMomentRow1232 : Integer.Sparse OriginalKey := [(Sum.inl 2293, 5)]

def keyMomentRow1233 : Integer.Sparse OriginalKey := [(Sum.inl 2743, 5)]

def keyMomentRow1234 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 5)]

def keyMomentRow1235 : Integer.Sparse OriginalKey := [(Sum.inl 3817, 5)]

def keyMomentRow1236 : Integer.Sparse OriginalKey := [(Sum.inl 3963, 5)]

def keyMomentRow1237 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 5)]

def keyMomentRow1238 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 5)]

def keyMomentRow1239 : Integer.Sparse OriginalKey := [(Sum.inl 3845, 5)]

def keyMomentRow1240 : Integer.Sparse OriginalKey := [(Sum.inl 3958, 5)]

def keyMomentRow1241 : Integer.Sparse OriginalKey := [(Sum.inl 3959, 5)]

def keyMomentRow1242 : Integer.Sparse OriginalKey := [(Sum.inl 3884, 5)]

def keyMomentRow1243 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 5)]

def keyMomentRow1244 : Integer.Sparse OriginalKey := [(Sum.inl 3961, 5)]

def keyMomentRow1245 : Integer.Sparse OriginalKey := [(Sum.inl 3962, 5)]

def keyMomentRow1246 : Integer.Sparse OriginalKey := [(Sum.inl 3953, 5)]

def keyMomentRow1247 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 5)]

def keyMomentChunk38 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1216, keyMomentRow1217, keyMomentRow1218, keyMomentRow1219, keyMomentRow1220, keyMomentRow1221, keyMomentRow1222, keyMomentRow1223, keyMomentRow1224, keyMomentRow1225, keyMomentRow1226, keyMomentRow1227, keyMomentRow1228, keyMomentRow1229, keyMomentRow1230, keyMomentRow1231, keyMomentRow1232, keyMomentRow1233, keyMomentRow1234, keyMomentRow1235, keyMomentRow1236, keyMomentRow1237, keyMomentRow1238, keyMomentRow1239, keyMomentRow1240, keyMomentRow1241, keyMomentRow1242, keyMomentRow1243, keyMomentRow1244, keyMomentRow1245, keyMomentRow1246, keyMomentRow1247]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1248 : Integer.Sparse OriginalKey := [(Sum.inl 3956, 5)]

def keyMomentRow1249 : Integer.Sparse OriginalKey := [(Sum.inl 3957, 5)]

def keyMomentRow1250 : Integer.Sparse OriginalKey := [(Sum.inl 3874, 5)]

def keyMomentRow1251 : Integer.Sparse OriginalKey := [(Sum.inl 2265, 5)]

def keyMomentRow1252 : Integer.Sparse OriginalKey := [(Sum.inl 3808, 5)]

def keyMomentRow1253 : Integer.Sparse OriginalKey := [(Sum.inl 3958, 5)]

def keyMomentRow1254 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 5)]

def keyMomentRow1255 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 5)]

def keyMomentRow1256 : Integer.Sparse OriginalKey := [(Sum.inl 3880, 5)]

def keyMomentRow1257 : Integer.Sparse OriginalKey := [(Sum.inl 3872, 5)]

def keyMomentRow1258 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 5)]

def keyMomentRow1259 : Integer.Sparse OriginalKey := [(Sum.inl 2278, 5)]

def keyMomentRow1260 : Integer.Sparse OriginalKey := [(Sum.inl 2731, 5)]

def keyMomentRow1261 : Integer.Sparse OriginalKey := [(Sum.inl 3044, 5)]

def keyMomentRow1262 : Integer.Sparse OriginalKey := [(Sum.inl 3813, 5)]

def keyMomentRow1263 : Integer.Sparse OriginalKey := [(Sum.inl 3884, 5)]

def keyMomentRow1264 : Integer.Sparse OriginalKey := [(Sum.inl 3506, 5)]

def keyMomentRow1265 : Integer.Sparse OriginalKey := [(Sum.inl 3068, 5)]

def keyMomentRow1266 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 5)]

def keyMomentRow1267 : Integer.Sparse OriginalKey := [(Sum.inl 3880, 5)]

def keyMomentRow1268 : Integer.Sparse OriginalKey := [(Sum.inl 3730, 5)]

def keyMomentRow1269 : Integer.Sparse OriginalKey := [(Sum.inl 3826, 5)]

def keyMomentRow1270 : Integer.Sparse OriginalKey := [(Sum.inl 3723, 5)]

def keyMomentRow1271 : Integer.Sparse OriginalKey := [(Sum.inl 3848, 5)]

def keyMomentRow1272 : Integer.Sparse OriginalKey := [(Sum.inl 3909, 5)]

def keyMomentRow1273 : Integer.Sparse OriginalKey := [(Sum.inl 2244, 5)]

def keyMomentRow1274 : Integer.Sparse OriginalKey := [(Sum.inl 2709, 5)]

def keyMomentRow1275 : Integer.Sparse OriginalKey := [(Sum.inl 3029, 5)]

def keyMomentRow1276 : Integer.Sparse OriginalKey := [(Sum.inl 3800, 5)]

def keyMomentRow1277 : Integer.Sparse OriginalKey := [(Sum.inl 3953, 5)]

def keyMomentRow1278 : Integer.Sparse OriginalKey := [(Sum.inl 3505, 5)]

def keyMomentRow1279 : Integer.Sparse OriginalKey := [(Sum.inl 2952, 5)]

def keyMomentChunk39 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1248, keyMomentRow1249, keyMomentRow1250, keyMomentRow1251, keyMomentRow1252, keyMomentRow1253, keyMomentRow1254, keyMomentRow1255, keyMomentRow1256, keyMomentRow1257, keyMomentRow1258, keyMomentRow1259, keyMomentRow1260, keyMomentRow1261, keyMomentRow1262, keyMomentRow1263, keyMomentRow1264, keyMomentRow1265, keyMomentRow1266, keyMomentRow1267, keyMomentRow1268, keyMomentRow1269, keyMomentRow1270, keyMomentRow1271, keyMomentRow1272, keyMomentRow1273, keyMomentRow1274, keyMomentRow1275, keyMomentRow1276, keyMomentRow1277, keyMomentRow1278, keyMomentRow1279]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow128 : Integer.Sparse OriginalKey := [(Sum.inl 154, 5)]

def keyMomentRow129 : Integer.Sparse OriginalKey := [(Sum.inl 41, 5)]

def keyMomentRow130 : Integer.Sparse OriginalKey := [(Sum.inl 102, 5)]

def keyMomentRow131 : Integer.Sparse OriginalKey := [(Sum.inl 143, 5)]

def keyMomentRow132 : Integer.Sparse OriginalKey := [(Sum.inl 32, 5)]

def keyMomentRow133 : Integer.Sparse OriginalKey := [(Sum.inl 19, 5)]

def keyMomentRow134 : Integer.Sparse OriginalKey := [(Sum.inl 73, 5)]

def keyMomentRow135 : Integer.Sparse OriginalKey := [(Sum.inl 97, 5)]

def keyMomentRow136 : Integer.Sparse OriginalKey := [(Sum.inl 197, 5)]

def keyMomentRow137 : Integer.Sparse OriginalKey := [(Sum.inl 249, 5)]

def keyMomentRow138 : Integer.Sparse OriginalKey := [(Sum.inl 14, 5)]

def keyMomentRow139 : Integer.Sparse OriginalKey := [(Sum.inl 67, 5)]

def keyMomentRow140 : Integer.Sparse OriginalKey := [(Sum.inl 87, 5)]

def keyMomentRow141 : Integer.Sparse OriginalKey := [(Sum.inl 227, 5)]

def keyMomentRow142 : Integer.Sparse OriginalKey := [(Sum.inl 60, 5)]

def keyMomentRow143 : Integer.Sparse OriginalKey := [(Sum.inl 169, 5)]

def keyMomentRow144 : Integer.Sparse OriginalKey := [(Sum.inl 58, 5)]

def keyMomentRow145 : Integer.Sparse OriginalKey := [(Sum.inl 102, 5)]

def keyMomentRow146 : Integer.Sparse OriginalKey := [(Sum.inl 97, 5)]

def keyMomentRow147 : Integer.Sparse OriginalKey := [(Sum.inl 76, 5)]

def keyMomentRow148 : Integer.Sparse OriginalKey := [(Sum.inl 60, 5)]

def keyMomentRow149 : Integer.Sparse OriginalKey := [(Sum.inl 87, 5)]

def keyMomentRow150 : Integer.Sparse OriginalKey := [(Sum.inl 58, 5)]

def keyMomentRow151 : Integer.Sparse OriginalKey := [(Sum.inl 101, 5)]

def keyMomentRow152 : Integer.Sparse OriginalKey := [(Sum.inl 74, 5)]

def keyMomentRow153 : Integer.Sparse OriginalKey := [(Sum.inl 103, 5)]

def keyMomentRow154 : Integer.Sparse OriginalKey := [(Sum.inl 98, 5)]

def keyMomentRow155 : Integer.Sparse OriginalKey := [(Sum.inl 75, 5)]

def keyMomentRow156 : Integer.Sparse OriginalKey := [(Sum.inl 91, 5)]

def keyMomentRow157 : Integer.Sparse OriginalKey := [(Sum.inr 2, 5)]

def keyMomentRow158 : Integer.Sparse OriginalKey := [(Sum.inl 94, 5)]

def keyMomentRow159 : Integer.Sparse OriginalKey := [(Sum.inl 93, 5)]

def keyMomentChunk4 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow128, keyMomentRow129, keyMomentRow130, keyMomentRow131, keyMomentRow132, keyMomentRow133, keyMomentRow134, keyMomentRow135, keyMomentRow136, keyMomentRow137, keyMomentRow138, keyMomentRow139, keyMomentRow140, keyMomentRow141, keyMomentRow142, keyMomentRow143, keyMomentRow144, keyMomentRow145, keyMomentRow146, keyMomentRow147, keyMomentRow148, keyMomentRow149, keyMomentRow150, keyMomentRow151, keyMomentRow152, keyMomentRow153, keyMomentRow154, keyMomentRow155, keyMomentRow156, keyMomentRow157, keyMomentRow158, keyMomentRow159]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1280 : Integer.Sparse OriginalKey := [(Sum.inl 2951, 5)]

def keyMomentRow1281 : Integer.Sparse OriginalKey := [(Sum.inl 3827, 5)]

def keyMomentRow1282 : Integer.Sparse OriginalKey := [(Sum.inl 2933, 5)]

def keyMomentRow1283 : Integer.Sparse OriginalKey := [(Sum.inl 1292, 5)]

def keyMomentRow1284 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 5)]

def keyMomentRow1285 : Integer.Sparse OriginalKey := [(Sum.inl 1291, 5)]

def keyMomentRow1286 : Integer.Sparse OriginalKey := [(Sum.inl 2632, 5)]

def keyMomentRow1287 : Integer.Sparse OriginalKey := [(Sum.inl 1261, 5)]

def keyMomentRow1288 : Integer.Sparse OriginalKey := [(Sum.inl 2631, 5)]

def keyMomentRow1289 : Integer.Sparse OriginalKey := [(Sum.inl 1260, 5)]

def keyMomentRow1290 : Integer.Sparse OriginalKey := [(Sum.inl 2587, 5)]

def keyMomentRow1291 : Integer.Sparse OriginalKey := [(Sum.inl 2750, 5)]

def keyMomentRow1292 : Integer.Sparse OriginalKey := [(Sum.inl 2566, 5)]

def keyMomentRow1293 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 5)]

def keyMomentRow1294 : Integer.Sparse OriginalKey := [(Sum.inl 3092, 5)]

def keyMomentRow1295 : Integer.Sparse OriginalKey := [(Sum.inl 3854, 5)]

def keyMomentRow1296 : Integer.Sparse OriginalKey := [(Sum.inl 3881, 5)]

def keyMomentRow1297 : Integer.Sparse OriginalKey := [(Sum.inl 3733, 5)]

def keyMomentRow1298 : Integer.Sparse OriginalKey := [(Sum.inl 3827, 5)]

def keyMomentRow1299 : Integer.Sparse OriginalKey := [(Sum.inl 3724, 5)]

def keyMomentRow1300 : Integer.Sparse OriginalKey := [(Sum.inl 3819, 5)]

def keyMomentRow1301 : Integer.Sparse OriginalKey := [(Sum.inl 3846, 5)]

def keyMomentRow1302 : Integer.Sparse OriginalKey := [(Sum.inl 2751, 5)]

def keyMomentRow1303 : Integer.Sparse OriginalKey := [(Sum.inl 3949, 5)]

def keyMomentRow1304 : Integer.Sparse OriginalKey := [(Sum.inl 2955, 5)]

def keyMomentRow1305 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 5)]

def keyMomentRow1306 : Integer.Sparse OriginalKey := [(Sum.inl 1295, 5)]

def keyMomentRow1307 : Integer.Sparse OriginalKey := [(Sum.inl 2633, 5)]

def keyMomentRow1308 : Integer.Sparse OriginalKey := [(Sum.inl 1262, 5)]

def keyMomentRow1309 : Integer.Sparse OriginalKey := [(Sum.inl 2591, 5)]

def keyMomentRow1310 : Integer.Sparse OriginalKey := [(Sum.inl 2751, 5)]

def keyMomentRow1311 : Integer.Sparse OriginalKey := [(Sum.inl 2643, 5)]

def keyMomentChunk40 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1280, keyMomentRow1281, keyMomentRow1282, keyMomentRow1283, keyMomentRow1284, keyMomentRow1285, keyMomentRow1286, keyMomentRow1287, keyMomentRow1288, keyMomentRow1289, keyMomentRow1290, keyMomentRow1291, keyMomentRow1292, keyMomentRow1293, keyMomentRow1294, keyMomentRow1295, keyMomentRow1296, keyMomentRow1297, keyMomentRow1298, keyMomentRow1299, keyMomentRow1300, keyMomentRow1301, keyMomentRow1302, keyMomentRow1303, keyMomentRow1304, keyMomentRow1305, keyMomentRow1306, keyMomentRow1307, keyMomentRow1308, keyMomentRow1309, keyMomentRow1310, keyMomentRow1311]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1312 : Integer.Sparse OriginalKey := [(Sum.inl 2632, 5)]

def keyMomentRow1313 : Integer.Sparse OriginalKey := [(Sum.inl 2620, 5)]

def keyMomentRow1314 : Integer.Sparse OriginalKey := [(Sum.inl 2614, 5)]

def keyMomentRow1315 : Integer.Sparse OriginalKey := [(Sum.inl 2641, 5)]

def keyMomentRow1316 : Integer.Sparse OriginalKey := [(Sum.inl 2631, 5)]

def keyMomentRow1317 : Integer.Sparse OriginalKey := [(Sum.inl 2617, 5)]

def keyMomentRow1318 : Integer.Sparse OriginalKey := [(Sum.inl 2633, 5)]

def keyMomentRow1319 : Integer.Sparse OriginalKey := [(Sum.inl 2618, 5)]

def keyMomentRow1320 : Integer.Sparse OriginalKey := [(Sum.inl 2635, 5)]

def keyMomentRow1321 : Integer.Sparse OriginalKey := [(Sum.inl 1264, 5)]

def keyMomentRow1322 : Integer.Sparse OriginalKey := [(Sum.inl 2569, 5)]

def keyMomentRow1323 : Integer.Sparse OriginalKey := [(Sum.inl 3633, 5)]

def keyMomentRow1324 : Integer.Sparse OriginalKey := [(Sum.inl 3907, 5)]

def keyMomentRow1325 : Integer.Sparse OriginalKey := [(Sum.inl 3886, 5)]

def keyMomentRow1326 : Integer.Sparse OriginalKey := [(Sum.inl 2115, 5)]

def keyMomentRow1327 : Integer.Sparse OriginalKey := [(Sum.inl 3582, 5)]

def keyMomentRow1328 : Integer.Sparse OriginalKey := [(Sum.inl 3913, 5)]

def keyMomentRow1329 : Integer.Sparse OriginalKey := [(Sum.inl 3885, 5)]

def keyMomentRow1330 : Integer.Sparse OriginalKey := [(Sum.inl 3732, 5)]

def keyMomentRow1331 : Integer.Sparse OriginalKey := [(Sum.inl 3857, 5)]

def keyMomentRow1332 : Integer.Sparse OriginalKey := [(Sum.inl 3910, 5)]

def keyMomentRow1333 : Integer.Sparse OriginalKey := [(Sum.inl 3850, 5)]

def keyMomentRow1334 : Integer.Sparse OriginalKey := [(Sum.inl 2106, 5)]

def keyMomentRow1335 : Integer.Sparse OriginalKey := [(Sum.inl 3731, 5)]

def keyMomentRow1336 : Integer.Sparse OriginalKey := [(Sum.inl 3849, 5)]

def keyMomentRow1337 : Integer.Sparse OriginalKey := [(Sum.inl 3786, 5)]

def keyMomentRow1338 : Integer.Sparse OriginalKey := [(Sum.inl 3623, 5)]

def keyMomentRow1339 : Integer.Sparse OriginalKey := [(Sum.inl 3885, 5)]

def keyMomentRow1340 : Integer.Sparse OriginalKey := [(Sum.inl 2110, 5)]

def keyMomentRow1341 : Integer.Sparse OriginalKey := [(Sum.inl 4010, 5)]

def keyMomentRow1342 : Integer.Sparse OriginalKey := [(Sum.inl 3789, 5)]

def keyMomentRow1343 : Integer.Sparse OriginalKey := [(Sum.inl 3875, 5)]

def keyMomentChunk41 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1312, keyMomentRow1313, keyMomentRow1314, keyMomentRow1315, keyMomentRow1316, keyMomentRow1317, keyMomentRow1318, keyMomentRow1319, keyMomentRow1320, keyMomentRow1321, keyMomentRow1322, keyMomentRow1323, keyMomentRow1324, keyMomentRow1325, keyMomentRow1326, keyMomentRow1327, keyMomentRow1328, keyMomentRow1329, keyMomentRow1330, keyMomentRow1331, keyMomentRow1332, keyMomentRow1333, keyMomentRow1334, keyMomentRow1335, keyMomentRow1336, keyMomentRow1337, keyMomentRow1338, keyMomentRow1339, keyMomentRow1340, keyMomentRow1341, keyMomentRow1342, keyMomentRow1343]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1344 : Integer.Sparse OriginalKey := [(Sum.inl 2105, 5)]

def keyMomentRow1345 : Integer.Sparse OriginalKey := [(Sum.inl 2112, 5)]

def keyMomentRow1346 : Integer.Sparse OriginalKey := [(Sum.inl 2954, 5)]

def keyMomentRow1347 : Integer.Sparse OriginalKey := [(Sum.inl 3876, 5)]

def keyMomentRow1348 : Integer.Sparse OriginalKey := [(Sum.inl 3787, 5)]

def keyMomentRow1349 : Integer.Sparse OriginalKey := [(Sum.inl 1297, 5)]

def keyMomentRow1350 : Integer.Sparse OriginalKey := [(Sum.inl 2783, 5)]

def keyMomentRow1351 : Integer.Sparse OriginalKey := [(Sum.inl 1294, 5)]

def keyMomentRow1352 : Integer.Sparse OriginalKey := [(Sum.inl 2782, 5)]

def keyMomentRow1353 : Integer.Sparse OriginalKey := [(Sum.inl 2765, 5)]

def keyMomentRow1354 : Integer.Sparse OriginalKey := [(Sum.inl 2109, 5)]

def keyMomentRow1355 : Integer.Sparse OriginalKey := [(Sum.inl 2116, 5)]

def keyMomentRow1356 : Integer.Sparse OriginalKey := [(Sum.inl 2764, 5)]

def keyMomentRow1357 : Integer.Sparse OriginalKey := [(Sum.inl 2590, 5)]

def keyMomentRow1358 : Integer.Sparse OriginalKey := [(Sum.inl 2589, 5)]

def keyMomentRow1359 : Integer.Sparse OriginalKey := [(Sum.inl 2294, 5)]

def keyMomentRow1360 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 5)]

def keyMomentRow1361 : Integer.Sparse OriginalKey := [(Sum.inl 3056, 5)]

def keyMomentRow1362 : Integer.Sparse OriginalKey := [(Sum.inl 3626, 5)]

def keyMomentRow1363 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 5)]

def keyMomentRow1364 : Integer.Sparse OriginalKey := [(Sum.inl 3396, 5)]

def keyMomentRow1365 : Integer.Sparse OriginalKey := [(Sum.inl 3079, 5)]

def keyMomentRow1366 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 5)]

def keyMomentRow1367 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 5)]

def keyMomentRow1368 : Integer.Sparse OriginalKey := [(Sum.inl 3395, 5)]

def keyMomentRow1369 : Integer.Sparse OriginalKey := [(Sum.inl 3506, 5)]

def keyMomentRow1370 : Integer.Sparse OriginalKey := [(Sum.inl 3379, 5)]

def keyMomentRow1371 : Integer.Sparse OriginalKey := [(Sum.inl 3505, 5)]

def keyMomentRow1372 : Integer.Sparse OriginalKey := [(Sum.inl 3378, 5)]

def keyMomentRow1373 : Integer.Sparse OriginalKey := [(Sum.inl 2266, 5)]

def keyMomentRow1374 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 5)]

def keyMomentRow1375 : Integer.Sparse OriginalKey := [(Sum.inl 3040, 5)]

def keyMomentChunk42 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1344, keyMomentRow1345, keyMomentRow1346, keyMomentRow1347, keyMomentRow1348, keyMomentRow1349, keyMomentRow1350, keyMomentRow1351, keyMomentRow1352, keyMomentRow1353, keyMomentRow1354, keyMomentRow1355, keyMomentRow1356, keyMomentRow1357, keyMomentRow1358, keyMomentRow1359, keyMomentRow1360, keyMomentRow1361, keyMomentRow1362, keyMomentRow1363, keyMomentRow1364, keyMomentRow1365, keyMomentRow1366, keyMomentRow1367, keyMomentRow1368, keyMomentRow1369, keyMomentRow1370, keyMomentRow1371, keyMomentRow1372, keyMomentRow1373, keyMomentRow1374, keyMomentRow1375]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1376 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 5)]

def keyMomentRow1377 : Integer.Sparse OriginalKey := [(Sum.inl 3809, 5)]

def keyMomentRow1378 : Integer.Sparse OriginalKey := [(Sum.inl 3959, 5)]

def keyMomentRow1379 : Integer.Sparse OriginalKey := [(Sum.inl 3395, 5)]

def keyMomentRow1380 : Integer.Sparse OriginalKey := [(Sum.inl 3066, 5)]

def keyMomentRow1381 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 5)]

def keyMomentRow1382 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 5)]

def keyMomentRow1383 : Integer.Sparse OriginalKey := [(Sum.inl 4022, 5)]

def keyMomentRow1384 : Integer.Sparse OriginalKey := [(Sum.inl 3730, 5)]

def keyMomentRow1385 : Integer.Sparse OriginalKey := [(Sum.inl 3722, 5)]

def keyMomentRow1386 : Integer.Sparse OriginalKey := [(Sum.inl 4024, 5)]

def keyMomentRow1387 : Integer.Sparse OriginalKey := [(Sum.inl 4025, 5)]

def keyMomentRow1388 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 5)]

def keyMomentRow1389 : Integer.Sparse OriginalKey := [(Sum.inl 2888, 5)]

def keyMomentRow1390 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 5)]

def keyMomentRow1391 : Integer.Sparse OriginalKey := [(Sum.inl 2885, 5)]

def keyMomentRow1392 : Integer.Sparse OriginalKey := [(Sum.inl 3733, 5)]

def keyMomentRow1393 : Integer.Sparse OriginalKey := [(Sum.inl 2867, 5)]

def keyMomentRow1394 : Integer.Sparse OriginalKey := [(Sum.inl 3949, 5)]

def keyMomentRow1395 : Integer.Sparse OriginalKey := [(Sum.inl 2864, 5)]

def keyMomentRow1396 : Integer.Sparse OriginalKey := [(Sum.inl 3946, 5)]

def keyMomentRow1397 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 5)]

def keyMomentRow1398 : Integer.Sparse OriginalKey := [(Sum.inl 3720, 5)]

def keyMomentRow1399 : Integer.Sparse OriginalKey := [(Sum.inl 2279, 5)]

def keyMomentRow1400 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 5)]

def keyMomentRow1401 : Integer.Sparse OriginalKey := [(Sum.inl 3045, 5)]

def keyMomentRow1402 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 5)]

def keyMomentRow1403 : Integer.Sparse OriginalKey := [(Sum.inl 3814, 5)]

def keyMomentRow1404 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 5)]

def keyMomentRow1405 : Integer.Sparse OriginalKey := [(Sum.inl 3379, 5)]

def keyMomentRow1406 : Integer.Sparse OriginalKey := [(Sum.inl 3069, 5)]

def keyMomentRow1407 : Integer.Sparse OriginalKey := [(Sum.inl 3841, 5)]

def keyMomentChunk43 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1376, keyMomentRow1377, keyMomentRow1378, keyMomentRow1379, keyMomentRow1380, keyMomentRow1381, keyMomentRow1382, keyMomentRow1383, keyMomentRow1384, keyMomentRow1385, keyMomentRow1386, keyMomentRow1387, keyMomentRow1388, keyMomentRow1389, keyMomentRow1390, keyMomentRow1391, keyMomentRow1392, keyMomentRow1393, keyMomentRow1394, keyMomentRow1395, keyMomentRow1396, keyMomentRow1397, keyMomentRow1398, keyMomentRow1399, keyMomentRow1400, keyMomentRow1401, keyMomentRow1402, keyMomentRow1403, keyMomentRow1404, keyMomentRow1405, keyMomentRow1406, keyMomentRow1407]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1408 : Integer.Sparse OriginalKey := [(Sum.inl 3872, 5)]

def keyMomentRow1409 : Integer.Sparse OriginalKey := [(Sum.inl 3722, 5)]

def keyMomentRow1410 : Integer.Sparse OriginalKey := [(Sum.inl 3723, 5)]

def keyMomentRow1411 : Integer.Sparse OriginalKey := [(Sum.inl 3715, 5)]

def keyMomentRow1412 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 5)]

def keyMomentRow1413 : Integer.Sparse OriginalKey := [(Sum.inl 3899, 5)]

def keyMomentRow1414 : Integer.Sparse OriginalKey := [(Sum.inl 2245, 5)]

def keyMomentRow1415 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 5)]

def keyMomentRow1416 : Integer.Sparse OriginalKey := [(Sum.inl 3030, 5)]

def keyMomentRow1417 : Integer.Sparse OriginalKey := [(Sum.inl 3378, 5)]

def keyMomentRow1418 : Integer.Sparse OriginalKey := [(Sum.inl 2930, 5)]

def keyMomentRow1419 : Integer.Sparse OriginalKey := [(Sum.inl 2928, 5)]

def keyMomentRow1420 : Integer.Sparse OriginalKey := [(Sum.inl 2916, 5)]

def keyMomentRow1421 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 5)]

def keyMomentRow1422 : Integer.Sparse OriginalKey := [(Sum.inl 1245, 5)]

def keyMomentRow1423 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 5)]

def keyMomentRow1424 : Integer.Sparse OriginalKey := [(Sum.inl 1241, 5)]

def keyMomentRow1425 : Integer.Sparse OriginalKey := [(Sum.inl 2620, 5)]

def keyMomentRow1426 : Integer.Sparse OriginalKey := [(Sum.inl 1219, 5)]

def keyMomentRow1427 : Integer.Sparse OriginalKey := [(Sum.inl 2617, 5)]

def keyMomentRow1428 : Integer.Sparse OriginalKey := [(Sum.inl 1216, 5)]

def keyMomentRow1429 : Integer.Sparse OriginalKey := [(Sum.inl 2557, 5)]

def keyMomentRow1430 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 5)]

def keyMomentRow1431 : Integer.Sparse OriginalKey := [(Sum.inl 2545, 5)]

def keyMomentRow1432 : Integer.Sparse OriginalKey := [(Sum.inl 2284, 5)]

def keyMomentRow1433 : Integer.Sparse OriginalKey := [(Sum.inl 2133, 5)]

def keyMomentRow1434 : Integer.Sparse OriginalKey := [(Sum.inl 1826, 5)]

def keyMomentRow1435 : Integer.Sparse OriginalKey := [(Sum.inl 2253, 5)]

def keyMomentRow1436 : Integer.Sparse OriginalKey := [(Sum.inl 2108, 5)]

def keyMomentRow1437 : Integer.Sparse OriginalKey := [(Sum.inl 1809, 5)]

def keyMomentRow1438 : Integer.Sparse OriginalKey := [(Sum.inl 1824, 5)]

def keyMomentRow1439 : Integer.Sparse OriginalKey := [(Sum.inl 2089, 5)]

def keyMomentChunk44 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1408, keyMomentRow1409, keyMomentRow1410, keyMomentRow1411, keyMomentRow1412, keyMomentRow1413, keyMomentRow1414, keyMomentRow1415, keyMomentRow1416, keyMomentRow1417, keyMomentRow1418, keyMomentRow1419, keyMomentRow1420, keyMomentRow1421, keyMomentRow1422, keyMomentRow1423, keyMomentRow1424, keyMomentRow1425, keyMomentRow1426, keyMomentRow1427, keyMomentRow1428, keyMomentRow1429, keyMomentRow1430, keyMomentRow1431, keyMomentRow1432, keyMomentRow1433, keyMomentRow1434, keyMomentRow1435, keyMomentRow1436, keyMomentRow1437, keyMomentRow1438, keyMomentRow1439]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1440 : Integer.Sparse OriginalKey := [(Sum.inl 1806, 5)]

def keyMomentRow1441 : Integer.Sparse OriginalKey := [(Sum.inl 1791, 5)]

def keyMomentRow1442 : Integer.Sparse OriginalKey := [(Sum.inl 2253, 5)]

def keyMomentRow1443 : Integer.Sparse OriginalKey := [(Sum.inl 2714, 5)]

def keyMomentRow1444 : Integer.Sparse OriginalKey := [(Sum.inl 3032, 5)]

def keyMomentRow1445 : Integer.Sparse OriginalKey := [(Sum.inl 3803, 5)]

def keyMomentRow1446 : Integer.Sparse OriginalKey := [(Sum.inl 3788, 5)]

def keyMomentRow1447 : Integer.Sparse OriginalKey := [(Sum.inl 3365, 5)]

def keyMomentRow1448 : Integer.Sparse OriginalKey := [(Sum.inl 3577, 5)]

def keyMomentRow1449 : Integer.Sparse OriginalKey := [(Sum.inl 2812, 5)]

def keyMomentRow1450 : Integer.Sparse OriginalKey := [(Sum.inl 3698, 5)]

def keyMomentRow1451 : Integer.Sparse OriginalKey := [(Sum.inl 2810, 5)]

def keyMomentRow1452 : Integer.Sparse OriginalKey := [(Sum.inl 3674, 5)]

def keyMomentRow1453 : Integer.Sparse OriginalKey := [(Sum.inl 2798, 5)]

def keyMomentRow1454 : Integer.Sparse OriginalKey := [(Sum.inl 2233, 5)]

def keyMomentRow1455 : Integer.Sparse OriginalKey := [(Sum.inl 2892, 5)]

def keyMomentRow1456 : Integer.Sparse OriginalKey := [(Sum.inl 2513, 5)]

def keyMomentRow1457 : Integer.Sparse OriginalKey := [(Sum.inl 1133, 5)]

def keyMomentRow1458 : Integer.Sparse OriginalKey := [(Sum.inl 2494, 5)]

def keyMomentRow1459 : Integer.Sparse OriginalKey := [(Sum.inl 1130, 5)]

def keyMomentRow1460 : Integer.Sparse OriginalKey := [(Sum.inl 2438, 5)]

def keyMomentRow1461 : Integer.Sparse OriginalKey := [(Sum.inl 1113, 5)]

def keyMomentRow1462 : Integer.Sparse OriginalKey := [(Sum.inl 607, 5)]

def keyMomentRow1463 : Integer.Sparse OriginalKey := [(Sum.inl 1058, 5)]

def keyMomentRow1464 : Integer.Sparse OriginalKey := [(Sum.inl 604, 5)]

def keyMomentRow1465 : Integer.Sparse OriginalKey := [(Sum.inl 946, 5)]

def keyMomentRow1466 : Integer.Sparse OriginalKey := [(Sum.inl 582, 5)]

def keyMomentRow1467 : Integer.Sparse OriginalKey := [(Sum.inl 944, 5)]

def keyMomentRow1468 : Integer.Sparse OriginalKey := [(Sum.inl 580, 5)]

def keyMomentRow1469 : Integer.Sparse OriginalKey := [(Sum.inl 2138, 5)]

def keyMomentRow1470 : Integer.Sparse OriginalKey := [(Sum.inl 1829, 5)]

def keyMomentRow1471 : Integer.Sparse OriginalKey := [(Sum.inl 2039, 5)]

def keyMomentChunk45 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1440, keyMomentRow1441, keyMomentRow1442, keyMomentRow1443, keyMomentRow1444, keyMomentRow1445, keyMomentRow1446, keyMomentRow1447, keyMomentRow1448, keyMomentRow1449, keyMomentRow1450, keyMomentRow1451, keyMomentRow1452, keyMomentRow1453, keyMomentRow1454, keyMomentRow1455, keyMomentRow1456, keyMomentRow1457, keyMomentRow1458, keyMomentRow1459, keyMomentRow1460, keyMomentRow1461, keyMomentRow1462, keyMomentRow1463, keyMomentRow1464, keyMomentRow1465, keyMomentRow1466, keyMomentRow1467, keyMomentRow1468, keyMomentRow1469, keyMomentRow1470, keyMomentRow1471]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1472 : Integer.Sparse OriginalKey := [(Sum.inl 2094, 5)]

def keyMomentRow1473 : Integer.Sparse OriginalKey := [(Sum.inl 1816, 5)]

def keyMomentRow1474 : Integer.Sparse OriginalKey := [(Sum.inl 1977, 5)]

def keyMomentRow1475 : Integer.Sparse OriginalKey := [(Sum.inl 1794, 5)]

def keyMomentRow1476 : Integer.Sparse OriginalKey := [(Sum.inl 2758, 5)]

def keyMomentRow1477 : Integer.Sparse OriginalKey := [(Sum.inl 3083, 5)]

def keyMomentRow1478 : Integer.Sparse OriginalKey := [(Sum.inl 3780, 5)]

def keyMomentRow1479 : Integer.Sparse OriginalKey := [(Sum.inl 3783, 5)]

def keyMomentRow1480 : Integer.Sparse OriginalKey := [(Sum.inl 3710, 5)]

def keyMomentRow1481 : Integer.Sparse OriginalKey := [(Sum.inl 3699, 5)]

def keyMomentRow1482 : Integer.Sparse OriginalKey := [(Sum.inl 2819, 5)]

def keyMomentRow1483 : Integer.Sparse OriginalKey := [(Sum.inl 3676, 5)]

def keyMomentRow1484 : Integer.Sparse OriginalKey := [(Sum.inl 2801, 5)]

def keyMomentRow1485 : Integer.Sparse OriginalKey := [(Sum.inl 3673, 5)]

def keyMomentRow1486 : Integer.Sparse OriginalKey := [(Sum.inl 3685, 5)]

def keyMomentRow1487 : Integer.Sparse OriginalKey := [(Sum.inl 2745, 5)]

def keyMomentRow1488 : Integer.Sparse OriginalKey := [(Sum.inl 2898, 5)]

def keyMomentRow1489 : Integer.Sparse OriginalKey := [(Sum.inl 2499, 5)]

def keyMomentRow1490 : Integer.Sparse OriginalKey := [(Sum.inl 1141, 5)]

def keyMomentRow1491 : Integer.Sparse OriginalKey := [(Sum.inl 2441, 5)]

def keyMomentRow1492 : Integer.Sparse OriginalKey := [(Sum.inl 1117, 5)]

def keyMomentRow1493 : Integer.Sparse OriginalKey := [(Sum.inl 2433, 5)]

def keyMomentRow1494 : Integer.Sparse OriginalKey := [(Sum.inl 2473, 5)]

def keyMomentRow1495 : Integer.Sparse OriginalKey := [(Sum.inl 1063, 5)]

def keyMomentRow1496 : Integer.Sparse OriginalKey := [(Sum.inl 616, 5)]

def keyMomentRow1497 : Integer.Sparse OriginalKey := [(Sum.inl 950, 5)]

def keyMomentRow1498 : Integer.Sparse OriginalKey := [(Sum.inl 586, 5)]

def keyMomentRow1499 : Integer.Sparse OriginalKey := [(Sum.inl 1830, 5)]

def keyMomentRow1500 : Integer.Sparse OriginalKey := [(Sum.inl 1978, 5)]

def keyMomentRow1501 : Integer.Sparse OriginalKey := [(Sum.inl 1795, 5)]

def keyMomentRow1502 : Integer.Sparse OriginalKey := [(Sum.inl 2362, 5)]

def keyMomentRow1503 : Integer.Sparse OriginalKey := [(Sum.inl 2353, 5)]

def keyMomentChunk46 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1472, keyMomentRow1473, keyMomentRow1474, keyMomentRow1475, keyMomentRow1476, keyMomentRow1477, keyMomentRow1478, keyMomentRow1479, keyMomentRow1480, keyMomentRow1481, keyMomentRow1482, keyMomentRow1483, keyMomentRow1484, keyMomentRow1485, keyMomentRow1486, keyMomentRow1487, keyMomentRow1488, keyMomentRow1489, keyMomentRow1490, keyMomentRow1491, keyMomentRow1492, keyMomentRow1493, keyMomentRow1494, keyMomentRow1495, keyMomentRow1496, keyMomentRow1497, keyMomentRow1498, keyMomentRow1499, keyMomentRow1500, keyMomentRow1501, keyMomentRow1502, keyMomentRow1503]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1504 : Integer.Sparse OriginalKey := [(Sum.inl 2350, 5)]

def keyMomentRow1505 : Integer.Sparse OriginalKey := [(Sum.inl 2356, 5)]

def keyMomentRow1506 : Integer.Sparse OriginalKey := [(Sum.inl 2352, 5)]

def keyMomentRow1507 : Integer.Sparse OriginalKey := [(Sum.inl 2348, 5)]

def keyMomentRow1508 : Integer.Sparse OriginalKey := [(Sum.inl 2361, 5)]

def keyMomentRow1509 : Integer.Sparse OriginalKey := [(Sum.inl 2349, 5)]

def keyMomentRow1510 : Integer.Sparse OriginalKey := [(Sum.inl 2355, 5)]

def keyMomentRow1511 : Integer.Sparse OriginalKey := [(Sum.inl 1119, 5)]

def keyMomentRow1512 : Integer.Sparse OriginalKey := [(Sum.inl 2347, 5)]

def keyMomentRow1513 : Integer.Sparse OriginalKey := [(Sum.inl 952, 5)]

def keyMomentRow1514 : Integer.Sparse OriginalKey := [(Sum.inl 588, 5)]

def keyMomentRow1515 : Integer.Sparse OriginalKey := [(Sum.inl 2294, 5)]

def keyMomentRow1516 : Integer.Sparse OriginalKey := [(Sum.inl 2279, 5)]

def keyMomentRow1517 : Integer.Sparse OriginalKey := [(Sum.inl 2115, 5)]

def keyMomentRow1518 : Integer.Sparse OriginalKey := [(Sum.inl 1817, 5)]

def keyMomentRow1519 : Integer.Sparse OriginalKey := [(Sum.inl 2266, 5)]

def keyMomentRow1520 : Integer.Sparse OriginalKey := [(Sum.inl 2110, 5)]

def keyMomentRow1521 : Integer.Sparse OriginalKey := [(Sum.inl 1814, 5)]

def keyMomentRow1522 : Integer.Sparse OriginalKey := [(Sum.inl 2058, 5)]

def keyMomentRow1523 : Integer.Sparse OriginalKey := [(Sum.inl 2245, 5)]

def keyMomentRow1524 : Integer.Sparse OriginalKey := [(Sum.inl 2028, 5)]

def keyMomentRow1525 : Integer.Sparse OriginalKey := [(Sum.inl 1804, 5)]

def keyMomentRow1526 : Integer.Sparse OriginalKey := [(Sum.inl 1811, 5)]

def keyMomentRow1527 : Integer.Sparse OriginalKey := [(Sum.inl 2023, 5)]

def keyMomentRow1528 : Integer.Sparse OriginalKey := [(Sum.inl 1966, 5)]

def keyMomentRow1529 : Integer.Sparse OriginalKey := [(Sum.inl 3626, 5)]

def keyMomentRow1530 : Integer.Sparse OriginalKey := [(Sum.inl 3814, 5)]

def keyMomentRow1531 : Integer.Sparse OriginalKey := [(Sum.inl 3732, 5)]

def keyMomentRow1532 : Integer.Sparse OriginalKey := [(Sum.inl 1814, 5)]

def keyMomentRow1533 : Integer.Sparse OriginalKey := [(Sum.inl 3809, 5)]

def keyMomentRow1534 : Integer.Sparse OriginalKey := [(Sum.inl 3789, 5)]

def keyMomentRow1535 : Integer.Sparse OriginalKey := [(Sum.inl 3708, 5)]

def keyMomentChunk47 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1504, keyMomentRow1505, keyMomentRow1506, keyMomentRow1507, keyMomentRow1508, keyMomentRow1509, keyMomentRow1510, keyMomentRow1511, keyMomentRow1512, keyMomentRow1513, keyMomentRow1514, keyMomentRow1515, keyMomentRow1516, keyMomentRow1517, keyMomentRow1518, keyMomentRow1519, keyMomentRow1520, keyMomentRow1521, keyMomentRow1522, keyMomentRow1523, keyMomentRow1524, keyMomentRow1525, keyMomentRow1526, keyMomentRow1527, keyMomentRow1528, keyMomentRow1529, keyMomentRow1530, keyMomentRow1531, keyMomentRow1532, keyMomentRow1533, keyMomentRow1534, keyMomentRow1535]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1536 : Integer.Sparse OriginalKey := [(Sum.inl 3782, 5)]

def keyMomentRow1537 : Integer.Sparse OriginalKey := [(Sum.inl 3801, 5)]

def keyMomentRow1538 : Integer.Sparse OriginalKey := [(Sum.inl 3719, 5)]

def keyMomentRow1539 : Integer.Sparse OriginalKey := [(Sum.inl 1802, 5)]

def keyMomentRow1540 : Integer.Sparse OriginalKey := [(Sum.inl 1819, 5)]

def keyMomentRow1541 : Integer.Sparse OriginalKey := [(Sum.inl 3397, 5)]

def keyMomentRow1542 : Integer.Sparse OriginalKey := [(Sum.inl 2817, 5)]

def keyMomentRow1543 : Integer.Sparse OriginalKey := [(Sum.inl 3706, 5)]

def keyMomentRow1544 : Integer.Sparse OriginalKey := [(Sum.inl 3693, 5)]

def keyMomentRow1545 : Integer.Sparse OriginalKey := [(Sum.inl 1810, 5)]

def keyMomentRow1546 : Integer.Sparse OriginalKey := [(Sum.inl 2814, 5)]

def keyMomentRow1547 : Integer.Sparse OriginalKey := [(Sum.inl 3692, 5)]

def keyMomentRow1548 : Integer.Sparse OriginalKey := [(Sum.inl 3671, 5)]

def keyMomentRow1549 : Integer.Sparse OriginalKey := [(Sum.inl 3619, 5)]

def keyMomentRow1550 : Integer.Sparse OriginalKey := [(Sum.inl 3899, 5)]

def keyMomentRow1551 : Integer.Sparse OriginalKey := [(Sum.inl 3731, 5)]

def keyMomentRow1552 : Integer.Sparse OriginalKey := [(Sum.inl 1811, 5)]

def keyMomentRow1553 : Integer.Sparse OriginalKey := [(Sum.inl 4025, 5)]

def keyMomentRow1554 : Integer.Sparse OriginalKey := [(Sum.inl 1812, 5)]

def keyMomentRow1555 : Integer.Sparse OriginalKey := [(Sum.inl 2896, 5)]

def keyMomentRow1556 : Integer.Sparse OriginalKey := [(Sum.inl 3721, 5)]

def keyMomentRow1557 : Integer.Sparse OriginalKey := [(Sum.inl 1805, 5)]

def keyMomentRow1558 : Integer.Sparse OriginalKey := [(Sum.inl 1143, 5)]

def keyMomentRow1559 : Integer.Sparse OriginalKey := [(Sum.inl 2522, 5)]

def keyMomentRow1560 : Integer.Sparse OriginalKey := [(Sum.inl 1138, 5)]

def keyMomentRow1561 : Integer.Sparse OriginalKey := [(Sum.inl 2515, 5)]

def keyMomentRow1562 : Integer.Sparse OriginalKey := [(Sum.inl 2488, 5)]

def keyMomentRow1563 : Integer.Sparse OriginalKey := [(Sum.inl 1807, 5)]

def keyMomentRow1564 : Integer.Sparse OriginalKey := [(Sum.inl 1815, 5)]

def keyMomentRow1565 : Integer.Sparse OriginalKey := [(Sum.inl 2483, 5)]

def keyMomentRow1566 : Integer.Sparse OriginalKey := [(Sum.inl 2431, 5)]

def keyMomentRow1567 : Integer.Sparse OriginalKey := [(Sum.inl 3709, 5)]

def keyMomentChunk48 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1536, keyMomentRow1537, keyMomentRow1538, keyMomentRow1539, keyMomentRow1540, keyMomentRow1541, keyMomentRow1542, keyMomentRow1543, keyMomentRow1544, keyMomentRow1545, keyMomentRow1546, keyMomentRow1547, keyMomentRow1548, keyMomentRow1549, keyMomentRow1550, keyMomentRow1551, keyMomentRow1552, keyMomentRow1553, keyMomentRow1554, keyMomentRow1555, keyMomentRow1556, keyMomentRow1557, keyMomentRow1558, keyMomentRow1559, keyMomentRow1560, keyMomentRow1561, keyMomentRow1562, keyMomentRow1563, keyMomentRow1564, keyMomentRow1565, keyMomentRow1566, keyMomentRow1567]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1568 : Integer.Sparse OriginalKey := [(Sum.inl 618, 5)]

def keyMomentRow1569 : Integer.Sparse OriginalKey := [(Sum.inl 613, 5)]

def keyMomentRow1570 : Integer.Sparse OriginalKey := [(Sum.inl 1087, 5)]

def keyMomentRow1571 : Integer.Sparse OriginalKey := [(Sum.inl 1049, 5)]

def keyMomentRow1572 : Integer.Sparse OriginalKey := [(Sum.inl 937, 5)]

def keyMomentRow1573 : Integer.Sparse OriginalKey := [(Sum.inl 1818, 5)]

def keyMomentRow1574 : Integer.Sparse OriginalKey := [(Sum.inl 610, 5)]

def keyMomentRow1575 : Integer.Sparse OriginalKey := [(Sum.inl 1044, 5)]

def keyMomentRow1576 : Integer.Sparse OriginalKey := [(Sum.inl 932, 5)]

def keyMomentRow1577 : Integer.Sparse OriginalKey := [(Sum.inl 2341, 5)]

def keyMomentRow1578 : Integer.Sparse OriginalKey := [(Sum.inl 929, 5)]

def keyMomentRow1579 : Integer.Sparse OriginalKey := [(Sum.inl 2338, 5)]

def keyMomentRow1580 : Integer.Sparse OriginalKey := [(Sum.inl 2789, 5)]

def keyMomentRow1581 : Integer.Sparse OriginalKey := [(Sum.inl 2967, 5)]

def keyMomentRow1582 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 5)]

def keyMomentRow1583 : Integer.Sparse OriginalKey := [(Sum.inl 2888, 5)]

def keyMomentRow1584 : Integer.Sparse OriginalKey := [(Sum.inl 2952, 5)]

def keyMomentRow1585 : Integer.Sparse OriginalKey := [(Sum.inl 2930, 5)]

def keyMomentRow1586 : Integer.Sparse OriginalKey := [(Sum.inl 2769, 5)]

def keyMomentRow1587 : Integer.Sparse OriginalKey := [(Sum.inl 2964, 5)]

def keyMomentRow1588 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 5)]

def keyMomentRow1589 : Integer.Sparse OriginalKey := [(Sum.inl 3097, 5)]

def keyMomentRow1590 : Integer.Sparse OriginalKey := [(Sum.inl 2885, 5)]

def keyMomentRow1591 : Integer.Sparse OriginalKey := [(Sum.inl 2951, 5)]

def keyMomentRow1592 : Integer.Sparse OriginalKey := [(Sum.inl 2928, 5)]

def keyMomentRow1593 : Integer.Sparse OriginalKey := [(Sum.inl 2878, 5)]

def keyMomentRow1594 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 5)]

def keyMomentRow1595 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 5)]

def keyMomentRow1596 : Integer.Sparse OriginalKey := [(Sum.inl 2886, 5)]

def keyMomentRow1597 : Integer.Sparse OriginalKey := [(Sum.inl 2955, 5)]

def keyMomentRow1598 : Integer.Sparse OriginalKey := [(Sum.inl 2865, 5)]

def keyMomentRow1599 : Integer.Sparse OriginalKey := [(Sum.inl 2882, 5)]

def keyMomentChunk49 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1568, keyMomentRow1569, keyMomentRow1570, keyMomentRow1571, keyMomentRow1572, keyMomentRow1573, keyMomentRow1574, keyMomentRow1575, keyMomentRow1576, keyMomentRow1577, keyMomentRow1578, keyMomentRow1579, keyMomentRow1580, keyMomentRow1581, keyMomentRow1582, keyMomentRow1583, keyMomentRow1584, keyMomentRow1585, keyMomentRow1586, keyMomentRow1587, keyMomentRow1588, keyMomentRow1589, keyMomentRow1590, keyMomentRow1591, keyMomentRow1592, keyMomentRow1593, keyMomentRow1594, keyMomentRow1595, keyMomentRow1596, keyMomentRow1597, keyMomentRow1598, keyMomentRow1599]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow160 : Integer.Sparse OriginalKey := [(Sum.inl 104, 5)]

def keyMomentRow161 : Integer.Sparse OriginalKey := [(Sum.inl 100, 5)]

def keyMomentRow162 : Integer.Sparse OriginalKey := [(Sum.inl 37, 5)]

def keyMomentRow163 : Integer.Sparse OriginalKey := [(Sum.inl 16, 5)]

def keyMomentRow164 : Integer.Sparse OriginalKey := [(Sum.inl 88, 5)]

def keyMomentRow165 : Integer.Sparse OriginalKey := [(Sum.inl 99, 5)]

def keyMomentRow166 : Integer.Sparse OriginalKey := [(Sum.inl 59, 5)]

def keyMomentRow167 : Integer.Sparse OriginalKey := [(Sum.inl 19, 5)]

def keyMomentRow168 : Integer.Sparse OriginalKey := [(Sum.inl 14, 5)]

def keyMomentRow169 : Integer.Sparse OriginalKey := [(Sum.inl 12, 5)]

def keyMomentRow170 : Integer.Sparse OriginalKey := [(Sum.inl 17, 5)]

def keyMomentRow171 : Integer.Sparse OriginalKey := [(Sum.inl 15, 5)]

def keyMomentRow172 : Integer.Sparse OriginalKey := [(Sum.inl 8, 5)]

def keyMomentRow173 : Integer.Sparse OriginalKey := [(Sum.inl 9, 5)]

def keyMomentRow174 : Integer.Sparse OriginalKey := [(Sum.inl 13, 5)]

def keyMomentRow175 : Integer.Sparse OriginalKey := [(Sum.inl 11, 5)]

def keyMomentRow176 : Integer.Sparse OriginalKey := [(Sum.inl 20, 5)]

def keyMomentRow177 : Integer.Sparse OriginalKey := [(Sum.inl 16, 5)]

def keyMomentRow178 : Integer.Sparse OriginalKey := [(Sum.inl 18, 5)]

def keyMomentRow179 : Integer.Sparse OriginalKey := [(Sum.inr 0, 5)]

def keyMomentRow180 : Integer.Sparse OriginalKey := [(Sum.inl 389, 5)]

def keyMomentRow181 : Integer.Sparse OriginalKey := [(Sum.inl 385, 5)]

def keyMomentRow182 : Integer.Sparse OriginalKey := [(Sum.inl 377, 5)]

def keyMomentRow183 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow184 : Integer.Sparse OriginalKey := [(Sum.inl 383, 5)]

def keyMomentRow185 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow186 : Integer.Sparse OriginalKey := [(Sum.inl 382, 5)]

def keyMomentRow187 : Integer.Sparse OriginalKey := [(Sum.inl 402, 5)]

def keyMomentRow188 : Integer.Sparse OriginalKey := [(Sum.inl 414, 5)]

def keyMomentRow189 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow190 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow191 : Integer.Sparse OriginalKey := [(Sum.inl 391, 5)]

def keyMomentChunk5 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow160, keyMomentRow161, keyMomentRow162, keyMomentRow163, keyMomentRow164, keyMomentRow165, keyMomentRow166, keyMomentRow167, keyMomentRow168, keyMomentRow169, keyMomentRow170, keyMomentRow171, keyMomentRow172, keyMomentRow173, keyMomentRow174, keyMomentRow175, keyMomentRow176, keyMomentRow177, keyMomentRow178, keyMomentRow179, keyMomentRow180, keyMomentRow181, keyMomentRow182, keyMomentRow183, keyMomentRow184, keyMomentRow185, keyMomentRow186, keyMomentRow187, keyMomentRow188, keyMomentRow189, keyMomentRow190, keyMomentRow191]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1600 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 5)]

def keyMomentRow1601 : Integer.Sparse OriginalKey := [(Sum.inl 2777, 5)]

def keyMomentRow1602 : Integer.Sparse OriginalKey := [(Sum.inl 2942, 5)]

def keyMomentRow1603 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 5)]

def keyMomentRow1604 : Integer.Sparse OriginalKey := [(Sum.inl 3086, 5)]

def keyMomentRow1605 : Integer.Sparse OriginalKey := [(Sum.inl 2867, 5)]

def keyMomentRow1606 : Integer.Sparse OriginalKey := [(Sum.inl 2933, 5)]

def keyMomentRow1607 : Integer.Sparse OriginalKey := [(Sum.inl 2916, 5)]

def keyMomentRow1608 : Integer.Sparse OriginalKey := [(Sum.inl 2861, 5)]

def keyMomentRow1609 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 5)]

def keyMomentRow1610 : Integer.Sparse OriginalKey := [(Sum.inl 2754, 5)]

def keyMomentRow1611 : Integer.Sparse OriginalKey := [(Sum.inl 2865, 5)]

def keyMomentRow1612 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 5)]

def keyMomentRow1613 : Integer.Sparse OriginalKey := [(Sum.inl 1243, 5)]

def keyMomentRow1614 : Integer.Sparse OriginalKey := [(Sum.inl 2618, 5)]

def keyMomentRow1615 : Integer.Sparse OriginalKey := [(Sum.inl 1217, 5)]

def keyMomentRow1616 : Integer.Sparse OriginalKey := [(Sum.inl 2558, 5)]

def keyMomentRow1617 : Integer.Sparse OriginalKey := [(Sum.inl 2712, 5)]

def keyMomentRow1618 : Integer.Sparse OriginalKey := [(Sum.inl 2134, 5)]

def keyMomentRow1619 : Integer.Sparse OriginalKey := [(Sum.inl 1825, 5)]

def keyMomentRow1620 : Integer.Sparse OriginalKey := [(Sum.inl 2090, 5)]

def keyMomentRow1621 : Integer.Sparse OriginalKey := [(Sum.inl 1808, 5)]

def keyMomentRow1622 : Integer.Sparse OriginalKey := [(Sum.inl 1973, 5)]

def keyMomentRow1623 : Integer.Sparse OriginalKey := [(Sum.inl 1790, 5)]

def keyMomentRow1624 : Integer.Sparse OriginalKey := [(Sum.inl 2759, 5)]

def keyMomentRow1625 : Integer.Sparse OriginalKey := [(Sum.inl 2902, 5)]

def keyMomentRow1626 : Integer.Sparse OriginalKey := [(Sum.inl 2984, 5)]

def keyMomentRow1627 : Integer.Sparse OriginalKey := [(Sum.inl 2848, 5)]

def keyMomentRow1628 : Integer.Sparse OriginalKey := [(Sum.inl 2979, 5)]

def keyMomentRow1629 : Integer.Sparse OriginalKey := [(Sum.inl 2811, 5)]

def keyMomentRow1630 : Integer.Sparse OriginalKey := [(Sum.inl 2900, 5)]

def keyMomentRow1631 : Integer.Sparse OriginalKey := [(Sum.inl 2797, 5)]

def keyMomentChunk50 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1600, keyMomentRow1601, keyMomentRow1602, keyMomentRow1603, keyMomentRow1604, keyMomentRow1605, keyMomentRow1606, keyMomentRow1607, keyMomentRow1608, keyMomentRow1609, keyMomentRow1610, keyMomentRow1611, keyMomentRow1612, keyMomentRow1613, keyMomentRow1614, keyMomentRow1615, keyMomentRow1616, keyMomentRow1617, keyMomentRow1618, keyMomentRow1619, keyMomentRow1620, keyMomentRow1621, keyMomentRow1622, keyMomentRow1623, keyMomentRow1624, keyMomentRow1625, keyMomentRow1626, keyMomentRow1627, keyMomentRow1628, keyMomentRow1629, keyMomentRow1630, keyMomentRow1631]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1632 : Integer.Sparse OriginalKey := [(Sum.inl 2846, 5)]

def keyMomentRow1633 : Integer.Sparse OriginalKey := [(Sum.inl 2981, 5)]

def keyMomentRow1634 : Integer.Sparse OriginalKey := [(Sum.inl 2746, 5)]

def keyMomentRow1635 : Integer.Sparse OriginalKey := [(Sum.inl 2847, 5)]

def keyMomentRow1636 : Integer.Sparse OriginalKey := [(Sum.inl 2495, 5)]

def keyMomentRow1637 : Integer.Sparse OriginalKey := [(Sum.inl 1132, 5)]

def keyMomentRow1638 : Integer.Sparse OriginalKey := [(Sum.inl 2437, 5)]

def keyMomentRow1639 : Integer.Sparse OriginalKey := [(Sum.inl 1112, 5)]

def keyMomentRow1640 : Integer.Sparse OriginalKey := [(Sum.inl 2426, 5)]

def keyMomentRow1641 : Integer.Sparse OriginalKey := [(Sum.inl 2470, 5)]

def keyMomentRow1642 : Integer.Sparse OriginalKey := [(Sum.inl 606, 5)]

def keyMomentRow1643 : Integer.Sparse OriginalKey := [(Sum.inl 945, 5)]

def keyMomentRow1644 : Integer.Sparse OriginalKey := [(Sum.inl 581, 5)]

def keyMomentRow1645 : Integer.Sparse OriginalKey := [(Sum.inl 1831, 5)]

def keyMomentRow1646 : Integer.Sparse OriginalKey := [(Sum.inl 1979, 5)]

def keyMomentRow1647 : Integer.Sparse OriginalKey := [(Sum.inl 1796, 5)]

def keyMomentRow1648 : Integer.Sparse OriginalKey := [(Sum.inl 2826, 5)]

def keyMomentRow1649 : Integer.Sparse OriginalKey := [(Sum.inl 2824, 5)]

def keyMomentRow1650 : Integer.Sparse OriginalKey := [(Sum.inl 2827, 5)]

def keyMomentRow1651 : Integer.Sparse OriginalKey := [(Sum.inl 2802, 5)]

def keyMomentRow1652 : Integer.Sparse OriginalKey := [(Sum.inl 2442, 5)]

def keyMomentRow1653 : Integer.Sparse OriginalKey := [(Sum.inl 1120, 5)]

def keyMomentRow1654 : Integer.Sparse OriginalKey := [(Sum.inl 953, 5)]

def keyMomentRow1655 : Integer.Sparse OriginalKey := [(Sum.inl 589, 5)]

def keyMomentRow1656 : Integer.Sparse OriginalKey := [(Sum.inl 2281, 5)]

def keyMomentRow1657 : Integer.Sparse OriginalKey := [(Sum.inl 2112, 5)]

def keyMomentRow1658 : Integer.Sparse OriginalKey := [(Sum.inl 1819, 5)]

def keyMomentRow1659 : Integer.Sparse OriginalKey := [(Sum.inl 2062, 5)]

def keyMomentRow1660 : Integer.Sparse OriginalKey := [(Sum.inl 2247, 5)]

def keyMomentRow1661 : Integer.Sparse OriginalKey := [(Sum.inl 1812, 5)]

def keyMomentRow1662 : Integer.Sparse OriginalKey := [(Sum.inl 2025, 5)]

def keyMomentRow1663 : Integer.Sparse OriginalKey := [(Sum.inl 1970, 5)]

def keyMomentChunk51 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1632, keyMomentRow1633, keyMomentRow1634, keyMomentRow1635, keyMomentRow1636, keyMomentRow1637, keyMomentRow1638, keyMomentRow1639, keyMomentRow1640, keyMomentRow1641, keyMomentRow1642, keyMomentRow1643, keyMomentRow1644, keyMomentRow1645, keyMomentRow1646, keyMomentRow1647, keyMomentRow1648, keyMomentRow1649, keyMomentRow1650, keyMomentRow1651, keyMomentRow1652, keyMomentRow1653, keyMomentRow1654, keyMomentRow1655, keyMomentRow1656, keyMomentRow1657, keyMomentRow1658, keyMomentRow1659, keyMomentRow1660, keyMomentRow1661, keyMomentRow1662, keyMomentRow1663]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1664 : Integer.Sparse OriginalKey := [(Sum.inl 1964, 5)]

def keyMomentRow1665 : Integer.Sparse OriginalKey := [(Sum.inl 3054, 5)]

def keyMomentRow1666 : Integer.Sparse OriginalKey := [(Sum.inl 2954, 5)]

def keyMomentRow1667 : Integer.Sparse OriginalKey := [(Sum.inl 2817, 5)]

def keyMomentRow1668 : Integer.Sparse OriginalKey := [(Sum.inl 2881, 5)]

def keyMomentRow1669 : Integer.Sparse OriginalKey := [(Sum.inl 3077, 5)]

def keyMomentRow1670 : Integer.Sparse OriginalKey := [(Sum.inl 2896, 5)]

def keyMomentRow1671 : Integer.Sparse OriginalKey := [(Sum.inl 2924, 5)]

def keyMomentRow1672 : Integer.Sparse OriginalKey := [(Sum.inl 2807, 5)]

def keyMomentRow1673 : Integer.Sparse OriginalKey := [(Sum.inl 2820, 5)]

def keyMomentRow1674 : Integer.Sparse OriginalKey := [(Sum.inl 2889, 5)]

def keyMomentRow1675 : Integer.Sparse OriginalKey := [(Sum.inl 2815, 5)]

def keyMomentRow1676 : Integer.Sparse OriginalKey := [(Sum.inl 2931, 5)]

def keyMomentRow1677 : Integer.Sparse OriginalKey := [(Sum.inl 2813, 5)]

def keyMomentRow1678 : Integer.Sparse OriginalKey := [(Sum.inl 2893, 5)]

def keyMomentRow1679 : Integer.Sparse OriginalKey := [(Sum.inl 3053, 5)]

def keyMomentRow1680 : Integer.Sparse OriginalKey := [(Sum.inl 2814, 5)]

def keyMomentRow1681 : Integer.Sparse OriginalKey := [(Sum.inl 2815, 5)]

def keyMomentRow1682 : Integer.Sparse OriginalKey := [(Sum.inl 2809, 5)]

def keyMomentRow1683 : Integer.Sparse OriginalKey := [(Sum.inl 1145, 5)]

def keyMomentRow1684 : Integer.Sparse OriginalKey := [(Sum.inl 2519, 5)]

def keyMomentRow1685 : Integer.Sparse OriginalKey := [(Sum.inl 2485, 5)]

def keyMomentRow1686 : Integer.Sparse OriginalKey := [(Sum.inl 2434, 5)]

def keyMomentRow1687 : Integer.Sparse OriginalKey := [(Sum.inl 2818, 5)]

def keyMomentRow1688 : Integer.Sparse OriginalKey := [(Sum.inl 2429, 5)]

def keyMomentRow1689 : Integer.Sparse OriginalKey := [(Sum.inl 620, 5)]

def keyMomentRow1690 : Integer.Sparse OriginalKey := [(Sum.inl 1091, 5)]

def keyMomentRow1691 : Integer.Sparse OriginalKey := [(Sum.inl 611, 5)]

def keyMomentRow1692 : Integer.Sparse OriginalKey := [(Sum.inl 1046, 5)]

def keyMomentRow1693 : Integer.Sparse OriginalKey := [(Sum.inl 939, 5)]

def keyMomentRow1694 : Integer.Sparse OriginalKey := [(Sum.inl 2345, 5)]

def keyMomentRow1695 : Integer.Sparse OriginalKey := [(Sum.inl 930, 5)]

def keyMomentChunk52 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1664, keyMomentRow1665, keyMomentRow1666, keyMomentRow1667, keyMomentRow1668, keyMomentRow1669, keyMomentRow1670, keyMomentRow1671, keyMomentRow1672, keyMomentRow1673, keyMomentRow1674, keyMomentRow1675, keyMomentRow1676, keyMomentRow1677, keyMomentRow1678, keyMomentRow1679, keyMomentRow1680, keyMomentRow1681, keyMomentRow1682, keyMomentRow1683, keyMomentRow1684, keyMomentRow1685, keyMomentRow1686, keyMomentRow1687, keyMomentRow1688, keyMomentRow1689, keyMomentRow1690, keyMomentRow1691, keyMomentRow1692, keyMomentRow1693, keyMomentRow1694, keyMomentRow1695]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1696 : Integer.Sparse OriginalKey := [(Sum.inl 2339, 5)]

def keyMomentRow1697 : Integer.Sparse OriginalKey := [(Sum.inl 1310, 5)]

def keyMomentRow1698 : Integer.Sparse OriginalKey := [(Sum.inl 1245, 5)]

def keyMomentRow1699 : Integer.Sparse OriginalKey := [(Sum.inl 1306, 5)]

def keyMomentRow1700 : Integer.Sparse OriginalKey := [(Sum.inl 1291, 5)]

def keyMomentRow1701 : Integer.Sparse OriginalKey := [(Sum.inl 1241, 5)]

def keyMomentRow1702 : Integer.Sparse OriginalKey := [(Sum.inl 1233, 5)]

def keyMomentRow1703 : Integer.Sparse OriginalKey := [(Sum.inl 1295, 5)]

def keyMomentRow1704 : Integer.Sparse OriginalKey := [(Sum.inl 1243, 5)]

def keyMomentRow1705 : Integer.Sparse OriginalKey := [(Sum.inl 1237, 5)]

def keyMomentRow1706 : Integer.Sparse OriginalKey := [(Sum.inl 1273, 5)]

def keyMomentRow1707 : Integer.Sparse OriginalKey := [(Sum.inl 1261, 5)]

def keyMomentRow1708 : Integer.Sparse OriginalKey := [(Sum.inl 1219, 5)]

def keyMomentRow1709 : Integer.Sparse OriginalKey := [(Sum.inl 1212, 5)]

def keyMomentRow1710 : Integer.Sparse OriginalKey := [(Sum.inl 1270, 5)]

def keyMomentRow1711 : Integer.Sparse OriginalKey := [(Sum.inl 1217, 5)]

def keyMomentRow1712 : Integer.Sparse OriginalKey := [(Sum.inl 1264, 5)]

def keyMomentRow1713 : Integer.Sparse OriginalKey := [(Sum.inl 1221, 5)]

def keyMomentRow1714 : Integer.Sparse OriginalKey := [(Sum.inl 1215, 5)]

def keyMomentRow1715 : Integer.Sparse OriginalKey := [(Sum.inl 1174, 5)]

def keyMomentRow1716 : Integer.Sparse OriginalKey := [(Sum.inl 1153, 5)]

def keyMomentRow1717 : Integer.Sparse OriginalKey := [(Sum.inl 1171, 5)]

def keyMomentRow1718 : Integer.Sparse OriginalKey := [(Sum.inl 1156, 5)]

def keyMomentRow1719 : Integer.Sparse OriginalKey := [(Sum.inl 1151, 5)]

def keyMomentRow1720 : Integer.Sparse OriginalKey := [(Sum.inl 1160, 5)]

def keyMomentRow1721 : Integer.Sparse OriginalKey := [(Sum.inl 1155, 5)]

def keyMomentRow1722 : Integer.Sparse OriginalKey := [(Sum.inl 1149, 5)]

def keyMomentRow1723 : Integer.Sparse OriginalKey := [(Sum.inl 1169, 5)]

def keyMomentRow1724 : Integer.Sparse OriginalKey := [(Sum.inl 1150, 5)]

def keyMomentRow1725 : Integer.Sparse OriginalKey := [(Sum.inl 1159, 5)]

def keyMomentRow1726 : Integer.Sparse OriginalKey := [(Sum.inl 1115, 5)]

def keyMomentRow1727 : Integer.Sparse OriginalKey := [(Sum.inl 1148, 5)]

def keyMomentChunk53 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1696, keyMomentRow1697, keyMomentRow1698, keyMomentRow1699, keyMomentRow1700, keyMomentRow1701, keyMomentRow1702, keyMomentRow1703, keyMomentRow1704, keyMomentRow1705, keyMomentRow1706, keyMomentRow1707, keyMomentRow1708, keyMomentRow1709, keyMomentRow1710, keyMomentRow1711, keyMomentRow1712, keyMomentRow1713, keyMomentRow1714, keyMomentRow1715, keyMomentRow1716, keyMomentRow1717, keyMomentRow1718, keyMomentRow1719, keyMomentRow1720, keyMomentRow1721, keyMomentRow1722, keyMomentRow1723, keyMomentRow1724, keyMomentRow1725, keyMomentRow1726, keyMomentRow1727]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1728 : Integer.Sparse OriginalKey := [(Sum.inl 584, 5)]

def keyMomentRow1729 : Integer.Sparse OriginalKey := [(Sum.inl 1297, 5)]

def keyMomentRow1730 : Integer.Sparse OriginalKey := [(Sum.inl 1143, 5)]

def keyMomentRow1731 : Integer.Sparse OriginalKey := [(Sum.inl 1239, 5)]

def keyMomentRow1732 : Integer.Sparse OriginalKey := [(Sum.inl 1128, 5)]

def keyMomentRow1733 : Integer.Sparse OriginalKey := [(Sum.inl 1294, 5)]

def keyMomentRow1734 : Integer.Sparse OriginalKey := [(Sum.inl 1138, 5)]

def keyMomentRow1735 : Integer.Sparse OriginalKey := [(Sum.inl 1236, 5)]

def keyMomentRow1736 : Integer.Sparse OriginalKey := [(Sum.inl 1126, 5)]

def keyMomentRow1737 : Integer.Sparse OriginalKey := [(Sum.inl 1145, 5)]

def keyMomentRow1738 : Integer.Sparse OriginalKey := [(Sum.inl 1246, 5)]

def keyMomentRow1739 : Integer.Sparse OriginalKey := [(Sum.inl 1134, 5)]

def keyMomentRow1740 : Integer.Sparse OriginalKey := [(Sum.inl 1293, 5)]

def keyMomentRow1741 : Integer.Sparse OriginalKey := [(Sum.inl 1135, 5)]

def keyMomentRow1742 : Integer.Sparse OriginalKey := [(Sum.inl 1235, 5)]

def keyMomentRow1743 : Integer.Sparse OriginalKey := [(Sum.inl 1240, 5)]

def keyMomentRow1744 : Integer.Sparse OriginalKey := [(Sum.inl 1129, 5)]

def keyMomentRow1745 : Integer.Sparse OriginalKey := [(Sum.inl 1140, 5)]

def keyMomentRow1746 : Integer.Sparse OriginalKey := [(Sum.inl 1242, 5)]

def keyMomentRow1747 : Integer.Sparse OriginalKey := [(Sum.inl 1131, 5)]

def keyMomentRow1748 : Integer.Sparse OriginalKey := [(Sum.inl 1139, 5)]

def keyMomentRow1749 : Integer.Sparse OriginalKey := [(Sum.inl 615, 5)]

def keyMomentRow1750 : Integer.Sparse OriginalKey := [(Sum.inl 1051, 5)]

def keyMomentRow1751 : Integer.Sparse OriginalKey := [(Sum.inl 934, 5)]

def keyMomentRow1752 : Integer.Sparse OriginalKey := [(Sum.inl 1144, 5)]

def keyMomentRow1753 : Integer.Sparse OriginalKey := [(Sum.inl 618, 5)]

def keyMomentRow1754 : Integer.Sparse OriginalKey := [(Sum.inl 613, 5)]

def keyMomentRow1755 : Integer.Sparse OriginalKey := [(Sum.inl 600, 5)]

def keyMomentRow1756 : Integer.Sparse OriginalKey := [(Sum.inl 620, 5)]

def keyMomentRow1757 : Integer.Sparse OriginalKey := [(Sum.inl 608, 5)]

def keyMomentRow1758 : Integer.Sparse OriginalKey := [(Sum.inl 610, 5)]

def keyMomentRow1759 : Integer.Sparse OriginalKey := [(Sum.inl 599, 5)]

def keyMomentChunk54 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1728, keyMomentRow1729, keyMomentRow1730, keyMomentRow1731, keyMomentRow1732, keyMomentRow1733, keyMomentRow1734, keyMomentRow1735, keyMomentRow1736, keyMomentRow1737, keyMomentRow1738, keyMomentRow1739, keyMomentRow1740, keyMomentRow1741, keyMomentRow1742, keyMomentRow1743, keyMomentRow1744, keyMomentRow1745, keyMomentRow1746, keyMomentRow1747, keyMomentRow1748, keyMomentRow1749, keyMomentRow1750, keyMomentRow1751, keyMomentRow1752, keyMomentRow1753, keyMomentRow1754, keyMomentRow1755, keyMomentRow1756, keyMomentRow1757, keyMomentRow1758, keyMomentRow1759]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1760 : Integer.Sparse OriginalKey := [(Sum.inl 611, 5)]

def keyMomentRow1761 : Integer.Sparse OriginalKey := [(Sum.inl 603, 5)]

def keyMomentRow1762 : Integer.Sparse OriginalKey := [(Sum.inl 615, 5)]

def keyMomentRow1763 : Integer.Sparse OriginalKey := [(Sum.inl 605, 5)]

def keyMomentRow1764 : Integer.Sparse OriginalKey := [(Sum.inl 614, 5)]

def keyMomentRow1765 : Integer.Sparse OriginalKey := [(Sum.inl 622, 5)]

def keyMomentRow1766 : Integer.Sparse OriginalKey := [(Sum.inl 619, 5)]

def keyMomentRow1767 : Integer.Sparse OriginalKey := [(Sum.inl 2738, 5)]

def keyMomentRow1768 : Integer.Sparse OriginalKey := [(Sum.inl 3050, 5)]

def keyMomentRow1769 : Integer.Sparse OriginalKey := [(Sum.inl 3625, 5)]

def keyMomentRow1770 : Integer.Sparse OriginalKey := [(Sum.inl 3580, 5)]

def keyMomentRow1771 : Integer.Sparse OriginalKey := [(Sum.inl 3073, 5)]

def keyMomentRow1772 : Integer.Sparse OriginalKey := [(Sum.inl 3571, 5)]

def keyMomentRow1773 : Integer.Sparse OriginalKey := [(Sum.inl 3388, 5)]

def keyMomentRow1774 : Integer.Sparse OriginalKey := [(Sum.inl 3375, 5)]

def keyMomentRow1775 : Integer.Sparse OriginalKey := [(Sum.inl 2781, 5)]

def keyMomentRow1776 : Integer.Sparse OriginalKey := [(Sum.inl 3096, 5)]

def keyMomentRow1777 : Integer.Sparse OriginalKey := [(Sum.inl 3572, 5)]

def keyMomentRow1778 : Integer.Sparse OriginalKey := [(Sum.inl 3392, 5)]

def keyMomentRow1779 : Integer.Sparse OriginalKey := [(Sum.inl 3376, 5)]

def keyMomentRow1780 : Integer.Sparse OriginalKey := [(Sum.inl 2603, 5)]

def keyMomentRow1781 : Integer.Sparse OriginalKey := [(Sum.inl 2560, 5)]

def keyMomentRow1782 : Integer.Sparse OriginalKey := [(Sum.inl 3581, 5)]

def keyMomentRow1783 : Integer.Sparse OriginalKey := [(Sum.inl 3391, 5)]

def keyMomentRow1784 : Integer.Sparse OriginalKey := [(Sum.inl 3544, 5)]

def keyMomentRow1785 : Integer.Sparse OriginalKey := [(Sum.inl 3622, 5)]

def keyMomentRow1786 : Integer.Sparse OriginalKey := [(Sum.inl 3533, 5)]

def keyMomentRow1787 : Integer.Sparse OriginalKey := [(Sum.inl 3390, 5)]

def keyMomentRow1788 : Integer.Sparse OriginalKey := [(Sum.inl 3532, 5)]

def keyMomentRow1789 : Integer.Sparse OriginalKey := [(Sum.inl 3118, 5)]

def keyMomentRow1790 : Integer.Sparse OriginalKey := [(Sum.inl 3380, 5)]

def keyMomentRow1791 : Integer.Sparse OriginalKey := [(Sum.inl 3633, 5)]

def keyMomentChunk55 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1760, keyMomentRow1761, keyMomentRow1762, keyMomentRow1763, keyMomentRow1764, keyMomentRow1765, keyMomentRow1766, keyMomentRow1767, keyMomentRow1768, keyMomentRow1769, keyMomentRow1770, keyMomentRow1771, keyMomentRow1772, keyMomentRow1773, keyMomentRow1774, keyMomentRow1775, keyMomentRow1776, keyMomentRow1777, keyMomentRow1778, keyMomentRow1779, keyMomentRow1780, keyMomentRow1781, keyMomentRow1782, keyMomentRow1783, keyMomentRow1784, keyMomentRow1785, keyMomentRow1786, keyMomentRow1787, keyMomentRow1788, keyMomentRow1789, keyMomentRow1790, keyMomentRow1791]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1792 : Integer.Sparse OriginalKey := [(Sum.inl 3583, 5)]

def keyMomentRow1793 : Integer.Sparse OriginalKey := [(Sum.inl 3397, 5)]

def keyMomentRow1794 : Integer.Sparse OriginalKey := [(Sum.inl 3548, 5)]

def keyMomentRow1795 : Integer.Sparse OriginalKey := [(Sum.inl 3623, 5)]

def keyMomentRow1796 : Integer.Sparse OriginalKey := [(Sum.inl 3394, 5)]

def keyMomentRow1797 : Integer.Sparse OriginalKey := [(Sum.inl 3534, 5)]

def keyMomentRow1798 : Integer.Sparse OriginalKey := [(Sum.inl 3496, 5)]

def keyMomentRow1799 : Integer.Sparse OriginalKey := [(Sum.inl 2783, 5)]

def keyMomentRow1800 : Integer.Sparse OriginalKey := [(Sum.inl 2522, 5)]

def keyMomentRow1801 : Integer.Sparse OriginalKey := [(Sum.inl 2740, 5)]

def keyMomentRow1802 : Integer.Sparse OriginalKey := [(Sum.inl 1094, 5)]

def keyMomentRow1803 : Integer.Sparse OriginalKey := [(Sum.inl 2291, 5)]

def keyMomentRow1804 : Integer.Sparse OriginalKey := [(Sum.inl 2739, 5)]

def keyMomentRow1805 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 5)]

def keyMomentRow1806 : Integer.Sparse OriginalKey := [(Sum.inl 3816, 5)]

def keyMomentRow1807 : Integer.Sparse OriginalKey := [(Sum.inl 3961, 5)]

def keyMomentRow1808 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 5)]

def keyMomentRow1809 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 5)]

def keyMomentRow1810 : Integer.Sparse OriginalKey := [(Sum.inl 3974, 5)]

def keyMomentRow1811 : Integer.Sparse OriginalKey := [(Sum.inl 4024, 5)]

def keyMomentRow1812 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 5)]

def keyMomentRow1813 : Integer.Sparse OriginalKey := [(Sum.inl 2782, 5)]

def keyMomentRow1814 : Integer.Sparse OriginalKey := [(Sum.inl 3097, 5)]

def keyMomentRow1815 : Integer.Sparse OriginalKey := [(Sum.inl 3983, 5)]

def keyMomentRow1816 : Integer.Sparse OriginalKey := [(Sum.inl 3959, 5)]

def keyMomentRow1817 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 5)]

def keyMomentRow1818 : Integer.Sparse OriginalKey := [(Sum.inl 2769, 5)]

def keyMomentRow1819 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 5)]

def keyMomentRow1820 : Integer.Sparse OriginalKey := [(Sum.inl 3908, 5)]

def keyMomentRow1821 : Integer.Sparse OriginalKey := [(Sum.inl 3913, 5)]

def keyMomentRow1822 : Integer.Sparse OriginalKey := [(Sum.inl 2266, 5)]

def keyMomentRow1823 : Integer.Sparse OriginalKey := [(Sum.inl 3627, 5)]

def keyMomentChunk56 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1792, keyMomentRow1793, keyMomentRow1794, keyMomentRow1795, keyMomentRow1796, keyMomentRow1797, keyMomentRow1798, keyMomentRow1799, keyMomentRow1800, keyMomentRow1801, keyMomentRow1802, keyMomentRow1803, keyMomentRow1804, keyMomentRow1805, keyMomentRow1806, keyMomentRow1807, keyMomentRow1808, keyMomentRow1809, keyMomentRow1810, keyMomentRow1811, keyMomentRow1812, keyMomentRow1813, keyMomentRow1814, keyMomentRow1815, keyMomentRow1816, keyMomentRow1817, keyMomentRow1818, keyMomentRow1819, keyMomentRow1820, keyMomentRow1821, keyMomentRow1822, keyMomentRow1823]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1824 : Integer.Sparse OriginalKey := [(Sum.inl 4049, 5)]

def keyMomentRow1825 : Integer.Sparse OriginalKey := [(Sum.inl 4010, 5)]

def keyMomentRow1826 : Integer.Sparse OriginalKey := [(Sum.inl 3809, 5)]

def keyMomentRow1827 : Integer.Sparse OriginalKey := [(Sum.inl 4047, 5)]

def keyMomentRow1828 : Integer.Sparse OriginalKey := [(Sum.inl 4048, 5)]

def keyMomentRow1829 : Integer.Sparse OriginalKey := [(Sum.inl 3903, 5)]

def keyMomentRow1830 : Integer.Sparse OriginalKey := [(Sum.inl 4025, 5)]

def keyMomentRow1831 : Integer.Sparse OriginalKey := [(Sum.inl 4046, 5)]

def keyMomentRow1832 : Integer.Sparse OriginalKey := [(Sum.inl 2262, 5)]

def keyMomentRow1833 : Integer.Sparse OriginalKey := [(Sum.inl 2720, 5)]

def keyMomentRow1834 : Integer.Sparse OriginalKey := [(Sum.inl 3036, 5)]

def keyMomentRow1835 : Integer.Sparse OriginalKey := [(Sum.inl 3805, 5)]

def keyMomentRow1836 : Integer.Sparse OriginalKey := [(Sum.inl 3956, 5)]

def keyMomentRow1837 : Integer.Sparse OriginalKey := [(Sum.inl 3497, 5)]

def keyMomentRow1838 : Integer.Sparse OriginalKey := [(Sum.inl 2879, 5)]

def keyMomentRow1839 : Integer.Sparse OriginalKey := [(Sum.inl 2878, 5)]

def keyMomentRow1840 : Integer.Sparse OriginalKey := [(Sum.inl 2861, 5)]

def keyMomentRow1841 : Integer.Sparse OriginalKey := [(Sum.inl 2763, 5)]

def keyMomentRow1842 : Integer.Sparse OriginalKey := [(Sum.inl 3084, 5)]

def keyMomentRow1843 : Integer.Sparse OriginalKey := [(Sum.inl 3978, 5)]

def keyMomentRow1844 : Integer.Sparse OriginalKey := [(Sum.inl 3946, 5)]

def keyMomentRow1845 : Integer.Sparse OriginalKey := [(Sum.inl 2882, 5)]

def keyMomentRow1846 : Integer.Sparse OriginalKey := [(Sum.inl 2862, 5)]

def keyMomentRow1847 : Integer.Sparse OriginalKey := [(Sum.inl 2600, 5)]

def keyMomentRow1848 : Integer.Sparse OriginalKey := [(Sum.inl 2557, 5)]

def keyMomentRow1849 : Integer.Sparse OriginalKey := [(Sum.inl 2558, 5)]

def keyMomentRow1850 : Integer.Sparse OriginalKey := [(Sum.inl 3903, 5)]

def keyMomentRow1851 : Integer.Sparse OriginalKey := [(Sum.inl 3857, 5)]

def keyMomentRow1852 : Integer.Sparse OriginalKey := [(Sum.inl 2058, 5)]

def keyMomentRow1853 : Integer.Sparse OriginalKey := [(Sum.inl 3544, 5)]

def keyMomentRow1854 : Integer.Sparse OriginalKey := [(Sum.inl 4047, 5)]

def keyMomentRow1855 : Integer.Sparse OriginalKey := [(Sum.inl 4008, 5)]

def keyMomentChunk57 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1824, keyMomentRow1825, keyMomentRow1826, keyMomentRow1827, keyMomentRow1828, keyMomentRow1829, keyMomentRow1830, keyMomentRow1831, keyMomentRow1832, keyMomentRow1833, keyMomentRow1834, keyMomentRow1835, keyMomentRow1836, keyMomentRow1837, keyMomentRow1838, keyMomentRow1839, keyMomentRow1840, keyMomentRow1841, keyMomentRow1842, keyMomentRow1843, keyMomentRow1844, keyMomentRow1845, keyMomentRow1846, keyMomentRow1847, keyMomentRow1848, keyMomentRow1849, keyMomentRow1850, keyMomentRow1851, keyMomentRow1852, keyMomentRow1853, keyMomentRow1854, keyMomentRow1855]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1856 : Integer.Sparse OriginalKey := [(Sum.inl 3782, 5)]

def keyMomentRow1857 : Integer.Sparse OriginalKey := [(Sum.inl 4044, 5)]

def keyMomentRow1858 : Integer.Sparse OriginalKey := [(Sum.inl 4046, 5)]

def keyMomentRow1859 : Integer.Sparse OriginalKey := [(Sum.inl 3843, 5)]

def keyMomentRow1860 : Integer.Sparse OriginalKey := [(Sum.inl 2881, 5)]

def keyMomentRow1861 : Integer.Sparse OriginalKey := [(Sum.inl 3961, 5)]

def keyMomentRow1862 : Integer.Sparse OriginalKey := [(Sum.inl 3845, 5)]

def keyMomentRow1863 : Integer.Sparse OriginalKey := [(Sum.inl 2880, 5)]

def keyMomentRow1864 : Integer.Sparse OriginalKey := [(Sum.inl 3957, 5)]

def keyMomentRow1865 : Integer.Sparse OriginalKey := [(Sum.inl 3108, 5)]

def keyMomentRow1866 : Integer.Sparse OriginalKey := [(Sum.inl 3922, 5)]

def keyMomentRow1867 : Integer.Sparse OriginalKey := [(Sum.inl 2868, 5)]

def keyMomentRow1868 : Integer.Sparse OriginalKey := [(Sum.inl 3913, 5)]

def keyMomentRow1869 : Integer.Sparse OriginalKey := [(Sum.inl 3983, 5)]

def keyMomentRow1870 : Integer.Sparse OriginalKey := [(Sum.inl 3706, 5)]

def keyMomentRow1871 : Integer.Sparse OriginalKey := [(Sum.inl 3961, 5)]

def keyMomentRow1872 : Integer.Sparse OriginalKey := [(Sum.inl 4010, 5)]

def keyMomentRow1873 : Integer.Sparse OriginalKey := [(Sum.inl 3964, 5)]

def keyMomentRow1874 : Integer.Sparse OriginalKey := [(Sum.inl 3974, 5)]

def keyMomentRow1875 : Integer.Sparse OriginalKey := [(Sum.inl 3703, 5)]

def keyMomentRow1876 : Integer.Sparse OriginalKey := [(Sum.inl 2889, 5)]

def keyMomentRow1877 : Integer.Sparse OriginalKey := [(Sum.inl 3963, 5)]

def keyMomentRow1878 : Integer.Sparse OriginalKey := [(Sum.inl 2884, 5)]

def keyMomentRow1879 : Integer.Sparse OriginalKey := [(Sum.inl 3958, 5)]

def keyMomentRow1880 : Integer.Sparse OriginalKey := [(Sum.inl 3705, 5)]

def keyMomentRow1881 : Integer.Sparse OriginalKey := [(Sum.inl 3945, 5)]

def keyMomentRow1882 : Integer.Sparse OriginalKey := [(Sum.inl 2782, 5)]

def keyMomentRow1883 : Integer.Sparse OriginalKey := [(Sum.inl 2515, 5)]

def keyMomentRow1884 : Integer.Sparse OriginalKey := [(Sum.inl 2739, 5)]

def keyMomentRow1885 : Integer.Sparse OriginalKey := [(Sum.inl 2508, 5)]

def keyMomentRow1886 : Integer.Sparse OriginalKey := [(Sum.inl 2519, 5)]

def keyMomentRow1887 : Integer.Sparse OriginalKey := [(Sum.inl 2743, 5)]

def keyMomentChunk58 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1856, keyMomentRow1857, keyMomentRow1858, keyMomentRow1859, keyMomentRow1860, keyMomentRow1861, keyMomentRow1862, keyMomentRow1863, keyMomentRow1864, keyMomentRow1865, keyMomentRow1866, keyMomentRow1867, keyMomentRow1868, keyMomentRow1869, keyMomentRow1870, keyMomentRow1871, keyMomentRow1872, keyMomentRow1873, keyMomentRow1874, keyMomentRow1875, keyMomentRow1876, keyMomentRow1877, keyMomentRow1878, keyMomentRow1879, keyMomentRow1880, keyMomentRow1881, keyMomentRow1882, keyMomentRow1883, keyMomentRow1884, keyMomentRow1885, keyMomentRow1886, keyMomentRow1887]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1888 : Integer.Sparse OriginalKey := [(Sum.inl 2512, 5)]

def keyMomentRow1889 : Integer.Sparse OriginalKey := [(Sum.inl 1087, 5)]

def keyMomentRow1890 : Integer.Sparse OriginalKey := [(Sum.inl 1091, 5)]

def keyMomentRow1891 : Integer.Sparse OriginalKey := [(Sum.inl 4083, 5)]

def keyMomentRow1892 : Integer.Sparse OriginalKey := [(Sum.inl 2741, 5)]

def keyMomentRow1893 : Integer.Sparse OriginalKey := [(Sum.inl 3962, 5)]

def keyMomentRow1894 : Integer.Sparse OriginalKey := [(Sum.inl 3619, 5)]

def keyMomentRow1895 : Integer.Sparse OriginalKey := [(Sum.inl 4025, 5)]

def keyMomentRow1896 : Integer.Sparse OriginalKey := [(Sum.inl 2263, 5)]

def keyMomentRow1897 : Integer.Sparse OriginalKey := [(Sum.inl 2721, 5)]

def keyMomentRow1898 : Integer.Sparse OriginalKey := [(Sum.inl 3957, 5)]

def keyMomentRow1899 : Integer.Sparse OriginalKey := [(Sum.inl 3526, 5)]

def keyMomentRow1900 : Integer.Sparse OriginalKey := [(Sum.inl 3075, 5)]

def keyMomentRow1901 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 5)]

def keyMomentRow1902 : Integer.Sparse OriginalKey := [(Sum.inl 2764, 5)]

def keyMomentRow1903 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 5)]

def keyMomentRow1904 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 5)]

def keyMomentRow1905 : Integer.Sparse OriginalKey := [(Sum.inl 2247, 5)]

def keyMomentRow1906 : Integer.Sparse OriginalKey := [(Sum.inl 3623, 5)]

def keyMomentRow1907 : Integer.Sparse OriginalKey := [(Sum.inl 3077, 5)]

def keyMomentRow1908 : Integer.Sparse OriginalKey := [(Sum.inl 4010, 5)]

def keyMomentRow1909 : Integer.Sparse OriginalKey := [(Sum.inl 2277, 5)]

def keyMomentRow1910 : Integer.Sparse OriginalKey := [(Sum.inl 2730, 5)]

def keyMomentRow1911 : Integer.Sparse OriginalKey := [(Sum.inl 3043, 5)]

def keyMomentRow1912 : Integer.Sparse OriginalKey := [(Sum.inl 3812, 5)]

def keyMomentRow1913 : Integer.Sparse OriginalKey := [(Sum.inl 3874, 5)]

def keyMomentRow1914 : Integer.Sparse OriginalKey := [(Sum.inl 3488, 5)]

def keyMomentRow1915 : Integer.Sparse OriginalKey := [(Sum.inl 2243, 5)]

def keyMomentRow1916 : Integer.Sparse OriginalKey := [(Sum.inl 2923, 5)]

def keyMomentRow1917 : Integer.Sparse OriginalKey := [(Sum.inl 1234, 5)]

def keyMomentRow1918 : Integer.Sparse OriginalKey := [(Sum.inl 1233, 5)]

def keyMomentRow1919 : Integer.Sparse OriginalKey := [(Sum.inl 1212, 5)]

def keyMomentChunk59 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1888, keyMomentRow1889, keyMomentRow1890, keyMomentRow1891, keyMomentRow1892, keyMomentRow1893, keyMomentRow1894, keyMomentRow1895, keyMomentRow1896, keyMomentRow1897, keyMomentRow1898, keyMomentRow1899, keyMomentRow1900, keyMomentRow1901, keyMomentRow1902, keyMomentRow1903, keyMomentRow1904, keyMomentRow1905, keyMomentRow1906, keyMomentRow1907, keyMomentRow1908, keyMomentRow1909, keyMomentRow1910, keyMomentRow1911, keyMomentRow1912, keyMomentRow1913, keyMomentRow1914, keyMomentRow1915, keyMomentRow1916, keyMomentRow1917, keyMomentRow1918, keyMomentRow1919]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow192 : Integer.Sparse OriginalKey := [(Sum.inl 422, 5)]

def keyMomentRow193 : Integer.Sparse OriginalKey := [(Sum.inl 418, 5)]

def keyMomentRow194 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow195 : Integer.Sparse OriginalKey := [(Sum.inl 270, 5)]

def keyMomentRow196 : Integer.Sparse OriginalKey := [(Sum.inl 419, 5)]

def keyMomentRow197 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow198 : Integer.Sparse OriginalKey := [(Sum.inl 404, 5)]

def keyMomentRow199 : Integer.Sparse OriginalKey := [(Sum.inl 417, 5)]

def keyMomentRow200 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow201 : Integer.Sparse OriginalKey := [(Sum.inl 397, 5)]

def keyMomentRow202 : Integer.Sparse OriginalKey := [(Sum.inl 396, 5)]

def keyMomentRow203 : Integer.Sparse OriginalKey := [(Sum.inl 1, 5)]

def keyMomentRow204 : Integer.Sparse OriginalKey := [(Sum.inl 4, 5)]

def keyMomentRow205 : Integer.Sparse OriginalKey := [(Sum.inl 469, 5)]

def keyMomentRow206 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow207 : Integer.Sparse OriginalKey := [(Sum.inl 465, 5)]

def keyMomentRow208 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow209 : Integer.Sparse OriginalKey := [(Sum.inl 468, 5)]

def keyMomentRow210 : Integer.Sparse OriginalKey := [(Sum.inl 466, 5)]

def keyMomentRow211 : Integer.Sparse OriginalKey := [(Sum.inl 3, 5)]

def keyMomentRow212 : Integer.Sparse OriginalKey := [(Sum.inl 461, 5)]

def keyMomentRow213 : Integer.Sparse OriginalKey := [(Sum.inl 464, 5)]

def keyMomentRow214 : Integer.Sparse OriginalKey := [(Sum.inl 266, 5)]

def keyMomentRow215 : Integer.Sparse OriginalKey := [(Sum.inl 465, 5)]

def keyMomentRow216 : Integer.Sparse OriginalKey := [(Sum.inl 483, 5)]

def keyMomentRow217 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow218 : Integer.Sparse OriginalKey := [(Sum.inl 478, 5)]

def keyMomentRow219 : Integer.Sparse OriginalKey := [(Sum.inl 480, 5)]

def keyMomentRow220 : Integer.Sparse OriginalKey := [(Sum.inl 481, 5)]

def keyMomentRow221 : Integer.Sparse OriginalKey := [(Sum.inl 479, 5)]

def keyMomentRow222 : Integer.Sparse OriginalKey := [(Sum.inl 482, 5)]

def keyMomentRow223 : Integer.Sparse OriginalKey := [(Sum.inr 3, 5)]

def keyMomentChunk6 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow192, keyMomentRow193, keyMomentRow194, keyMomentRow195, keyMomentRow196, keyMomentRow197, keyMomentRow198, keyMomentRow199, keyMomentRow200, keyMomentRow201, keyMomentRow202, keyMomentRow203, keyMomentRow204, keyMomentRow205, keyMomentRow206, keyMomentRow207, keyMomentRow208, keyMomentRow209, keyMomentRow210, keyMomentRow211, keyMomentRow212, keyMomentRow213, keyMomentRow214, keyMomentRow215, keyMomentRow216, keyMomentRow217, keyMomentRow218, keyMomentRow219, keyMomentRow220, keyMomentRow221, keyMomentRow222, keyMomentRow223]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1920 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 5)]

def keyMomentRow1921 : Integer.Sparse OriginalKey := [(Sum.inl 3720, 5)]

def keyMomentRow1922 : Integer.Sparse OriginalKey := [(Sum.inl 2750, 5)]

def keyMomentRow1923 : Integer.Sparse OriginalKey := [(Sum.inl 2925, 5)]

def keyMomentRow1924 : Integer.Sparse OriginalKey := [(Sum.inl 1237, 5)]

def keyMomentRow1925 : Integer.Sparse OriginalKey := [(Sum.inl 2575, 5)]

def keyMomentRow1926 : Integer.Sparse OriginalKey := [(Sum.inl 2545, 5)]

def keyMomentRow1927 : Integer.Sparse OriginalKey := [(Sum.inl 1215, 5)]

def keyMomentRow1928 : Integer.Sparse OriginalKey := [(Sum.inl 3906, 5)]

def keyMomentRow1929 : Integer.Sparse OriginalKey := [(Sum.inl 3850, 5)]

def keyMomentRow1930 : Integer.Sparse OriginalKey := [(Sum.inl 2028, 5)]

def keyMomentRow1931 : Integer.Sparse OriginalKey := [(Sum.inl 3533, 5)]

def keyMomentRow1932 : Integer.Sparse OriginalKey := [(Sum.inl 3903, 5)]

def keyMomentRow1933 : Integer.Sparse OriginalKey := [(Sum.inl 3875, 5)]

def keyMomentRow1934 : Integer.Sparse OriginalKey := [(Sum.inl 3719, 5)]

def keyMomentRow1935 : Integer.Sparse OriginalKey := [(Sum.inl 3843, 5)]

def keyMomentRow1936 : Integer.Sparse OriginalKey := [(Sum.inl 3901, 5)]

def keyMomentRow1937 : Integer.Sparse OriginalKey := [(Sum.inl 3837, 5)]

def keyMomentRow1938 : Integer.Sparse OriginalKey := [(Sum.inl 2025, 5)]

def keyMomentRow1939 : Integer.Sparse OriginalKey := [(Sum.inl 3534, 5)]

def keyMomentRow1940 : Integer.Sparse OriginalKey := [(Sum.inl 2924, 5)]

def keyMomentRow1941 : Integer.Sparse OriginalKey := [(Sum.inl 3974, 5)]

def keyMomentRow1942 : Integer.Sparse OriginalKey := [(Sum.inl 1236, 5)]

def keyMomentRow1943 : Integer.Sparse OriginalKey := [(Sum.inl 2739, 5)]

def keyMomentRow1944 : Integer.Sparse OriginalKey := [(Sum.inl 2722, 5)]

def keyMomentRow1945 : Integer.Sparse OriginalKey := [(Sum.inl 1235, 5)]

def keyMomentRow1946 : Integer.Sparse OriginalKey := [(Sum.inl 2721, 5)]

def keyMomentRow1947 : Integer.Sparse OriginalKey := [(Sum.inl 3907, 5)]

def keyMomentRow1948 : Integer.Sparse OriginalKey := [(Sum.inl 3876, 5)]

def keyMomentRow1949 : Integer.Sparse OriginalKey := [(Sum.inl 3693, 5)]

def keyMomentRow1950 : Integer.Sparse OriginalKey := [(Sum.inl 3845, 5)]

def keyMomentRow1951 : Integer.Sparse OriginalKey := [(Sum.inl 3902, 5)]

def keyMomentChunk60 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1920, keyMomentRow1921, keyMomentRow1922, keyMomentRow1923, keyMomentRow1924, keyMomentRow1925, keyMomentRow1926, keyMomentRow1927, keyMomentRow1928, keyMomentRow1929, keyMomentRow1930, keyMomentRow1931, keyMomentRow1932, keyMomentRow1933, keyMomentRow1934, keyMomentRow1935, keyMomentRow1936, keyMomentRow1937, keyMomentRow1938, keyMomentRow1939, keyMomentRow1940, keyMomentRow1941, keyMomentRow1942, keyMomentRow1943, keyMomentRow1944, keyMomentRow1945, keyMomentRow1946, keyMomentRow1947, keyMomentRow1948, keyMomentRow1949, keyMomentRow1950, keyMomentRow1951]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1952 : Integer.Sparse OriginalKey := [(Sum.inl 3721, 5)]

def keyMomentRow1953 : Integer.Sparse OriginalKey := [(Sum.inl 3838, 5)]

def keyMomentRow1954 : Integer.Sparse OriginalKey := [(Sum.inl 3689, 5)]

def keyMomentRow1955 : Integer.Sparse OriginalKey := [(Sum.inl 3910, 5)]

def keyMomentRow1956 : Integer.Sparse OriginalKey := [(Sum.inl 3692, 5)]

def keyMomentRow1957 : Integer.Sparse OriginalKey := [(Sum.inl 2931, 5)]

def keyMomentRow1958 : Integer.Sparse OriginalKey := [(Sum.inl 3958, 5)]

def keyMomentRow1959 : Integer.Sparse OriginalKey := [(Sum.inl 1246, 5)]

def keyMomentRow1960 : Integer.Sparse OriginalKey := [(Sum.inl 2743, 5)]

def keyMomentRow1961 : Integer.Sparse OriginalKey := [(Sum.inl 1240, 5)]

def keyMomentRow1962 : Integer.Sparse OriginalKey := [(Sum.inl 2723, 5)]

def keyMomentRow1963 : Integer.Sparse OriginalKey := [(Sum.inl 2561, 5)]

def keyMomentRow1964 : Integer.Sparse OriginalKey := [(Sum.inl 2556, 5)]

def keyMomentRow1965 : Integer.Sparse OriginalKey := [(Sum.inl 2765, 5)]

def keyMomentRow1966 : Integer.Sparse OriginalKey := [(Sum.inl 2488, 5)]

def keyMomentRow1967 : Integer.Sparse OriginalKey := [(Sum.inl 2722, 5)]

def keyMomentRow1968 : Integer.Sparse OriginalKey := [(Sum.inl 2479, 5)]

def keyMomentRow1969 : Integer.Sparse OriginalKey := [(Sum.inl 2764, 5)]

def keyMomentRow1970 : Integer.Sparse OriginalKey := [(Sum.inl 2483, 5)]

def keyMomentRow1971 : Integer.Sparse OriginalKey := [(Sum.inl 1242, 5)]

def keyMomentRow1972 : Integer.Sparse OriginalKey := [(Sum.inl 2726, 5)]

def keyMomentRow1973 : Integer.Sparse OriginalKey := [(Sum.inl 2482, 5)]

def keyMomentRow1974 : Integer.Sparse OriginalKey := [(Sum.inl 1049, 5)]

def keyMomentRow1975 : Integer.Sparse OriginalKey := [(Sum.inl 1044, 5)]

def keyMomentRow1976 : Integer.Sparse OriginalKey := [(Sum.inl 1046, 5)]

def keyMomentRow1977 : Integer.Sparse OriginalKey := [(Sum.inl 1051, 5)]

def keyMomentRow1978 : Integer.Sparse OriginalKey := [(Sum.inl 2131, 5)]

def keyMomentRow1979 : Integer.Sparse OriginalKey := [(Sum.inl 1821, 5)]

def keyMomentRow1980 : Integer.Sparse OriginalKey := [(Sum.inl 2252, 5)]

def keyMomentRow1981 : Integer.Sparse OriginalKey := [(Sum.inl 2104, 5)]

def keyMomentRow1982 : Integer.Sparse OriginalKey := [(Sum.inl 2252, 5)]

def keyMomentRow1983 : Integer.Sparse OriginalKey := [(Sum.inl 2806, 5)]

def keyMomentChunk61 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1952, keyMomentRow1953, keyMomentRow1954, keyMomentRow1955, keyMomentRow1956, keyMomentRow1957, keyMomentRow1958, keyMomentRow1959, keyMomentRow1960, keyMomentRow1961, keyMomentRow1962, keyMomentRow1963, keyMomentRow1964, keyMomentRow1965, keyMomentRow1966, keyMomentRow1967, keyMomentRow1968, keyMomentRow1969, keyMomentRow1970, keyMomentRow1971, keyMomentRow1972, keyMomentRow1973, keyMomentRow1974, keyMomentRow1975, keyMomentRow1976, keyMomentRow1977, keyMomentRow1978, keyMomentRow1979, keyMomentRow1980, keyMomentRow1981, keyMomentRow1982, keyMomentRow1983]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow1984 : Integer.Sparse OriginalKey := [(Sum.inl 1125, 5)]

def keyMomentRow1985 : Integer.Sparse OriginalKey := [(Sum.inl 597, 5)]

def keyMomentRow1986 : Integer.Sparse OriginalKey := [(Sum.inl 577, 5)]

def keyMomentRow1987 : Integer.Sparse OriginalKey := [(Sum.inl 2132, 5)]

def keyMomentRow1988 : Integer.Sparse OriginalKey := [(Sum.inl 1822, 5)]

def keyMomentRow1989 : Integer.Sparse OriginalKey := [(Sum.inl 2088, 5)]

def keyMomentRow1990 : Integer.Sparse OriginalKey := [(Sum.inl 1803, 5)]

def keyMomentRow1991 : Integer.Sparse OriginalKey := [(Sum.inl 601, 5)]

def keyMomentRow1992 : Integer.Sparse OriginalKey := [(Sum.inl 578, 5)]

def keyMomentRow1993 : Integer.Sparse OriginalKey := [(Sum.inl 1823, 5)]

def keyMomentRow1994 : Integer.Sparse OriginalKey := [(Sum.inl 1789, 5)]

def keyMomentRow1995 : Integer.Sparse OriginalKey := [(Sum.inl 2529, 5)]

def keyMomentRow1996 : Integer.Sparse OriginalKey := [(Sum.inl 2524, 5)]

def keyMomentRow1997 : Integer.Sparse OriginalKey := [(Sum.inl 1111, 5)]

def keyMomentRow1998 : Integer.Sparse OriginalKey := [(Sum.inl 579, 5)]

def keyMomentRow1999 : Integer.Sparse OriginalKey := [(Sum.inl 2105, 5)]

def keyMomentRow2000 : Integer.Sparse OriginalKey := [(Sum.inl 1802, 5)]

def keyMomentRow2001 : Integer.Sparse OriginalKey := [(Sum.inl 2051, 5)]

def keyMomentRow2002 : Integer.Sparse OriginalKey := [(Sum.inl 2243, 5)]

def keyMomentRow2003 : Integer.Sparse OriginalKey := [(Sum.inl 2019, 5)]

def keyMomentRow2004 : Integer.Sparse OriginalKey := [(Sum.inl 3812, 5)]

def keyMomentRow2005 : Integer.Sparse OriginalKey := [(Sum.inl 3786, 5)]

def keyMomentRow2006 : Integer.Sparse OriginalKey := [(Sum.inl 1966, 5)]

def keyMomentRow2007 : Integer.Sparse OriginalKey := [(Sum.inl 3493, 5)]

def keyMomentRow2008 : Integer.Sparse OriginalKey := [(Sum.inl 3805, 5)]

def keyMomentRow2009 : Integer.Sparse OriginalKey := [(Sum.inl 2807, 5)]

def keyMomentRow2010 : Integer.Sparse OriginalKey := [(Sum.inl 3703, 5)]

def keyMomentRow2011 : Integer.Sparse OriginalKey := [(Sum.inl 3689, 5)]

def keyMomentRow2012 : Integer.Sparse OriginalKey := [(Sum.inl 1964, 5)]

def keyMomentRow2013 : Integer.Sparse OriginalKey := [(Sum.inl 3496, 5)]

def keyMomentRow2014 : Integer.Sparse OriginalKey := [(Sum.inl 1126, 5)]

def keyMomentRow2015 : Integer.Sparse OriginalKey := [(Sum.inl 2508, 5)]

def keyMomentChunk62 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow1984, keyMomentRow1985, keyMomentRow1986, keyMomentRow1987, keyMomentRow1988, keyMomentRow1989, keyMomentRow1990, keyMomentRow1991, keyMomentRow1992, keyMomentRow1993, keyMomentRow1994, keyMomentRow1995, keyMomentRow1996, keyMomentRow1997, keyMomentRow1998, keyMomentRow1999, keyMomentRow2000, keyMomentRow2001, keyMomentRow2002, keyMomentRow2003, keyMomentRow2004, keyMomentRow2005, keyMomentRow2006, keyMomentRow2007, keyMomentRow2008, keyMomentRow2009, keyMomentRow2010, keyMomentRow2011, keyMomentRow2012, keyMomentRow2013, keyMomentRow2014, keyMomentRow2015]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2016 : Integer.Sparse OriginalKey := [(Sum.inl 2479, 5)]

def keyMomentRow2017 : Integer.Sparse OriginalKey := [(Sum.inl 599, 5)]

def keyMomentRow2018 : Integer.Sparse OriginalKey := [(Sum.inl 1039, 5)]

def keyMomentRow2019 : Integer.Sparse OriginalKey := [(Sum.inl 1827, 5)]

def keyMomentRow2020 : Integer.Sparse OriginalKey := [(Sum.inl 1792, 5)]

def keyMomentRow2021 : Integer.Sparse OriginalKey := [(Sum.inl 583, 5)]

def keyMomentRow2022 : Integer.Sparse OriginalKey := [(Sum.inl 2278, 5)]

def keyMomentRow2023 : Integer.Sparse OriginalKey := [(Sum.inl 2107, 5)]

def keyMomentRow2024 : Integer.Sparse OriginalKey := [(Sum.inl 1810, 5)]

def keyMomentRow2025 : Integer.Sparse OriginalKey := [(Sum.inl 2054, 5)]

def keyMomentRow2026 : Integer.Sparse OriginalKey := [(Sum.inl 2244, 5)]

def keyMomentRow2027 : Integer.Sparse OriginalKey := [(Sum.inl 1805, 5)]

def keyMomentRow2028 : Integer.Sparse OriginalKey := [(Sum.inl 2020, 5)]

def keyMomentRow2029 : Integer.Sparse OriginalKey := [(Sum.inl 3813, 5)]

def keyMomentRow2030 : Integer.Sparse OriginalKey := [(Sum.inl 3787, 5)]

def keyMomentRow2031 : Integer.Sparse OriginalKey := [(Sum.inl 3671, 5)]

def keyMomentRow2032 : Integer.Sparse OriginalKey := [(Sum.inl 3781, 5)]

def keyMomentRow2033 : Integer.Sparse OriginalKey := [(Sum.inl 3800, 5)]

def keyMomentRow2034 : Integer.Sparse OriginalKey := [(Sum.inl 2813, 5)]

def keyMomentRow2035 : Integer.Sparse OriginalKey := [(Sum.inl 3705, 5)]

def keyMomentRow2036 : Integer.Sparse OriginalKey := [(Sum.inl 2809, 5)]

def keyMomentRow2037 : Integer.Sparse OriginalKey := [(Sum.inl 3690, 5)]

def keyMomentRow2038 : Integer.Sparse OriginalKey := [(Sum.inl 3670, 5)]

def keyMomentRow2039 : Integer.Sparse OriginalKey := [(Sum.inl 3909, 5)]

def keyMomentRow2040 : Integer.Sparse OriginalKey := [(Sum.inl 2893, 5)]

def keyMomentRow2041 : Integer.Sparse OriginalKey := [(Sum.inl 3945, 5)]

def keyMomentRow2042 : Integer.Sparse OriginalKey := [(Sum.inl 1134, 5)]

def keyMomentRow2043 : Integer.Sparse OriginalKey := [(Sum.inl 2512, 5)]

def keyMomentRow2044 : Integer.Sparse OriginalKey := [(Sum.inl 1129, 5)]

def keyMomentRow2045 : Integer.Sparse OriginalKey := [(Sum.inl 2480, 5)]

def keyMomentRow2046 : Integer.Sparse OriginalKey := [(Sum.inl 2428, 5)]

def keyMomentRow2047 : Integer.Sparse OriginalKey := [(Sum.inl 608, 5)]

def keyMomentChunk63 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2016, keyMomentRow2017, keyMomentRow2018, keyMomentRow2019, keyMomentRow2020, keyMomentRow2021, keyMomentRow2022, keyMomentRow2023, keyMomentRow2024, keyMomentRow2025, keyMomentRow2026, keyMomentRow2027, keyMomentRow2028, keyMomentRow2029, keyMomentRow2030, keyMomentRow2031, keyMomentRow2032, keyMomentRow2033, keyMomentRow2034, keyMomentRow2035, keyMomentRow2036, keyMomentRow2037, keyMomentRow2038, keyMomentRow2039, keyMomentRow2040, keyMomentRow2041, keyMomentRow2042, keyMomentRow2043, keyMomentRow2044, keyMomentRow2045, keyMomentRow2046, keyMomentRow2047]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2048 : Integer.Sparse OriginalKey := [(Sum.inl 603, 5)]

def keyMomentRow2049 : Integer.Sparse OriginalKey := [(Sum.inl 1041, 5)]

def keyMomentRow2050 : Integer.Sparse OriginalKey := [(Sum.inl 2337, 5)]

def keyMomentRow2051 : Integer.Sparse OriginalKey := [(Sum.inl 922, 5)]

def keyMomentRow2052 : Integer.Sparse OriginalKey := [(Sum.inl 2332, 5)]

def keyMomentRow2053 : Integer.Sparse OriginalKey := [(Sum.inl 2109, 5)]

def keyMomentRow2054 : Integer.Sparse OriginalKey := [(Sum.inl 1807, 5)]

def keyMomentRow2055 : Integer.Sparse OriginalKey := [(Sum.inl 2022, 5)]

def keyMomentRow2056 : Integer.Sparse OriginalKey := [(Sum.inl 2590, 5)]

def keyMomentRow2057 : Integer.Sparse OriginalKey := [(Sum.inl 2431, 5)]

def keyMomentRow2058 : Integer.Sparse OriginalKey := [(Sum.inl 2553, 5)]

def keyMomentRow2059 : Integer.Sparse OriginalKey := [(Sum.inl 2434, 5)]

def keyMomentRow2060 : Integer.Sparse OriginalKey := [(Sum.inl 2561, 5)]

def keyMomentRow2061 : Integer.Sparse OriginalKey := [(Sum.inl 2428, 5)]

def keyMomentRow2062 : Integer.Sparse OriginalKey := [(Sum.inl 2589, 5)]

def keyMomentRow2063 : Integer.Sparse OriginalKey := [(Sum.inl 2429, 5)]

def keyMomentRow2064 : Integer.Sparse OriginalKey := [(Sum.inl 1131, 5)]

def keyMomentRow2065 : Integer.Sparse OriginalKey := [(Sum.inl 2482, 5)]

def keyMomentRow2066 : Integer.Sparse OriginalKey := [(Sum.inl 2425, 5)]

def keyMomentRow2067 : Integer.Sparse OriginalKey := [(Sum.inl 605, 5)]

def keyMomentRow2068 : Integer.Sparse OriginalKey := [(Sum.inl 937, 5)]

def keyMomentRow2069 : Integer.Sparse OriginalKey := [(Sum.inl 932, 5)]

def keyMomentRow2070 : Integer.Sparse OriginalKey := [(Sum.inl 939, 5)]

def keyMomentRow2071 : Integer.Sparse OriginalKey := [(Sum.inl 929, 5)]

def keyMomentRow2072 : Integer.Sparse OriginalKey := [(Sum.inl 930, 5)]

def keyMomentRow2073 : Integer.Sparse OriginalKey := [(Sum.inl 934, 5)]

def keyMomentRow2074 : Integer.Sparse OriginalKey := [(Sum.inl 2116, 5)]

def keyMomentRow2075 : Integer.Sparse OriginalKey := [(Sum.inl 1815, 5)]

def keyMomentRow2076 : Integer.Sparse OriginalKey := [(Sum.inl 2029, 5)]

def keyMomentRow2077 : Integer.Sparse OriginalKey := [(Sum.inl 1967, 5)]

def keyMomentRow2078 : Integer.Sparse OriginalKey := [(Sum.inl 3709, 5)]

def keyMomentRow2079 : Integer.Sparse OriginalKey := [(Sum.inl 3779, 5)]

def keyMomentChunk64 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2048, keyMomentRow2049, keyMomentRow2050, keyMomentRow2051, keyMomentRow2052, keyMomentRow2053, keyMomentRow2054, keyMomentRow2055, keyMomentRow2056, keyMomentRow2057, keyMomentRow2058, keyMomentRow2059, keyMomentRow2060, keyMomentRow2061, keyMomentRow2062, keyMomentRow2063, keyMomentRow2064, keyMomentRow2065, keyMomentRow2066, keyMomentRow2067, keyMomentRow2068, keyMomentRow2069, keyMomentRow2070, keyMomentRow2071, keyMomentRow2072, keyMomentRow2073, keyMomentRow2074, keyMomentRow2075, keyMomentRow2076, keyMomentRow2077, keyMomentRow2078, keyMomentRow2079]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2080 : Integer.Sparse OriginalKey := [(Sum.inl 2818, 5)]

def keyMomentRow2081 : Integer.Sparse OriginalKey := [(Sum.inl 3694, 5)]

def keyMomentRow2082 : Integer.Sparse OriginalKey := [(Sum.inl 3672, 5)]

def keyMomentRow2083 : Integer.Sparse OriginalKey := [(Sum.inl 1139, 5)]

def keyMomentRow2084 : Integer.Sparse OriginalKey := [(Sum.inl 2489, 5)]

def keyMomentRow2085 : Integer.Sparse OriginalKey := [(Sum.inl 2432, 5)]

def keyMomentRow2086 : Integer.Sparse OriginalKey := [(Sum.inl 614, 5)]

def keyMomentRow2087 : Integer.Sparse OriginalKey := [(Sum.inl 1050, 5)]

def keyMomentRow2088 : Integer.Sparse OriginalKey := [(Sum.inl 933, 5)]

def keyMomentRow2089 : Integer.Sparse OriginalKey := [(Sum.inl 2342, 5)]

def keyMomentRow2090 : Integer.Sparse OriginalKey := [(Sum.inl 1818, 5)]

def keyMomentRow2091 : Integer.Sparse OriginalKey := [(Sum.inl 2341, 5)]

def keyMomentRow2092 : Integer.Sparse OriginalKey := [(Sum.inl 2330, 5)]

def keyMomentRow2093 : Integer.Sparse OriginalKey := [(Sum.inl 2345, 5)]

def keyMomentRow2094 : Integer.Sparse OriginalKey := [(Sum.inl 2337, 5)]

def keyMomentRow2095 : Integer.Sparse OriginalKey := [(Sum.inl 2338, 5)]

def keyMomentRow2096 : Integer.Sparse OriginalKey := [(Sum.inl 2339, 5)]

def keyMomentRow2097 : Integer.Sparse OriginalKey := [(Sum.inl 1144, 5)]

def keyMomentRow2098 : Integer.Sparse OriginalKey := [(Sum.inl 2334, 5)]

def keyMomentRow2099 : Integer.Sparse OriginalKey := [(Sum.inl 619, 5)]

def keyMomentRow2100 : Integer.Sparse OriginalKey := [(Sum.inl 2344, 5)]

def keyMomentRow2101 : Integer.Sparse OriginalKey := [(Sum.inl 2, 1), (Sum.inl 4085, 4)]

def keyMomentRow2102 : Integer.Sparse OriginalKey := [(Sum.inl 3114, 1), (Sum.inl 4897, 4)]

def keyMomentRow2103 : Integer.Sparse OriginalKey := [(Sum.inl 1, 1), (Sum.inl 4084, 4)]

def keyMomentRow2104 : Integer.Sparse OriginalKey := [(Sum.inl 3231, 1), (Sum.inl 4901, 4)]

def keyMomentRow2105 : Integer.Sparse OriginalKey := [(Sum.inl 2778, 1), (Sum.inl 4899, 4)]

def keyMomentRow2106 : Integer.Sparse OriginalKey := [(Sum.inl 3230, 1), (Sum.inl 4894, 4)]

def keyMomentRow2107 : Integer.Sparse OriginalKey := [(Sum.inl 3229, 1), (Sum.inl 4895, 4)]

def keyMomentRow2108 : Integer.Sparse OriginalKey := [(Sum.inl 3225, 1), (Sum.inl 4896, 4)]

def keyMomentRow2109 : Integer.Sparse OriginalKey := [(Sum.inl 3224, 1), (Sum.inl 4898, 4)]

def keyMomentRow2110 : Integer.Sparse OriginalKey := [(Sum.inl 2755, 1), (Sum.inl 4890, 4)]

def keyMomentRow2111 : Integer.Sparse OriginalKey := [(Sum.inl 3229, 1), (Sum.inl 4895, 4)]

def keyMomentChunk65 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2080, keyMomentRow2081, keyMomentRow2082, keyMomentRow2083, keyMomentRow2084, keyMomentRow2085, keyMomentRow2086, keyMomentRow2087, keyMomentRow2088, keyMomentRow2089, keyMomentRow2090, keyMomentRow2091, keyMomentRow2092, keyMomentRow2093, keyMomentRow2094, keyMomentRow2095, keyMomentRow2096, keyMomentRow2097, keyMomentRow2098, keyMomentRow2099, keyMomentRow2100, keyMomentRow2101, keyMomentRow2102, keyMomentRow2103, keyMomentRow2104, keyMomentRow2105, keyMomentRow2106, keyMomentRow2107, keyMomentRow2108, keyMomentRow2109, keyMomentRow2110, keyMomentRow2111]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2112 : Integer.Sparse OriginalKey := [(Sum.inl 0, 1), (Sum.inl 4083, 4)]

def keyMomentRow2113 : Integer.Sparse OriginalKey := [(Sum.inl 3223, 1), (Sum.inl 4889, 4)]

def keyMomentRow2114 : Integer.Sparse OriginalKey := [(Sum.inl 3227, 1), (Sum.inl 4888, 4)]

def keyMomentRow2115 : Integer.Sparse OriginalKey := [(Sum.inl 3228, 1), (Sum.inl 4893, 4)]

def keyMomentRow2116 : Integer.Sparse OriginalKey := [(Sum.inl 3223, 1), (Sum.inl 4889, 4)]

def keyMomentRow2117 : Integer.Sparse OriginalKey := [(Sum.inl 3226, 1), (Sum.inl 4887, 4)]

def keyMomentRow2118 : Integer.Sparse OriginalKey := [(Sum.inl 3114, 1), (Sum.inl 4897, 4)]

def keyMomentRow2119 : Integer.Sparse OriginalKey := [(Sum.inl 3113, 1), (Sum.inl 5272, 4)]

def keyMomentRow2120 : Integer.Sparse OriginalKey := [(Sum.inl 3112, 1), (Sum.inl 5274, 4)]

def keyMomentRow2121 : Integer.Sparse OriginalKey := [(Sum.inl 3110, 1), (Sum.inl 5275, 4)]

def keyMomentRow2122 : Integer.Sparse OriginalKey := [(Sum.inl 2777, 1), (Sum.inl 5276, 4)]

def keyMomentRow2123 : Integer.Sparse OriginalKey := [(Sum.inl 3089, 1), (Sum.inl 5258, 4)]

def keyMomentRow2124 : Integer.Sparse OriginalKey := [(Sum.inl 3088, 1), (Sum.inl 5259, 4)]

def keyMomentRow2125 : Integer.Sparse OriginalKey := [(Sum.inl 3086, 1), (Sum.inl 5260, 4)]

def keyMomentRow2126 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 1), (Sum.inl 5267, 4)]

def keyMomentRow2127 : Integer.Sparse OriginalKey := [(Sum.inl 2754, 1), (Sum.inl 5270, 4)]

def keyMomentRow2128 : Integer.Sparse OriginalKey := [(Sum.inl 3109, 1), (Sum.inl 5271, 4)]

def keyMomentRow2129 : Integer.Sparse OriginalKey := [(Sum.inl 3111, 1), (Sum.inl 5273, 4)]

def keyMomentRow2130 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 1), (Sum.inl 5251, 4)]

def keyMomentRow2131 : Integer.Sparse OriginalKey := [(Sum.inl 3085, 1), (Sum.inl 5256, 4)]

def keyMomentRow2132 : Integer.Sparse OriginalKey := [(Sum.inl 3087, 1), (Sum.inl 5257, 4)]

def keyMomentRow2133 : Integer.Sparse OriginalKey := [(Sum.inl 3037, 1), (Sum.inl 5265, 4)]

def keyMomentRow2134 : Integer.Sparse OriginalKey := [(Sum.inl 3125, 1), (Sum.inl 5305, 4)]

def keyMomentRow2135 : Integer.Sparse OriginalKey := [(Sum.inl 2789, 1), (Sum.inl 5311, 4)]

def keyMomentRow2136 : Integer.Sparse OriginalKey := [(Sum.inl 3103, 1), (Sum.inl 5291, 4)]

def keyMomentRow2137 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 1), (Sum.inl 5295, 4)]

def keyMomentRow2138 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 1), (Sum.inl 5276, 4)]

def keyMomentRow2139 : Integer.Sparse OriginalKey := [(Sum.inl 2769, 1), (Sum.inl 5295, 4)]

def keyMomentRow2140 : Integer.Sparse OriginalKey := [(Sum.inl 3119, 1), (Sum.inl 5304, 4)]

def keyMomentRow2141 : Integer.Sparse OriginalKey := [(Sum.inl 3075, 1), (Sum.inl 5270, 4)]

def keyMomentRow2142 : Integer.Sparse OriginalKey := [(Sum.inl 3097, 1), (Sum.inl 5289, 4)]

def keyMomentRow2143 : Integer.Sparse OriginalKey := [(Sum.inl 3099, 1), (Sum.inl 5290, 4)]

def keyMomentChunk66 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2112, keyMomentRow2113, keyMomentRow2114, keyMomentRow2115, keyMomentRow2116, keyMomentRow2117, keyMomentRow2118, keyMomentRow2119, keyMomentRow2120, keyMomentRow2121, keyMomentRow2122, keyMomentRow2123, keyMomentRow2124, keyMomentRow2125, keyMomentRow2126, keyMomentRow2127, keyMomentRow2128, keyMomentRow2129, keyMomentRow2130, keyMomentRow2131, keyMomentRow2132, keyMomentRow2133, keyMomentRow2134, keyMomentRow2135, keyMomentRow2136, keyMomentRow2137, keyMomentRow2138, keyMomentRow2139, keyMomentRow2140, keyMomentRow2141, keyMomentRow2142, keyMomentRow2143]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2144 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 1), (Sum.inl 5299, 4)]

def keyMomentRow2145 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 1), (Sum.inl 5281, 4)]

def keyMomentRow2146 : Integer.Sparse OriginalKey := [(Sum.inl 2778, 1), (Sum.inl 4899, 4)]

def keyMomentRow2147 : Integer.Sparse OriginalKey := [(Sum.inl 2777, 1), (Sum.inl 5276, 4)]

def keyMomentRow2148 : Integer.Sparse OriginalKey := [(Sum.inl 2776, 1), (Sum.inl 5302, 4)]

def keyMomentRow2149 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 1), (Sum.inl 5300, 4)]

def keyMomentRow2150 : Integer.Sparse OriginalKey := [(Sum.inl 2771, 1), (Sum.inl 5297, 4)]

def keyMomentRow2151 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 1), (Sum.inl 5267, 4)]

def keyMomentRow2152 : Integer.Sparse OriginalKey := [(Sum.inl 2731, 1), (Sum.inl 5266, 4)]

def keyMomentRow2153 : Integer.Sparse OriginalKey := [(Sum.inl 2729, 1), (Sum.inl 5264, 4)]

def keyMomentRow2154 : Integer.Sparse OriginalKey := [(Sum.inl 2677, 1), (Sum.inl 5232, 4)]

def keyMomentRow2155 : Integer.Sparse OriginalKey := [(Sum.inl 2748, 1), (Sum.inl 5279, 4)]

def keyMomentRow2156 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 1), (Sum.inl 5299, 4)]

def keyMomentRow2157 : Integer.Sparse OriginalKey := [(Sum.inl 2775, 1), (Sum.inl 5301, 4)]

def keyMomentRow2158 : Integer.Sparse OriginalKey := [(Sum.inl 2697, 1), (Sum.inl 5243, 4)]

def keyMomentRow2159 : Integer.Sparse OriginalKey := [(Sum.inl 2728, 1), (Sum.inl 5263, 4)]

def keyMomentRow2160 : Integer.Sparse OriginalKey := [(Sum.inl 2730, 1), (Sum.inl 5265, 4)]

def keyMomentRow2161 : Integer.Sparse OriginalKey := [(Sum.inl 2676, 1), (Sum.inl 5231, 4)]

def keyMomentRow2162 : Integer.Sparse OriginalKey := [(Sum.inl 2755, 1), (Sum.inl 4890, 4)]

def keyMomentRow2163 : Integer.Sparse OriginalKey := [(Sum.inl 2754, 1), (Sum.inl 5270, 4)]

def keyMomentRow2164 : Integer.Sparse OriginalKey := [(Sum.inl 2753, 1), (Sum.inl 5284, 4)]

def keyMomentRow2165 : Integer.Sparse OriginalKey := [(Sum.inl 2751, 1), (Sum.inl 5282, 4)]

def keyMomentRow2166 : Integer.Sparse OriginalKey := [(Sum.inl 2748, 1), (Sum.inl 5279, 4)]

def keyMomentRow2167 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 1), (Sum.inl 5251, 4)]

def keyMomentRow2168 : Integer.Sparse OriginalKey := [(Sum.inl 2708, 1), (Sum.inl 5249, 4)]

def keyMomentRow2169 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 1), (Sum.inl 5219, 4)]

def keyMomentRow2170 : Integer.Sparse OriginalKey := [(Sum.inl 2747, 1), (Sum.inl 5278, 4)]

def keyMomentRow2171 : Integer.Sparse OriginalKey := [(Sum.inl 2750, 1), (Sum.inl 5281, 4)]

def keyMomentRow2172 : Integer.Sparse OriginalKey := [(Sum.inl 2769, 1), (Sum.inl 5295, 4)]

def keyMomentRow2173 : Integer.Sparse OriginalKey := [(Sum.inl 2761, 1), (Sum.inl 5175, 4)]

def keyMomentRow2174 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 1), (Sum.inl 5260, 4)]

def keyMomentRow2175 : Integer.Sparse OriginalKey := [(Sum.inl 2719, 1), (Sum.inl 5161, 4)]

def keyMomentChunk67 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2144, keyMomentRow2145, keyMomentRow2146, keyMomentRow2147, keyMomentRow2148, keyMomentRow2149, keyMomentRow2150, keyMomentRow2151, keyMomentRow2152, keyMomentRow2153, keyMomentRow2154, keyMomentRow2155, keyMomentRow2156, keyMomentRow2157, keyMomentRow2158, keyMomentRow2159, keyMomentRow2160, keyMomentRow2161, keyMomentRow2162, keyMomentRow2163, keyMomentRow2164, keyMomentRow2165, keyMomentRow2166, keyMomentRow2167, keyMomentRow2168, keyMomentRow2169, keyMomentRow2170, keyMomentRow2171, keyMomentRow2172, keyMomentRow2173, keyMomentRow2174, keyMomentRow2175]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2176 : Integer.Sparse OriginalKey := [(Sum.inl 2670, 1), (Sum.inl 5140, 4)]

def keyMomentRow2177 : Integer.Sparse OriginalKey := [(Sum.inl 2760, 1), (Sum.inl 5288, 4)]

def keyMomentRow2178 : Integer.Sparse OriginalKey := [(Sum.inl 2763, 1), (Sum.inl 5289, 4)]

def keyMomentRow2179 : Integer.Sparse OriginalKey := [(Sum.inl 2718, 1), (Sum.inl 5255, 4)]

def keyMomentRow2180 : Integer.Sparse OriginalKey := [(Sum.inl 2669, 1), (Sum.inl 5226, 4)]

def keyMomentRow2181 : Integer.Sparse OriginalKey := [(Sum.inl 2789, 1), (Sum.inl 5311, 4)]

def keyMomentRow2182 : Integer.Sparse OriginalKey := [(Sum.inl 2780, 1), (Sum.inl 4626, 4)]

def keyMomentRow2183 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 1), (Sum.inl 5276, 4)]

def keyMomentRow2184 : Integer.Sparse OriginalKey := [(Sum.inl 2737, 1), (Sum.inl 4617, 4)]

def keyMomentRow2185 : Integer.Sparse OriginalKey := [(Sum.inl 2683, 1), (Sum.inl 4611, 4)]

def keyMomentRow2186 : Integer.Sparse OriginalKey := [(Sum.inl 2761, 1), (Sum.inl 5175, 4)]

def keyMomentRow2187 : Integer.Sparse OriginalKey := [(Sum.inl 2781, 1), (Sum.inl 5295, 4)]

def keyMomentRow2188 : Integer.Sparse OriginalKey := [(Sum.inl 2779, 1), (Sum.inl 5303, 4)]

def keyMomentRow2189 : Integer.Sparse OriginalKey := [(Sum.inl 2702, 1), (Sum.inl 4600, 4)]

def keyMomentRow2190 : Integer.Sparse OriginalKey := [(Sum.inl 2735, 1), (Sum.inl 5173, 4)]

def keyMomentRow2191 : Integer.Sparse OriginalKey := [(Sum.inl 2738, 1), (Sum.inl 5270, 4)]

def keyMomentRow2192 : Integer.Sparse OriginalKey := [(Sum.inl 2736, 1), (Sum.inl 5269, 4)]

def keyMomentRow2193 : Integer.Sparse OriginalKey := [(Sum.inl 2681, 1), (Sum.inl 5151, 4)]

def keyMomentRow2194 : Integer.Sparse OriginalKey := [(Sum.inl 2682, 1), (Sum.inl 5236, 4)]

def keyMomentRow2195 : Integer.Sparse OriginalKey := [(Sum.inl 2700, 1), (Sum.inl 5150, 4)]

def keyMomentRow2196 : Integer.Sparse OriginalKey := [(Sum.inl 2285, 1), (Sum.inl 4900, 4)]

def keyMomentRow2197 : Integer.Sparse OriginalKey := [(Sum.inl 2222, 1), (Sum.inl 4844, 4)]

def keyMomentRow2198 : Integer.Sparse OriginalKey := [(Sum.inl 2284, 1), (Sum.inl 4892, 4)]

def keyMomentRow2199 : Integer.Sparse OriginalKey := [(Sum.inl 2282, 1), (Sum.inl 4872, 4)]

def keyMomentRow2200 : Integer.Sparse OriginalKey := [(Sum.inl 2163, 1), (Sum.inl 4694, 4)]

def keyMomentRow2201 : Integer.Sparse OriginalKey := [(Sum.inl 2221, 1), (Sum.inl 4819, 4)]

def keyMomentRow2202 : Integer.Sparse OriginalKey := [(Sum.inl 2220, 1), (Sum.inl 4808, 4)]

def keyMomentRow2203 : Integer.Sparse OriginalKey := [(Sum.inl 2162, 1), (Sum.inl 4687, 4)]

def keyMomentRow2204 : Integer.Sparse OriginalKey := [(Sum.inl 2161, 1), (Sum.inl 4671, 4)]

def keyMomentRow2205 : Integer.Sparse OriginalKey := [(Sum.inl 2180, 1), (Sum.inl 4702, 4)]

def keyMomentRow2206 : Integer.Sparse OriginalKey := [(Sum.inl 2220, 1), (Sum.inl 4808, 4)]

def keyMomentRow2207 : Integer.Sparse OriginalKey := [(Sum.inl 2283, 1), (Sum.inl 4886, 4)]

def keyMomentChunk68 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2176, keyMomentRow2177, keyMomentRow2178, keyMomentRow2179, keyMomentRow2180, keyMomentRow2181, keyMomentRow2182, keyMomentRow2183, keyMomentRow2184, keyMomentRow2185, keyMomentRow2186, keyMomentRow2187, keyMomentRow2188, keyMomentRow2189, keyMomentRow2190, keyMomentRow2191, keyMomentRow2192, keyMomentRow2193, keyMomentRow2194, keyMomentRow2195, keyMomentRow2196, keyMomentRow2197, keyMomentRow2198, keyMomentRow2199, keyMomentRow2200, keyMomentRow2201, keyMomentRow2202, keyMomentRow2203, keyMomentRow2204, keyMomentRow2205, keyMomentRow2206, keyMomentRow2207]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2208 : Integer.Sparse OriginalKey := [(Sum.inl 2160, 1), (Sum.inl 4667, 4)]

def keyMomentRow2209 : Integer.Sparse OriginalKey := [(Sum.inl 2179, 1), (Sum.inl 4765, 4)]

def keyMomentRow2210 : Integer.Sparse OriginalKey := [(Sum.inl 2219, 1), (Sum.inl 4793, 4)]

def keyMomentRow2211 : Integer.Sparse OriginalKey := [(Sum.inl 2160, 1), (Sum.inl 4667, 4)]

def keyMomentRow2212 : Integer.Sparse OriginalKey := [(Sum.inl 2255, 1), (Sum.inl 4892, 4)]

def keyMomentRow2213 : Integer.Sparse OriginalKey := [(Sum.inl 2254, 1), (Sum.inl 4880, 4)]

def keyMomentRow2214 : Integer.Sparse OriginalKey := [(Sum.inl 2253, 1), (Sum.inl 4891, 4)]

def keyMomentRow2215 : Integer.Sparse OriginalKey := [(Sum.inl 2251, 1), (Sum.inl 4867, 4)]

def keyMomentRow2216 : Integer.Sparse OriginalKey := [(Sum.inl 2249, 1), (Sum.inl 4700, 4)]

def keyMomentRow2217 : Integer.Sparse OriginalKey := [(Sum.inl 2196, 1), (Sum.inl 4816, 4)]

def keyMomentRow2218 : Integer.Sparse OriginalKey := [(Sum.inl 2195, 1), (Sum.inl 4803, 4)]

def keyMomentRow2219 : Integer.Sparse OriginalKey := [(Sum.inl 2194, 1), (Sum.inl 4773, 4)]

def keyMomentRow2220 : Integer.Sparse OriginalKey := [(Sum.inl 2144, 1), (Sum.inl 4665, 4)]

def keyMomentRow2221 : Integer.Sparse OriginalKey := [(Sum.inl 2248, 1), (Sum.inl 4698, 4)]

def keyMomentRow2222 : Integer.Sparse OriginalKey := [(Sum.inl 2250, 1), (Sum.inl 4852, 4)]

def keyMomentRow2223 : Integer.Sparse OriginalKey := [(Sum.inl 2252, 1), (Sum.inl 4885, 4)]

def keyMomentRow2224 : Integer.Sparse OriginalKey := [(Sum.inl 2280, 1), (Sum.inl 4884, 4)]

def keyMomentRow2225 : Integer.Sparse OriginalKey := [(Sum.inl 2273, 1), (Sum.inl 4704, 4)]

def keyMomentRow2226 : Integer.Sparse OriginalKey := [(Sum.inl 2217, 1), (Sum.inl 4821, 4)]

def keyMomentRow2227 : Integer.Sparse OriginalKey := [(Sum.inl 2212, 1), (Sum.inl 4776, 4)]

def keyMomentRow2228 : Integer.Sparse OriginalKey := [(Sum.inl 2155, 1), (Sum.inl 4669, 4)]

def keyMomentRow2229 : Integer.Sparse OriginalKey := [(Sum.inl 2272, 1), (Sum.inl 4703, 4)]

def keyMomentRow2230 : Integer.Sparse OriginalKey := [(Sum.inl 2274, 1), (Sum.inl 4856, 4)]

def keyMomentRow2231 : Integer.Sparse OriginalKey := [(Sum.inl 2176, 1), (Sum.inl 4756, 4)]

def keyMomentRow2232 : Integer.Sparse OriginalKey := [(Sum.inl 2211, 1), (Sum.inl 4775, 4)]

def keyMomentRow2233 : Integer.Sparse OriginalKey := [(Sum.inl 2213, 1), (Sum.inl 4795, 4)]

def keyMomentRow2234 : Integer.Sparse OriginalKey := [(Sum.inl 2154, 1), (Sum.inl 4668, 4)]

def keyMomentRow2235 : Integer.Sparse OriginalKey := [(Sum.inl 2235, 1), (Sum.inl 4886, 4)]

def keyMomentRow2236 : Integer.Sparse OriginalKey := [(Sum.inl 2234, 1), (Sum.inl 4878, 4)]

def keyMomentRow2237 : Integer.Sparse OriginalKey := [(Sum.inl 2233, 1), (Sum.inl 4885, 4)]

def keyMomentRow2238 : Integer.Sparse OriginalKey := [(Sum.inl 2232, 1), (Sum.inl 4863, 4)]

def keyMomentRow2239 : Integer.Sparse OriginalKey := [(Sum.inl 2231, 1), (Sum.inl 4695, 4)]

def keyMomentChunk69 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2208, keyMomentRow2209, keyMomentRow2210, keyMomentRow2211, keyMomentRow2212, keyMomentRow2213, keyMomentRow2214, keyMomentRow2215, keyMomentRow2216, keyMomentRow2217, keyMomentRow2218, keyMomentRow2219, keyMomentRow2220, keyMomentRow2221, keyMomentRow2222, keyMomentRow2223, keyMomentRow2224, keyMomentRow2225, keyMomentRow2226, keyMomentRow2227, keyMomentRow2228, keyMomentRow2229, keyMomentRow2230, keyMomentRow2231, keyMomentRow2232, keyMomentRow2233, keyMomentRow2234, keyMomentRow2235, keyMomentRow2236, keyMomentRow2237, keyMomentRow2238, keyMomentRow2239]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow224 : Integer.Sparse OriginalKey := [(Sum.inl 487, 5)]

def keyMomentRow225 : Integer.Sparse OriginalKey := [(Sum.inl 490, 5)]

def keyMomentRow226 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow227 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow228 : Integer.Sparse OriginalKey := [(Sum.inl 485, 5)]

def keyMomentRow229 : Integer.Sparse OriginalKey := [(Sum.inl 486, 5)]

def keyMomentRow230 : Integer.Sparse OriginalKey := [(Sum.inl 487, 5)]

def keyMomentRow231 : Integer.Sparse OriginalKey := [(Sum.inl 491, 5)]

def keyMomentRow232 : Integer.Sparse OriginalKey := [(Sum.inl 484, 5)]

def keyMomentRow233 : Integer.Sparse OriginalKey := [(Sum.inl 486, 5)]

def keyMomentRow234 : Integer.Sparse OriginalKey := [(Sum.inl 501, 5)]

def keyMomentRow235 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow236 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow237 : Integer.Sparse OriginalKey := [(Sum.inl 498, 5)]

def keyMomentRow238 : Integer.Sparse OriginalKey := [(Sum.inl 500, 5)]

def keyMomentRow239 : Integer.Sparse OriginalKey := [(Sum.inl 384, 5)]

def keyMomentRow240 : Integer.Sparse OriginalKey := [(Sum.inl 385, 5)]

def keyMomentRow241 : Integer.Sparse OriginalKey := [(Sum.inl 495, 5)]

def keyMomentRow242 : Integer.Sparse OriginalKey := [(Sum.inl 405, 5)]

def keyMomentRow243 : Integer.Sparse OriginalKey := [(Sum.inr 3, 5)]

def keyMomentRow244 : Integer.Sparse OriginalKey := [(Sum.inl 468, 5)]

def keyMomentRow245 : Integer.Sparse OriginalKey := [(Sum.inl 489, 5)]

def keyMomentRow246 : Integer.Sparse OriginalKey := [(Sum.inl 490, 5)]

def keyMomentRow247 : Integer.Sparse OriginalKey := [(Sum.inl 261, 5)]

def keyMomentRow248 : Integer.Sparse OriginalKey := [(Sum.inl 462, 5)]

def keyMomentRow249 : Integer.Sparse OriginalKey := [(Sum.inl 6, 5)]

def keyMomentRow250 : Integer.Sparse OriginalKey := [(Sum.inl 507, 5)]

def keyMomentRow251 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow252 : Integer.Sparse OriginalKey := [(Sum.inl 5, 5)]

def keyMomentRow253 : Integer.Sparse OriginalKey := [(Sum.inl 412, 5)]

def keyMomentRow254 : Integer.Sparse OriginalKey := [(Sum.inl 503, 5)]

def keyMomentRow255 : Integer.Sparse OriginalKey := [(Sum.inl 506, 5)]

def keyMomentChunk7 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow224, keyMomentRow225, keyMomentRow226, keyMomentRow227, keyMomentRow228, keyMomentRow229, keyMomentRow230, keyMomentRow231, keyMomentRow232, keyMomentRow233, keyMomentRow234, keyMomentRow235, keyMomentRow236, keyMomentRow237, keyMomentRow238, keyMomentRow239, keyMomentRow240, keyMomentRow241, keyMomentRow242, keyMomentRow243, keyMomentRow244, keyMomentRow245, keyMomentRow246, keyMomentRow247, keyMomentRow248, keyMomentRow249, keyMomentRow250, keyMomentRow251, keyMomentRow252, keyMomentRow253, keyMomentRow254, keyMomentRow255]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2240 : Integer.Sparse OriginalKey := [(Sum.inl 2246, 1), (Sum.inl 4879, 4)]

def keyMomentRow2241 : Integer.Sparse OriginalKey := [(Sum.inl 2239, 1), (Sum.inl 4697, 4)]

def keyMomentRow2242 : Integer.Sparse OriginalKey := [(Sum.inl 2192, 1), (Sum.inl 4815, 4)]

def keyMomentRow2243 : Integer.Sparse OriginalKey := [(Sum.inl 2189, 1), (Sum.inl 4771, 4)]

def keyMomentRow2244 : Integer.Sparse OriginalKey := [(Sum.inl 2140, 1), (Sum.inl 4663, 4)]

def keyMomentRow2245 : Integer.Sparse OriginalKey := [(Sum.inl 2238, 1), (Sum.inl 4696, 4)]

def keyMomentRow2246 : Integer.Sparse OriginalKey := [(Sum.inl 2240, 1), (Sum.inl 4851, 4)]

def keyMomentRow2247 : Integer.Sparse OriginalKey := [(Sum.inl 2267, 1), (Sum.inl 4881, 4)]

def keyMomentRow2248 : Integer.Sparse OriginalKey := [(Sum.inl 2258, 1), (Sum.inl 4560, 4)]

def keyMomentRow2249 : Integer.Sparse OriginalKey := [(Sum.inl 2207, 1), (Sum.inl 4817, 4)]

def keyMomentRow2250 : Integer.Sparse OriginalKey := [(Sum.inl 2200, 1), (Sum.inl 4552, 4)]

def keyMomentRow2251 : Integer.Sparse OriginalKey := [(Sum.inl 2149, 1), (Sum.inl 4536, 4)]

def keyMomentRow2252 : Integer.Sparse OriginalKey := [(Sum.inl 2256, 1), (Sum.inl 4699, 4)]

def keyMomentRow2253 : Integer.Sparse OriginalKey := [(Sum.inl 2259, 1), (Sum.inl 4853, 4)]

def keyMomentRow2254 : Integer.Sparse OriginalKey := [(Sum.inl 2257, 1), (Sum.inl 4701, 4)]

def keyMomentRow2255 : Integer.Sparse OriginalKey := [(Sum.inl 2172, 1), (Sum.inl 4532, 4)]

def keyMomentRow2256 : Integer.Sparse OriginalKey := [(Sum.inl 2198, 1), (Sum.inl 4772, 4)]

def keyMomentRow2257 : Integer.Sparse OriginalKey := [(Sum.inl 2201, 1), (Sum.inl 4792, 4)]

def keyMomentRow2258 : Integer.Sparse OriginalKey := [(Sum.inl 2199, 1), (Sum.inl 4774, 4)]

def keyMomentRow2259 : Integer.Sparse OriginalKey := [(Sum.inl 2147, 1), (Sum.inl 4664, 4)]

def keyMomentRow2260 : Integer.Sparse OriginalKey := [(Sum.inl 2148, 1), (Sum.inl 4666, 4)]

def keyMomentRow2261 : Integer.Sparse OriginalKey := [(Sum.inl 1747, 1), (Sum.inl 4508, 4)]

def keyMomentRow2262 : Integer.Sparse OriginalKey := [(Sum.inl 1531, 1), (Sum.inl 4193, 4)]

def keyMomentRow2263 : Integer.Sparse OriginalKey := [(Sum.inl 1746, 1), (Sum.inl 4478, 4)]

def keyMomentRow2264 : Integer.Sparse OriginalKey := [(Sum.inl 1530, 1), (Sum.inl 4184, 4)]

def keyMomentRow2265 : Integer.Sparse OriginalKey := [(Sum.inl 1529, 1), (Sum.inl 4162, 4)]

def keyMomentRow2266 : Integer.Sparse OriginalKey := [(Sum.inl 1687, 1), (Sum.inl 4362, 4)]

def keyMomentRow2267 : Integer.Sparse OriginalKey := [(Sum.inl 1745, 1), (Sum.inl 4464, 4)]

def keyMomentRow2268 : Integer.Sparse OriginalKey := [(Sum.inl 2286, 1), (Sum.inl 4705, 4)]

def keyMomentRow2269 : Integer.Sparse OriginalKey := [(Sum.inl 1528, 1), (Sum.inl 4157, 4)]

def keyMomentRow2270 : Integer.Sparse OriginalKey := [(Sum.inl 1686, 1), (Sum.inl 4353, 4)]

def keyMomentRow2271 : Integer.Sparse OriginalKey := [(Sum.inl 1744, 1), (Sum.inl 4442, 4)]

def keyMomentChunk70 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2240, keyMomentRow2241, keyMomentRow2242, keyMomentRow2243, keyMomentRow2244, keyMomentRow2245, keyMomentRow2246, keyMomentRow2247, keyMomentRow2248, keyMomentRow2249, keyMomentRow2250, keyMomentRow2251, keyMomentRow2252, keyMomentRow2253, keyMomentRow2254, keyMomentRow2255, keyMomentRow2256, keyMomentRow2257, keyMomentRow2258, keyMomentRow2259, keyMomentRow2260, keyMomentRow2261, keyMomentRow2262, keyMomentRow2263, keyMomentRow2264, keyMomentRow2265, keyMomentRow2266, keyMomentRow2267, keyMomentRow2268, keyMomentRow2269, keyMomentRow2270, keyMomentRow2271]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2272 : Integer.Sparse OriginalKey := [(Sum.inl 2223, 1), (Sum.inl 4777, 4)]

def keyMomentRow2273 : Integer.Sparse OriginalKey := [(Sum.inl 1685, 1), (Sum.inl 4336, 4)]

def keyMomentRow2274 : Integer.Sparse OriginalKey := [(Sum.inl 2164, 1), (Sum.inl 4670, 4)]

def keyMomentRow2275 : Integer.Sparse OriginalKey := [(Sum.inl 1684, 1), (Sum.inl 4331, 4)]

def keyMomentRow2276 : Integer.Sparse OriginalKey := [(Sum.inl 2181, 1), (Sum.inl 4757, 4)]

def keyMomentRow2277 : Integer.Sparse OriginalKey := [(Sum.inl 1746, 1), (Sum.inl 4478, 4)]

def keyMomentRow2278 : Integer.Sparse OriginalKey := [(Sum.inl 1745, 1), (Sum.inl 4464, 4)]

def keyMomentRow2279 : Integer.Sparse OriginalKey := [(Sum.inl 1743, 1), (Sum.inl 4375, 4)]

def keyMomentRow2280 : Integer.Sparse OriginalKey := [(Sum.inl 1685, 1), (Sum.inl 4336, 4)]

def keyMomentRow2281 : Integer.Sparse OriginalKey := [(Sum.inl 1742, 1), (Sum.inl 4371, 4)]

def keyMomentRow2282 : Integer.Sparse OriginalKey := [(Sum.inl 1744, 1), (Sum.inl 4442, 4)]

def keyMomentRow2283 : Integer.Sparse OriginalKey := [(Sum.inl 1684, 1), (Sum.inl 4331, 4)]

def keyMomentRow2284 : Integer.Sparse OriginalKey := [(Sum.inl 1715, 1), (Sum.inl 4475, 4)]

def keyMomentRow2285 : Integer.Sparse OriginalKey := [(Sum.inl 1714, 1), (Sum.inl 4459, 4)]

def keyMomentRow2286 : Integer.Sparse OriginalKey := [(Sum.inl 1712, 1), (Sum.inl 4368, 4)]

def keyMomentRow2287 : Integer.Sparse OriginalKey := [(Sum.inl 1667, 1), (Sum.inl 4328, 4)]

def keyMomentRow2288 : Integer.Sparse OriginalKey := [(Sum.inl 1711, 1), (Sum.inl 4366, 4)]

def keyMomentRow2289 : Integer.Sparse OriginalKey := [(Sum.inl 1713, 1), (Sum.inl 4439, 4)]

def keyMomentRow2290 : Integer.Sparse OriginalKey := [(Sum.inl 1740, 1), (Sum.inl 4480, 4)]

def keyMomentRow2291 : Integer.Sparse OriginalKey := [(Sum.inl 1735, 1), (Sum.inl 4373, 4)]

def keyMomentRow2292 : Integer.Sparse OriginalKey := [(Sum.inl 1679, 1), (Sum.inl 4334, 4)]

def keyMomentRow2293 : Integer.Sparse OriginalKey := [(Sum.inl 1734, 1), (Sum.inl 4372, 4)]

def keyMomentRow2294 : Integer.Sparse OriginalKey := [(Sum.inl 1736, 1), (Sum.inl 4444, 4)]

def keyMomentRow2295 : Integer.Sparse OriginalKey := [(Sum.inl 1678, 1), (Sum.inl 4332, 4)]

def keyMomentRow2296 : Integer.Sparse OriginalKey := [(Sum.inl 1699, 1), (Sum.inl 4473, 4)]

def keyMomentRow2297 : Integer.Sparse OriginalKey := [(Sum.inl 1697, 1), (Sum.inl 4363, 4)]

def keyMomentRow2298 : Integer.Sparse OriginalKey := [(Sum.inl 1709, 1), (Sum.inl 4474, 4)]

def keyMomentRow2299 : Integer.Sparse OriginalKey := [(Sum.inl 1704, 1), (Sum.inl 4365, 4)]

def keyMomentRow2300 : Integer.Sparse OriginalKey := [(Sum.inl 1703, 1), (Sum.inl 4364, 4)]

def keyMomentRow2301 : Integer.Sparse OriginalKey := [(Sum.inl 1729, 1), (Sum.inl 4476, 4)]

def keyMomentRow2302 : Integer.Sparse OriginalKey := [(Sum.inl 1722, 1), (Sum.inl 4370, 4)]

def keyMomentRow2303 : Integer.Sparse OriginalKey := [(Sum.inl 1672, 1), (Sum.inl 4330, 4)]

def keyMomentChunk71 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2272, keyMomentRow2273, keyMomentRow2274, keyMomentRow2275, keyMomentRow2276, keyMomentRow2277, keyMomentRow2278, keyMomentRow2279, keyMomentRow2280, keyMomentRow2281, keyMomentRow2282, keyMomentRow2283, keyMomentRow2284, keyMomentRow2285, keyMomentRow2286, keyMomentRow2287, keyMomentRow2288, keyMomentRow2289, keyMomentRow2290, keyMomentRow2291, keyMomentRow2292, keyMomentRow2293, keyMomentRow2294, keyMomentRow2295, keyMomentRow2296, keyMomentRow2297, keyMomentRow2298, keyMomentRow2299, keyMomentRow2300, keyMomentRow2301, keyMomentRow2302, keyMomentRow2303]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2304 : Integer.Sparse OriginalKey := [(Sum.inl 1720, 1), (Sum.inl 4367, 4)]

def keyMomentRow2305 : Integer.Sparse OriginalKey := [(Sum.inl 1723, 1), (Sum.inl 4440, 4)]

def keyMomentRow2306 : Integer.Sparse OriginalKey := [(Sum.inl 1721, 1), (Sum.inl 4369, 4)]

def keyMomentRow2307 : Integer.Sparse OriginalKey := [(Sum.inl 1670, 1), (Sum.inl 4327, 4)]

def keyMomentRow2308 : Integer.Sparse OriginalKey := [(Sum.inl 1757, 1), (Sum.inl 4481, 4)]

def keyMomentRow2309 : Integer.Sparse OriginalKey := [(Sum.inl 1540, 1), (Sum.inl 4189, 4)]

def keyMomentRow2310 : Integer.Sparse OriginalKey := [(Sum.inl 1532, 1), (Sum.inl 4159, 4)]

def keyMomentRow2311 : Integer.Sparse OriginalKey := [(Sum.inl 1695, 1), (Sum.inl 4358, 4)]

def keyMomentRow2312 : Integer.Sparse OriginalKey := [(Sum.inl 1749, 1), (Sum.inl 4445, 4)]

def keyMomentRow2313 : Integer.Sparse OriginalKey := [(Sum.inl 1748, 1), (Sum.inl 4374, 4)]

def keyMomentRow2314 : Integer.Sparse OriginalKey := [(Sum.inl 1688, 1), (Sum.inl 4333, 4)]

def keyMomentRow2315 : Integer.Sparse OriginalKey := [(Sum.inl 1689, 1), (Sum.inl 4335, 4)]

def keyMomentRow2316 : Integer.Sparse OriginalKey := [(Sum.inl 1529, 1), (Sum.inl 4162, 4)]

def keyMomentRow2317 : Integer.Sparse OriginalKey := [(Sum.inl 1528, 1), (Sum.inl 4157, 4)]

def keyMomentRow2318 : Integer.Sparse OriginalKey := [(Sum.inl 1511, 1), (Sum.inl 4154, 4)]

def keyMomentRow2319 : Integer.Sparse OriginalKey := [(Sum.inl 1510, 1), (Sum.inl 4152, 4)]

def keyMomentRow2320 : Integer.Sparse OriginalKey := [(Sum.inl 1523, 1), (Sum.inl 4160, 4)]

def keyMomentRow2321 : Integer.Sparse OriginalKey := [(Sum.inl 1522, 1), (Sum.inl 4158, 4)]

def keyMomentRow2322 : Integer.Sparse OriginalKey := [(Sum.inl 1501, 1), (Sum.inl 4149, 4)]

def keyMomentRow2323 : Integer.Sparse OriginalKey := [(Sum.inl 1505, 1), (Sum.inl 4151, 4)]

def keyMomentRow2324 : Integer.Sparse OriginalKey := [(Sum.inl 1504, 1), (Sum.inl 4150, 4)]

def keyMomentRow2325 : Integer.Sparse OriginalKey := [(Sum.inl 1516, 1), (Sum.inl 4156, 4)]

def keyMomentRow2326 : Integer.Sparse OriginalKey := [(Sum.inl 1514, 1), (Sum.inl 4153, 4)]

def keyMomentRow2327 : Integer.Sparse OriginalKey := [(Sum.inl 1515, 1), (Sum.inl 4155, 4)]

def keyMomentRow2328 : Integer.Sparse OriginalKey := [(Sum.inl 1534, 1), (Sum.inl 4163, 4)]

def keyMomentRow2329 : Integer.Sparse OriginalKey := [(Sum.inl 1532, 1), (Sum.inl 4159, 4)]

def keyMomentRow2330 : Integer.Sparse OriginalKey := [(Sum.inl 1533, 1), (Sum.inl 4161, 4)]

def keyMomentRow2331 : Integer.Sparse OriginalKey := [(Sum.inl 3114, 1), (Sum.inl 4897, 4)]

def keyMomentRow2332 : Integer.Sparse OriginalKey := [(Sum.inl 3112, 1), (Sum.inl 5274, 4)]

def keyMomentRow2333 : Integer.Sparse OriginalKey := [(Sum.inl 3110, 1), (Sum.inl 5275, 4)]

def keyMomentRow2334 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 1), (Sum.inl 5268, 4)]

def keyMomentRow2335 : Integer.Sparse OriginalKey := [(Sum.inl 3089, 1), (Sum.inl 5258, 4)]

def keyMomentChunk72 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2304, keyMomentRow2305, keyMomentRow2306, keyMomentRow2307, keyMomentRow2308, keyMomentRow2309, keyMomentRow2310, keyMomentRow2311, keyMomentRow2312, keyMomentRow2313, keyMomentRow2314, keyMomentRow2315, keyMomentRow2316, keyMomentRow2317, keyMomentRow2318, keyMomentRow2319, keyMomentRow2320, keyMomentRow2321, keyMomentRow2322, keyMomentRow2323, keyMomentRow2324, keyMomentRow2325, keyMomentRow2326, keyMomentRow2327, keyMomentRow2328, keyMomentRow2329, keyMomentRow2330, keyMomentRow2331, keyMomentRow2332, keyMomentRow2333, keyMomentRow2334, keyMomentRow2335]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2336 : Integer.Sparse OriginalKey := [(Sum.inl 3109, 1), (Sum.inl 5271, 4)]

def keyMomentRow2337 : Integer.Sparse OriginalKey := [(Sum.inl 3039, 1), (Sum.inl 5266, 4)]

def keyMomentRow2338 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 1), (Sum.inl 5267, 4)]

def keyMomentRow2339 : Integer.Sparse OriginalKey := [(Sum.inl 3088, 1), (Sum.inl 5259, 4)]

def keyMomentRow2340 : Integer.Sparse OriginalKey := [(Sum.inl 3111, 1), (Sum.inl 5273, 4)]

def keyMomentRow2341 : Integer.Sparse OriginalKey := [(Sum.inl 3037, 1), (Sum.inl 5265, 4)]

def keyMomentRow2342 : Integer.Sparse OriginalKey := [(Sum.inl 3065, 1), (Sum.inl 5250, 4)]

def keyMomentRow2343 : Integer.Sparse OriginalKey := [(Sum.inl 3087, 1), (Sum.inl 5257, 4)]

def keyMomentRow2344 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 1), (Sum.inl 5251, 4)]

def keyMomentRow2345 : Integer.Sparse OriginalKey := [(Sum.inl 3103, 1), (Sum.inl 5291, 4)]

def keyMomentRow2346 : Integer.Sparse OriginalKey := [(Sum.inl 3119, 1), (Sum.inl 5304, 4)]

def keyMomentRow2347 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 1), (Sum.inl 5300, 4)]

def keyMomentRow2348 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 1), (Sum.inl 5299, 4)]

def keyMomentRow2349 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 1), (Sum.inl 5282, 4)]

def keyMomentRow2350 : Integer.Sparse OriginalKey := [(Sum.inl 3099, 1), (Sum.inl 5290, 4)]

def keyMomentRow2351 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 1), (Sum.inl 5281, 4)]

def keyMomentRow2352 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 1), (Sum.inl 5276, 4)]

def keyMomentRow2353 : Integer.Sparse OriginalKey := [(Sum.inl 3075, 1), (Sum.inl 5270, 4)]

def keyMomentRow2354 : Integer.Sparse OriginalKey := [(Sum.inl 1, 1), (Sum.inl 4084, 4)]

def keyMomentRow2355 : Integer.Sparse OriginalKey := [(Sum.inl 3112, 1), (Sum.inl 5274, 4)]

def keyMomentRow2356 : Integer.Sparse OriginalKey := [(Sum.inl 4, 1), (Sum.inl 4092, 4)]

def keyMomentRow2357 : Integer.Sparse OriginalKey := [(Sum.inl 4006, 1), (Sum.inl 5413, 4)]

def keyMomentRow2358 : Integer.Sparse OriginalKey := [(Sum.inl 2776, 1), (Sum.inl 5302, 4)]

def keyMomentRow2359 : Integer.Sparse OriginalKey := [(Sum.inl 4035, 1), (Sum.inl 5409, 4)]

def keyMomentRow2360 : Integer.Sparse OriginalKey := [(Sum.inl 3996, 1), (Sum.inl 5410, 4)]

def keyMomentRow2361 : Integer.Sparse OriginalKey := [(Sum.inl 3883, 1), (Sum.inl 5411, 4)]

def keyMomentRow2362 : Integer.Sparse OriginalKey := [(Sum.inl 3856, 1), (Sum.inl 5412, 4)]

def keyMomentRow2363 : Integer.Sparse OriginalKey := [(Sum.inl 2753, 1), (Sum.inl 5284, 4)]

def keyMomentRow2364 : Integer.Sparse OriginalKey := [(Sum.inl 3996, 1), (Sum.inl 5410, 4)]

def keyMomentRow2365 : Integer.Sparse OriginalKey := [(Sum.inl 3, 1), (Sum.inl 4091, 4)]

def keyMomentRow2366 : Integer.Sparse OriginalKey := [(Sum.inl 3847, 1), (Sum.inl 5406, 4)]

def keyMomentRow2367 : Integer.Sparse OriginalKey := [(Sum.inl 3977, 1), (Sum.inl 5405, 4)]

def keyMomentChunk73 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2336, keyMomentRow2337, keyMomentRow2338, keyMomentRow2339, keyMomentRow2340, keyMomentRow2341, keyMomentRow2342, keyMomentRow2343, keyMomentRow2344, keyMomentRow2345, keyMomentRow2346, keyMomentRow2347, keyMomentRow2348, keyMomentRow2349, keyMomentRow2350, keyMomentRow2351, keyMomentRow2352, keyMomentRow2353, keyMomentRow2354, keyMomentRow2355, keyMomentRow2356, keyMomentRow2357, keyMomentRow2358, keyMomentRow2359, keyMomentRow2360, keyMomentRow2361, keyMomentRow2362, keyMomentRow2363, keyMomentRow2364, keyMomentRow2365, keyMomentRow2366, keyMomentRow2367]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2368 : Integer.Sparse OriginalKey := [(Sum.inl 4038, 1), (Sum.inl 5408, 4)]

def keyMomentRow2369 : Integer.Sparse OriginalKey := [(Sum.inl 3847, 1), (Sum.inl 5406, 4)]

def keyMomentRow2370 : Integer.Sparse OriginalKey := [(Sum.inl 3230, 1), (Sum.inl 4894, 4)]

def keyMomentRow2371 : Integer.Sparse OriginalKey := [(Sum.inl 3089, 1), (Sum.inl 5258, 4)]

def keyMomentRow2372 : Integer.Sparse OriginalKey := [(Sum.inl 4035, 1), (Sum.inl 5409, 4)]

def keyMomentRow2373 : Integer.Sparse OriginalKey := [(Sum.inl 4003, 1), (Sum.inl 5428, 4)]

def keyMomentRow2374 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 1), (Sum.inl 5267, 4)]

def keyMomentRow2375 : Integer.Sparse OriginalKey := [(Sum.inl 4032, 1), (Sum.inl 5423, 4)]

def keyMomentRow2376 : Integer.Sparse OriginalKey := [(Sum.inl 3990, 1), (Sum.inl 5424, 4)]

def keyMomentRow2377 : Integer.Sparse OriginalKey := [(Sum.inl 3872, 1), (Sum.inl 5425, 4)]

def keyMomentRow2378 : Integer.Sparse OriginalKey := [(Sum.inl 3841, 1), (Sum.inl 5426, 4)]

def keyMomentRow2379 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 1), (Sum.inl 5251, 4)]

def keyMomentRow2380 : Integer.Sparse OriginalKey := [(Sum.inl 3990, 1), (Sum.inl 5424, 4)]

def keyMomentRow2381 : Integer.Sparse OriginalKey := [(Sum.inl 4034, 1), (Sum.inl 5427, 4)]

def keyMomentRow2382 : Integer.Sparse OriginalKey := [(Sum.inl 3103, 1), (Sum.inl 5291, 4)]

def keyMomentRow2383 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 1), (Sum.inl 5276, 4)]

def keyMomentRow2384 : Integer.Sparse OriginalKey := [(Sum.inl 4027, 1), (Sum.inl 5432, 4)]

def keyMomentRow2385 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 1), (Sum.inl 5299, 4)]

def keyMomentRow2386 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 1), (Sum.inl 5267, 4)]

def keyMomentRow2387 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 1), (Sum.inl 5260, 4)]

def keyMomentRow2388 : Integer.Sparse OriginalKey := [(Sum.inl 3993, 1), (Sum.inl 5438, 4)]

def keyMomentRow2389 : Integer.Sparse OriginalKey := [(Sum.inl 3526, 1), (Sum.inl 5265, 4)]

def keyMomentRow2390 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 1), (Sum.inl 5430, 4)]

def keyMomentRow2391 : Integer.Sparse OriginalKey := [(Sum.inl 4026, 1), (Sum.inl 5431, 4)]

def keyMomentRow2392 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 1), (Sum.inl 5425, 4)]

def keyMomentRow2393 : Integer.Sparse OriginalKey := [(Sum.inl 4027, 1), (Sum.inl 5432, 4)]

def keyMomentRow2394 : Integer.Sparse OriginalKey := [(Sum.inl 3993, 1), (Sum.inl 5438, 4)]

def keyMomentRow2395 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 1), (Sum.inl 5436, 4)]

def keyMomentRow2396 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 1), (Sum.inl 5425, 4)]

def keyMomentRow2397 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 1), (Sum.inl 5429, 4)]

def keyMomentRow2398 : Integer.Sparse OriginalKey := [(Sum.inl 4026, 1), (Sum.inl 5431, 4)]

def keyMomentRow2399 : Integer.Sparse OriginalKey := [(Sum.inl 4030, 1), (Sum.inl 5449, 4)]

def keyMomentChunk74 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2368, keyMomentRow2369, keyMomentRow2370, keyMomentRow2371, keyMomentRow2372, keyMomentRow2373, keyMomentRow2374, keyMomentRow2375, keyMomentRow2376, keyMomentRow2377, keyMomentRow2378, keyMomentRow2379, keyMomentRow2380, keyMomentRow2381, keyMomentRow2382, keyMomentRow2383, keyMomentRow2384, keyMomentRow2385, keyMomentRow2386, keyMomentRow2387, keyMomentRow2388, keyMomentRow2389, keyMomentRow2390, keyMomentRow2391, keyMomentRow2392, keyMomentRow2393, keyMomentRow2394, keyMomentRow2395, keyMomentRow2396, keyMomentRow2397, keyMomentRow2398, keyMomentRow2399]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2400 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 1), (Sum.inl 5300, 4)]

def keyMomentRow2401 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 1), (Sum.inl 5266, 4)]

def keyMomentRow2402 : Integer.Sparse OriginalKey := [(Sum.inl 3959, 1), (Sum.inl 5446, 4)]

def keyMomentRow2403 : Integer.Sparse OriginalKey := [(Sum.inl 4028, 1), (Sum.inl 5448, 4)]

def keyMomentRow2404 : Integer.Sparse OriginalKey := [(Sum.inl 4024, 1), (Sum.inl 5445, 4)]

def keyMomentRow2405 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 1), (Sum.inl 5267, 4)]

def keyMomentRow2406 : Integer.Sparse OriginalKey := [(Sum.inl 3526, 1), (Sum.inl 5265, 4)]

def keyMomentRow2407 : Integer.Sparse OriginalKey := [(Sum.inl 3549, 1), (Sum.inl 5268, 4)]

def keyMomentRow2408 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 1), (Sum.inl 5266, 4)]

def keyMomentRow2409 : Integer.Sparse OriginalKey := [(Sum.inl 3231, 1), (Sum.inl 4901, 4)]

def keyMomentRow2410 : Integer.Sparse OriginalKey := [(Sum.inl 3110, 1), (Sum.inl 5275, 4)]

def keyMomentRow2411 : Integer.Sparse OriginalKey := [(Sum.inl 4006, 1), (Sum.inl 5413, 4)]

def keyMomentRow2412 : Integer.Sparse OriginalKey := [(Sum.inl 4004, 1), (Sum.inl 5475, 4)]

def keyMomentRow2413 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 1), (Sum.inl 5300, 4)]

def keyMomentRow2414 : Integer.Sparse OriginalKey := [(Sum.inl 4003, 1), (Sum.inl 5428, 4)]

def keyMomentRow2415 : Integer.Sparse OriginalKey := [(Sum.inl 3995, 1), (Sum.inl 5473, 4)]

def keyMomentRow2416 : Integer.Sparse OriginalKey := [(Sum.inl 3881, 1), (Sum.inl 5446, 4)]

def keyMomentRow2417 : Integer.Sparse OriginalKey := [(Sum.inl 3854, 1), (Sum.inl 5436, 4)]

def keyMomentRow2418 : Integer.Sparse OriginalKey := [(Sum.inl 2751, 1), (Sum.inl 5282, 4)]

def keyMomentRow2419 : Integer.Sparse OriginalKey := [(Sum.inl 3995, 1), (Sum.inl 5473, 4)]

def keyMomentRow2420 : Integer.Sparse OriginalKey := [(Sum.inl 4005, 1), (Sum.inl 5474, 4)]

def keyMomentRow2421 : Integer.Sparse OriginalKey := [(Sum.inl 3846, 1), (Sum.inl 5429, 4)]

def keyMomentRow2422 : Integer.Sparse OriginalKey := [(Sum.inl 3976, 1), (Sum.inl 5471, 4)]

def keyMomentRow2423 : Integer.Sparse OriginalKey := [(Sum.inl 4002, 1), (Sum.inl 5472, 4)]

def keyMomentRow2424 : Integer.Sparse OriginalKey := [(Sum.inl 3846, 1), (Sum.inl 5429, 4)]

def keyMomentRow2425 : Integer.Sparse OriginalKey := [(Sum.inl 3229, 1), (Sum.inl 4895, 4)]

def keyMomentRow2426 : Integer.Sparse OriginalKey := [(Sum.inl 3109, 1), (Sum.inl 5271, 4)]

def keyMomentRow2427 : Integer.Sparse OriginalKey := [(Sum.inl 3996, 1), (Sum.inl 5410, 4)]

def keyMomentRow2428 : Integer.Sparse OriginalKey := [(Sum.inl 3995, 1), (Sum.inl 5473, 4)]

def keyMomentRow2429 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 1), (Sum.inl 5299, 4)]

def keyMomentRow2430 : Integer.Sparse OriginalKey := [(Sum.inl 3990, 1), (Sum.inl 5424, 4)]

def keyMomentRow2431 : Integer.Sparse OriginalKey := [(Sum.inl 3871, 1), (Sum.inl 5430, 4)]

def keyMomentChunk75 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2400, keyMomentRow2401, keyMomentRow2402, keyMomentRow2403, keyMomentRow2404, keyMomentRow2405, keyMomentRow2406, keyMomentRow2407, keyMomentRow2408, keyMomentRow2409, keyMomentRow2410, keyMomentRow2411, keyMomentRow2412, keyMomentRow2413, keyMomentRow2414, keyMomentRow2415, keyMomentRow2416, keyMomentRow2417, keyMomentRow2418, keyMomentRow2419, keyMomentRow2420, keyMomentRow2421, keyMomentRow2422, keyMomentRow2423, keyMomentRow2424, keyMomentRow2425, keyMomentRow2426, keyMomentRow2427, keyMomentRow2428, keyMomentRow2429, keyMomentRow2430, keyMomentRow2431]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2432 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 1), (Sum.inl 5425, 4)]

def keyMomentRow2433 : Integer.Sparse OriginalKey := [(Sum.inl 2750, 1), (Sum.inl 5281, 4)]

def keyMomentRow2434 : Integer.Sparse OriginalKey := [(Sum.inl 3994, 1), (Sum.inl 5478, 4)]

def keyMomentRow2435 : Integer.Sparse OriginalKey := [(Sum.inl 3119, 1), (Sum.inl 5304, 4)]

def keyMomentRow2436 : Integer.Sparse OriginalKey := [(Sum.inl 2781, 1), (Sum.inl 5295, 4)]

def keyMomentRow2437 : Integer.Sparse OriginalKey := [(Sum.inl 3993, 1), (Sum.inl 5438, 4)]

def keyMomentRow2438 : Integer.Sparse OriginalKey := [(Sum.inl 3572, 1), (Sum.inl 5289, 4)]

def keyMomentRow2439 : Integer.Sparse OriginalKey := [(Sum.inl 3540, 1), (Sum.inl 5260, 4)]

def keyMomentRow2440 : Integer.Sparse OriginalKey := [(Sum.inl 2763, 1), (Sum.inl 5289, 4)]

def keyMomentRow2441 : Integer.Sparse OriginalKey := [(Sum.inl 3997, 1), (Sum.inl 5484, 4)]

def keyMomentRow2442 : Integer.Sparse OriginalKey := [(Sum.inl 3978, 1), (Sum.inl 5480, 4)]

def keyMomentRow2443 : Integer.Sparse OriginalKey := [(Sum.inl 3848, 1), (Sum.inl 5430, 4)]

def keyMomentRow2444 : Integer.Sparse OriginalKey := [(Sum.inl 3225, 1), (Sum.inl 4896, 4)]

def keyMomentRow2445 : Integer.Sparse OriginalKey := [(Sum.inl 3086, 1), (Sum.inl 5260, 4)]

def keyMomentRow2446 : Integer.Sparse OriginalKey := [(Sum.inl 3883, 1), (Sum.inl 5411, 4)]

def keyMomentRow2447 : Integer.Sparse OriginalKey := [(Sum.inl 3881, 1), (Sum.inl 5446, 4)]

def keyMomentRow2448 : Integer.Sparse OriginalKey := [(Sum.inl 2729, 1), (Sum.inl 5264, 4)]

def keyMomentRow2449 : Integer.Sparse OriginalKey := [(Sum.inl 3872, 1), (Sum.inl 5425, 4)]

def keyMomentRow2450 : Integer.Sparse OriginalKey := [(Sum.inl 3880, 1), (Sum.inl 5445, 4)]

def keyMomentRow2451 : Integer.Sparse OriginalKey := [(Sum.inl 3866, 1), (Sum.inl 5382, 4)]

def keyMomentRow2452 : Integer.Sparse OriginalKey := [(Sum.inl 3834, 1), (Sum.inl 5381, 4)]

def keyMomentRow2453 : Integer.Sparse OriginalKey := [(Sum.inl 2708, 1), (Sum.inl 5249, 4)]

def keyMomentRow2454 : Integer.Sparse OriginalKey := [(Sum.inl 3871, 1), (Sum.inl 5430, 4)]

def keyMomentRow2455 : Integer.Sparse OriginalKey := [(Sum.inl 3882, 1), (Sum.inl 5447, 4)]

def keyMomentRow2456 : Integer.Sparse OriginalKey := [(Sum.inl 3227, 1), (Sum.inl 4888, 4)]

def keyMomentRow2457 : Integer.Sparse OriginalKey := [(Sum.inl 3085, 1), (Sum.inl 5256, 4)]

def keyMomentRow2458 : Integer.Sparse OriginalKey := [(Sum.inl 3977, 1), (Sum.inl 5405, 4)]

def keyMomentRow2459 : Integer.Sparse OriginalKey := [(Sum.inl 3976, 1), (Sum.inl 5471, 4)]

def keyMomentRow2460 : Integer.Sparse OriginalKey := [(Sum.inl 2728, 1), (Sum.inl 5263, 4)]

def keyMomentRow2461 : Integer.Sparse OriginalKey := [(Sum.inl 3097, 1), (Sum.inl 5289, 4)]

def keyMomentRow2462 : Integer.Sparse OriginalKey := [(Sum.inl 2735, 1), (Sum.inl 5173, 4)]

def keyMomentRow2463 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 1), (Sum.inl 5430, 4)]

def keyMomentChunk76 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2432, keyMomentRow2433, keyMomentRow2434, keyMomentRow2435, keyMomentRow2436, keyMomentRow2437, keyMomentRow2438, keyMomentRow2439, keyMomentRow2440, keyMomentRow2441, keyMomentRow2442, keyMomentRow2443, keyMomentRow2444, keyMomentRow2445, keyMomentRow2446, keyMomentRow2447, keyMomentRow2448, keyMomentRow2449, keyMomentRow2450, keyMomentRow2451, keyMomentRow2452, keyMomentRow2453, keyMomentRow2454, keyMomentRow2455, keyMomentRow2456, keyMomentRow2457, keyMomentRow2458, keyMomentRow2459, keyMomentRow2460, keyMomentRow2461, keyMomentRow2462, keyMomentRow2463]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2464 : Integer.Sparse OriginalKey := [(Sum.inl 3558, 1), (Sum.inl 5160, 4)]

def keyMomentRow2465 : Integer.Sparse OriginalKey := [(Sum.inl 3517, 1), (Sum.inl 5138, 4)]

def keyMomentRow2466 : Integer.Sparse OriginalKey := [(Sum.inl 2718, 1), (Sum.inl 5255, 4)]

def keyMomentRow2467 : Integer.Sparse OriginalKey := [(Sum.inl 3978, 1), (Sum.inl 5480, 4)]

def keyMomentRow2468 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 1), (Sum.inl 5295, 4)]

def keyMomentRow2469 : Integer.Sparse OriginalKey := [(Sum.inl 2737, 1), (Sum.inl 4617, 4)]

def keyMomentRow2470 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 1), (Sum.inl 5299, 4)]

def keyMomentRow2471 : Integer.Sparse OriginalKey := [(Sum.inl 3303, 1), (Sum.inl 4616, 4)]

def keyMomentRow2472 : Integer.Sparse OriginalKey := [(Sum.inl 3296, 1), (Sum.inl 4607, 4)]

def keyMomentRow2473 : Integer.Sparse OriginalKey := [(Sum.inl 2719, 1), (Sum.inl 5161, 4)]

def keyMomentRow2474 : Integer.Sparse OriginalKey := [(Sum.inl 3572, 1), (Sum.inl 5289, 4)]

def keyMomentRow2475 : Integer.Sparse OriginalKey := [(Sum.inl 2736, 1), (Sum.inl 5269, 4)]

def keyMomentRow2476 : Integer.Sparse OriginalKey := [(Sum.inl 3289, 1), (Sum.inl 4599, 4)]

def keyMomentRow2477 : Integer.Sparse OriginalKey := [(Sum.inl 3558, 1), (Sum.inl 5160, 4)]

def keyMomentRow2478 : Integer.Sparse OriginalKey := [(Sum.inl 3571, 1), (Sum.inl 5281, 4)]

def keyMomentRow2479 : Integer.Sparse OriginalKey := [(Sum.inl 3973, 1), (Sum.inl 5461, 4)]

def keyMomentRow2480 : Integer.Sparse OriginalKey := [(Sum.inl 3557, 1), (Sum.inl 5144, 4)]

def keyMomentRow2481 : Integer.Sparse OriginalKey := [(Sum.inl 3842, 1), (Sum.inl 5419, 4)]

def keyMomentRow2482 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 1), (Sum.inl 5436, 4)]

def keyMomentRow2483 : Integer.Sparse OriginalKey := [(Sum.inl 3884, 1), (Sum.inl 5446, 4)]

def keyMomentRow2484 : Integer.Sparse OriginalKey := [(Sum.inl 3868, 1), (Sum.inl 5385, 4)]

def keyMomentRow2485 : Integer.Sparse OriginalKey := [(Sum.inl 3832, 1), (Sum.inl 5379, 4)]

def keyMomentRow2486 : Integer.Sparse OriginalKey := [(Sum.inl 3869, 1), (Sum.inl 5414, 4)]

def keyMomentRow2487 : Integer.Sparse OriginalKey := [(Sum.inl 3874, 1), (Sum.inl 5429, 4)]

def keyMomentRow2488 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 1), (Sum.inl 5429, 4)]

def keyMomentRow2489 : Integer.Sparse OriginalKey := [(Sum.inl 3869, 1), (Sum.inl 5414, 4)]

def keyMomentRow2490 : Integer.Sparse OriginalKey := [(Sum.inl 3959, 1), (Sum.inl 5446, 4)]

def keyMomentRow2491 : Integer.Sparse OriginalKey := [(Sum.inl 3565, 1), (Sum.inl 5164, 4)]

def keyMomentRow2492 : Integer.Sparse OriginalKey := [(Sum.inl 3955, 1), (Sum.inl 5470, 4)]

def keyMomentRow2493 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 1), (Sum.inl 5300, 4)]

def keyMomentRow2494 : Integer.Sparse OriginalKey := [(Sum.inl 3306, 1), (Sum.inl 4620, 4)]

def keyMomentRow2495 : Integer.Sparse OriginalKey := [(Sum.inl 3294, 1), (Sum.inl 4603, 4)]

def keyMomentChunk77 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2464, keyMomentRow2465, keyMomentRow2466, keyMomentRow2467, keyMomentRow2468, keyMomentRow2469, keyMomentRow2470, keyMomentRow2471, keyMomentRow2472, keyMomentRow2473, keyMomentRow2474, keyMomentRow2475, keyMomentRow2476, keyMomentRow2477, keyMomentRow2478, keyMomentRow2479, keyMomentRow2480, keyMomentRow2481, keyMomentRow2482, keyMomentRow2483, keyMomentRow2484, keyMomentRow2485, keyMomentRow2486, keyMomentRow2487, keyMomentRow2488, keyMomentRow2489, keyMomentRow2490, keyMomentRow2491, keyMomentRow2492, keyMomentRow2493, keyMomentRow2494, keyMomentRow2495]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2496 : Integer.Sparse OriginalKey := [(Sum.inl 3565, 1), (Sum.inl 5164, 4)]

def keyMomentRow2497 : Integer.Sparse OriginalKey := [(Sum.inl 3580, 1), (Sum.inl 5282, 4)]

def keyMomentRow2498 : Integer.Sparse OriginalKey := [(Sum.inl 3960, 1), (Sum.inl 5463, 4)]

def keyMomentRow2499 : Integer.Sparse OriginalKey := [(Sum.inl 3562, 1), (Sum.inl 5145, 4)]

def keyMomentRow2500 : Integer.Sparse OriginalKey := [(Sum.inl 3538, 1), (Sum.inl 5188, 4)]

def keyMomentRow2501 : Integer.Sparse OriginalKey := [(Sum.inl 3524, 1), (Sum.inl 5184, 4)]

def keyMomentRow2502 : Integer.Sparse OriginalKey := [(Sum.inl 3537, 1), (Sum.inl 5187, 4)]

def keyMomentRow2503 : Integer.Sparse OriginalKey := [(Sum.inl 3523, 1), (Sum.inl 5139, 4)]

def keyMomentRow2504 : Integer.Sparse OriginalKey := [(Sum.inl 3529, 1), (Sum.inl 5185, 4)]

def keyMomentRow2505 : Integer.Sparse OriginalKey := [(Sum.inl 3302, 1), (Sum.inl 4609, 4)]

def keyMomentRow2506 : Integer.Sparse OriginalKey := [(Sum.inl 3530, 1), (Sum.inl 5147, 4)]

def keyMomentRow2507 : Integer.Sparse OriginalKey := [(Sum.inl 3542, 1), (Sum.inl 5189, 4)]

def keyMomentRow2508 : Integer.Sparse OriginalKey := [(Sum.inl 2778, 1), (Sum.inl 4899, 4)]

def keyMomentRow2509 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 1), (Sum.inl 5268, 4)]

def keyMomentRow2510 : Integer.Sparse OriginalKey := [(Sum.inl 2776, 1), (Sum.inl 5302, 4)]

def keyMomentRow2511 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 1), (Sum.inl 5300, 4)]

def keyMomentRow2512 : Integer.Sparse OriginalKey := [(Sum.inl 2680, 1), (Sum.inl 5235, 4)]

def keyMomentRow2513 : Integer.Sparse OriginalKey := [(Sum.inl 2732, 1), (Sum.inl 5267, 4)]

def keyMomentRow2514 : Integer.Sparse OriginalKey := [(Sum.inl 2773, 1), (Sum.inl 5299, 4)]

def keyMomentRow2515 : Integer.Sparse OriginalKey := [(Sum.inl 2678, 1), (Sum.inl 5233, 4)]

def keyMomentRow2516 : Integer.Sparse OriginalKey := [(Sum.inl 2677, 1), (Sum.inl 5232, 4)]

def keyMomentRow2517 : Integer.Sparse OriginalKey := [(Sum.inl 2664, 1), (Sum.inl 5222, 4)]

def keyMomentRow2518 : Integer.Sparse OriginalKey := [(Sum.inl 2731, 1), (Sum.inl 5266, 4)]

def keyMomentRow2519 : Integer.Sparse OriginalKey := [(Sum.inl 2775, 1), (Sum.inl 5301, 4)]

def keyMomentRow2520 : Integer.Sparse OriginalKey := [(Sum.inl 2676, 1), (Sum.inl 5231, 4)]

def keyMomentRow2521 : Integer.Sparse OriginalKey := [(Sum.inl 2698, 1), (Sum.inl 5244, 4)]

def keyMomentRow2522 : Integer.Sparse OriginalKey := [(Sum.inl 2730, 1), (Sum.inl 5265, 4)]

def keyMomentRow2523 : Integer.Sparse OriginalKey := [(Sum.inl 2697, 1), (Sum.inl 5243, 4)]

def keyMomentRow2524 : Integer.Sparse OriginalKey := [(Sum.inl 3225, 1), (Sum.inl 4896, 4)]

def keyMomentRow2525 : Integer.Sparse OriginalKey := [(Sum.inl 3039, 1), (Sum.inl 5266, 4)]

def keyMomentRow2526 : Integer.Sparse OriginalKey := [(Sum.inl 3883, 1), (Sum.inl 5411, 4)]

def keyMomentRow2527 : Integer.Sparse OriginalKey := [(Sum.inl 3881, 1), (Sum.inl 5446, 4)]

def keyMomentChunk78 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2496, keyMomentRow2497, keyMomentRow2498, keyMomentRow2499, keyMomentRow2500, keyMomentRow2501, keyMomentRow2502, keyMomentRow2503, keyMomentRow2504, keyMomentRow2505, keyMomentRow2506, keyMomentRow2507, keyMomentRow2508, keyMomentRow2509, keyMomentRow2510, keyMomentRow2511, keyMomentRow2512, keyMomentRow2513, keyMomentRow2514, keyMomentRow2515, keyMomentRow2516, keyMomentRow2517, keyMomentRow2518, keyMomentRow2519, keyMomentRow2520, keyMomentRow2521, keyMomentRow2522, keyMomentRow2523, keyMomentRow2524, keyMomentRow2525, keyMomentRow2526, keyMomentRow2527]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2528 : Integer.Sparse OriginalKey := [(Sum.inl 2678, 1), (Sum.inl 5233, 4)]

def keyMomentRow2529 : Integer.Sparse OriginalKey := [(Sum.inl 3872, 1), (Sum.inl 5425, 4)]

def keyMomentRow2530 : Integer.Sparse OriginalKey := [(Sum.inl 3871, 1), (Sum.inl 5430, 4)]

def keyMomentRow2531 : Integer.Sparse OriginalKey := [(Sum.inl 3870, 1), (Sum.inl 5420, 4)]

def keyMomentRow2532 : Integer.Sparse OriginalKey := [(Sum.inl 3834, 1), (Sum.inl 5381, 4)]

def keyMomentRow2533 : Integer.Sparse OriginalKey := [(Sum.inl 2662, 1), (Sum.inl 5220, 4)]

def keyMomentRow2534 : Integer.Sparse OriginalKey := [(Sum.inl 3880, 1), (Sum.inl 5445, 4)]

def keyMomentRow2535 : Integer.Sparse OriginalKey := [(Sum.inl 3882, 1), (Sum.inl 5447, 4)]

def keyMomentRow2536 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 1), (Sum.inl 5300, 4)]

def keyMomentRow2537 : Integer.Sparse OriginalKey := [(Sum.inl 2687, 1), (Sum.inl 5206, 4)]

def keyMomentRow2538 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 1), (Sum.inl 5436, 4)]

def keyMomentRow2539 : Integer.Sparse OriginalKey := [(Sum.inl 3570, 1), (Sum.inl 5198, 4)]

def keyMomentRow2540 : Integer.Sparse OriginalKey := [(Sum.inl 3538, 1), (Sum.inl 5188, 4)]

def keyMomentRow2541 : Integer.Sparse OriginalKey := [(Sum.inl 2673, 1), (Sum.inl 5229, 4)]

def keyMomentRow2542 : Integer.Sparse OriginalKey := [(Sum.inl 3884, 1), (Sum.inl 5446, 4)]

def keyMomentRow2543 : Integer.Sparse OriginalKey := [(Sum.inl 3524, 1), (Sum.inl 5184, 4)]

def keyMomentRow2544 : Integer.Sparse OriginalKey := [(Sum.inl 3873, 1), (Sum.inl 5421, 4)]

def keyMomentRow2545 : Integer.Sparse OriginalKey := [(Sum.inl 3874, 1), (Sum.inl 5429, 4)]

def keyMomentRow2546 : Integer.Sparse OriginalKey := [(Sum.inl 3832, 1), (Sum.inl 5379, 4)]

def keyMomentRow2547 : Integer.Sparse OriginalKey := [(Sum.inl 3224, 1), (Sum.inl 4898, 4)]

def keyMomentRow2548 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 1), (Sum.inl 5267, 4)]

def keyMomentRow2549 : Integer.Sparse OriginalKey := [(Sum.inl 3856, 1), (Sum.inl 5412, 4)]

def keyMomentRow2550 : Integer.Sparse OriginalKey := [(Sum.inl 3854, 1), (Sum.inl 5436, 4)]

def keyMomentRow2551 : Integer.Sparse OriginalKey := [(Sum.inl 2677, 1), (Sum.inl 5232, 4)]

def keyMomentRow2552 : Integer.Sparse OriginalKey := [(Sum.inl 3841, 1), (Sum.inl 5426, 4)]

def keyMomentRow2553 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 1), (Sum.inl 5425, 4)]

def keyMomentRow2554 : Integer.Sparse OriginalKey := [(Sum.inl 3834, 1), (Sum.inl 5381, 4)]

def keyMomentRow2555 : Integer.Sparse OriginalKey := [(Sum.inl 3833, 1), (Sum.inl 5376, 4)]

def keyMomentRow2556 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 1), (Sum.inl 5219, 4)]

def keyMomentRow2557 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 1), (Sum.inl 5425, 4)]

def keyMomentRow2558 : Integer.Sparse OriginalKey := [(Sum.inl 3855, 1), (Sum.inl 5437, 4)]

def keyMomentRow2559 : Integer.Sparse OriginalKey := [(Sum.inl 3223, 1), (Sum.inl 4889, 4)]

def keyMomentChunk79 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2528, keyMomentRow2529, keyMomentRow2530, keyMomentRow2531, keyMomentRow2532, keyMomentRow2533, keyMomentRow2534, keyMomentRow2535, keyMomentRow2536, keyMomentRow2537, keyMomentRow2538, keyMomentRow2539, keyMomentRow2540, keyMomentRow2541, keyMomentRow2542, keyMomentRow2543, keyMomentRow2544, keyMomentRow2545, keyMomentRow2546, keyMomentRow2547, keyMomentRow2548, keyMomentRow2549, keyMomentRow2550, keyMomentRow2551, keyMomentRow2552, keyMomentRow2553, keyMomentRow2554, keyMomentRow2555, keyMomentRow2556, keyMomentRow2557, keyMomentRow2558, keyMomentRow2559]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow256 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow257 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow258 : Integer.Sparse OriginalKey := [(Sum.inl 504, 5)]

def keyMomentRow259 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow260 : Integer.Sparse OriginalKey := [(Sum.inl 272, 5)]

def keyMomentRow261 : Integer.Sparse OriginalKey := [(Sum.inl 469, 5)]

def keyMomentRow262 : Integer.Sparse OriginalKey := [(Sum.inl 516, 5)]

def keyMomentRow263 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow264 : Integer.Sparse OriginalKey := [(Sum.inl 483, 5)]

def keyMomentRow265 : Integer.Sparse OriginalKey := [(Sum.inl 498, 5)]

def keyMomentRow266 : Integer.Sparse OriginalKey := [(Sum.inl 491, 5)]

def keyMomentRow267 : Integer.Sparse OriginalKey := [(Sum.inl 514, 5)]

def keyMomentRow268 : Integer.Sparse OriginalKey := [(Sum.inl 515, 5)]

def keyMomentRow269 : Integer.Sparse OriginalKey := [(Sum.inl 512, 5)]

def keyMomentRow270 : Integer.Sparse OriginalKey := [(Sum.inl 513, 5)]

def keyMomentRow271 : Integer.Sparse OriginalKey := [(Sum.inr 4, 5)]

def keyMomentRow272 : Integer.Sparse OriginalKey := [(Sum.inl 489, 5)]

def keyMomentRow273 : Integer.Sparse OriginalKey := [(Sum.inl 268, 5)]

def keyMomentRow274 : Integer.Sparse OriginalKey := [(Sum.inl 467, 5)]

def keyMomentRow275 : Integer.Sparse OriginalKey := [(Sum.inl 498, 5)]

def keyMomentRow276 : Integer.Sparse OriginalKey := [(Sum.inl 381, 5)]

def keyMomentRow277 : Integer.Sparse OriginalKey := [(Sum.inl 480, 5)]

def keyMomentRow278 : Integer.Sparse OriginalKey := [(Sum.inl 444, 5)]

def keyMomentRow279 : Integer.Sparse OriginalKey := [(Sum.inl 443, 5)]

def keyMomentRow280 : Integer.Sparse OriginalKey := [(Sum.inl 485, 5)]

def keyMomentRow281 : Integer.Sparse OriginalKey := [(Sum.inl 499, 5)]

def keyMomentRow282 : Integer.Sparse OriginalKey := [(Sum.inl 521, 5)]

def keyMomentRow283 : Integer.Sparse OriginalKey := [(Sum.inl 479, 5)]

def keyMomentRow284 : Integer.Sparse OriginalKey := [(Sum.inl 409, 5)]

def keyMomentRow285 : Integer.Sparse OriginalKey := [(Sum.inl 387, 5)]

def keyMomentRow286 : Integer.Sparse OriginalKey := [(Sum.inl 150, 5)]

def keyMomentRow287 : Integer.Sparse OriginalKey := [(Sum.inl 145, 5)]

def keyMomentChunk8 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow256, keyMomentRow257, keyMomentRow258, keyMomentRow259, keyMomentRow260, keyMomentRow261, keyMomentRow262, keyMomentRow263, keyMomentRow264, keyMomentRow265, keyMomentRow266, keyMomentRow267, keyMomentRow268, keyMomentRow269, keyMomentRow270, keyMomentRow271, keyMomentRow272, keyMomentRow273, keyMomentRow274, keyMomentRow275, keyMomentRow276, keyMomentRow277, keyMomentRow278, keyMomentRow279, keyMomentRow280, keyMomentRow281, keyMomentRow282, keyMomentRow283, keyMomentRow284, keyMomentRow285, keyMomentRow286, keyMomentRow287]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2560 : Integer.Sparse OriginalKey := [(Sum.inl 3037, 1), (Sum.inl 5265, 4)]

def keyMomentRow2561 : Integer.Sparse OriginalKey := [(Sum.inl 3847, 1), (Sum.inl 5406, 4)]

def keyMomentRow2562 : Integer.Sparse OriginalKey := [(Sum.inl 3846, 1), (Sum.inl 5429, 4)]

def keyMomentRow2563 : Integer.Sparse OriginalKey := [(Sum.inl 2676, 1), (Sum.inl 5231, 4)]

def keyMomentRow2564 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 1), (Sum.inl 5299, 4)]

def keyMomentRow2565 : Integer.Sparse OriginalKey := [(Sum.inl 2681, 1), (Sum.inl 5151, 4)]

def keyMomentRow2566 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 1), (Sum.inl 5425, 4)]

def keyMomentRow2567 : Integer.Sparse OriginalKey := [(Sum.inl 3557, 1), (Sum.inl 5144, 4)]

def keyMomentRow2568 : Integer.Sparse OriginalKey := [(Sum.inl 3516, 1), (Sum.inl 5129, 4)]

def keyMomentRow2569 : Integer.Sparse OriginalKey := [(Sum.inl 3848, 1), (Sum.inl 5430, 4)]

def keyMomentRow2570 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 1), (Sum.inl 5276, 4)]

def keyMomentRow2571 : Integer.Sparse OriginalKey := [(Sum.inl 2683, 1), (Sum.inl 4611, 4)]

def keyMomentRow2572 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 1), (Sum.inl 5267, 4)]

def keyMomentRow2573 : Integer.Sparse OriginalKey := [(Sum.inl 3296, 1), (Sum.inl 4607, 4)]

def keyMomentRow2574 : Integer.Sparse OriginalKey := [(Sum.inl 3295, 1), (Sum.inl 4592, 4)]

def keyMomentRow2575 : Integer.Sparse OriginalKey := [(Sum.inl 2670, 1), (Sum.inl 5140, 4)]

def keyMomentRow2576 : Integer.Sparse OriginalKey := [(Sum.inl 3540, 1), (Sum.inl 5260, 4)]

def keyMomentRow2577 : Integer.Sparse OriginalKey := [(Sum.inl 2682, 1), (Sum.inl 5236, 4)]

def keyMomentRow2578 : Integer.Sparse OriginalKey := [(Sum.inl 3288, 1), (Sum.inl 4589, 4)]

def keyMomentRow2579 : Integer.Sparse OriginalKey := [(Sum.inl 3517, 1), (Sum.inl 5138, 4)]

def keyMomentRow2580 : Integer.Sparse OriginalKey := [(Sum.inl 3539, 1), (Sum.inl 5251, 4)]

def keyMomentRow2581 : Integer.Sparse OriginalKey := [(Sum.inl 3842, 1), (Sum.inl 5419, 4)]

def keyMomentRow2582 : Integer.Sparse OriginalKey := [(Sum.inl 3516, 1), (Sum.inl 5129, 4)]

def keyMomentRow2583 : Integer.Sparse OriginalKey := [(Sum.inl 3835, 1), (Sum.inl 5377, 4)]

def keyMomentRow2584 : Integer.Sparse OriginalKey := [(Sum.inl 2255, 1), (Sum.inl 4892, 4)]

def keyMomentRow2585 : Integer.Sparse OriginalKey := [(Sum.inl 2197, 1), (Sum.inl 4836, 4)]

def keyMomentRow2586 : Integer.Sparse OriginalKey := [(Sum.inl 2253, 1), (Sum.inl 4891, 4)]

def keyMomentRow2587 : Integer.Sparse OriginalKey := [(Sum.inl 2251, 1), (Sum.inl 4867, 4)]

def keyMomentRow2588 : Integer.Sparse OriginalKey := [(Sum.inl 2146, 1), (Sum.inl 4683, 4)]

def keyMomentRow2589 : Integer.Sparse OriginalKey := [(Sum.inl 2196, 1), (Sum.inl 4816, 4)]

def keyMomentRow2590 : Integer.Sparse OriginalKey := [(Sum.inl 2250, 1), (Sum.inl 4852, 4)]

def keyMomentRow2591 : Integer.Sparse OriginalKey := [(Sum.inl 2145, 1), (Sum.inl 4680, 4)]

def keyMomentChunk80 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2560, keyMomentRow2561, keyMomentRow2562, keyMomentRow2563, keyMomentRow2564, keyMomentRow2565, keyMomentRow2566, keyMomentRow2567, keyMomentRow2568, keyMomentRow2569, keyMomentRow2570, keyMomentRow2571, keyMomentRow2572, keyMomentRow2573, keyMomentRow2574, keyMomentRow2575, keyMomentRow2576, keyMomentRow2577, keyMomentRow2578, keyMomentRow2579, keyMomentRow2580, keyMomentRow2581, keyMomentRow2582, keyMomentRow2583, keyMomentRow2584, keyMomentRow2585, keyMomentRow2586, keyMomentRow2587, keyMomentRow2588, keyMomentRow2589, keyMomentRow2590, keyMomentRow2591]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2592 : Integer.Sparse OriginalKey := [(Sum.inl 2144, 1), (Sum.inl 4665, 4)]

def keyMomentRow2593 : Integer.Sparse OriginalKey := [(Sum.inl 2171, 1), (Sum.inl 4762, 4)]

def keyMomentRow2594 : Integer.Sparse OriginalKey := [(Sum.inl 2195, 1), (Sum.inl 4803, 4)]

def keyMomentRow2595 : Integer.Sparse OriginalKey := [(Sum.inl 2252, 1), (Sum.inl 4885, 4)]

def keyMomentRow2596 : Integer.Sparse OriginalKey := [(Sum.inl 3222, 1), (Sum.inl 4891, 4)]

def keyMomentRow2597 : Integer.Sparse OriginalKey := [(Sum.inl 3016, 1), (Sum.inl 5254, 4)]

def keyMomentRow2598 : Integer.Sparse OriginalKey := [(Sum.inl 3803, 1), (Sum.inl 5407, 4)]

def keyMomentRow2599 : Integer.Sparse OriginalKey := [(Sum.inl 3802, 1), (Sum.inl 5402, 4)]

def keyMomentRow2600 : Integer.Sparse OriginalKey := [(Sum.inl 2654, 1), (Sum.inl 5216, 4)]

def keyMomentRow2601 : Integer.Sparse OriginalKey := [(Sum.inl 3025, 1), (Sum.inl 5287, 4)]

def keyMomentRow2602 : Integer.Sparse OriginalKey := [(Sum.inl 2659, 1), (Sum.inl 4976, 4)]

def keyMomentRow2603 : Integer.Sparse OriginalKey := [(Sum.inl 3762, 1), (Sum.inl 5360, 4)]

def keyMomentRow2604 : Integer.Sparse OriginalKey := [(Sum.inl 3553, 1), (Sum.inl 4963, 4)]

def keyMomentRow2605 : Integer.Sparse OriginalKey := [(Sum.inl 3509, 1), (Sum.inl 4957, 4)]

def keyMomentRow2606 : Integer.Sparse OriginalKey := [(Sum.inl 2653, 1), (Sum.inl 5215, 4)]

def keyMomentRow2607 : Integer.Sparse OriginalKey := [(Sum.inl 3761, 1), (Sum.inl 5353, 4)]

def keyMomentRow2608 : Integer.Sparse OriginalKey := [(Sum.inl 3221, 1), (Sum.inl 4885, 4)]

def keyMomentRow2609 : Integer.Sparse OriginalKey := [(Sum.inl 3023, 1), (Sum.inl 5286, 4)]

def keyMomentRow2610 : Integer.Sparse OriginalKey := [(Sum.inl 2655, 1), (Sum.inl 5116, 4)]

def keyMomentRow2611 : Integer.Sparse OriginalKey := [(Sum.inl 3024, 1), (Sum.inl 5103, 4)]

def keyMomentRow2612 : Integer.Sparse OriginalKey := [(Sum.inl 2657, 1), (Sum.inl 4548, 4)]

def keyMomentRow2613 : Integer.Sparse OriginalKey := [(Sum.inl 3464, 1), (Sum.inl 5086, 4)]

def keyMomentRow2614 : Integer.Sparse OriginalKey := [(Sum.inl 3259, 1), (Sum.inl 4545, 4)]

def keyMomentRow2615 : Integer.Sparse OriginalKey := [(Sum.inl 3258, 1), (Sum.inl 4529, 4)]

def keyMomentRow2616 : Integer.Sparse OriginalKey := [(Sum.inl 2652, 1), (Sum.inl 5035, 4)]

def keyMomentRow2617 : Integer.Sparse OriginalKey := [(Sum.inl 3463, 1), (Sum.inl 5074, 4)]

def keyMomentRow2618 : Integer.Sparse OriginalKey := [(Sum.inl 2656, 1), (Sum.inl 5217, 4)]

def keyMomentRow2619 : Integer.Sparse OriginalKey := [(Sum.inl 1716, 1), (Sum.inl 4500, 4)]

def keyMomentRow2620 : Integer.Sparse OriginalKey := [(Sum.inl 1513, 1), (Sum.inl 4179, 4)]

def keyMomentRow2621 : Integer.Sparse OriginalKey := [(Sum.inl 1715, 1), (Sum.inl 4475, 4)]

def keyMomentRow2622 : Integer.Sparse OriginalKey := [(Sum.inl 1512, 1), (Sum.inl 4176, 4)]

def keyMomentRow2623 : Integer.Sparse OriginalKey := [(Sum.inl 1511, 1), (Sum.inl 4154, 4)]

def keyMomentChunk81 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2592, keyMomentRow2593, keyMomentRow2594, keyMomentRow2595, keyMomentRow2596, keyMomentRow2597, keyMomentRow2598, keyMomentRow2599, keyMomentRow2600, keyMomentRow2601, keyMomentRow2602, keyMomentRow2603, keyMomentRow2604, keyMomentRow2605, keyMomentRow2606, keyMomentRow2607, keyMomentRow2608, keyMomentRow2609, keyMomentRow2610, keyMomentRow2611, keyMomentRow2612, keyMomentRow2613, keyMomentRow2614, keyMomentRow2615, keyMomentRow2616, keyMomentRow2617, keyMomentRow2618, keyMomentRow2619, keyMomentRow2620, keyMomentRow2621, keyMomentRow2622, keyMomentRow2623]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2624 : Integer.Sparse OriginalKey := [(Sum.inl 1714, 1), (Sum.inl 4459, 4)]

def keyMomentRow2625 : Integer.Sparse OriginalKey := [(Sum.inl 2658, 1), (Sum.inl 4945, 4)]

def keyMomentRow2626 : Integer.Sparse OriginalKey := [(Sum.inl 1510, 1), (Sum.inl 4152, 4)]

def keyMomentRow2627 : Integer.Sparse OriginalKey := [(Sum.inl 1668, 1), (Sum.inl 4345, 4)]

def keyMomentRow2628 : Integer.Sparse OriginalKey := [(Sum.inl 1713, 1), (Sum.inl 4439, 4)]

def keyMomentRow2629 : Integer.Sparse OriginalKey := [(Sum.inl 3407, 1), (Sum.inl 4942, 4)]

def keyMomentRow2630 : Integer.Sparse OriginalKey := [(Sum.inl 1667, 1), (Sum.inl 4328, 4)]

def keyMomentRow2631 : Integer.Sparse OriginalKey := [(Sum.inl 3406, 1), (Sum.inl 4931, 4)]

def keyMomentRow2632 : Integer.Sparse OriginalKey := [(Sum.inl 2217, 1), (Sum.inl 4821, 4)]

def keyMomentRow2633 : Integer.Sparse OriginalKey := [(Sum.inl 2274, 1), (Sum.inl 4856, 4)]

def keyMomentRow2634 : Integer.Sparse OriginalKey := [(Sum.inl 2158, 1), (Sum.inl 4690, 4)]

def keyMomentRow2635 : Integer.Sparse OriginalKey := [(Sum.inl 2154, 1), (Sum.inl 4668, 4)]

def keyMomentRow2636 : Integer.Sparse OriginalKey := [(Sum.inl 2178, 1), (Sum.inl 4768, 4)]

def keyMomentRow2637 : Integer.Sparse OriginalKey := [(Sum.inl 2213, 1), (Sum.inl 4795, 4)]

def keyMomentRow2638 : Integer.Sparse OriginalKey := [(Sum.inl 3762, 1), (Sum.inl 5360, 4)]

def keyMomentRow2639 : Integer.Sparse OriginalKey := [(Sum.inl 3761, 1), (Sum.inl 5353, 4)]

def keyMomentRow2640 : Integer.Sparse OriginalKey := [(Sum.inl 3760, 1), (Sum.inl 5339, 4)]

def keyMomentRow2641 : Integer.Sparse OriginalKey := [(Sum.inl 3772, 1), (Sum.inl 5361, 4)]

def keyMomentRow2642 : Integer.Sparse OriginalKey := [(Sum.inl 3555, 1), (Sum.inl 4966, 4)]

def keyMomentRow2643 : Integer.Sparse OriginalKey := [(Sum.inl 3508, 1), (Sum.inl 4955, 4)]

def keyMomentRow2644 : Integer.Sparse OriginalKey := [(Sum.inl 3755, 1), (Sum.inl 5338, 4)]

def keyMomentRow2645 : Integer.Sparse OriginalKey := [(Sum.inl 3768, 1), (Sum.inl 5348, 4)]

def keyMomentRow2646 : Integer.Sparse OriginalKey := [(Sum.inl 3759, 1), (Sum.inl 5359, 4)]

def keyMomentRow2647 : Integer.Sparse OriginalKey := [(Sum.inl 3556, 1), (Sum.inl 5112, 4)]

def keyMomentRow2648 : Integer.Sparse OriginalKey := [(Sum.inl 3480, 1), (Sum.inl 5090, 4)]

def keyMomentRow2649 : Integer.Sparse OriginalKey := [(Sum.inl 3271, 1), (Sum.inl 4556, 4)]

def keyMomentRow2650 : Integer.Sparse OriginalKey := [(Sum.inl 3267, 1), (Sum.inl 4533, 4)]

def keyMomentRow2651 : Integer.Sparse OriginalKey := [(Sum.inl 3454, 1), (Sum.inl 5040, 4)]

def keyMomentRow2652 : Integer.Sparse OriginalKey := [(Sum.inl 3476, 1), (Sum.inl 5067, 4)]

def keyMomentRow2653 : Integer.Sparse OriginalKey := [(Sum.inl 3763, 1), (Sum.inl 5340, 4)]

def keyMomentRow2654 : Integer.Sparse OriginalKey := [(Sum.inl 1740, 1), (Sum.inl 4480, 4)]

def keyMomentRow2655 : Integer.Sparse OriginalKey := [(Sum.inl 1526, 1), (Sum.inl 4188, 4)]

def keyMomentChunk82 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2624, keyMomentRow2625, keyMomentRow2626, keyMomentRow2627, keyMomentRow2628, keyMomentRow2629, keyMomentRow2630, keyMomentRow2631, keyMomentRow2632, keyMomentRow2633, keyMomentRow2634, keyMomentRow2635, keyMomentRow2636, keyMomentRow2637, keyMomentRow2638, keyMomentRow2639, keyMomentRow2640, keyMomentRow2641, keyMomentRow2642, keyMomentRow2643, keyMomentRow2644, keyMomentRow2645, keyMomentRow2646, keyMomentRow2647, keyMomentRow2648, keyMomentRow2649, keyMomentRow2650, keyMomentRow2651, keyMomentRow2652, keyMomentRow2653, keyMomentRow2654, keyMomentRow2655]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2656 : Integer.Sparse OriginalKey := [(Sum.inl 1522, 1), (Sum.inl 4158, 4)]

def keyMomentRow2657 : Integer.Sparse OriginalKey := [(Sum.inl 1682, 1), (Sum.inl 4357, 4)]

def keyMomentRow2658 : Integer.Sparse OriginalKey := [(Sum.inl 1736, 1), (Sum.inl 4444, 4)]

def keyMomentRow2659 : Integer.Sparse OriginalKey := [(Sum.inl 3418, 1), (Sum.inl 4951, 4)]

def keyMomentRow2660 : Integer.Sparse OriginalKey := [(Sum.inl 1678, 1), (Sum.inl 4332, 4)]

def keyMomentRow2661 : Integer.Sparse OriginalKey := [(Sum.inl 3414, 1), (Sum.inl 4933, 4)]

def keyMomentRow2662 : Integer.Sparse OriginalKey := [(Sum.inl 2155, 1), (Sum.inl 4669, 4)]

def keyMomentRow2663 : Integer.Sparse OriginalKey := [(Sum.inl 2176, 1), (Sum.inl 4756, 4)]

def keyMomentRow2664 : Integer.Sparse OriginalKey := [(Sum.inl 3509, 1), (Sum.inl 4957, 4)]

def keyMomentRow2665 : Integer.Sparse OriginalKey := [(Sum.inl 3512, 1), (Sum.inl 4959, 4)]

def keyMomentRow2666 : Integer.Sparse OriginalKey := [(Sum.inl 3508, 1), (Sum.inl 4955, 4)]

def keyMomentRow2667 : Integer.Sparse OriginalKey := [(Sum.inl 3510, 1), (Sum.inl 4956, 4)]

def keyMomentRow2668 : Integer.Sparse OriginalKey := [(Sum.inl 3268, 1), (Sum.inl 4534, 4)]

def keyMomentRow2669 : Integer.Sparse OriginalKey := [(Sum.inl 3452, 1), (Sum.inl 4954, 4)]

def keyMomentRow2670 : Integer.Sparse OriginalKey := [(Sum.inl 3511, 1), (Sum.inl 4958, 4)]

def keyMomentRow2671 : Integer.Sparse OriginalKey := [(Sum.inl 1523, 1), (Sum.inl 4160, 4)]

def keyMomentRow2672 : Integer.Sparse OriginalKey := [(Sum.inl 1679, 1), (Sum.inl 4334, 4)]

def keyMomentRow2673 : Integer.Sparse OriginalKey := [(Sum.inl 3415, 1), (Sum.inl 4934, 4)]

def keyMomentRow2674 : Integer.Sparse OriginalKey := [(Sum.inl 2744, 1), (Sum.inl 5276, 4)]

def keyMomentRow2675 : Integer.Sparse OriginalKey := [(Sum.inl 2781, 1), (Sum.inl 5295, 4)]

def keyMomentRow2676 : Integer.Sparse OriginalKey := [(Sum.inl 2687, 1), (Sum.inl 5206, 4)]

def keyMomentRow2677 : Integer.Sparse OriginalKey := [(Sum.inl 2681, 1), (Sum.inl 5151, 4)]

def keyMomentRow2678 : Integer.Sparse OriginalKey := [(Sum.inl 2706, 1), (Sum.inl 5205, 4)]

def keyMomentRow2679 : Integer.Sparse OriginalKey := [(Sum.inl 2738, 1), (Sum.inl 5270, 4)]

def keyMomentRow2680 : Integer.Sparse OriginalKey := [(Sum.inl 2700, 1), (Sum.inl 5150, 4)]

def keyMomentRow2681 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 1), (Sum.inl 5299, 4)]

def keyMomentRow2682 : Integer.Sparse OriginalKey := [(Sum.inl 3572, 1), (Sum.inl 5289, 4)]

def keyMomentRow2683 : Integer.Sparse OriginalKey := [(Sum.inl 3570, 1), (Sum.inl 5198, 4)]

def keyMomentRow2684 : Integer.Sparse OriginalKey := [(Sum.inl 3557, 1), (Sum.inl 5144, 4)]

def keyMomentRow2685 : Integer.Sparse OriginalKey := [(Sum.inl 3569, 1), (Sum.inl 5197, 4)]

def keyMomentRow2686 : Integer.Sparse OriginalKey := [(Sum.inl 3571, 1), (Sum.inl 5281, 4)]

def keyMomentRow2687 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 1), (Sum.inl 5300, 4)]

def keyMomentChunk83 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2656, keyMomentRow2657, keyMomentRow2658, keyMomentRow2659, keyMomentRow2660, keyMomentRow2661, keyMomentRow2662, keyMomentRow2663, keyMomentRow2664, keyMomentRow2665, keyMomentRow2666, keyMomentRow2667, keyMomentRow2668, keyMomentRow2669, keyMomentRow2670, keyMomentRow2671, keyMomentRow2672, keyMomentRow2673, keyMomentRow2674, keyMomentRow2675, keyMomentRow2676, keyMomentRow2677, keyMomentRow2678, keyMomentRow2679, keyMomentRow2680, keyMomentRow2681, keyMomentRow2682, keyMomentRow2683, keyMomentRow2684, keyMomentRow2685, keyMomentRow2686, keyMomentRow2687]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2688 : Integer.Sparse OriginalKey := [(Sum.inl 3579, 1), (Sum.inl 5201, 4)]

def keyMomentRow2689 : Integer.Sparse OriginalKey := [(Sum.inl 3530, 1), (Sum.inl 5147, 4)]

def keyMomentRow2690 : Integer.Sparse OriginalKey := [(Sum.inl 3578, 1), (Sum.inl 5199, 4)]

def keyMomentRow2691 : Integer.Sparse OriginalKey := [(Sum.inl 3580, 1), (Sum.inl 5282, 4)]

def keyMomentRow2692 : Integer.Sparse OriginalKey := [(Sum.inl 3562, 1), (Sum.inl 5145, 4)]

def keyMomentRow2693 : Integer.Sparse OriginalKey := [(Sum.inl 3541, 1), (Sum.inl 5267, 4)]

def keyMomentRow2694 : Integer.Sparse OriginalKey := [(Sum.inl 3540, 1), (Sum.inl 5260, 4)]

def keyMomentRow2695 : Integer.Sparse OriginalKey := [(Sum.inl 3538, 1), (Sum.inl 5188, 4)]

def keyMomentRow2696 : Integer.Sparse OriginalKey := [(Sum.inl 3516, 1), (Sum.inl 5129, 4)]

def keyMomentRow2697 : Integer.Sparse OriginalKey := [(Sum.inl 3537, 1), (Sum.inl 5187, 4)]

def keyMomentRow2698 : Integer.Sparse OriginalKey := [(Sum.inl 3539, 1), (Sum.inl 5251, 4)]

def keyMomentRow2699 : Integer.Sparse OriginalKey := [(Sum.inl 3526, 1), (Sum.inl 5265, 4)]

def keyMomentRow2700 : Integer.Sparse OriginalKey := [(Sum.inl 3524, 1), (Sum.inl 5184, 4)]

def keyMomentRow2701 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 1), (Sum.inl 5266, 4)]

def keyMomentRow2702 : Integer.Sparse OriginalKey := [(Sum.inl 3530, 1), (Sum.inl 5147, 4)]

def keyMomentRow2703 : Integer.Sparse OriginalKey := [(Sum.inl 3549, 1), (Sum.inl 5268, 4)]

def keyMomentRow2704 : Integer.Sparse OriginalKey := [(Sum.inl 3302, 1), (Sum.inl 4609, 4)]

def keyMomentRow2705 : Integer.Sparse OriginalKey := [(Sum.inl 3291, 1), (Sum.inl 4591, 4)]

def keyMomentRow2706 : Integer.Sparse OriginalKey := [(Sum.inl 3523, 1), (Sum.inl 5139, 4)]

def keyMomentRow2707 : Integer.Sparse OriginalKey := [(Sum.inl 3543, 1), (Sum.inl 5252, 4)]

def keyMomentRow2708 : Integer.Sparse OriginalKey := [(Sum.inl 3542, 1), (Sum.inl 5189, 4)]

def keyMomentRow2709 : Integer.Sparse OriginalKey := [(Sum.inl 3519, 1), (Sum.inl 5128, 4)]

def keyMomentRow2710 : Integer.Sparse OriginalKey := [(Sum.inl 2207, 1), (Sum.inl 4817, 4)]

def keyMomentRow2711 : Integer.Sparse OriginalKey := [(Sum.inl 2259, 1), (Sum.inl 4853, 4)]

def keyMomentRow2712 : Integer.Sparse OriginalKey := [(Sum.inl 2153, 1), (Sum.inl 4682, 4)]

def keyMomentRow2713 : Integer.Sparse OriginalKey := [(Sum.inl 2147, 1), (Sum.inl 4664, 4)]

def keyMomentRow2714 : Integer.Sparse OriginalKey := [(Sum.inl 2175, 1), (Sum.inl 4761, 4)]

def keyMomentRow2715 : Integer.Sparse OriginalKey := [(Sum.inl 2201, 1), (Sum.inl 4792, 4)]

def keyMomentRow2716 : Integer.Sparse OriginalKey := [(Sum.inl 3464, 1), (Sum.inl 5086, 4)]

def keyMomentRow2717 : Integer.Sparse OriginalKey := [(Sum.inl 3463, 1), (Sum.inl 5074, 4)]

def keyMomentRow2718 : Integer.Sparse OriginalKey := [(Sum.inl 3462, 1), (Sum.inl 5042, 4)]

def keyMomentRow2719 : Integer.Sparse OriginalKey := [(Sum.inl 3480, 1), (Sum.inl 5090, 4)]

def keyMomentChunk84 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2688, keyMomentRow2689, keyMomentRow2690, keyMomentRow2691, keyMomentRow2692, keyMomentRow2693, keyMomentRow2694, keyMomentRow2695, keyMomentRow2696, keyMomentRow2697, keyMomentRow2698, keyMomentRow2699, keyMomentRow2700, keyMomentRow2701, keyMomentRow2702, keyMomentRow2703, keyMomentRow2704, keyMomentRow2705, keyMomentRow2706, keyMomentRow2707, keyMomentRow2708, keyMomentRow2709, keyMomentRow2710, keyMomentRow2711, keyMomentRow2712, keyMomentRow2713, keyMomentRow2714, keyMomentRow2715, keyMomentRow2716, keyMomentRow2717, keyMomentRow2718, keyMomentRow2719]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2720 : Integer.Sparse OriginalKey := [(Sum.inl 3475, 1), (Sum.inl 4965, 4)]

def keyMomentRow2721 : Integer.Sparse OriginalKey := [(Sum.inl 3452, 1), (Sum.inl 4954, 4)]

def keyMomentRow2722 : Integer.Sparse OriginalKey := [(Sum.inl 3474, 1), (Sum.inl 5044, 4)]

def keyMomentRow2723 : Integer.Sparse OriginalKey := [(Sum.inl 3476, 1), (Sum.inl 5067, 4)]

def keyMomentRow2724 : Integer.Sparse OriginalKey := [(Sum.inl 3461, 1), (Sum.inl 5085, 4)]

def keyMomentRow2725 : Integer.Sparse OriginalKey := [(Sum.inl 3458, 1), (Sum.inl 5041, 4)]

def keyMomentRow2726 : Integer.Sparse OriginalKey := [(Sum.inl 3472, 1), (Sum.inl 5087, 4)]

def keyMomentRow2727 : Integer.Sparse OriginalKey := [(Sum.inl 3266, 1), (Sum.inl 4547, 4)]

def keyMomentRow2728 : Integer.Sparse OriginalKey := [(Sum.inl 3260, 1), (Sum.inl 4528, 4)]

def keyMomentRow2729 : Integer.Sparse OriginalKey := [(Sum.inl 3451, 1), (Sum.inl 5034, 4)]

def keyMomentRow2730 : Integer.Sparse OriginalKey := [(Sum.inl 3466, 1), (Sum.inl 5065, 4)]

def keyMomentRow2731 : Integer.Sparse OriginalKey := [(Sum.inl 3465, 1), (Sum.inl 5043, 4)]

def keyMomentRow2732 : Integer.Sparse OriginalKey := [(Sum.inl 1729, 1), (Sum.inl 4476, 4)]

def keyMomentRow2733 : Integer.Sparse OriginalKey := [(Sum.inl 1520, 1), (Sum.inl 4178, 4)]

def keyMomentRow2734 : Integer.Sparse OriginalKey := [(Sum.inl 1514, 1), (Sum.inl 4153, 4)]

def keyMomentRow2735 : Integer.Sparse OriginalKey := [(Sum.inl 1676, 1), (Sum.inl 4347, 4)]

def keyMomentRow2736 : Integer.Sparse OriginalKey := [(Sum.inl 1723, 1), (Sum.inl 4440, 4)]

def keyMomentRow2737 : Integer.Sparse OriginalKey := [(Sum.inl 3413, 1), (Sum.inl 4944, 4)]

def keyMomentRow2738 : Integer.Sparse OriginalKey := [(Sum.inl 1670, 1), (Sum.inl 4327, 4)]

def keyMomentRow2739 : Integer.Sparse OriginalKey := [(Sum.inl 3408, 1), (Sum.inl 4930, 4)]

def keyMomentRow2740 : Integer.Sparse OriginalKey := [(Sum.inl 2164, 1), (Sum.inl 4670, 4)]

def keyMomentRow2741 : Integer.Sparse OriginalKey := [(Sum.inl 2181, 1), (Sum.inl 4757, 4)]

def keyMomentRow2742 : Integer.Sparse OriginalKey := [(Sum.inl 3406, 1), (Sum.inl 4931, 4)]

def keyMomentRow2743 : Integer.Sparse OriginalKey := [(Sum.inl 3415, 1), (Sum.inl 4934, 4)]

def keyMomentRow2744 : Integer.Sparse OriginalKey := [(Sum.inl 3414, 1), (Sum.inl 4933, 4)]

def keyMomentRow2745 : Integer.Sparse OriginalKey := [(Sum.inl 3272, 1), (Sum.inl 4535, 4)]

def keyMomentRow2746 : Integer.Sparse OriginalKey := [(Sum.inl 3408, 1), (Sum.inl 4930, 4)]

def keyMomentRow2747 : Integer.Sparse OriginalKey := [(Sum.inl 1533, 1), (Sum.inl 4161, 4)]

def keyMomentRow2748 : Integer.Sparse OriginalKey := [(Sum.inl 1689, 1), (Sum.inl 4335, 4)]

def keyMomentRow2749 : Integer.Sparse OriginalKey := [(Sum.inl 3419, 1), (Sum.inl 4935, 4)]

def keyMomentRow2750 : Integer.Sparse OriginalKey := [(Sum.inl 2683, 1), (Sum.inl 4611, 4)]

def keyMomentRow2751 : Integer.Sparse OriginalKey := [(Sum.inl 2702, 1), (Sum.inl 4600, 4)]

def keyMomentChunk85 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2720, keyMomentRow2721, keyMomentRow2722, keyMomentRow2723, keyMomentRow2724, keyMomentRow2725, keyMomentRow2726, keyMomentRow2727, keyMomentRow2728, keyMomentRow2729, keyMomentRow2730, keyMomentRow2731, keyMomentRow2732, keyMomentRow2733, keyMomentRow2734, keyMomentRow2735, keyMomentRow2736, keyMomentRow2737, keyMomentRow2738, keyMomentRow2739, keyMomentRow2740, keyMomentRow2741, keyMomentRow2742, keyMomentRow2743, keyMomentRow2744, keyMomentRow2745, keyMomentRow2746, keyMomentRow2747, keyMomentRow2748, keyMomentRow2749, keyMomentRow2750, keyMomentRow2751]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2752 : Integer.Sparse OriginalKey := [(Sum.inl 3296, 1), (Sum.inl 4607, 4)]

def keyMomentRow2753 : Integer.Sparse OriginalKey := [(Sum.inl 3289, 1), (Sum.inl 4599, 4)]

def keyMomentRow2754 : Integer.Sparse OriginalKey := [(Sum.inl 3302, 1), (Sum.inl 4609, 4)]

def keyMomentRow2755 : Integer.Sparse OriginalKey := [(Sum.inl 3294, 1), (Sum.inl 4603, 4)]

def keyMomentRow2756 : Integer.Sparse OriginalKey := [(Sum.inl 3295, 1), (Sum.inl 4592, 4)]

def keyMomentRow2757 : Integer.Sparse OriginalKey := [(Sum.inl 3288, 1), (Sum.inl 4589, 4)]

def keyMomentRow2758 : Integer.Sparse OriginalKey := [(Sum.inl 3288, 1), (Sum.inl 4589, 4)]

def keyMomentRow2759 : Integer.Sparse OriginalKey := [(Sum.inl 3291, 1), (Sum.inl 4591, 4)]

def keyMomentRow2760 : Integer.Sparse OriginalKey := [(Sum.inl 3290, 1), (Sum.inl 4590, 4)]

def keyMomentRow2761 : Integer.Sparse OriginalKey := [(Sum.inl 3298, 1), (Sum.inl 4594, 4)]

def keyMomentRow2762 : Integer.Sparse OriginalKey := [(Sum.inl 3291, 1), (Sum.inl 4591, 4)]

def keyMomentRow2763 : Integer.Sparse OriginalKey := [(Sum.inl 3297, 1), (Sum.inl 4593, 4)]

def keyMomentRow2764 : Integer.Sparse OriginalKey := [(Sum.inl 2149, 1), (Sum.inl 4536, 4)]

def keyMomentRow2765 : Integer.Sparse OriginalKey := [(Sum.inl 2172, 1), (Sum.inl 4532, 4)]

def keyMomentRow2766 : Integer.Sparse OriginalKey := [(Sum.inl 3258, 1), (Sum.inl 4529, 4)]

def keyMomentRow2767 : Integer.Sparse OriginalKey := [(Sum.inl 3268, 1), (Sum.inl 4534, 4)]

def keyMomentRow2768 : Integer.Sparse OriginalKey := [(Sum.inl 3267, 1), (Sum.inl 4533, 4)]

def keyMomentRow2769 : Integer.Sparse OriginalKey := [(Sum.inl 3255, 1), (Sum.inl 4527, 4)]

def keyMomentRow2770 : Integer.Sparse OriginalKey := [(Sum.inl 3262, 1), (Sum.inl 4531, 4)]

def keyMomentRow2771 : Integer.Sparse OriginalKey := [(Sum.inl 3260, 1), (Sum.inl 4528, 4)]

def keyMomentRow2772 : Integer.Sparse OriginalKey := [(Sum.inl 3261, 1), (Sum.inl 4530, 4)]

def keyMomentRow2773 : Integer.Sparse OriginalKey := [(Sum.inl 1516, 1), (Sum.inl 4156, 4)]

def keyMomentRow2774 : Integer.Sparse OriginalKey := [(Sum.inl 1672, 1), (Sum.inl 4330, 4)]

def keyMomentRow2775 : Integer.Sparse OriginalKey := [(Sum.inl 3272, 1), (Sum.inl 4535, 4)]

def keyMomentRow2776 : Integer.Sparse OriginalKey := [(Sum.inl 2755, 1), (Sum.inl 4890, 4)]

def keyMomentRow2777 : Integer.Sparse OriginalKey := [(Sum.inl 2753, 1), (Sum.inl 5284, 4)]

def keyMomentRow2778 : Integer.Sparse OriginalKey := [(Sum.inl 2751, 1), (Sum.inl 5282, 4)]

def keyMomentRow2779 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 1), (Sum.inl 5251, 4)]

def keyMomentRow2780 : Integer.Sparse OriginalKey := [(Sum.inl 2662, 1), (Sum.inl 5220, 4)]

def keyMomentRow2781 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 1), (Sum.inl 5219, 4)]

def keyMomentRow2782 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 1), (Sum.inl 5260, 4)]

def keyMomentRow2783 : Integer.Sparse OriginalKey := [(Sum.inl 2763, 1), (Sum.inl 5289, 4)]

def keyMomentChunk86 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2752, keyMomentRow2753, keyMomentRow2754, keyMomentRow2755, keyMomentRow2756, keyMomentRow2757, keyMomentRow2758, keyMomentRow2759, keyMomentRow2760, keyMomentRow2761, keyMomentRow2762, keyMomentRow2763, keyMomentRow2764, keyMomentRow2765, keyMomentRow2766, keyMomentRow2767, keyMomentRow2768, keyMomentRow2769, keyMomentRow2770, keyMomentRow2771, keyMomentRow2772, keyMomentRow2773, keyMomentRow2774, keyMomentRow2775, keyMomentRow2776, keyMomentRow2777, keyMomentRow2778, keyMomentRow2779, keyMomentRow2780, keyMomentRow2781, keyMomentRow2782, keyMomentRow2783]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2784 : Integer.Sparse OriginalKey := [(Sum.inl 2669, 1), (Sum.inl 5226, 4)]

def keyMomentRow2785 : Integer.Sparse OriginalKey := [(Sum.inl 2670, 1), (Sum.inl 5140, 4)]

def keyMomentRow2786 : Integer.Sparse OriginalKey := [(Sum.inl 2682, 1), (Sum.inl 5236, 4)]

def keyMomentRow2787 : Integer.Sparse OriginalKey := [(Sum.inl 3229, 1), (Sum.inl 4895, 4)]

def keyMomentRow2788 : Integer.Sparse OriginalKey := [(Sum.inl 3088, 1), (Sum.inl 5259, 4)]

def keyMomentRow2789 : Integer.Sparse OriginalKey := [(Sum.inl 3996, 1), (Sum.inl 5410, 4)]

def keyMomentRow2790 : Integer.Sparse OriginalKey := [(Sum.inl 3995, 1), (Sum.inl 5473, 4)]

def keyMomentRow2791 : Integer.Sparse OriginalKey := [(Sum.inl 3990, 1), (Sum.inl 5424, 4)]

def keyMomentRow2792 : Integer.Sparse OriginalKey := [(Sum.inl 3994, 1), (Sum.inl 5478, 4)]

def keyMomentRow2793 : Integer.Sparse OriginalKey := [(Sum.inl 3880, 1), (Sum.inl 5445, 4)]

def keyMomentRow2794 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 1), (Sum.inl 5425, 4)]

def keyMomentRow2795 : Integer.Sparse OriginalKey := [(Sum.inl 3993, 1), (Sum.inl 5438, 4)]

def keyMomentRow2796 : Integer.Sparse OriginalKey := [(Sum.inl 3997, 1), (Sum.inl 5484, 4)]

def keyMomentRow2797 : Integer.Sparse OriginalKey := [(Sum.inl 3848, 1), (Sum.inl 5430, 4)]

def keyMomentRow2798 : Integer.Sparse OriginalKey := [(Sum.inl 3540, 1), (Sum.inl 5260, 4)]

def keyMomentRow2799 : Integer.Sparse OriginalKey := [(Sum.inl 3227, 1), (Sum.inl 4888, 4)]

def keyMomentRow2800 : Integer.Sparse OriginalKey := [(Sum.inl 3065, 1), (Sum.inl 5250, 4)]

def keyMomentRow2801 : Integer.Sparse OriginalKey := [(Sum.inl 3977, 1), (Sum.inl 5405, 4)]

def keyMomentRow2802 : Integer.Sparse OriginalKey := [(Sum.inl 3976, 1), (Sum.inl 5471, 4)]

def keyMomentRow2803 : Integer.Sparse OriginalKey := [(Sum.inl 2698, 1), (Sum.inl 5244, 4)]

def keyMomentRow2804 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 1), (Sum.inl 5282, 4)]

def keyMomentRow2805 : Integer.Sparse OriginalKey := [(Sum.inl 2706, 1), (Sum.inl 5205, 4)]

def keyMomentRow2806 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 1), (Sum.inl 5429, 4)]

def keyMomentRow2807 : Integer.Sparse OriginalKey := [(Sum.inl 3569, 1), (Sum.inl 5197, 4)]

def keyMomentRow2808 : Integer.Sparse OriginalKey := [(Sum.inl 3537, 1), (Sum.inl 5187, 4)]

def keyMomentRow2809 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 1), (Sum.inl 5430, 4)]

def keyMomentRow2810 : Integer.Sparse OriginalKey := [(Sum.inl 3978, 1), (Sum.inl 5480, 4)]

def keyMomentRow2811 : Integer.Sparse OriginalKey := [(Sum.inl 3873, 1), (Sum.inl 5421, 4)]

def keyMomentRow2812 : Integer.Sparse OriginalKey := [(Sum.inl 3959, 1), (Sum.inl 5446, 4)]

def keyMomentRow2813 : Integer.Sparse OriginalKey := [(Sum.inl 3578, 1), (Sum.inl 5199, 4)]

def keyMomentRow2814 : Integer.Sparse OriginalKey := [(Sum.inl 3529, 1), (Sum.inl 5185, 4)]

def keyMomentRow2815 : Integer.Sparse OriginalKey := [(Sum.inl 3517, 1), (Sum.inl 5138, 4)]

def keyMomentChunk87 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2784, keyMomentRow2785, keyMomentRow2786, keyMomentRow2787, keyMomentRow2788, keyMomentRow2789, keyMomentRow2790, keyMomentRow2791, keyMomentRow2792, keyMomentRow2793, keyMomentRow2794, keyMomentRow2795, keyMomentRow2796, keyMomentRow2797, keyMomentRow2798, keyMomentRow2799, keyMomentRow2800, keyMomentRow2801, keyMomentRow2802, keyMomentRow2803, keyMomentRow2804, keyMomentRow2805, keyMomentRow2806, keyMomentRow2807, keyMomentRow2808, keyMomentRow2809, keyMomentRow2810, keyMomentRow2811, keyMomentRow2812, keyMomentRow2813, keyMomentRow2814, keyMomentRow2815]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2816 : Integer.Sparse OriginalKey := [(Sum.inl 3523, 1), (Sum.inl 5139, 4)]

def keyMomentRow2817 : Integer.Sparse OriginalKey := [(Sum.inl 3842, 1), (Sum.inl 5419, 4)]

def keyMomentRow2818 : Integer.Sparse OriginalKey := [(Sum.inl 3542, 1), (Sum.inl 5189, 4)]

def keyMomentRow2819 : Integer.Sparse OriginalKey := [(Sum.inl 0, 1), (Sum.inl 4083, 4)]

def keyMomentRow2820 : Integer.Sparse OriginalKey := [(Sum.inl 3111, 1), (Sum.inl 5273, 4)]

def keyMomentRow2821 : Integer.Sparse OriginalKey := [(Sum.inl 3, 1), (Sum.inl 4091, 4)]

def keyMomentRow2822 : Integer.Sparse OriginalKey := [(Sum.inl 4034, 1), (Sum.inl 5427, 4)]

def keyMomentRow2823 : Integer.Sparse OriginalKey := [(Sum.inl 3855, 1), (Sum.inl 5437, 4)]

def keyMomentRow2824 : Integer.Sparse OriginalKey := [(Sum.inl 3228, 1), (Sum.inl 4893, 4)]

def keyMomentRow2825 : Integer.Sparse OriginalKey := [(Sum.inl 3087, 1), (Sum.inl 5257, 4)]

def keyMomentRow2826 : Integer.Sparse OriginalKey := [(Sum.inl 4038, 1), (Sum.inl 5408, 4)]

def keyMomentRow2827 : Integer.Sparse OriginalKey := [(Sum.inl 3099, 1), (Sum.inl 5290, 4)]

def keyMomentRow2828 : Integer.Sparse OriginalKey := [(Sum.inl 4026, 1), (Sum.inl 5431, 4)]

def keyMomentRow2829 : Integer.Sparse OriginalKey := [(Sum.inl 3539, 1), (Sum.inl 5251, 4)]

def keyMomentRow2830 : Integer.Sparse OriginalKey := [(Sum.inl 4026, 1), (Sum.inl 5431, 4)]

def keyMomentRow2831 : Integer.Sparse OriginalKey := [(Sum.inl 4028, 1), (Sum.inl 5448, 4)]

def keyMomentRow2832 : Integer.Sparse OriginalKey := [(Sum.inl 3539, 1), (Sum.inl 5251, 4)]

def keyMomentRow2833 : Integer.Sparse OriginalKey := [(Sum.inl 3543, 1), (Sum.inl 5252, 4)]

def keyMomentRow2834 : Integer.Sparse OriginalKey := [(Sum.inl 3223, 1), (Sum.inl 4889, 4)]

def keyMomentRow2835 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 1), (Sum.inl 5251, 4)]

def keyMomentRow2836 : Integer.Sparse OriginalKey := [(Sum.inl 3847, 1), (Sum.inl 5406, 4)]

def keyMomentRow2837 : Integer.Sparse OriginalKey := [(Sum.inl 3846, 1), (Sum.inl 5429, 4)]

def keyMomentRow2838 : Integer.Sparse OriginalKey := [(Sum.inl 2697, 1), (Sum.inl 5243, 4)]

def keyMomentRow2839 : Integer.Sparse OriginalKey := [(Sum.inl 3226, 1), (Sum.inl 4887, 4)]

def keyMomentRow2840 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 1), (Sum.inl 5281, 4)]

def keyMomentRow2841 : Integer.Sparse OriginalKey := [(Sum.inl 3075, 1), (Sum.inl 5270, 4)]

def keyMomentRow2842 : Integer.Sparse OriginalKey := [(Sum.inl 2702, 1), (Sum.inl 4600, 4)]

def keyMomentRow2843 : Integer.Sparse OriginalKey := [(Sum.inl 3526, 1), (Sum.inl 5265, 4)]

def keyMomentRow2844 : Integer.Sparse OriginalKey := [(Sum.inl 3289, 1), (Sum.inl 4599, 4)]

def keyMomentRow2845 : Integer.Sparse OriginalKey := [(Sum.inl 3288, 1), (Sum.inl 4589, 4)]

def keyMomentRow2846 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 1), (Sum.inl 5425, 4)]

def keyMomentRow2847 : Integer.Sparse OriginalKey := [(Sum.inl 3848, 1), (Sum.inl 5430, 4)]

def keyMomentChunk88 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2816, keyMomentRow2817, keyMomentRow2818, keyMomentRow2819, keyMomentRow2820, keyMomentRow2821, keyMomentRow2822, keyMomentRow2823, keyMomentRow2824, keyMomentRow2825, keyMomentRow2826, keyMomentRow2827, keyMomentRow2828, keyMomentRow2829, keyMomentRow2830, keyMomentRow2831, keyMomentRow2832, keyMomentRow2833, keyMomentRow2834, keyMomentRow2835, keyMomentRow2836, keyMomentRow2837, keyMomentRow2838, keyMomentRow2839, keyMomentRow2840, keyMomentRow2841, keyMomentRow2842, keyMomentRow2843, keyMomentRow2844, keyMomentRow2845, keyMomentRow2846, keyMomentRow2847]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2848 : Integer.Sparse OriginalKey := [(Sum.inl 3832, 1), (Sum.inl 5379, 4)]

def keyMomentRow2849 : Integer.Sparse OriginalKey := [(Sum.inl 4024, 1), (Sum.inl 5445, 4)]

def keyMomentRow2850 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 1), (Sum.inl 5266, 4)]

def keyMomentRow2851 : Integer.Sparse OriginalKey := [(Sum.inl 3294, 1), (Sum.inl 4603, 4)]

def keyMomentRow2852 : Integer.Sparse OriginalKey := [(Sum.inl 3290, 1), (Sum.inl 4590, 4)]

def keyMomentRow2853 : Integer.Sparse OriginalKey := [(Sum.inl 3516, 1), (Sum.inl 5129, 4)]

def keyMomentRow2854 : Integer.Sparse OriginalKey := [(Sum.inl 3291, 1), (Sum.inl 4591, 4)]

def keyMomentRow2855 : Integer.Sparse OriginalKey := [(Sum.inl 3835, 1), (Sum.inl 5377, 4)]

def keyMomentRow2856 : Integer.Sparse OriginalKey := [(Sum.inl 3297, 1), (Sum.inl 4593, 4)]

def keyMomentRow2857 : Integer.Sparse OriginalKey := [(Sum.inl 2235, 1), (Sum.inl 4886, 4)]

def keyMomentRow2858 : Integer.Sparse OriginalKey := [(Sum.inl 2187, 1), (Sum.inl 4830, 4)]

def keyMomentRow2859 : Integer.Sparse OriginalKey := [(Sum.inl 2233, 1), (Sum.inl 4885, 4)]

def keyMomentRow2860 : Integer.Sparse OriginalKey := [(Sum.inl 2232, 1), (Sum.inl 4863, 4)]

def keyMomentRow2861 : Integer.Sparse OriginalKey := [(Sum.inl 3221, 1), (Sum.inl 4885, 4)]

def keyMomentRow2862 : Integer.Sparse OriginalKey := [(Sum.inl 3059, 1), (Sum.inl 5277, 4)]

def keyMomentRow2863 : Integer.Sparse OriginalKey := [(Sum.inl 2690, 1), (Sum.inl 4975, 4)]

def keyMomentRow2864 : Integer.Sparse OriginalKey := [(Sum.inl 3058, 1), (Sum.inl 5097, 4)]

def keyMomentRow2865 : Integer.Sparse OriginalKey := [(Sum.inl 2688, 1), (Sum.inl 4540, 4)]

def keyMomentRow2866 : Integer.Sparse OriginalKey := [(Sum.inl 1700, 1), (Sum.inl 4494, 4)]

def keyMomentRow2867 : Integer.Sparse OriginalKey := [(Sum.inl 1699, 1), (Sum.inl 4473, 4)]

def keyMomentRow2868 : Integer.Sparse OriginalKey := [(Sum.inl 1502, 1), (Sum.inl 4169, 4)]

def keyMomentRow2869 : Integer.Sparse OriginalKey := [(Sum.inl 1501, 1), (Sum.inl 4149, 4)]

def keyMomentRow2870 : Integer.Sparse OriginalKey := [(Sum.inl 2192, 1), (Sum.inl 4815, 4)]

def keyMomentRow2871 : Integer.Sparse OriginalKey := [(Sum.inl 2240, 1), (Sum.inl 4851, 4)]

def keyMomentRow2872 : Integer.Sparse OriginalKey := [(Sum.inl 2142, 1), (Sum.inl 4677, 4)]

def keyMomentRow2873 : Integer.Sparse OriginalKey := [(Sum.inl 3554, 1), (Sum.inl 4964, 4)]

def keyMomentRow2874 : Integer.Sparse OriginalKey := [(Sum.inl 3257, 1), (Sum.inl 4542, 4)]

def keyMomentRow2875 : Integer.Sparse OriginalKey := [(Sum.inl 1709, 1), (Sum.inl 4474, 4)]

def keyMomentRow2876 : Integer.Sparse OriginalKey := [(Sum.inl 1508, 1), (Sum.inl 4173, 4)]

def keyMomentRow2877 : Integer.Sparse OriginalKey := [(Sum.inl 1504, 1), (Sum.inl 4150, 4)]

def keyMomentRow2878 : Integer.Sparse OriginalKey := [(Sum.inl 2140, 1), (Sum.inl 4663, 4)]

def keyMomentRow2879 : Integer.Sparse OriginalKey := [(Sum.inl 3510, 1), (Sum.inl 4956, 4)]

def keyMomentChunk89 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2848, keyMomentRow2849, keyMomentRow2850, keyMomentRow2851, keyMomentRow2852, keyMomentRow2853, keyMomentRow2854, keyMomentRow2855, keyMomentRow2856, keyMomentRow2857, keyMomentRow2858, keyMomentRow2859, keyMomentRow2860, keyMomentRow2861, keyMomentRow2862, keyMomentRow2863, keyMomentRow2864, keyMomentRow2865, keyMomentRow2866, keyMomentRow2867, keyMomentRow2868, keyMomentRow2869, keyMomentRow2870, keyMomentRow2871, keyMomentRow2872, keyMomentRow2873, keyMomentRow2874, keyMomentRow2875, keyMomentRow2876, keyMomentRow2877, keyMomentRow2878, keyMomentRow2879]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow288 : Integer.Sparse OriginalKey := [(Sum.inl 330, 5)]

def keyMomentRow289 : Integer.Sparse OriginalKey := [(Sum.inl 394, 5)]

def keyMomentRow290 : Integer.Sparse OriginalKey := [(Sum.inl 491, 5)]

def keyMomentRow291 : Integer.Sparse OriginalKey := [(Sum.inl 447, 5)]

def keyMomentRow292 : Integer.Sparse OriginalKey := [(Sum.inl 470, 5)]

def keyMomentRow293 : Integer.Sparse OriginalKey := [(Sum.inl 484, 5)]

def keyMomentRow294 : Integer.Sparse OriginalKey := [(Sum.inl 483, 5)]

def keyMomentRow295 : Integer.Sparse OriginalKey := [(Sum.inl 410, 5)]

def keyMomentRow296 : Integer.Sparse OriginalKey := [(Sum.inl 390, 5)]

def keyMomentRow297 : Integer.Sparse OriginalKey := [(Sum.inl 153, 5)]

def keyMomentRow298 : Integer.Sparse OriginalKey := [(Sum.inl 333, 5)]

def keyMomentRow299 : Integer.Sparse OriginalKey := [(Sum.inl 395, 5)]

def keyMomentRow300 : Integer.Sparse OriginalKey := [(Sum.inl 346, 5)]

def keyMomentRow301 : Integer.Sparse OriginalKey := [(Sum.inl 147, 5)]

def keyMomentRow302 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentRow303 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow304 : Integer.Sparse OriginalKey := [(Sum.inl 402, 5)]

def keyMomentRow305 : Integer.Sparse OriginalKey := [(Sum.inl 503, 5)]

def keyMomentRow306 : Integer.Sparse OriginalKey := [(Sum.inl 446, 5)]

def keyMomentRow307 : Integer.Sparse OriginalKey := [(Sum.inl 493, 5)]

def keyMomentRow308 : Integer.Sparse OriginalKey := [(Sum.inl 487, 5)]

def keyMomentRow309 : Integer.Sparse OriginalKey := [(Sum.inl 244, 5)]

def keyMomentRow310 : Integer.Sparse OriginalKey := [(Sum.inl 456, 5)]

def keyMomentRow311 : Integer.Sparse OriginalKey := [(Sum.inl 494, 5)]

def keyMomentRow312 : Integer.Sparse OriginalKey := [(Sum.inl 248, 5)]

def keyMomentRow313 : Integer.Sparse OriginalKey := [(Sum.inl 459, 5)]

def keyMomentRow314 : Integer.Sparse OriginalKey := [(Sum.inr 5, 5)]

def keyMomentRow315 : Integer.Sparse OriginalKey := [(Sum.inl 496, 5)]

def keyMomentRow316 : Integer.Sparse OriginalKey := [(Sum.inl 249, 5)]

def keyMomentRow317 : Integer.Sparse OriginalKey := [(Sum.inl 494, 5)]

def keyMomentRow318 : Integer.Sparse OriginalKey := [(Sum.inl 337, 5)]

def keyMomentRow319 : Integer.Sparse OriginalKey := [(Sum.inl 420, 5)]

def keyMomentChunk9 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow288, keyMomentRow289, keyMomentRow290, keyMomentRow291, keyMomentRow292, keyMomentRow293, keyMomentRow294, keyMomentRow295, keyMomentRow296, keyMomentRow297, keyMomentRow298, keyMomentRow299, keyMomentRow300, keyMomentRow301, keyMomentRow302, keyMomentRow303, keyMomentRow304, keyMomentRow305, keyMomentRow306, keyMomentRow307, keyMomentRow308, keyMomentRow309, keyMomentRow310, keyMomentRow311, keyMomentRow312, keyMomentRow313, keyMomentRow314, keyMomentRow315, keyMomentRow316, keyMomentRow317, keyMomentRow318, keyMomentRow319]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Keys90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def keyMomentRow2880 : Integer.Sparse OriginalKey := [(Sum.inl 3255, 1), (Sum.inl 4527, 4)]

def keyMomentRow2881 : Integer.Sparse OriginalKey := [(Sum.inl 1505, 1), (Sum.inl 4151, 4)]

def keyMomentRow2882 : Integer.Sparse OriginalKey := [(Sum.inl 2148, 1), (Sum.inl 4666, 4)]

def keyMomentRow2883 : Integer.Sparse OriginalKey := [(Sum.inl 3511, 1), (Sum.inl 4958, 4)]

def keyMomentRow2884 : Integer.Sparse OriginalKey := [(Sum.inl 3261, 1), (Sum.inl 4530, 4)]

def keyMomentRow2885 : Integer.Sparse OriginalKey := [(Sum.inl 1515, 1), (Sum.inl 4155, 4)]

def keyMomentChunk90 : Array (Integer.Sparse OriginalKey) := #[keyMomentRow2880, keyMomentRow2881, keyMomentRow2882, keyMomentRow2883, keyMomentRow2884, keyMomentRow2885]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyMomentRows (i : Fin 2886) : Integer.Sparse OriginalKey :=
  ((#[keyMomentChunk0, keyMomentChunk1, keyMomentChunk2, keyMomentChunk3, keyMomentChunk4, keyMomentChunk5, keyMomentChunk6, keyMomentChunk7, keyMomentChunk8, keyMomentChunk9, keyMomentChunk10, keyMomentChunk11, keyMomentChunk12, keyMomentChunk13, keyMomentChunk14, keyMomentChunk15, keyMomentChunk16, keyMomentChunk17, keyMomentChunk18, keyMomentChunk19, keyMomentChunk20, keyMomentChunk21, keyMomentChunk22, keyMomentChunk23, keyMomentChunk24, keyMomentChunk25, keyMomentChunk26, keyMomentChunk27, keyMomentChunk28, keyMomentChunk29, keyMomentChunk30, keyMomentChunk31, keyMomentChunk32, keyMomentChunk33, keyMomentChunk34, keyMomentChunk35, keyMomentChunk36, keyMomentChunk37, keyMomentChunk38, keyMomentChunk39, keyMomentChunk40, keyMomentChunk41, keyMomentChunk42, keyMomentChunk43, keyMomentChunk44, keyMomentChunk45, keyMomentChunk46, keyMomentChunk47, keyMomentChunk48, keyMomentChunk49, keyMomentChunk50, keyMomentChunk51, keyMomentChunk52, keyMomentChunk53, keyMomentChunk54, keyMomentChunk55, keyMomentChunk56, keyMomentChunk57, keyMomentChunk58, keyMomentChunk59, keyMomentChunk60, keyMomentChunk61, keyMomentChunk62, keyMomentChunk63, keyMomentChunk64, keyMomentChunk65, keyMomentChunk66, keyMomentChunk67, keyMomentChunk68, keyMomentChunk69, keyMomentChunk70, keyMomentChunk71, keyMomentChunk72, keyMomentChunk73, keyMomentChunk74, keyMomentChunk75, keyMomentChunk76, keyMomentChunk77, keyMomentChunk78, keyMomentChunk79, keyMomentChunk80, keyMomentChunk81, keyMomentChunk82, keyMomentChunk83, keyMomentChunk84, keyMomentChunk85, keyMomentChunk86, keyMomentChunk87, keyMomentChunk88, keyMomentChunk89, keyMomentChunk90])[i.val / 32]!)[i.val % 32]!

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def originalBlock0 : Integer.Sparse OriginalKey := [(Sum.inl 0, 124824600000), (Sum.inl 1, 204952102800), (Sum.inl 2, 46361001600), (Sum.inl 259, -28398225600), (Sum.inl 261, -57745742400), (Sum.inl 265, -96426374400), (Sum.inl 266, -92088806400), (Sum.inl 267, 57745742400), (Sum.inl 268, -74818108800), (Sum.inl 269, 29585910000), (Sum.inl 270, 15042729600), (Sum.inl 272, 74818108800), (Sum.inl 375, 66564864000), (Sum.inl 377, 2565312000), (Sum.inl 382, 10113696000), (Sum.inl 384, -40587208800), (Sum.inl 386, 132276268800), (Sum.inl 387, -99108561600), (Sum.inl 388, -58283520000), (Sum.inl 389, -18229479600), (Sum.inl 391, 10684548000), (Sum.inl 402, -2565312000), (Sum.inl 405, -11037744000), (Sum.inl 406, -132276268800), (Sum.inl 415, 58283520000), (Sum.inl 419, 9198120000), (Sum.inl 420, -1327536000), (Sum.inl 421, -23343196800), (Sum.inr 0, -1034712000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def originalBlock1 : Integer.Sparse OriginalKey := [(Sum.inl 270, -9312408000), (Sum.inl 324, -23181379200), (Sum.inl 342, -8433043200), (Sum.inl 357, 7727126400), (Sum.inl 359, -3810643200), (Sum.inl 363, -10113696000), (Sum.inl 364, -169069953600), (Sum.inl 376, -50527488000), (Sum.inl 377, -1700488800), (Sum.inl 380, -66564864000), (Sum.inl 381, -7706640000), (Sum.inl 384, 15391872000), (Sum.inl 386, 19684944000), (Sum.inl 391, 58283520000), (Sum.inl 392, 2611036800), (Sum.inl 393, 41502110400), (Sum.inl 394, 3810643200), (Sum.inl 397, 7727126400), (Sum.inl 399, -5222073600), (Sum.inl 400, -73233489600), (Sum.inl 403, 36842960000), (Sum.inl 404, 944716000), (Sum.inl 406, -19684944000), (Sum.inl 408, 12245371200), (Sum.inl 409, 19176436800), (Sum.inl 410, 7706640000), (Sum.inl 412, -102764742000), (Sum.inl 414, 50143123200), (Sum.inl 421, -58283520000)]

end MUB6.Certificate.MixedTargetSemantics

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

def originalBlock10 : Integer.Sparse OriginalKey := [(Sum.inl 152, -29255313600), (Sum.inl 247, -8378760000), (Sum.inl 268, 57721097600), (Sum.inl 270, -1034712000), (Sum.inl 348, 106974828000), (Sum.inl 354, 16911316800), (Sum.inl 363, 34746307200), (Sum.inl 364, -53590060800), (Sum.inl 365, -1691913600), (Sum.inl 366, -81153576000), (Sum.inl 383, -38407920000), (Sum.inl 384, 10261248000), (Sum.inl 402, -24210780000), (Sum.inl 409, 32543697600), (Sum.inl 410, 23298000000), (Sum.inl 412, -18229479600), (Sum.inl 414, -14865691200), (Sum.inl 415, -30311160000), (Sum.inl 416, -105157382400), (Sum.inl 443, -12184101600), (Sum.inl 467, 226857830600), (Sum.inl 475, -161540352000), (Sum.inl 480, -120642024000), (Sum.inl 487, 124531236000), (Sum.inl 491, 71029532000), (Sum.inl 497, 24456750000), (Sum.inl 498, 54565524000), (Sum.inl 499, 15310002000), (Sum.inl 501, 209980368000), (Sum.inl 503, 4842156000)]

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

def originalBlock11 : Integer.Sparse OriginalKey := [(Sum.inl 139, 52192488000), (Sum.inl 145, -155482908000), (Sum.inl 148, 4924267200), (Sum.inl 165, -41283910080), (Sum.inl 177, 17204184000), (Sum.inl 238, 134580009600), (Sum.inl 246, 15109920000), (Sum.inl 263, -206083480800), (Sum.inl 264, 3449040000), (Sum.inl 269, 170653975200), (Sum.inl 322, 24456750000), (Sum.inl 346, 129721088400), (Sum.inl 364, 62555337600), (Sum.inl 373, 29089003800), (Sum.inl 377, 41785320000), (Sum.inl 384, -123409252000), (Sum.inl 391, -38407920000), (Sum.inl 440, -20481206400), (Sum.inl 443, -201116028000), (Sum.inl 458, -314148300000), (Sum.inl 463, -425229843600), (Sum.inl 468, 362043469000), (Sum.inl 476, -24456750000), (Sum.inl 478, -39327360000), (Sum.inl 480, -24456750000), (Sum.inl 481, -49145616000), (Sum.inl 484, -22965003000), (Sum.inl 489, -3277280000), (Sum.inl 491, 259582776000), (Sum.inl 492, -22965003000)]

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

def originalBlock12 : Integer.Sparse OriginalKey := [(Sum.inl 10, 89720006400), (Sum.inl 12, -50104365600), (Sum.inl 27, -15109920000), (Sum.inl 29, -21316464000), (Sum.inl 101, -17957184000), (Sum.inl 114, -40440666000), (Sum.inl 123, -4924267200), (Sum.inl 142, -158613252000), (Sum.inl 167, -34746307200), (Sum.inl 184, -39027840000), (Sum.inl 229, -7695936000), (Sum.inl 240, -124792128000), (Sum.inl 278, 111972744000), (Sum.inl 280, 314148300000), (Sum.inl 282, -421123128000), (Sum.inl 288, -16911316800), (Sum.inl 309, 29197063000), (Sum.inl 313, 38407920000), (Sum.inl 325, -29495520000), (Sum.inl 356, -21835584000), (Sum.inl 398, -38407920000), (Sum.inl 426, 24456750000), (Sum.inl 427, 362656380000), (Sum.inl 428, 22965003000), (Sum.inl 429, 29495520000), (Sum.inl 432, -97030044000), (Sum.inl 434, 414899520000), (Sum.inl 435, -278136775000), (Sum.inl 446, -209980368000), (Sum.inl 467, 67977108000), (Sum.inr 6, 41489952000)]

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

def originalBlock13 : Integer.Sparse OriginalKey := [(Sum.inl 15, -77240793600), (Sum.inl 17, 1824895200), (Sum.inl 36, 15109920000), (Sum.inl 103, 12826560000), (Sum.inl 116, 84325466400), (Sum.inl 130, 155482908000), (Sum.inl 149, 113295180000), (Sum.inl 168, 23043463200), (Sum.inl 171, 41893800000), (Sum.inl 173, -14848344000), (Sum.inl 179, -63511747200), (Sum.inl 182, 240426432000), (Sum.inl 185, -47681049600), (Sum.inl 209, 31703544000), (Sum.inl 223, -30264364800), (Sum.inl 235, -63525398400), (Sum.inl 248, 63511747200), (Sum.inl 251, -50137099200), (Sum.inl 261, 45396547200), (Sum.inl 268, -62302344000), (Sum.inl 269, -20785348800), (Sum.inl 270, -32362272000), (Sum.inl 278, 144516050400), (Sum.inl 279, -153198993600), (Sum.inl 296, -24456750000), (Sum.inl 300, -22965003000), (Sum.inl 412, -157627584000), (Sum.inl 439, -58510627200), (Sum.inl 455, 44597073600), (Sum.inl 467, 410692212000), (Sum.inl 468, -58510627200), (Sum.inl 507, -118409896800)]

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

def originalBlock14 : Integer.Sparse OriginalKey := [(Sum.inl 38, -15893683200), (Sum.inl 127, -58510627200), (Sum.inl 160, -55087923200), (Sum.inl 175, 50272560000), (Sum.inl 178, -50272560000), (Sum.inl 179, 24611414400), (Sum.inl 180, -24611414400), (Sum.inl 286, -58510627200), (Sum.inl 295, 44597073600), (Sum.inl 306, -3290412000), (Sum.inl 314, 14865691200), (Sum.inl 316, 30311160000), (Sum.inl 317, 7276982400), (Sum.inl 335, 105157382400), (Sum.inl 343, -23356972800), (Sum.inl 369, -30311160000), (Sum.inl 424, -14865691200), (Sum.inl 432, -177981876000), (Sum.inl 438, -296676033600), (Sum.inl 448, -3033532800), (Sum.inl 449, 150930969600), (Sum.inl 450, 6067065600), (Sum.inl 451, 137360937600), (Sum.inl 471, -105157382400), (Sum.inl 490, -26388340800), (Sum.inl 492, -7276982400), (Sum.inl 496, -42667430400), (Sum.inl 505, -41905377600)]

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

def originalBlock15 : Integer.Sparse OriginalKey := [(Sum.inl 33, -70922448000), (Sum.inl 65, -45396547200), (Sum.inl 68, 63525398400), (Sum.inl 71, 14848344000), (Sum.inl 95, 30264364800), (Sum.inl 98, 14716992000), (Sum.inl 111, 19561056000), (Sum.inl 186, -41893800000), (Sum.inl 275, -44597073600), (Sum.inl 328, 30015273600), (Sum.inl 339, -52776681600), (Sum.inl 343, -104526662400), (Sum.inl 345, 24456750000), (Sum.inl 346, -58466748000), (Sum.inl 347, -24456750000), (Sum.inl 348, 106974828000), (Sum.inl 349, 24456750000), (Sum.inl 350, -106974828000), (Sum.inl 354, -23917920000), (Sum.inl 373, 16841002200), (Sum.inl 377, 23760280000), (Sum.inl 384, 20443142000), (Sum.inl 385, 70687015000), (Sum.inl 394, -12248001600), (Sum.inl 395, 16841002200), (Sum.inl 402, -24210780000), (Sum.inl 405, 141744323200), (Sum.inl 406, -21695798400), (Sum.inl 409, -4403787000), (Sum.inl 410, 9117984000), (Sum.inl 420, 11834438400), (Sum.inl 452, -3033532800)]

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

def originalBlock16 : Integer.Sparse OriginalKey := [(Sum.inl 11, 99670795200), (Sum.inl 18, -74766672000), (Sum.inl 122, -155482908000), (Sum.inl 146, -22659036000), (Sum.inl 147, 155482908000), (Sum.inl 164, 124466313600), (Sum.inl 169, -112150008000), (Sum.inl 176, 23917920000), (Sum.inl 180, 6752059200), (Sum.inl 187, -151369243200), (Sum.inl 236, 51687412800), (Sum.inl 239, 79932124800), (Sum.inl 249, -6752059200), (Sum.inl 262, 1888848000), (Sum.inl 270, 5498928000), (Sum.inl 281, 106974828000), (Sum.inl 292, 24456750000), (Sum.inl 297, -48508080000), (Sum.inl 298, -24456750000), (Sum.inl 299, 22965003000), (Sum.inl 300, -22965003000), (Sum.inl 301, -29495520000), (Sum.inl 303, 29495520000), (Sum.inl 306, 51711972000), (Sum.inl 308, -70687015000), (Sum.inl 309, 112176967000), (Sum.inl 323, -24456750000), (Sum.inl 374, -22965003000), (Sum.inl 379, -29495520000), (Sum.inr 1, 2565312000), (Sum.inr 2, -2565312000), (Sum.inr 6, -41489952000)]

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

def originalBlock17 : Integer.Sparse OriginalKey := [(Sum.inl 40, 31918795200), (Sum.inl 66, -30264364800), (Sum.inl 72, 422812800), (Sum.inl 96, 45396547200), (Sum.inl 112, -51687412800), (Sum.inl 114, -113219761200), (Sum.inl 117, 4123264800), (Sum.inl 133, -9363715200), (Sum.inl 139, 127701228000), (Sum.inl 140, 152493757200), (Sum.inl 145, 27325780200), (Sum.inl 147, 24184013600), (Sum.inl 148, -24503810400), (Sum.inl 207, -43507699200), (Sum.inl 211, -422812800), (Sum.inl 224, 26486668800), (Sum.inl 283, 8424604800), (Sum.inl 286, -12683246400), (Sum.inl 287, -8424604800), (Sum.inl 290, -15407899200), (Sum.inl 334, 1862697600), (Sum.inl 336, -3725395200), (Sum.inl 339, -26388340800), (Sum.inl 341, -26388340800), (Sum.inl 344, 1862697600), (Sum.inl 351, -8424604800), (Sum.inl 352, 8424604800), (Sum.inl 353, -252078960000), (Sum.inl 355, 252078960000), (Sum.inl 405, 66222478400), (Sum.inl 407, -38012548800), (Sum.inl 412, -9363715200)]

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

def originalBlock18 : Integer.Sparse OriginalKey := [(Sum.inl 13, -12602724000), (Sum.inl 22, -8376883200), (Sum.inl 26, 16753766400), (Sum.inl 33, 2303568000), (Sum.inl 34, -8376883200), (Sum.inl 35, 53645860800), (Sum.inl 38, 72943934400), (Sum.inl 40, -2303568000), (Sum.inl 42, -4855406400), (Sum.inl 70, 353001600), (Sum.inl 100, -9521544000), (Sum.inl 115, -114445105200), (Sum.inl 116, 41635852800), (Sum.inl 118, 29731382400), (Sum.inl 119, -353001600), (Sum.inl 121, 29731382400), (Sum.inl 124, -29731382400), (Sum.inl 125, -7276982400), (Sum.inl 126, 7276982400), (Sum.inl 127, -58510627200), (Sum.inl 129, -29255313600), (Sum.inl 131, -20785348800), (Sum.inl 132, -29731382400), (Sum.inl 133, -29255313600), (Sum.inl 142, -67977108000), (Sum.inl 143, 4002672000), (Sum.inl 146, 22659036000), (Sum.inl 149, 113295180000), (Sum.inl 158, 2595219200), (Sum.inl 160, -2596374400), (Sum.inl 162, 81471988800), (Sum.inl 397, 3863563200)]

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

def originalBlock19 : Integer.Sparse OriginalKey := [(Sum.inl 113, -4718736000), (Sum.inl 316, 24467961600), (Sum.inl 357, 3863563200), (Sum.inl 358, 49636036800), (Sum.inl 359, -7621286400), (Sum.inl 360, -20806603200), (Sum.inl 361, -75431952000), (Sum.inl 362, -99272073600), (Sum.inl 367, 4763304000), (Sum.inl 368, 15441432000), (Sum.inl 369, 93783028800), (Sum.inl 371, -56534784000), (Sum.inl 376, -1070020800), (Sum.inl 377, -5101466400), (Sum.inl 378, 115774934400), (Sum.inl 387, 120455524800), (Sum.inl 388, 3212034400), (Sum.inl 390, -115774934400), (Sum.inl 394, 7621286400), (Sum.inl 395, 49636036800), (Sum.inl 400, -4763304000), (Sum.inl 401, 20806603200), (Sum.inl 403, 14754548800), (Sum.inl 404, -944716000), (Sum.inl 414, -15441432000), (Sum.inl 415, 21023280000), (Sum.inl 416, -63564067200), (Sum.inl 420, 24323265600), (Sum.inl 489, 4915920000), (Sum.inl 518, 22557888000), (Sum.inl 521, 4915920000), (Sum.inr 4, -4915920000)]

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

def originalBlock2 : Integer.Sparse OriginalKey := [(Sum.inl 148, -105705571200), (Sum.inl 159, -14173675200), (Sum.inl 165, 47226761280), (Sum.inl 166, -174262449600), (Sum.inl 170, 14642695200), (Sum.inl 181, 107818617600), (Sum.inl 188, -18134899200), (Sum.inl 191, 165345336000), (Sum.inl 193, 75033744000), (Sum.inl 194, -2725992000), (Sum.inl 208, -61895664000), (Sum.inl 218, -58574232000), (Sum.inl 225, 130712227200), (Sum.inl 228, 115226812800), (Sum.inl 246, -7706640000), (Sum.inl 250, -74818108800), (Sum.inl 258, 96879938400), (Sum.inl 263, 55860511200), (Sum.inl 264, -46304864400), (Sum.inl 271, 15419606400), (Sum.inl 328, -9787881600), (Sum.inl 340, 66564864000), (Sum.inl 342, -33069067200), (Sum.inl 367, 6668625600), (Sum.inl 387, 44211552000), (Sum.inl 388, 3589920800), (Sum.inl 406, -109956460800), (Sum.inl 413, 2611036800), (Sum.inl 416, -44568225600)]

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

def originalBlock20 : Integer.Sparse OriginalKey := [(Sum.inl 0, 48879417600), (Sum.inl 3, 29220955200), (Sum.inl 111, -11410603200), (Sum.inl 112, 11410603200), (Sum.inl 265, -97758835200), (Sum.inl 310, -48837120000), (Sum.inl 312, 48837120000), (Sum.inl 355, -1213512000), (Sum.inl 382, -62887622400), (Sum.inl 386, -62887622400), (Sum.inl 387, 51295080000), (Sum.inl 390, -46379160000), (Sum.inl 411, 62887622400), (Sum.inl 420, 58337715200), (Sum.inl 436, -76224000), (Sum.inl 437, 76224000), (Sum.inl 438, 1213512000), (Sum.inl 464, -29220955200), (Sum.inl 479, -9831840000), (Sum.inl 483, -4915920000), (Sum.inl 488, 1195348000), (Sum.inl 492, 29220955200), (Sum.inl 496, -35035459200), (Sum.inl 502, -1165012800), (Sum.inl 503, -107665080000), (Sum.inl 514, -45039552000), (Sum.inl 516, 22481664000), (Sum.inl 528, 1165012800), (Sum.inl 530, 107665080000), (Sum.inr 5, -7785657600), (Sum.inr 7, 1434417600)]

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

def originalBlock21 : Integer.Sparse OriginalKey := [(Sum.inl 5, 107140838400), (Sum.inl 7, 175021876800), (Sum.inl 224, 26323257600), (Sum.inl 259, 48879417600), (Sum.inl 262, -13161628800), (Sum.inl 319, 58441910400), (Sum.inl 327, 62887622400), (Sum.inl 373, -58441910400), (Sum.inl 374, -29220955200), (Sum.inl 376, -717208800), (Sum.inl 378, 2629765600), (Sum.inl 387, 253025049600), (Sum.inl 397, -3891744000), (Sum.inl 416, -126512524800), (Sum.inl 479, -20406261600), (Sum.inl 488, -1195348000), (Sum.inl 489, 3277280000), (Sum.inl 490, -67578660000), (Sum.inl 494, -8606505600), (Sum.inl 504, 26607974400), (Sum.inl 505, 1410213600), (Sum.inl 506, -121506962400), (Sum.inl 526, -53215948800), (Sum.inl 529, 26607974400), (Sum.inl 531, 32650992000), (Sum.inl 532, -6819163200), (Sum.inr 7, -1434417600)]

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

def originalBlock22 : Integer.Sparse OriginalKey := [(Sum.inl 149, -84698448000), (Sum.inl 301, 48837120000), (Sum.inl 305, 3891744000), (Sum.inl 306, 300814920000), (Sum.inl 325, -76224000), (Sum.inl 326, 3891744000), (Sum.inl 376, 717208800), (Sum.inl 377, -35728000000), (Sum.inl 378, 5976740000), (Sum.inl 387, 22557888000), (Sum.inl 390, -22481664000), (Sum.inl 402, -300814920000), (Sum.inl 403, -26607974400), (Sum.inl 404, 26607974400), (Sum.inl 405, 103604644800), (Sum.inl 429, 76224000), (Sum.inl 432, 142078536000), (Sum.inl 479, 6454879200), (Sum.inl 483, 22481664000), (Sum.inl 488, -26607974400), (Sum.inl 489, -26607974400), (Sum.inl 496, -315115968000), (Sum.inl 520, -3574368000), (Sum.inl 521, -29076624000), (Sum.inl 526, -113391273600), (Sum.inl 527, 87559444800), (Sum.inl 532, -317392761600), (Sum.inl 533, -25831828800)]

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

def originalBlock23 : Integer.Sparse OriginalKey := [(Sum.inl 8, -7727126400), (Sum.inl 9, 4829454000), (Sum.inl 21, -49636036800), (Sum.inl 24, 49636036800), (Sum.inl 98, 62331835200), (Sum.inl 100, 14050012800), (Sum.inl 163, 3863563200), (Sum.inl 171, 75431952000), (Sum.inl 172, 49636036800), (Sum.inl 207, -13161628800), (Sum.inl 220, 4534636800), (Sum.inl 232, -115774934400), (Sum.inl 242, -49636036800), (Sum.inl 243, -20806603200), (Sum.inl 257, -4829454000), (Sum.inl 259, -20017828800), (Sum.inl 260, 566829600), (Sum.inl 303, -48837120000), (Sum.inl 321, -2868835200), (Sum.inl 339, 23943540000), (Sum.inl 371, -126512524800), (Sum.inl 379, 39005280000), (Sum.inl 407, -51802322400), (Sum.inl 429, 9831840000), (Sum.inl 436, 22557888000), (Sum.inl 448, -5825064000), (Sum.inl 449, 31142630400), (Sum.inl 502, -6990076800), (Sum.inl 504, 14366124000), (Sum.inl 505, 3892828800), (Sum.inl 525, 26607974400), (Sum.inl 531, 142370884800)]

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

def originalBlock24 : Integer.Sparse OriginalKey := [(Sum.inl 22, -20806603200), (Sum.inl 26, 20152521600), (Sum.inl 30, 6635121600), (Sum.inl 91, 24193723200), (Sum.inl 124, 84698448000), (Sum.inl 155, -4660051200), (Sum.inl 157, 112325131200), (Sum.inl 174, -6019252800), (Sum.inl 178, -65316998400), (Sum.inl 221, -55464763200), (Sum.inl 234, 115774934400), (Sum.inl 245, -11384424000), (Sum.inl 260, 77605268800), (Sum.inl 268, -24323265600), (Sum.inl 289, -227990496000), (Sum.inl 293, 76224000), (Sum.inl 301, -9831840000), (Sum.inl 310, -22557888000), (Sum.inl 312, 22481664000), (Sum.inl 334, 26607974400), (Sum.inl 336, -26607974400), (Sum.inl 423, -76224000), (Sum.inl 424, 85911960000), (Sum.inl 437, -22481664000), (Sum.inl 450, 6990076800), (Sum.inl 467, 315115968000), (Sum.inl 472, 26607974400), (Sum.inl 503, -101840016000), (Sum.inl 517, -61727616000), (Sum.inl 520, 178693257600), (Sum.inl 521, -120210436800)]

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

def originalBlock25 : Integer.Sparse OriginalKey := [(Sum.inl 28, 21023280000), (Sum.inl 63, 56534784000), (Sum.inl 68, -50921232000), (Sum.inl 70, -14050012800), (Sum.inl 71, 4718736000), (Sum.inl 72, -11410603200), (Sum.inl 93, -101764262400), (Sum.inl 94, -377886400), (Sum.inl 158, -2595219200), (Sum.inl 161, -107665080000), (Sum.inl 175, -45491241600), (Sum.inl 183, 11384424000), (Sum.inl 210, 56534784000), (Sum.inl 222, -3400977600), (Sum.inl 227, -63920740800), (Sum.inl 247, -21023280000), (Sum.inl 252, 26825856000), (Sum.inl 285, -300814920000), (Sum.inl 291, 48837120000), (Sum.inl 293, -48837120000), (Sum.inl 294, -3891744000), (Sum.inl 303, -39005280000), (Sum.inl 321, -5737670400), (Sum.inl 325, 39005280000), (Sum.inl 332, 300814920000), (Sum.inl 339, 4788708000), (Sum.inl 341, -14366124000), (Sum.inl 343, -59635324800), (Sum.inl 452, 107665080000), (Sum.inl 508, -61727616000), (Sum.inl 509, 185182848000)]

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

def originalBlock26 : Integer.Sparse OriginalKey := [(Sum.inl 34, 654081600), (Sum.inl 39, -27658401600), (Sum.inl 69, -56534784000), (Sum.inl 99, 75584118400), (Sum.inl 186, -7442750400), (Sum.inl 275, -530018928000), (Sum.inl 277, 530018928000), (Sum.inl 510, -61727616000), (Sum.inl 2243, 87401882400), (Sum.inl 2244, -145855027200), (Sum.inl 2245, -168474076800), (Sum.inl 2247, -117286099200), (Sum.inl 2262, 58520227200), (Sum.inl 2263, -42889089600), (Sum.inl 2264, -9860337600), (Sum.inl 2265, 233656876800), (Sum.inl 2266, -440929881600), (Sum.inl 2268, -183194366400), (Sum.inl 2277, 64643558400), (Sum.inl 2278, -48822120000), (Sum.inl 2279, -116521248000), (Sum.inl 2281, -14162515200), (Sum.inl 2291, -123163785600), (Sum.inl 2293, 17971008000), (Sum.inl 2294, -141720868800), (Sum.inl 2734, -3134764800), (Sum.inl 2740, 13808236800), (Sum.inl 2742, 623786404800), (Sum.inl 4083, -44512792800), (Sum.inl 4084, 58247496000), (Sum.inl 4085, -47519064000)]

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

def originalBlock27 : Integer.Sparse OriginalKey := [(Sum.inl 2281, 100921248000), (Sum.inl 2709, 28946280000), (Sum.inl 2710, -26656881600), (Sum.inl 2720, 97322748000), (Sum.inl 2721, -295986379200), (Sum.inl 2722, -696694147200), (Sum.inl 2723, -76490400000), (Sum.inl 2724, -267514728000), (Sum.inl 2730, 77572192800), (Sum.inl 2731, -57933312000), (Sum.inl 2732, -133912464000), (Sum.inl 2734, 81518184000), (Sum.inl 2738, -4206873600), (Sum.inl 2739, 167513299200), (Sum.inl 2741, 256316952000), (Sum.inl 2743, 193296283200), (Sum.inl 2744, -195205056000), (Sum.inl 2750, 256316952000), (Sum.inl 2751, -79317120000), (Sum.inl 2754, 153518121600), (Sum.inl 2763, 66923863200), (Sum.inl 2764, -216647524800), (Sum.inl 2765, 295226760000), (Sum.inl 2769, 143346724800), (Sum.inl 2773, -3486544800), (Sum.inl 2774, -11194968000), (Sum.inl 2777, 120136953600), (Sum.inl 2781, 4206873600), (Sum.inl 2782, -405845558400), (Sum.inl 2783, -13808236800), (Sum.inl 2789, -20558654400), (Sum.inl 3046, 89440963200)]

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

def originalBlock28 : Integer.Sparse OriginalKey := [(Sum.inl 2247, -174572121600), (Sum.inl 2967, -223665216000), (Sum.inl 3029, -224603040000), (Sum.inl 3030, -230066688000), (Sum.inl 3031, 122193288000), (Sum.inl 3036, 185657551200), (Sum.inl 3037, -122127909600), (Sum.inl 3038, 453932740800), (Sum.inl 3039, 363586641600), (Sum.inl 3040, 63284976000), (Sum.inl 3043, -150613941600), (Sum.inl 3044, -265529937600), (Sum.inl 3045, -122182963200), (Sum.inl 3050, -82472414400), (Sum.inl 3051, -24274857600), (Sum.inl 3052, 101779036800), (Sum.inl 3053, 112210552800), (Sum.inl 3054, -130700284800), (Sum.inl 3055, 298234190400), (Sum.inl 3056, 18422688000), (Sum.inl 3064, 50477025600), (Sum.inl 3066, -107147030400), (Sum.inl 3068, -133529400000), (Sum.inl 3069, -36039360000), (Sum.inl 3073, -11452219200), (Sum.inl 3074, 96354604800), (Sum.inl 3075, -79620278400), (Sum.inl 3077, 86516385600), (Sum.inl 3078, 420923390400), (Sum.inl 3079, -125527713600), (Sum.inl 3086, -100954051200), (Sum.inl 3098, 79620278400)]

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

def originalBlock29 : Integer.Sparse OriginalKey := [(Sum.inl 1270, -96909681600), (Sum.inl 1273, 35395430400), (Sum.inl 1306, -148971484800), (Sum.inl 1310, -524726400), (Sum.inl 1797, 144016876800), (Sum.inl 1813, 168099926400), (Sum.inl 1820, -16735478400), (Sum.inl 1828, -19947182400), (Sum.inl 1832, -25832145600), (Sum.inl 1980, 141881760000), (Sum.inl 2037, 109550995200), (Sum.inl 2092, 377580144000), (Sum.inl 2113, -20125161600), (Sum.inl 2136, -1083571200), (Sum.inl 2255, 16422998400), (Sum.inl 2285, 13298904000), (Sum.inl 2573, 92375839200), (Sum.inl 2575, 257009330400), (Sum.inl 2600, 56825815200), (Sum.inl 2603, 82472414400), (Sum.inl 2641, 79317120000), (Sum.inl 2643, 95704392000), (Sum.inl 2754, -82458482400), (Sum.inl 2769, -324603897600), (Sum.inl 2777, -295226760000), (Sum.inl 2789, -101779036800), (Sum.inl 2964, -180246960000), (Sum.inl 3084, -1114852608000), (Sum.inl 3096, -20397945600), (Sum.inl 3097, 922143398400), (Sum.inl 3108, 96354604800), (Sum.inl 3118, 31850164800)]

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

def originalBlock3 : Integer.Sparse OriginalKey := [(Sum.inl 117, 46557357600), (Sum.inl 134, 14173675200), (Sum.inl 163, 7727126400), (Sum.inl 164, -10113696000), (Sum.inl 167, 10113696000), (Sum.inl 168, 34616181600), (Sum.inl 189, -8433043200), (Sum.inl 190, 8433043200), (Sum.inl 192, 198414403200), (Sum.inl 195, -198414403200), (Sum.inl 196, -87279115200), (Sum.inl 212, -66564864000), (Sum.inl 213, 66564864000), (Sum.inl 214, 7706640000), (Sum.inl 220, 2267318400), (Sum.inl 221, 50527488000), (Sum.inl 222, -3400977600), (Sum.inl 229, -17957184000), (Sum.inl 239, 51720134400), (Sum.inl 240, -96580137600), (Sum.inl 248, 248425200000), (Sum.inl 251, 8965728000), (Sum.inl 253, -19684944000), (Sum.inl 254, 19684944000), (Sum.inl 255, 58283520000), (Sum.inl 256, -58283520000), (Sum.inl 257, -6761235600), (Sum.inl 259, -31579680000), (Sum.inl 260, 29960194400), (Sum.inl 268, -7358496000), (Sum.inr 1, -2565312000)]

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

def originalBlock30 : Integer.Sparse OriginalKey := [(Sum.inl 1793, 99178046400), (Sum.inl 1957, -12711038400), (Sum.inl 1965, 59570256000), (Sum.inl 1971, 82667304000), (Sum.inl 1976, 54554630400), (Sum.inl 2010, -104616098400), (Sum.inl 2026, 80224992000), (Sum.inl 2235, -46422338400), (Sum.inl 2255, 262748664000), (Sum.inl 2716, 4757112000), (Sum.inl 2803, 203471083200), (Sum.inl 2816, 26576592000), (Sum.inl 2821, -60127800000), (Sum.inl 3033, -112964961600), (Sum.inl 3062, -122193288000), (Sum.inl 3127, -72062251200), (Sum.inl 3129, -171148118400), (Sum.inl 3131, -425560963200), (Sum.inl 3134, 251729265600), (Sum.inl 3136, 184248835200), (Sum.inl 3138, 219537662400), (Sum.inl 3156, -115587273600), (Sum.inl 3161, 13808236800), (Sum.inl 3163, 285355459200), (Sum.inl 3170, 177138796800), (Sum.inl 3174, -289204118400), (Sum.inl 3180, -232689249600), (Sum.inl 3196, 171867772800), (Sum.inl 3198, 11144980800), (Sum.inl 3202, 305008488000), (Sum.inl 3221, -173340256800), (Sum.inl 3222, -358010620800)]

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

def originalBlock31 : Integer.Sparse OriginalKey := [(Sum.inl 1116, -29951558400), (Sum.inl 1121, -232907784000), (Sum.inl 1137, 12422548800), (Sum.inl 1146, 4459440000), (Sum.inl 2235, 166565865600), (Sum.inl 2430, 530583784800), (Sum.inl 2435, 141914044800), (Sum.inl 2440, -28946280000), (Sum.inl 2443, -164832672000), (Sum.inl 2471, 143588186400), (Sum.inl 2486, -269302944000), (Sum.inl 2497, 59748652800), (Sum.inl 2520, 101779036800), (Sum.inl 2707, -22523472000), (Sum.inl 2800, -106209801600), (Sum.inl 2890, 36039360000), (Sum.inl 2895, -135693849600), (Sum.inl 2899, -259488537600), (Sum.inl 3128, -21651192000), (Sum.inl 3130, -76525828800), (Sum.inl 3132, 21651192000), (Sum.inl 3133, -16387202400), (Sum.inl 3137, 133529400000), (Sum.inl 3155, 79620278400), (Sum.inl 3158, -79620278400), (Sum.inl 3162, -166399216800), (Sum.inl 3172, 254624500800), (Sum.inl 3179, -233168486400), (Sum.inl 3189, -31225200000), (Sum.inl 3197, 50477025600), (Sum.inl 3199, 183257613600), (Sum.inl 3221, -86516385600)]

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

def originalBlock32 : Integer.Sparse OriginalKey := [(Sum.inl 585, -61808472000), (Sum.inl 590, -14480793600), (Sum.inl 612, -15534465600), (Sum.inl 621, 9720763200), (Sum.inl 909, 230156186400), (Sum.inl 914, 216296064000), (Sum.inl 931, 22920076800), (Sum.inl 940, -82667304000), (Sum.inl 949, -198242707200), (Sum.inl 954, -93059640000), (Sum.inl 1024, -79117749600), (Sum.inl 1047, -366300350400), (Sum.inl 1061, -99690657600), (Sum.inl 1315, 93070348800), (Sum.inl 1323, -131117145600), (Sum.inl 1326, 7365492000), (Sum.inl 1332, -92852160000), (Sum.inl 1336, 91300396800), (Sum.inl 1348, 40987425600), (Sum.inl 1367, 70893633600), (Sum.inl 1369, -99690657600), (Sum.inl 1385, -92446591200), (Sum.inl 1406, -592104729600), (Sum.inl 1408, -459016435200), (Sum.inl 1436, -86275296000), (Sum.inl 1438, 1055433600), (Sum.inl 2323, -153505543200), (Sum.inl 2327, 37460064000), (Sum.inl 2340, -154989753600), (Sum.inl 2346, 101296324800), (Sum.inl 2423, 151100589600), (Sum.inl 3164, -254624500800)]

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

def originalBlock33 : Integer.Sparse OriginalKey := [(Sum.inl 587, 131568940800), (Sum.inl 617, 79813992000), (Sum.inl 936, -93070348800), (Sum.inl 951, 198242707200), (Sum.inl 1027, -111800008800), (Sum.inl 1064, 99690657600), (Sum.inl 1118, 126861240000), (Sum.inl 1142, 136548936000), (Sum.inl 1314, 158876304000), (Sum.inl 1316, -254624500800), (Sum.inl 1317, 195132369600), (Sum.inl 1318, -117814651200), (Sum.inl 1319, -80607873600), (Sum.inl 1320, 315940809600), (Sum.inl 1321, -280370515200), (Sum.inl 1322, 254624500800), (Sum.inl 1325, -229519732800), (Sum.inl 1327, -141962623200), (Sum.inl 1328, -61129704000), (Sum.inl 1330, -21777398400), (Sum.inl 1334, 231192648000), (Sum.inl 1335, 195656760000), (Sum.inl 1337, -50370840000), (Sum.inl 1338, 110542320000), (Sum.inl 1366, -50477025600), (Sum.inl 1370, 50477025600), (Sum.inl 1372, 235478107200), (Sum.inl 1375, -306371740800), (Sum.inl 1383, 123753472800), (Sum.inl 1388, -61129704000), (Sum.inl 1391, -62623768800), (Sum.inl 1435, 22523472000)]

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

def originalBlock34 : Integer.Sparse OriginalKey := [(Sum.inl 591, 60910944000), (Sum.inl 623, -33449788800), (Sum.inl 624, -9654350400), (Sum.inl 626, 106376856000), (Sum.inl 627, -22862107200), (Sum.inl 628, 9654350400), (Sum.inl 629, 36039360000), (Sum.inl 630, -36039360000), (Sum.inl 631, -96217968000), (Sum.inl 633, 122648020800), (Sum.inl 634, -121776561600), (Sum.inl 635, -50064960000), (Sum.inl 636, -106301697600), (Sum.inl 637, 133529400000), (Sum.inl 638, 139214414400), (Sum.inl 639, -93059640000), (Sum.inl 640, -133529400000), (Sum.inl 641, 69128280000), (Sum.inl 642, -208342694400), (Sum.inl 643, 93059640000), (Sum.inl 653, 23713099200), (Sum.inl 654, 8398324800), (Sum.inl 911, 196881108000), (Sum.inl 1324, -236194022400), (Sum.inl 1333, 203092327200), (Sum.inl 2740, 48570624000), (Sum.inl 3052, 15216600000), (Sum.inl 3075, -44919432000), (Sum.inl 3534, 221244028800), (Sum.inl 3547, -3010183200), (Sum.inl 3548, 38313403200), (Sum.inl 3549, 61158211200)]

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

def originalBlock35 : Integer.Sparse OriginalKey := [(Sum.inl 2294, -15483340800), (Sum.inl 2742, 614185550400), (Sum.inl 2744, 104068437600), (Sum.inl 2783, -48570624000), (Sum.inl 2789, -15216600000), (Sum.inl 3054, -47880384000), (Sum.inl 3098, 44919432000), (Sum.inl 3525, -185802336000), (Sum.inl 3526, -205196112000), (Sum.inl 3535, -47050699200), (Sum.inl 3541, -113098987200), (Sum.inl 3572, 185802336000), (Sum.inl 3573, 205184534400), (Sum.inl 3583, -221255606400), (Sum.inl 3584, 161990908800), (Sum.inl 3618, 31183603200), (Sum.inl 3619, -104801284800), (Sum.inl 3622, 137223000000), (Sum.inl 3623, 144178344000), (Sum.inl 3625, 80551305600), (Sum.inl 3626, -135069948000), (Sum.inl 3627, 65356324800), (Sum.inl 3628, -168406603200), (Sum.inl 3629, -164136484800), (Sum.inl 3632, 14595009600), (Sum.inl 3633, 105398992800), (Sum.inl 3635, -160502640000), (Sum.inl 3636, -33658200000), (Sum.inl 3817, 94144846800), (Sum.inl 4084, 158436696000), (Sum.inl 4092, -650456920000)]

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

def originalBlock36 : Integer.Sparse OriginalKey := [(Sum.inl 2264, -158436696000), (Sum.inl 2722, -804731822400), (Sum.inl 3038, -186950205600), (Sum.inl 3051, 36814225600), (Sum.inl 3052, 59002704000), (Sum.inl 3064, 206075520000), (Sum.inl 3077, -347131800000), (Sum.inl 3541, 189456811200), (Sum.inl 3800, -157808876000), (Sum.inl 3801, -34911060000), (Sum.inl 3805, 55524372000), (Sum.inl 3806, 17804046000), (Sum.inl 3807, 1132317305600), (Sum.inl 3808, 511992224000), (Sum.inl 3809, 390848535200), (Sum.inl 3812, 1455966000), (Sum.inl 3813, -87436574000), (Sum.inl 3814, -5379840000), (Sum.inl 3816, -56980338000), (Sum.inl 3837, -605028768000), (Sum.inl 3838, 79544392000), (Sum.inl 3839, -521504863200), (Sum.inl 3840, 323321760000), (Sum.inl 3841, 95601117600), (Sum.inl 3843, 56980338000), (Sum.inl 3844, 17804046000), (Sum.inl 3845, -94144846800), (Sum.inl 3850, 107202548000), (Sum.inl 3854, -235885186000), (Sum.inl 4091, -17804046000)]

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

def originalBlock37 : Integer.Sparse OriginalKey := [(Sum.inl 2279, -124867533600), (Sum.inl 2730, -1455966000), (Sum.inl 2731, 1455966000), (Sum.inl 2732, -122152946400), (Sum.inl 2734, 274451563200), (Sum.inl 2765, 190546272000), (Sum.inl 2773, -235885186000), (Sum.inl 2774, 235885186000), (Sum.inl 2777, -55586808000), (Sum.inl 3037, -163384452000), (Sum.inl 3039, 163384452000), (Sum.inl 3055, -36814225600), (Sum.inl 3086, 141056280000), (Sum.inl 3629, -216736704000), (Sum.inl 3632, -110520960000), (Sum.inl 3840, -1455966000), (Sum.inl 3846, -108963988000), (Sum.inl 3848, -55524372000), (Sum.inl 3849, -17804046000), (Sum.inl 3850, 107202548000), (Sum.inl 3871, 157808876000), (Sum.inl 3872, 34911060000), (Sum.inl 3874, -55524372000), (Sum.inl 3875, -17804046000), (Sum.inl 3876, -591536616000), (Sum.inl 3877, 130656328000), (Sum.inl 3881, 108963988000), (Sum.inl 3884, 55524372000), (Sum.inl 3885, 17804046000), (Sum.inl 3886, -107202548000), (Sum.inl 3905, 148702010400), (Sum.inl 3907, -19757059200)]

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

def originalBlock38 : Integer.Sparse OriginalKey := [(Sum.inl 2277, 54936134400), (Sum.inl 2278, -54936134400), (Sum.inl 2281, -39458671200), (Sum.inl 2293, -68581632000), (Sum.inl 2743, -158671862400), (Sum.inl 3054, 76709700000), (Sum.inl 3055, 59153952000), (Sum.inl 3078, 183814200000), (Sum.inl 3584, 128818771200), (Sum.inl 3633, 110520960000), (Sum.inl 3812, 168040209600), (Sum.inl 3813, 17809507200), (Sum.inl 3814, -302522371200), (Sum.inl 3817, 563925546400), (Sum.inl 3845, -617258680000), (Sum.inl 3877, 120114460800), (Sum.inl 3884, 301198514000), (Sum.inl 3901, -284384068800), (Sum.inl 3903, -453523627200), (Sum.inl 3904, 188055000000), (Sum.inl 3906, -110639640000), (Sum.inl 3907, -49458676800), (Sum.inl 3908, 101054520000), (Sum.inl 3910, 96329068800), (Sum.inl 3913, 326717707200), (Sum.inl 3953, 434398496000), (Sum.inl 3954, 343718712000), (Sum.inl 3958, -949990736000), (Sum.inl 3959, -349051104800), (Sum.inl 3961, 56980338000), (Sum.inl 3962, 17804046000), (Sum.inl 3963, -166919857200)]

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

def originalBlock39 : Integer.Sparse OriginalKey := [(Sum.inl 2244, -455153568000), (Sum.inl 2265, 455153568000), (Sum.inl 2278, 68581632000), (Sum.inl 2709, 553129632000), (Sum.inl 2731, 6491932800), (Sum.inl 2952, 323592720000), (Sum.inl 3029, -117830160000), (Sum.inl 3044, -167719992000), (Sum.inl 3068, -80392320000), (Sum.inl 3098, 123712824000), (Sum.inl 3505, 174490872000), (Sum.inl 3506, 48189340800), (Sum.inl 3573, 272814672000), (Sum.inl 3723, -223688776800), (Sum.inl 3730, 212536924800), (Sum.inl 3800, 247390920000), (Sum.inl 3808, -247390920000), (Sum.inl 3813, -579891380800), (Sum.inl 3826, -216104352000), (Sum.inl 3840, 605028768000), (Sum.inl 3848, -56980338000), (Sum.inl 3872, 247390920000), (Sum.inl 3874, -1455966000), (Sum.inl 3880, 682613036000), (Sum.inl 3884, 166919857200), (Sum.inl 3909, -17804046000), (Sum.inl 3953, 440636496000), (Sum.inl 3956, -55524372000), (Sum.inl 3957, -17804046000), (Sum.inl 3958, -440636496000), (Sum.inl 3972, 150460056000)]

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

def originalBlock4 : Integer.Sparse OriginalKey := [(Sum.inl 14, -60004357200), (Sum.inl 19, -30184692800), (Sum.inl 32, -33000508800), (Sum.inl 41, 4335177600), (Sum.inl 58, -265908600000), (Sum.inl 60, 55422432000), (Sum.inl 67, 61895664000), (Sum.inl 73, 2725992000), (Sum.inl 74, 7706640000), (Sum.inl 75, -7706640000), (Sum.inl 76, -33000508800), (Sum.inl 87, 189297187200), (Sum.inl 91, 25263744000), (Sum.inl 93, -53685456000), (Sum.inl 94, 377886400), (Sum.inl 97, -11872209600), (Sum.inl 98, 3679248000), (Sum.inl 101, -7695936000), (Sum.inl 102, -46276012800), (Sum.inl 103, 12826560000), (Sum.inl 143, 14716992000), (Sum.inl 154, -7638192000), (Sum.inl 169, -22430001600), (Sum.inl 197, -165345336000), (Sum.inl 227, -44211552000), (Sum.inl 249, -248425200000), (Sum.inr 2, 2565312000)]

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

def originalBlock40 : Integer.Sparse OriginalKey := [(Sum.inl 1260, -187721556000), (Sum.inl 1261, -203013501600), (Sum.inl 1262, 187721556000), (Sum.inl 1291, -204795234400), (Sum.inl 1292, 59002704000), (Sum.inl 1295, 204795234400), (Sum.inl 2566, 1455966000), (Sum.inl 2587, 55524372000), (Sum.inl 2591, -55524372000), (Sum.inl 2631, -111488096000), (Sum.inl 2632, -85094162000), (Sum.inl 2633, 111488096000), (Sum.inl 2643, 108566040000), (Sum.inl 2750, 17804046000), (Sum.inl 2751, -570933678000), (Sum.inl 2773, 12229912000), (Sum.inl 2774, 139950017600), (Sum.inl 2933, -263307600000), (Sum.inl 2951, 451380168000), (Sum.inl 2955, -451380168000), (Sum.inl 3092, -103421880000), (Sum.inl 3724, -343718712000), (Sum.inl 3733, 136514180000), (Sum.inl 3819, 55524372000), (Sum.inl 3827, -724574936000), (Sum.inl 3846, 17804046000), (Sum.inl 3854, 12229912000), (Sum.inl 3881, 557554140000), (Sum.inl 3949, -150460056000)]

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

def originalBlock41 : Integer.Sparse OriginalKey := [(Sum.inl 1264, 187047667200), (Sum.inl 2106, 7531161600), (Sum.inl 2110, -229885401600), (Sum.inl 2115, -124867533600), (Sum.inl 2569, -1455966000), (Sum.inl 2614, 1455966000), (Sum.inl 2617, -247390920000), (Sum.inl 2618, 263307600000), (Sum.inl 2620, 71642647200), (Sum.inl 2631, -290176440000), (Sum.inl 2632, -85094162000), (Sum.inl 2633, 290176440000), (Sum.inl 2635, 85094162000), (Sum.inl 2641, 117830160000), (Sum.inl 3582, 110520960000), (Sum.inl 3623, 128354832000), (Sum.inl 3633, 305094744000), (Sum.inl 3731, -107724052800), (Sum.inl 3732, -41009284800), (Sum.inl 3786, 113352984000), (Sum.inl 3789, 11333937600), (Sum.inl 3849, -6812294400), (Sum.inl 3850, -390303998400), (Sum.inl 3857, 162978240000), (Sum.inl 3875, -205539480000), (Sum.inl 3885, 199792382400), (Sum.inl 3886, 232991841600), (Sum.inl 3907, 433938175200), (Sum.inl 3910, 127302427200), (Sum.inl 3913, 545441040000), (Sum.inl 4010, 205539480000)]

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

def originalBlock42 : Integer.Sparse OriginalKey := [(Sum.inl 1294, 76709700000), (Sum.inl 1297, -39458671200), (Sum.inl 2105, -14850288000), (Sum.inl 2109, -7531161600), (Sum.inl 2112, -133578662400), (Sum.inl 2116, 14850288000), (Sum.inl 2266, -182143392000), (Sum.inl 2294, -140718600000), (Sum.inl 2589, 4832212800), (Sum.inl 2590, 127183958400), (Sum.inl 2724, 306671894400), (Sum.inl 2744, -526839600000), (Sum.inl 2764, -125322345600), (Sum.inl 2765, -186816417600), (Sum.inl 2782, -371835806400), (Sum.inl 2783, -110520960000), (Sum.inl 2954, -22667875200), (Sum.inl 3040, -38852256000), (Sum.inl 3056, -126127992000), (Sum.inl 3079, -201346320000), (Sum.inl 3378, -17910561600), (Sum.inl 3379, -58822180800), (Sum.inl 3395, 251674977600), (Sum.inl 3396, 277508563200), (Sum.inl 3505, 32825736000), (Sum.inl 3506, -131822880000), (Sum.inl 3541, -167468640000), (Sum.inl 3573, 81846465600), (Sum.inl 3584, 603335601600), (Sum.inl 3626, 359809380000), (Sum.inl 3787, -261555840000), (Sum.inl 3876, 261555840000)]

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

def originalBlock43 : Integer.Sparse OriginalKey := [(Sum.inl 2279, 361853520000), (Sum.inl 2732, 406475515200), (Sum.inl 2864, 35637960000), (Sum.inl 2867, -237827995200), (Sum.inl 2885, -183691496800), (Sum.inl 2888, -25885348800), (Sum.inl 3045, 243495408000), (Sum.inl 3066, -42757920000), (Sum.inl 3069, 80392320000), (Sum.inl 3379, 48730814400), (Sum.inl 3395, 185644665600), (Sum.inl 3535, 123035280000), (Sum.inl 3541, -123035280000), (Sum.inl 3584, -123035280000), (Sum.inl 3720, 1455966000), (Sum.inl 3722, -274536384000), (Sum.inl 3730, -199284840000), (Sum.inl 3733, -101913674000), (Sum.inl 3809, -456724480000), (Sum.inl 3814, 359549216800), (Sum.inl 3839, 581582988000), (Sum.inl 3841, -701015448000), (Sum.inl 3877, -459513561200), (Sum.inl 3946, 55524372000), (Sum.inl 3949, -56859332000), (Sum.inl 3954, 17804046000), (Sum.inl 3959, 203220442800), (Sum.inl 3972, 66626660000), (Sum.inl 4022, 326025590400), (Sum.inl 4024, -56980338000), (Sum.inl 4025, -17804046000)]

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

def originalBlock44 : Integer.Sparse OriginalKey := [(Sum.inl 1216, 6660396000), (Sum.inl 1219, 237001824000), (Sum.inl 1241, 228400907200), (Sum.inl 1245, 142255420800), (Sum.inl 1809, -94033929600), (Sum.inl 1824, 21789864000), (Sum.inl 1826, 62670528000), (Sum.inl 2089, -502883025600), (Sum.inl 2108, -488395392000), (Sum.inl 2133, 312777264000), (Sum.inl 2245, 227576784000), (Sum.inl 2253, -368839929600), (Sum.inl 2284, 140718600000), (Sum.inl 2545, -1455966000), (Sum.inl 2557, -55524372000), (Sum.inl 2617, 721796000), (Sum.inl 2620, 209131082000), (Sum.inl 2710, 120478362000), (Sum.inl 2732, 183518108000), (Sum.inl 2744, 123035280000), (Sum.inl 2916, 15916680000), (Sum.inl 2928, 150460056000), (Sum.inl 2930, 272814672000), (Sum.inl 3030, 117830160000), (Sum.inl 3378, 149101848000), (Sum.inl 3715, 299006860800), (Sum.inl 3722, -422303109600), (Sum.inl 3723, 305829372000), (Sum.inl 3839, 56980338000), (Sum.inl 3872, -100609136000), (Sum.inl 3899, 17804046000)]

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

def originalBlock45 : Integer.Sparse OriginalKey := [(Sum.inl 580, 23325720000), (Sum.inl 582, 16149292800), (Sum.inl 604, 177820420800), (Sum.inl 607, 61158211200), (Sum.inl 944, 152976600000), (Sum.inl 946, 131822880000), (Sum.inl 1058, 167468640000), (Sum.inl 1113, -234184442400), (Sum.inl 1130, -251563615200), (Sum.inl 1133, 34752691200), (Sum.inl 1791, -179201630400), (Sum.inl 1806, -255378897600), (Sum.inl 1829, 179556456000), (Sum.inl 2039, 167468640000), (Sum.inl 2138, 214062336000), (Sum.inl 2233, -227576784000), (Sum.inl 2253, -179710128000), (Sum.inl 2438, -124036920000), (Sum.inl 2494, 23445780000), (Sum.inl 2513, -123035280000), (Sum.inl 2714, -498059928000), (Sum.inl 2798, -179487304800), (Sum.inl 2810, -54492343200), (Sum.inl 2812, 202893460800), (Sum.inl 2892, 174490872000), (Sum.inl 3032, 58921608000), (Sum.inl 3365, 119640744000), (Sum.inl 3577, 123035280000), (Sum.inl 3674, -89725020000), (Sum.inl 3698, 95986680000), (Sum.inl 3788, 72775010400), (Sum.inl 3803, 65243594400)]

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

def originalBlock46 : Integer.Sparse OriginalKey := [(Sum.inl 586, -23337297600), (Sum.inl 616, -62880211200), (Sum.inl 950, -152976600000), (Sum.inl 1063, -167468640000), (Sum.inl 1117, -6660396000), (Sum.inl 1141, 23162708000), (Sum.inl 1794, 17898984000), (Sum.inl 1795, 219962712000), (Sum.inl 1816, 233584339200), (Sum.inl 1830, 63457464000), (Sum.inl 1977, -32825736000), (Sum.inl 1978, 131822880000), (Sum.inl 2094, 421013404800), (Sum.inl 2353, -106544532000), (Sum.inl 2362, -263564760000), (Sum.inl 2433, 55524372000), (Sum.inl 2441, -721796000), (Sum.inl 2473, 17804046000), (Sum.inl 2499, -206963888000), (Sum.inl 2745, -138282408000), (Sum.inl 2758, -215087481600), (Sum.inl 2801, -35637960000), (Sum.inl 2819, 238183840000), (Sum.inl 2898, -150460056000), (Sum.inl 3083, -37634400000), (Sum.inl 3673, -55524372000), (Sum.inl 3676, 56859332000), (Sum.inl 3685, -17804046000), (Sum.inl 3699, 87531428000), (Sum.inl 3710, 96277519200), (Sum.inl 3780, 119432460000), (Sum.inl 3783, 33982476000)]

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

def originalBlock47 : Integer.Sparse OriginalKey := [(Sum.inl 588, -25179842400), (Sum.inl 952, -131822880000), (Sum.inl 1119, -34749050400), (Sum.inl 1804, 74353968000), (Sum.inl 1811, 142901064000), (Sum.inl 1814, 68559696000), (Sum.inl 1817, -46450022400), (Sum.inl 1966, 136692408000), (Sum.inl 2023, 2355379200), (Sum.inl 2028, 21155846400), (Sum.inl 2058, -69976252800), (Sum.inl 2110, -147022876800), (Sum.inl 2115, -194453344800), (Sum.inl 2245, 76033483200), (Sum.inl 2266, 160502640000), (Sum.inl 2279, 11064384000), (Sum.inl 2294, 33658200000), (Sum.inl 2347, 1455966000), (Sum.inl 2348, -1455966000), (Sum.inl 2349, -15916680000), (Sum.inl 2350, -56402145600), (Sum.inl 2352, 385383631200), (Sum.inl 2355, -85094162000), (Sum.inl 2356, 191638694000), (Sum.inl 2361, -117830160000), (Sum.inl 3626, -88358040000), (Sum.inl 3708, 615399480000), (Sum.inl 3732, -379579550400), (Sum.inl 3789, 26989660800), (Sum.inl 3809, -646495560000), (Sum.inl 3814, -533854281600)]

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

def originalBlock48 : Integer.Sparse OriginalKey := [(Sum.inl 1138, -302522371200), (Sum.inl 1143, -124867533600), (Sum.inl 1802, 62467296000), (Sum.inl 1805, -14850288000), (Sum.inl 1807, 94809945600), (Sum.inl 1810, -94809945600), (Sum.inl 1811, -12423974400), (Sum.inl 1812, -229885401600), (Sum.inl 1815, 14850288000), (Sum.inl 1819, -124867533600), (Sum.inl 2431, 286319414400), (Sum.inl 2483, 313377345600), (Sum.inl 2488, -13306478400), (Sum.inl 2515, 492089726400), (Sum.inl 2522, 110520960000), (Sum.inl 2814, -107724052800), (Sum.inl 2817, -41009284800), (Sum.inl 2896, 11333937600), (Sum.inl 3397, -110520960000), (Sum.inl 3619, -128354832000), (Sum.inl 3671, 67570512000), (Sum.inl 3692, 6812294400), (Sum.inl 3693, 114004324800), (Sum.inl 3706, -300181939200), (Sum.inl 3709, -65388960000), (Sum.inl 3719, 36152198400), (Sum.inl 3721, 270928440000), (Sum.inl 3731, -11333937600), (Sum.inl 3782, -4200700800), (Sum.inl 3801, -315357427200), (Sum.inl 3899, 238970664000), (Sum.inl 4025, -205539480000)]

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

def originalBlock49 : Integer.Sparse OriginalKey := [(Sum.inl 610, -104801284800), (Sum.inl 613, -122621248800), (Sum.inl 618, -15483340800), (Sum.inl 929, 61189516800), (Sum.inl 932, 48820406400), (Sum.inl 937, -74353968000), (Sum.inl 1044, -139578379200), (Sum.inl 1049, -160921344000), (Sum.inl 1087, -136273704000), (Sum.inl 1818, -62467296000), (Sum.inl 2338, -4832212800), (Sum.inl 2341, -31951497600), (Sum.inl 2769, -148000032000), (Sum.inl 2789, -107818008000), (Sum.inl 2865, -415254528000), (Sum.inl 2878, 55524372000), (Sum.inl 2882, -55524372000), (Sum.inl 2885, 79109856800), (Sum.inl 2886, 91306568800), (Sum.inl 2888, 246641601600), (Sum.inl 2928, 398020176000), (Sum.inl 2930, -101729798400), (Sum.inl 2951, 451224064000), (Sum.inl 2952, -338778936000), (Sum.inl 2955, -607230628000), (Sum.inl 2964, -141056280000), (Sum.inl 2967, -200737104000), (Sum.inl 3051, -11215868000), (Sum.inl 3055, 11215868000), (Sum.inl 3074, 17804046000), (Sum.inl 3097, 299709156000), (Sum.inl 3098, 724123195200)]

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

def originalBlock5 : Integer.Sparse OriginalKey := [(Sum.inl 8, -3863563200), (Sum.inl 9, 6761235600), (Sum.inl 11, -9950788800), (Sum.inl 12, -12784298400), (Sum.inl 13, -13906862400), (Sum.inl 14, 5607147600), (Sum.inl 15, -12479212800), (Sum.inl 16, 54397209600), (Sum.inl 17, -18464990400), (Sum.inl 18, -14953334400), (Sum.inl 19, -6960335200), (Sum.inl 20, 22854296400), (Sum.inl 37, 33000508800), (Sum.inl 59, -58574232000), (Sum.inl 88, 96879938400), (Sum.inl 99, 30408132800), (Sum.inl 100, -9198120000), (Sum.inl 104, 23138006400), (Sum.inl 377, -2565312000), (Sum.inl 382, 99833702400), (Sum.inl 383, -23917920000), (Sum.inl 384, -57169735200), (Sum.inl 385, -21316464000), (Sum.inl 387, 102036312000), (Sum.inl 389, -8280106800), (Sum.inl 391, 30886833600), (Sum.inl 402, 2565312000), (Sum.inl 409, -74875276800), (Sum.inl 410, 23917920000), (Sum.inl 414, -53070873600), (Sum.inr 0, 1034712000)]

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

def originalBlock50 : Integer.Sparse OriginalKey := [(Sum.inl 1217, 520354932000), (Sum.inl 1243, 46768380800), (Sum.inl 1790, -121384593600), (Sum.inl 1808, -131701392000), (Sum.inl 1825, 88499160000), (Sum.inl 1973, 185802336000), (Sum.inl 2090, -724134772800), (Sum.inl 2134, 107818008000), (Sum.inl 2558, 55524372000), (Sum.inl 2618, 663368164000), (Sum.inl 2712, 17804046000), (Sum.inl 2734, -11215868000), (Sum.inl 2754, -138282408000), (Sum.inl 2759, -197879966400), (Sum.inl 2777, 345879998400), (Sum.inl 2797, 287508036000), (Sum.inl 2811, -91306568800), (Sum.inl 2848, -138074949600), (Sum.inl 2861, -55524372000), (Sum.inl 2865, -150460056000), (Sum.inl 2867, 58965092800), (Sum.inl 2900, 441407308000), (Sum.inl 2902, 364269600000), (Sum.inl 2916, -89212524000), (Sum.inl 2933, -174634444000), (Sum.inl 2942, -223213320000), (Sum.inl 2979, -11215868000), (Sum.inl 2984, 404016036000), (Sum.inl 3038, 11215868000), (Sum.inl 3064, -17804046000), (Sum.inl 3078, -17804046000), (Sum.inl 3086, -703725192000)]

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

def originalBlock51 : Integer.Sparse OriginalKey := [(Sum.inl 581, 23321860800), (Sum.inl 589, -23333438400), (Sum.inl 606, 38313403200), (Sum.inl 945, 152976600000), (Sum.inl 953, -152976600000), (Sum.inl 1112, -701416092000), (Sum.inl 1120, 181061160000), (Sum.inl 1132, -46768380800), (Sum.inl 1796, 223091236800), (Sum.inl 1812, -81656510400), (Sum.inl 1819, -155325823200), (Sum.inl 1831, 112237944000), (Sum.inl 1970, 58644724800), (Sum.inl 1979, 152976600000), (Sum.inl 2025, -176322196800), (Sum.inl 2062, -103475491200), (Sum.inl 2112, 35658345600), (Sum.inl 2247, -14346633600), (Sum.inl 2281, 207627019200), (Sum.inl 2426, -55524372000), (Sum.inl 2437, -774134464000), (Sum.inl 2442, 110766300000), (Sum.inl 2470, -17804046000), (Sum.inl 2495, 11215868000), (Sum.inl 2746, 138282408000), (Sum.inl 2802, 127746492000), (Sum.inl 2824, -308807652000), (Sum.inl 2826, -276589620000), (Sum.inl 2827, 165823320000), (Sum.inl 2846, 55524372000), (Sum.inl 2847, 150460056000), (Sum.inl 2981, 17804046000)]

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

def originalBlock52 : Integer.Sparse OriginalKey := [(Sum.inl 611, 184805035200), (Sum.inl 620, 92289996000), (Sum.inl 930, 52231190400), (Sum.inl 939, -58644724800), (Sum.inl 1046, 112642344000), (Sum.inl 1091, 103475491200), (Sum.inl 1145, 61432257600), (Sum.inl 1964, 25795296000), (Sum.inl 2345, -89979715200), (Sum.inl 2429, 19328851200), (Sum.inl 2434, 58414905600), (Sum.inl 2485, -188055000000), (Sum.inl 2519, -109514289600), (Sum.inl 2807, 76530432000), (Sum.inl 2809, -65388960000), (Sum.inl 2813, -44965622400), (Sum.inl 2814, -11333937600), (Sum.inl 2815, 133211174400), (Sum.inl 2817, -170892388800), (Sum.inl 2818, 65388960000), (Sum.inl 2820, 33886166400), (Sum.inl 2881, 269973768000), (Sum.inl 2889, -160459478400), (Sum.inl 2893, -28154620800), (Sum.inl 2896, 93570868800), (Sum.inl 2924, 367673112000), (Sum.inl 2931, -123308870400), (Sum.inl 2954, -215448105600), (Sum.inl 3053, -238970664000), (Sum.inl 3054, -67818499200), (Sum.inl 3077, -28154620800)]

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

def originalBlock53 : Integer.Sparse OriginalKey := [(Sum.inl 1115, -41814830400), (Sum.inl 1148, -1455966000), (Sum.inl 1149, 1455966000), (Sum.inl 1150, 15916680000), (Sum.inl 1151, -100908033600), (Sum.inl 1153, -72123009600), (Sum.inl 1155, 100286203200), (Sum.inl 1156, -107217408000), (Sum.inl 1159, -38942758000), (Sum.inl 1160, 146160166000), (Sum.inl 1169, 117830160000), (Sum.inl 1171, 182096016000), (Sum.inl 1174, 16118664000), (Sum.inl 1212, -1455966000), (Sum.inl 1215, 1455966000), (Sum.inl 1217, -15916680000), (Sum.inl 1219, 64717060800), (Sum.inl 1221, 25848996000), (Sum.inl 1233, 1455966000), (Sum.inl 1237, -1455966000), (Sum.inl 1241, 4259304000), (Sum.inl 1243, -116252037600), (Sum.inl 1245, 63092460000), (Sum.inl 1261, -38942758000), (Sum.inl 1264, 38942758000), (Sum.inl 1270, -117830160000), (Sum.inl 1273, -170334312000), (Sum.inl 1291, 146160166000), (Sum.inl 1295, -146160166000), (Sum.inl 1306, -11761704000), (Sum.inl 1310, -16118664000), (Sum.inl 2339, -19328851200)]

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

def originalBlock54 : Integer.Sparse OriginalKey := [(Sum.inl 584, -3010183200), (Sum.inl 599, -2886739200), (Sum.inl 600, 9158889600), (Sum.inl 608, -9158889600), (Sum.inl 610, -146987582400), (Sum.inl 613, 53442345600), (Sum.inl 615, -106916083200), (Sum.inl 618, 49696488000), (Sum.inl 620, 154025107200), (Sum.inl 934, -8799801600), (Sum.inl 1051, 68330572800), (Sum.inl 1126, -3052483200), (Sum.inl 1128, 8799801600), (Sum.inl 1129, 24408979200), (Sum.inl 1131, 66875923200), (Sum.inl 1134, -50184307200), (Sum.inl 1135, -118522728000), (Sum.inl 1138, -208211889600), (Sum.inl 1139, -24408979200), (Sum.inl 1140, 148702010400), (Sum.inl 1143, -22634251200), (Sum.inl 1144, -13639132800), (Sum.inl 1145, 18067399200), (Sum.inl 1235, 181130500800), (Sum.inl 1236, 408321456000), (Sum.inl 1239, -68330572800), (Sum.inl 1240, -181130500800), (Sum.inl 1242, -8285990400), (Sum.inl 1246, -400035465600), (Sum.inl 1293, 118522728000), (Sum.inl 1294, 235039104000), (Sum.inl 1297, 187650129600)]

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

def originalBlock55 : Integer.Sparse OriginalKey := [(Sum.inl 603, 5773478400), (Sum.inl 605, -9158889600), (Sum.inl 611, 303959246400), (Sum.inl 614, -2886739200), (Sum.inl 615, 154796803200), (Sum.inl 619, 9158889600), (Sum.inl 622, -21797928000), (Sum.inl 2560, -34782019200), (Sum.inl 2603, 34587763200), (Sum.inl 2738, -37714435200), (Sum.inl 2781, 37714435200), (Sum.inl 3050, -34587763200), (Sum.inl 3073, 118322150400), (Sum.inl 3096, -265845772800), (Sum.inl 3118, 147523622400), (Sum.inl 3375, 17391009600), (Sum.inl 3376, -125853436800), (Sum.inl 3380, 65186582400), (Sum.inl 3388, 758620800), (Sum.inl 3390, -64490198400), (Sum.inl 3391, -104066668800), (Sum.inl 3392, -1517241600), (Sum.inl 3532, -42494037600), (Sum.inl 3533, 79300857600), (Sum.inl 3544, 65659708800), (Sum.inl 3571, 186520291200), (Sum.inl 3572, -125853436800), (Sum.inl 3580, 758620800), (Sum.inl 3581, -5860713600), (Sum.inl 3622, 225408684000), (Sum.inl 3625, 17391009600), (Sum.inl 3633, -51482323200)]

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

def originalBlock56 : Integer.Sparse OriginalKey := [(Sum.inl 1094, -56011392000), (Sum.inl 2266, 5451292800), (Sum.inl 2291, -67663094400), (Sum.inl 2522, -111758764800), (Sum.inl 2724, -14455296000), (Sum.inl 2739, -100547280000), (Sum.inl 2740, -79300857600), (Sum.inl 2769, -34825190400), (Sum.inl 2782, 100547280000), (Sum.inl 2783, -154841582400), (Sum.inl 3051, 4578019200), (Sum.inl 3074, 239144803200), (Sum.inl 3097, -239144803200), (Sum.inl 3394, 173892648000), (Sum.inl 3397, 92333035200), (Sum.inl 3496, -22401120000), (Sum.inl 3534, 87296277600), (Sum.inl 3535, 22114080000), (Sum.inl 3548, -65659708800), (Sum.inl 3583, -95207880000), (Sum.inl 3623, -247809804000), (Sum.inl 3627, 131802278400), (Sum.inl 3816, 9749131200), (Sum.inl 3839, 9749131200), (Sum.inl 3908, 72635508000), (Sum.inl 3913, 36178819200), (Sum.inl 3959, 59043168000), (Sum.inl 3961, -29521584000), (Sum.inl 3972, -93724876800), (Sum.inl 3974, 187449753600), (Sum.inl 3983, -93724876800), (Sum.inl 4024, -29521584000)]

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

def originalBlock57 : Integer.Sparse OriginalKey := [(Sum.inl 2058, -5451292800), (Sum.inl 2262, 67663094400), (Sum.inl 2557, 33529276800), (Sum.inl 2558, 33529276800), (Sum.inl 2600, 116609155200), (Sum.inl 2720, 251459798400), (Sum.inl 2763, -251459798400), (Sum.inl 2861, -36050760000), (Sum.inl 2862, -93724876800), (Sum.inl 2878, 209649542400), (Sum.inl 2879, -11057040000), (Sum.inl 2882, -209649542400), (Sum.inl 3036, -86361984000), (Sum.inl 3084, -239144803200), (Sum.inl 3497, -11057040000), (Sum.inl 3544, -131802278400), (Sum.inl 3805, -36050760000), (Sum.inl 3809, -46324634400), (Sum.inl 3857, -36178819200), (Sum.inl 3903, -228773476800), (Sum.inl 3946, -209649542400), (Sum.inl 3956, 209649542400), (Sum.inl 3978, -93724876800), (Sum.inl 4008, 47344773600), (Sum.inl 4010, 47344773600), (Sum.inl 4025, -47344773600), (Sum.inl 4046, -385046460000), (Sum.inl 4047, -101105690400), (Sum.inl 4048, 385046460000), (Sum.inl 4049, 120339007200)]

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

def originalBlock58 : Integer.Sparse OriginalKey := [(Sum.inl 2508, 80347200000), (Sum.inl 2515, 41414037600), (Sum.inl 2519, 226007498400), (Sum.inl 2739, 396129600), (Sum.inl 2743, 120224980800), (Sum.inl 2782, -86783011200), (Sum.inl 2868, 93724876800), (Sum.inl 2880, -47344773600), (Sum.inl 2881, -177749359200), (Sum.inl 2884, 244866256800), (Sum.inl 2889, 232868361600), (Sum.inl 3108, 239144803200), (Sum.inl 3703, -67426080000), (Sum.inl 3705, 67426080000), (Sum.inl 3706, 18359102400), (Sum.inl 3782, -114155827200), (Sum.inl 3843, 75394639200), (Sum.inl 3845, -39877780800), (Sum.inl 3913, 19147368000), (Sum.inl 3922, 93724876800), (Sum.inl 3945, -213430944000), (Sum.inl 3957, -161568348000), (Sum.inl 3958, 374999292000), (Sum.inl 3961, 218643662400), (Sum.inl 3963, -169533650400), (Sum.inl 3964, -299102709600), (Sum.inl 3974, 598477404000), (Sum.inl 3983, 54236452800), (Sum.inl 4010, -760045752000), (Sum.inl 4044, -68343328800), (Sum.inl 4046, 161568348000)]

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

def originalBlock59 : Integer.Sparse OriginalKey := [(Sum.inl 1087, -93138657600), (Sum.inl 1091, 91385529600), (Sum.inl 1212, 26301628800), (Sum.inl 1233, -180127958400), (Sum.inl 1234, -11057040000), (Sum.inl 2243, 44176348800), (Sum.inl 2247, -26431459200), (Sum.inl 2263, -88352697600), (Sum.inl 2277, 67663094400), (Sum.inl 2512, -80347200000), (Sum.inl 2721, -320022432000), (Sum.inl 2730, -150912518400), (Sum.inl 2741, 320022432000), (Sum.inl 2764, -320022432000), (Sum.inl 2923, -9559209600), (Sum.inl 3043, 81783964800), (Sum.inl 3074, -91588550400), (Sum.inl 3075, 9559209600), (Sum.inl 3077, -145359590400), (Sum.inl 3078, -91588550400), (Sum.inl 3488, -11057040000), (Sum.inl 3526, 9559209600), (Sum.inl 3619, -9559209600), (Sum.inl 3623, -192723350400), (Sum.inl 3812, 26301628800), (Sum.inl 3874, -180127958400), (Sum.inl 3954, -91588550400), (Sum.inl 3957, -91588550400), (Sum.inl 3962, 91588550400), (Sum.inl 4010, -593839584000), (Sum.inl 4025, 91588550400), (Sum.inl 4083, 44176348800)]

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

def originalBlock6 : Integer.Sparse OriginalKey := [(Sum.inl 1, 116878672800), (Sum.inl 3, 22965003000), (Sum.inl 4, 577196406200), (Sum.inl 266, -116878672800), (Sum.inl 270, -15893683200), (Sum.inl 384, 1972852800), (Sum.inl 396, -30264364800), (Sum.inl 397, 31733121600), (Sum.inl 404, -82997721600), (Sum.inl 405, -7358496000), (Sum.inl 412, -72895300800), (Sum.inl 417, 30264364800), (Sum.inl 418, 53645860800), (Sum.inl 419, 60462720000), (Sum.inl 420, 50137099200), (Sum.inl 422, 32362272000), (Sum.inl 461, -24456750000), (Sum.inl 464, -22965003000), (Sum.inl 465, -834214643200), (Sum.inl 466, 24456750000), (Sum.inl 467, -368713824000), (Sum.inl 468, 43337598000), (Sum.inl 469, 368713824000), (Sum.inl 478, 158304144000), (Sum.inl 479, -24456750000), (Sum.inl 480, 161540352000), (Sum.inl 481, -57869799600), (Sum.inl 482, -22965003000), (Sum.inl 483, -368713824000), (Sum.inr 3, 17816880000)]

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

def originalBlock60 : Integer.Sparse OriginalKey := [(Sum.inl 1215, -28823112000), (Sum.inl 1235, -94689547200), (Sum.inl 1236, -86203929600), (Sum.inl 1237, 180127958400), (Sum.inl 2025, 52862918400), (Sum.inl 2028, -5451292800), (Sum.inl 2545, -28823112000), (Sum.inl 2575, -51536793600), (Sum.inl 2721, 106796328000), (Sum.inl 2722, -79763748000), (Sum.inl 2739, -44407620000), (Sum.inl 2750, 320022432000), (Sum.inl 2773, 150912518400), (Sum.inl 2924, 145359590400), (Sum.inl 2925, 183177100800), (Sum.inl 3533, -131802278400), (Sum.inl 3534, 385446700800), (Sum.inl 3693, -161138572800), (Sum.inl 3719, 160480461600), (Sum.inl 3720, 180127958400), (Sum.inl 3837, 80743329600), (Sum.inl 3843, 49110012000), (Sum.inl 3845, -162919072800), (Sum.inl 3850, -36178819200), (Sum.inl 3875, -94689547200), (Sum.inl 3876, 119896999200), (Sum.inl 3901, -546614808000), (Sum.inl 3902, 141289116000), (Sum.inl 3903, -120339007200), (Sum.inl 3906, -72635508000), (Sum.inl 3907, 180012633600), (Sum.inl 3974, 593839584000)]

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

def originalBlock61 : Integer.Sparse OriginalKey := [(Sum.inl 1044, 86213352000), (Sum.inl 1046, 172426704000), (Sum.inl 1049, 202591809600), (Sum.inl 1051, -36658953600), (Sum.inl 1240, -152363520000), (Sum.inl 1242, -74132755200), (Sum.inl 1246, -114231048000), (Sum.inl 1821, 34587763200), (Sum.inl 2104, -758620800), (Sum.inl 2131, 37714435200), (Sum.inl 2252, -85054104000), (Sum.inl 2479, -80347200000), (Sum.inl 2482, 80347200000), (Sum.inl 2483, -28177156800), (Sum.inl 2488, 94004774400), (Sum.inl 2556, -20279232000), (Sum.inl 2561, -94575744000), (Sum.inl 2722, 155741839200), (Sum.inl 2723, -86517096000), (Sum.inl 2726, -583452000), (Sum.inl 2743, 138983364000), (Sum.inl 2764, 28177156800), (Sum.inl 2765, -45574161600), (Sum.inl 2806, 11057040000), (Sum.inl 2931, 145359590400), (Sum.inl 3689, 94575744000), (Sum.inl 3692, -145419960000), (Sum.inl 3721, 73250863200), (Sum.inl 3838, 405325692000), (Sum.inl 3910, 145419960000), (Sum.inl 3958, 593839584000)]

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

def originalBlock62 : Integer.Sparse OriginalKey := [(Sum.inl 577, -17391009600), (Sum.inl 578, -60666854400), (Sum.inl 579, 17391009600), (Sum.inl 597, -758620800), (Sum.inl 601, 758620800), (Sum.inl 1111, 2521483200), (Sum.inl 1125, 11057040000), (Sum.inl 1126, 86203929600), (Sum.inl 1789, 17391009600), (Sum.inl 1802, 104066668800), (Sum.inl 1803, 758620800), (Sum.inl 1822, 29201472000), (Sum.inl 1823, -34587763200), (Sum.inl 1964, -26431459200), (Sum.inl 1966, 5451292800), (Sum.inl 2019, -79300857600), (Sum.inl 2051, -65659708800), (Sum.inl 2088, -60666854400), (Sum.inl 2105, 5860713600), (Sum.inl 2132, -37714435200), (Sum.inl 2243, -225408684000), (Sum.inl 2508, 44407620000), (Sum.inl 2524, 2521483200), (Sum.inl 2529, -30247171200), (Sum.inl 2807, 177749359200), (Sum.inl 3493, 131802278400), (Sum.inl 3496, -192723350400), (Sum.inl 3689, 39877780800), (Sum.inl 3703, -102107570400), (Sum.inl 3786, 36178819200), (Sum.inl 3805, 120339007200), (Sum.inl 3812, 72635508000)]

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

def originalBlock63 : Integer.Sparse OriginalKey := [(Sum.inl 583, 60666854400), (Sum.inl 599, -29314742400), (Sum.inl 608, -18860419200), (Sum.inl 1039, 2238463200), (Sum.inl 1129, 490668614400), (Sum.inl 1134, 150425112000), (Sum.inl 1792, 60666854400), (Sum.inl 1805, 118115030400), (Sum.inl 1810, 5876784000), (Sum.inl 1827, -29201472000), (Sum.inl 2020, 20092917600), (Sum.inl 2054, 65659708800), (Sum.inl 2107, 151610664000), (Sum.inl 2244, 247809804000), (Sum.inl 2278, 51482323200), (Sum.inl 2428, 67426080000), (Sum.inl 2479, 79763748000), (Sum.inl 2480, -340506504000), (Sum.inl 2512, -138983364000), (Sum.inl 2809, 21438684000), (Sum.inl 2813, 29279136000), (Sum.inl 2893, 60369600), (Sum.inl 3670, -94575744000), (Sum.inl 3671, 8361532800), (Sum.inl 3690, -72141828000), (Sum.inl 3705, 169533650400), (Sum.inl 3781, 46382980800), (Sum.inl 3787, -174133452000), (Sum.inl 3800, 618756636000), (Sum.inl 3813, -199160001600), (Sum.inl 3909, -145419960000), (Sum.inl 3945, -593839584000)]

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

def originalBlock64 : Integer.Sparse OriginalKey := [(Sum.inl 603, 8407771200), (Sum.inl 605, -56057462400), (Sum.inl 922, 22401120000), (Sum.inl 929, -86213352000), (Sum.inl 930, -172426704000), (Sum.inl 932, -109453152000), (Sum.inl 934, 36658953600), (Sum.inl 937, 56011392000), (Sum.inl 939, -91385529600), (Sum.inl 1041, -26878046400), (Sum.inl 1131, 83058000000), (Sum.inl 1807, 152868595200), (Sum.inl 1815, -227517480000), (Sum.inl 1967, 22401120000), (Sum.inl 2022, 79300857600), (Sum.inl 2029, -64895157600), (Sum.inl 2109, 154841582400), (Sum.inl 2116, -56402784000), (Sum.inl 2332, 233710176000), (Sum.inl 2337, 27149664000), (Sum.inl 2425, -80347200000), (Sum.inl 2428, 80347200000), (Sum.inl 2429, -112708627200), (Sum.inl 2431, 89104528800), (Sum.inl 2434, -172331316000), (Sum.inl 2482, 583452000), (Sum.inl 2553, -156137968800), (Sum.inl 2561, -120224980800), (Sum.inl 2589, -28177156800), (Sum.inl 2590, 132357172800), (Sum.inl 3709, 273196620000), (Sum.inl 3779, -618756636000)]

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

def originalBlock65 : Integer.Sparse OriginalKey := [(Sum.inl 1, 198521277840), (Sum.inl 2, 28588357440), (Sum.inl 614, 20906971200), (Sum.inl 619, 74917881600), (Sum.inl 933, -22401120000), (Sum.inl 1050, 24639583200), (Sum.inl 1139, -243615547200), (Sum.inl 1144, -45119308800), (Sum.inl 1818, -139319649600), (Sum.inl 2330, -27149664000), (Sum.inl 2334, 27149664000), (Sum.inl 2337, 27149664000), (Sum.inl 2338, 173597116800), (Sum.inl 2339, -32711332800), (Sum.inl 2341, -90105403200), (Sum.inl 2342, -233710176000), (Sum.inl 2344, -27149664000), (Sum.inl 2345, -315823680000), (Sum.inl 2432, 20279232000), (Sum.inl 2489, 320227272000), (Sum.inl 2755, 52544808000), (Sum.inl 2778, 22112948160), (Sum.inl 2818, -218960167200), (Sum.inl 3114, 173684799360), (Sum.inl 3224, -6833967600), (Sum.inl 3225, -4352643360), (Sum.inl 3229, 369038421120), (Sum.inl 3230, 218407535040), (Sum.inl 3231, 84976313760), (Sum.inl 3672, 213430944000), (Sum.inl 3694, -141289116000), (Sum.inl 4084, 794085111360), (Sum.inl 4085, 114353429760), (Sum.inl 4890, 210179232000), (Sum.inl 4894, 873630140160), (Sum.inl 4895, 1476153684480), (Sum.inl 4896, -17410573440), (Sum.inl 4897, 694739197440), (Sum.inl 4898, -27335870400), (Sum.inl 4899, 88451792640), (Sum.inl 4901, 339905255040)]

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

def originalBlock66 : Integer.Sparse OriginalKey := [(Sum.inl 0, 131229672720), (Sum.inl 2754, 81173468160), (Sum.inl 2769, -61828894080), (Sum.inl 2777, 20783692320), (Sum.inl 2789, -40049530080), (Sum.inl 3037, -47344442160), (Sum.inl 3038, -29358881040), (Sum.inl 3052, -16215945520), (Sum.inl 3064, 2628710400), (Sum.inl 3075, -19790860320), (Sum.inl 3085, 37334957520), (Sum.inl 3086, -59143728960), (Sum.inl 3087, -31265090760), (Sum.inl 3088, 20936366640), (Sum.inl 3089, -15832544160), (Sum.inl 3097, -224386793040), (Sum.inl 3098, -22095397440), (Sum.inl 3099, -106234789400), (Sum.inl 3103, -59091869600), (Sum.inl 3109, 74963023680), (Sum.inl 3110, 81239126400), (Sum.inl 3111, 82255072920), (Sum.inl 3112, 40264353360), (Sum.inl 3113, 99197019360), (Sum.inl 3114, 16189117920), (Sum.inl 3119, 186807476960), (Sum.inl 3125, 10032668640), (Sum.inl 3223, -66771600000), (Sum.inl 3226, -6363334320), (Sum.inl 3227, -26760117120), (Sum.inl 3228, 18091419840), (Sum.inl 4083, 524918690880), (Sum.inl 4887, -25453337280), (Sum.inl 4888, -107040468480), (Sum.inl 4889, -267086400000), (Sum.inl 4893, 72365679360), (Sum.inl 4897, 64756471680), (Sum.inl 5251, 10514841600), (Sum.inl 5256, 149339830080), (Sum.inl 5257, -125060363040), (Sum.inl 5258, -63330176640), (Sum.inl 5259, 83745466560), (Sum.inl 5260, -236574915840), (Sum.inl 5265, -189377768640), (Sum.inl 5267, -117435524160), (Sum.inl 5270, 245530431360), (Sum.inl 5271, 299852094720), (Sum.inl 5272, 396788077440), (Sum.inl 5273, 329020291680), (Sum.inl 5274, 161057413440), (Sum.inl 5275, 324956505600), (Sum.inl 5276, 18270987200), (Sum.inl 5289, -897547172160), (Sum.inl 5290, -424939157600), (Sum.inl 5291, -236367478400), (Sum.inl 5295, -335697166080), (Sum.inl 5304, 747229907840), (Sum.inl 5305, 40130674560), (Sum.inl 5311, -160198120320)]

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

def originalBlock67 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 22459008000), (Sum.inl 2676, 35352758640), (Sum.inl 2677, 41502743040), (Sum.inl 2697, -10195068000), (Sum.inl 2708, 31531533120), (Sum.inl 2710, 18952239360), (Sum.inl 2719, -1269676800), (Sum.inl 2724, -198362880), (Sum.inl 2728, -144585806880), (Sum.inl 2729, -71129433600), (Sum.inl 2730, -4411204680), (Sum.inl 2731, 26557454640), (Sum.inl 2732, -257170321440), (Sum.inl 2747, -35781227520), (Sum.inl 2748, -90568526400), (Sum.inl 2750, 109742042880), (Sum.inl 2751, -30261856320), (Sum.inl 2753, -26688552960), (Sum.inl 2754, -145433555520), (Sum.inl 2755, -66991429440), (Sum.inl 2761, 7047137280), (Sum.inl 2769, -179535872640), (Sum.inl 2771, -28722546720), (Sum.inl 2773, -181490878800), (Sum.inl 2774, -61019927040), (Sum.inl 2775, 498528600), (Sum.inl 2776, -179224764720), (Sum.inl 2777, -261293431200), (Sum.inl 2778, -51294132000), (Sum.inl 3051, -38713886160), (Sum.inl 3074, 51869179200), (Sum.inl 4890, -267965717760), (Sum.inl 4899, -205176528000), (Sum.inl 5161, -5078707200), (Sum.inl 5175, 28188549120), (Sum.inl 5219, 89836032000), (Sum.inl 5231, 141411034560), (Sum.inl 5232, 166010972160), (Sum.inl 5243, -40780272000), (Sum.inl 5249, 126126132480), (Sum.inl 5251, 75808957440), (Sum.inl 5260, -793451520), (Sum.inl 5263, -578343227520), (Sum.inl 5264, -284517734400), (Sum.inl 5265, -17644818720), (Sum.inl 5266, 106229818560), (Sum.inl 5267, -1028681285760), (Sum.inl 5270, -581734222080), (Sum.inl 5276, -1045173724800), (Sum.inl 5278, -143124910080), (Sum.inl 5279, -362274105600), (Sum.inl 5281, 646444888320), (Sum.inl 5282, -121047425280), (Sum.inl 5284, -106754211840), (Sum.inl 5295, -718143490560), (Sum.inl 5297, -114890186880), (Sum.inl 5299, -880819059840), (Sum.inl 5300, -244079708160), (Sum.inl 5301, 1994114400), (Sum.inl 5302, -716899058880)]

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

def originalBlock68 : Integer.Sparse OriginalKey := [(Sum.inl 2161, 12247949280), (Sum.inl 2162, 28779193920), (Sum.inl 2163, 2785553280), (Sum.inl 2180, 2152584000), (Sum.inl 2220, 45154914240), (Sum.inl 2221, -64386633600), (Sum.inl 2222, -70512808320), (Sum.inl 2282, -8729926560), (Sum.inl 2283, 28430653200), (Sum.inl 2284, -35933301360), (Sum.inl 2285, -10946874240), (Sum.inl 2669, 41492083200), (Sum.inl 2670, -5614752000), (Sum.inl 2681, 30987058800), (Sum.inl 2682, -5186510400), (Sum.inl 2683, 3331916000), (Sum.inl 2700, -5864927880), (Sum.inl 2702, 27803192880), (Sum.inl 2718, -19789087680), (Sum.inl 2735, 131029924320), (Sum.inl 2736, 86974335360), (Sum.inl 2737, 32040920640), (Sum.inl 2738, 95785122320), (Sum.inl 2744, -108445633760), (Sum.inl 2760, -11068343040), (Sum.inl 2761, -34052750400), (Sum.inl 2763, -244351925760), (Sum.inl 2779, 27361002240), (Sum.inl 2780, -5820135840), (Sum.inl 2781, -202090914000), (Sum.inl 2789, -79879749600), (Sum.inl 4600, 111212771520), (Sum.inl 4611, 13327664000), (Sum.inl 4617, 128163682560), (Sum.inl 4626, -23280543360), (Sum.inl 4671, 48991797120), (Sum.inl 4687, 115116775680), (Sum.inl 4694, 11142213120), (Sum.inl 4702, 8610336000), (Sum.inl 4808, 180619656960), (Sum.inl 4819, -257546534400), (Sum.inl 4844, -282051233280), (Sum.inl 4872, -34919706240), (Sum.inl 4886, 113722612800), (Sum.inl 4892, -143733205440), (Sum.inl 4900, -43787496960), (Sum.inl 5140, -22459008000), (Sum.inl 5150, -23459711520), (Sum.inl 5151, 123948235200), (Sum.inl 5173, 524119697280), (Sum.inl 5175, -136211001600), (Sum.inl 5226, 165968332800), (Sum.inl 5236, -20746041600), (Sum.inl 5255, -79156350720), (Sum.inl 5269, 347897341440), (Sum.inl 5270, 383140489280), (Sum.inl 5276, -433782535040), (Sum.inl 5288, -44273372160), (Sum.inl 5289, -977407703040), (Sum.inl 5295, -808363656000), (Sum.inl 5303, 109444008960), (Sum.inl 5311, -319518998400)]

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

def originalBlock69 : Integer.Sparse OriginalKey := [(Sum.inl 2144, 13111545984), (Sum.inl 2154, -22251735600), (Sum.inl 2155, -30881651760), (Sum.inl 2160, 9309291840), (Sum.inl 2176, -34073200800), (Sum.inl 2179, 10174585920), (Sum.inl 2194, 13468067520), (Sum.inl 2195, 15186376800), (Sum.inl 2196, 90265586880), (Sum.inl 2211, 82874491680), (Sum.inl 2212, 90834899520), (Sum.inl 2213, -20093569560), (Sum.inl 2217, 37452674880), (Sum.inl 2219, 14458983120), (Sum.inl 2231, 13876855680), (Sum.inl 2232, -15890849280), (Sum.inl 2233, 31275884160), (Sum.inl 2234, 140375734080), (Sum.inl 2235, 71848187280), (Sum.inl 2248, -75491113920), (Sum.inl 2249, -59917721280), (Sum.inl 2250, 141650632560), (Sum.inl 2251, 94717871040), (Sum.inl 2252, 17611916400), (Sum.inl 2253, 127482366800), (Sum.inl 2254, 105727698240), (Sum.inl 2255, 41118433920), (Sum.inl 2272, 16489344000), (Sum.inl 2273, 40687487520), (Sum.inl 2274, 248886167040), (Sum.inl 2280, 127434411360), (Sum.inl 4665, 52446183936), (Sum.inl 4667, 37237167360), (Sum.inl 4668, -89006942400), (Sum.inl 4669, -123526607040), (Sum.inl 4695, 55507422720), (Sum.inl 4698, -301964455680), (Sum.inl 4700, -239670885120), (Sum.inl 4703, 65957376000), (Sum.inl 4704, 162749950080), (Sum.inl 4756, -136292803200), (Sum.inl 4765, 40698343680), (Sum.inl 4773, 53872270080), (Sum.inl 4775, 331497966720), (Sum.inl 4776, 363339598080), (Sum.inl 4793, 57835932480), (Sum.inl 4795, -80374278240), (Sum.inl 4803, 60745507200), (Sum.inl 4816, 361062347520), (Sum.inl 4821, 149810699520), (Sum.inl 4852, 566602530240), (Sum.inl 4856, 995544668160), (Sum.inl 4863, -63563397120), (Sum.inl 4867, 378871484160), (Sum.inl 4878, 561502936320), (Sum.inl 4880, 422910792960), (Sum.inl 4884, 509737645440), (Sum.inl 4885, 195551202240), (Sum.inl 4886, 287392749120), (Sum.inl 4891, 509929467200), (Sum.inl 4892, 164473735680)]

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

def originalBlock7 : Integer.Sparse OriginalKey := [(Sum.inl 5, 108778471200), (Sum.inl 6, 210023582400), (Sum.inl 261, 33515040000), (Sum.inl 384, 181259011200), (Sum.inl 385, -52580853600), (Sum.inl 405, -30311160000), (Sum.inl 409, 207173472000), (Sum.inl 410, -207173472000), (Sum.inl 412, -29255313600), (Sum.inl 420, 30311160000), (Sum.inl 462, 29731382400), (Sum.inl 468, -58510627200), (Sum.inl 484, 24456750000), (Sum.inl 485, 24456750000), (Sum.inl 486, 45930006000), (Sum.inl 487, 273525490000), (Sum.inl 489, 29731382400), (Sum.inl 490, -48421560000), (Sum.inl 491, 207173472000), (Sum.inl 495, -29255313600), (Sum.inl 496, 66238440000), (Sum.inl 498, -24456750000), (Sum.inl 500, -22965003000), (Sum.inl 501, -136762745000), (Sum.inl 503, -29731382400), (Sum.inl 506, -87185200800), (Sum.inl 507, 36869853600), (Sum.inr 3, -17816880000)]

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

def originalBlock70 : Integer.Sparse OriginalKey := [(Sum.inl 1528, -1027497360), (Sum.inl 1529, -3924651520), (Sum.inl 1530, -4758454560), (Sum.inl 1531, -646280640), (Sum.inl 1686, 20981767680), (Sum.inl 1687, -3210480000), (Sum.inl 1744, 18184504880), (Sum.inl 1745, -48398638560), (Sum.inl 1746, -25185862720), (Sum.inl 1747, -29704458240), (Sum.inl 2140, -22459008000), (Sum.inl 2147, -23975871120), (Sum.inl 2148, -41492083200), (Sum.inl 2149, -53975601840), (Sum.inl 2172, -17825395200), (Sum.inl 2189, -14236499520), (Sum.inl 2192, 65403264000), (Sum.inl 2198, -46727562960), (Sum.inl 2199, -14076578880), (Sum.inl 2200, -77691031680), (Sum.inl 2201, -3888915600), (Sum.inl 2207, -20547720000), (Sum.inl 2238, 31022502720), (Sum.inl 2239, -317340480), (Sum.inl 2240, -34636753920), (Sum.inl 2246, 387034596480), (Sum.inl 2256, -81358596480), (Sum.inl 2257, 9476558400), (Sum.inl 2258, -7593210720), (Sum.inl 2259, -26794424880), (Sum.inl 2267, 65283607200), (Sum.inl 2286, 37284743040), (Sum.inl 4157, -4109989440), (Sum.inl 4162, -15698606080), (Sum.inl 4184, -19033818240), (Sum.inl 4193, -2585122560), (Sum.inl 4353, 83927070720), (Sum.inl 4362, -12841920000), (Sum.inl 4442, 72738019520), (Sum.inl 4464, -193594554240), (Sum.inl 4478, -100743450880), (Sum.inl 4508, -118817832960), (Sum.inl 4532, -71301580800), (Sum.inl 4536, -215902407360), (Sum.inl 4552, -310764126720), (Sum.inl 4560, -30372842880), (Sum.inl 4663, -89836032000), (Sum.inl 4664, -95903484480), (Sum.inl 4666, -165968332800), (Sum.inl 4696, 124090010880), (Sum.inl 4697, -1269361920), (Sum.inl 4699, -325434385920), (Sum.inl 4701, 37906233600), (Sum.inl 4705, 149138972160), (Sum.inl 4771, -56945998080), (Sum.inl 4772, -186910251840), (Sum.inl 4774, -56306315520), (Sum.inl 4792, -15555662400), (Sum.inl 4815, 261613056000), (Sum.inl 4817, -82190880000), (Sum.inl 4851, -138547015680), (Sum.inl 4853, -107177699520), (Sum.inl 4879, 1548138385920), (Sum.inl 4881, 261134428800)]

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

def originalBlock71 : Integer.Sparse OriginalKey := [(Sum.inl 1667, 9755589600), (Sum.inl 1672, 14396377440), (Sum.inl 1678, 34751568000), (Sum.inl 1679, 36587845440), (Sum.inl 1684, 16067916960), (Sum.inl 1685, 24209954880), (Sum.inl 1697, 14621172480), (Sum.inl 1699, -17877500160), (Sum.inl 1703, 53361129600), (Sum.inl 1704, 15506176320), (Sum.inl 1709, -45802977600), (Sum.inl 1711, -126326566320), (Sum.inl 1712, -128076984960), (Sum.inl 1713, -21978605760), (Sum.inl 1714, -19642180080), (Sum.inl 1715, 36446353920), (Sum.inl 1722, 45650111040), (Sum.inl 1729, 60118089920), (Sum.inl 1734, -2541376080), (Sum.inl 1735, 61205507520), (Sum.inl 1736, 18377043840), (Sum.inl 1740, 59460313280), (Sum.inl 1742, 3168586560), (Sum.inl 1743, -229294560), (Sum.inl 1744, -32912653520), (Sum.inl 1745, -25204183200), (Sum.inl 1746, -69533421440), (Sum.inl 2164, -90318763200), (Sum.inl 2181, -56027260920), (Sum.inl 2223, 12093438960), (Sum.inl 4328, 39022358400), (Sum.inl 4330, 57585509760), (Sum.inl 4331, 64271667840), (Sum.inl 4332, 139006272000), (Sum.inl 4334, 146351381760), (Sum.inl 4336, 96839819520), (Sum.inl 4363, 58484689920), (Sum.inl 4364, 213444518400), (Sum.inl 4365, 62024705280), (Sum.inl 4366, -505306265280), (Sum.inl 4368, -512307939840), (Sum.inl 4370, 182600444160), (Sum.inl 4371, 12674346240), (Sum.inl 4372, -10165504320), (Sum.inl 4373, 244822030080), (Sum.inl 4375, -917178240), (Sum.inl 4439, -87914423040), (Sum.inl 4442, -131650614080), (Sum.inl 4444, 73508175360), (Sum.inl 4459, -78568720320), (Sum.inl 4464, -100816732800), (Sum.inl 4473, -71510000640), (Sum.inl 4474, -183211910400), (Sum.inl 4475, 145785415680), (Sum.inl 4476, 240472359680), (Sum.inl 4478, -278133685760), (Sum.inl 4480, 237841253120), (Sum.inl 4670, -361275052800), (Sum.inl 4757, -224109043680), (Sum.inl 4777, 48373755840)]

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

def originalBlock72 : Integer.Sparse OriginalKey := [(Sum.inl 1501, -11229504000), (Sum.inl 1504, -20746041600), (Sum.inl 1505, 19651632000), (Sum.inl 1510, -10159945920), (Sum.inl 1511, -16433028000), (Sum.inl 1514, 24670783920), (Sum.inl 1515, 36305572800), (Sum.inl 1516, 28493753680), (Sum.inl 1522, 28477512240), (Sum.inl 1523, 28138372240), (Sum.inl 1528, -2048698800), (Sum.inl 1529, -1135962080), (Sum.inl 1532, 13645038720), (Sum.inl 1533, 65612752640), (Sum.inl 1534, 2446403760), (Sum.inl 1540, 7954347360), (Sum.inl 1670, 25195671720), (Sum.inl 1688, 34694184720), (Sum.inl 1689, 55110368040), (Sum.inl 1695, 23602894080), (Sum.inl 1720, -40972413840), (Sum.inl 1721, 36844286400), (Sum.inl 1723, -77676135840), (Sum.inl 1748, 116784693840), (Sum.inl 1749, -19191440400), (Sum.inl 1757, -12603127200), (Sum.inl 2734, -27617621760), (Sum.inl 3089, 10138864800), (Sum.inl 3110, 68274009600), (Sum.inl 3112, 63950874000), (Sum.inl 3114, 13749933600), (Sum.inl 4149, -44918016000), (Sum.inl 4150, -82984166400), (Sum.inl 4151, 78606528000), (Sum.inl 4152, -40639783680), (Sum.inl 4153, 98683135680), (Sum.inl 4154, -65732112000), (Sum.inl 4155, 145222291200), (Sum.inl 4156, 113975014720), (Sum.inl 4157, -8194795200), (Sum.inl 4158, 113910048960), (Sum.inl 4159, 54580154880), (Sum.inl 4160, 112553488960), (Sum.inl 4161, 262451010560), (Sum.inl 4162, -4543848320), (Sum.inl 4163, 9785615040), (Sum.inl 4189, 31817389440), (Sum.inl 4327, 100782686880), (Sum.inl 4333, 138776738880), (Sum.inl 4335, 220441472160), (Sum.inl 4358, 94411576320), (Sum.inl 4367, -163889655360), (Sum.inl 4369, 147377145600), (Sum.inl 4374, 467138775360), (Sum.inl 4440, -310704543360), (Sum.inl 4445, -76765761600), (Sum.inl 4481, -50412508800), (Sum.inl 4897, 54999734400), (Sum.inl 5258, 40555459200), (Sum.inl 5268, -110470487040), (Sum.inl 5274, 255803496000), (Sum.inl 5275, 273096038400)]

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

def originalBlock73 : Integer.Sparse OriginalKey := [(Sum.inl 1, 126626353200), (Sum.inl 3, 284801434440), (Sum.inl 4, 709566437880), (Sum.inl 2753, 17250203520), (Sum.inl 2776, 94694929440), (Sum.inl 3037, -42708115440), (Sum.inl 3038, -31378885680), (Sum.inl 3039, -121147853760), (Sum.inl 3051, 13639726320), (Sum.inl 3052, 7161813520), (Sum.inl 3055, -4546412160), (Sum.inl 3064, -3525346560), (Sum.inl 3065, 14341033920), (Sum.inl 3074, 49078791360), (Sum.inl 3075, 4332624480), (Sum.inl 3078, -2610481920), (Sum.inl 3087, -47280171000), (Sum.inl 3088, -16312046640), (Sum.inl 3099, -67065433960), (Sum.inl 3103, 20512214240), (Sum.inl 3109, 27036763920), (Sum.inl 3111, 68642441640), (Sum.inl 3112, 179046816960), (Sum.inl 3119, 10132584400), (Sum.inl 3847, -39662974560), (Sum.inl 3856, -82568679560), (Sum.inl 3883, 17100179040), (Sum.inl 3977, 8053488080), (Sum.inl 3996, 160753153040), (Sum.inl 4006, -29606574240), (Sum.inl 4035, -118232166400), (Sum.inl 4084, 506505412800), (Sum.inl 4091, 1139205737760), (Sum.inl 4092, 2838265751520), (Sum.inl 5250, 57364135680), (Sum.inl 5251, -14101386240), (Sum.inl 5257, -189120684000), (Sum.inl 5259, -65248186560), (Sum.inl 5265, -170832461760), (Sum.inl 5266, -484591415040), (Sum.inl 5267, -125515542720), (Sum.inl 5270, 17330497920), (Sum.inl 5271, 108147055680), (Sum.inl 5273, 274569766560), (Sum.inl 5274, 716187267840), (Sum.inl 5276, 28647254080), (Sum.inl 5281, 196315165440), (Sum.inl 5282, -10441927680), (Sum.inl 5284, 69000814080), (Sum.inl 5290, -268261735840), (Sum.inl 5291, 82048856960), (Sum.inl 5299, 54558905280), (Sum.inl 5300, -18185648640), (Sum.inl 5302, 378779717760), (Sum.inl 5304, 40530337600), (Sum.inl 5405, 32213952320), (Sum.inl 5406, -158651898240), (Sum.inl 5409, -472928665600), (Sum.inl 5410, 643012612160), (Sum.inl 5411, 68400716160), (Sum.inl 5412, -330274718240), (Sum.inl 5413, -118426296960)]

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

def originalBlock74 : Integer.Sparse OriginalKey := [(Sum.inl 2710, -10938011520), (Sum.inl 2724, -6312192000), (Sum.inl 2732, -77627280960), (Sum.inl 2744, -45145603680), (Sum.inl 3089, -144898064640), (Sum.inl 3103, -34148752320), (Sum.inl 3230, 22604714640), (Sum.inl 3526, -16009994800), (Sum.inl 3541, 2851571760), (Sum.inl 3573, 40053479760), (Sum.inl 3839, 48009824800), (Sum.inl 3841, -33567760200), (Sum.inl 3847, -49374989440), (Sum.inl 3872, -156245208240), (Sum.inl 3877, 57340892880), (Sum.inl 3954, -2890879280), (Sum.inl 3972, -35794478480), (Sum.inl 3990, -45952289840), (Sum.inl 3993, 157674448800), (Sum.inl 4003, 120897845280), (Sum.inl 4026, -277488378480), (Sum.inl 4027, -114090427360), (Sum.inl 4030, 97266550160), (Sum.inl 4032, -201403157520), (Sum.inl 4034, 48045374040), (Sum.inl 4035, -246620576520), (Sum.inl 4038, -65205723240), (Sum.inl 4894, 90418858560), (Sum.inl 5251, -43752046080), (Sum.inl 5258, -579592258560), (Sum.inl 5260, -25248768000), (Sum.inl 5265, -64039979200), (Sum.inl 5267, -299102836800), (Sum.inl 5276, -180582414720), (Sum.inl 5291, -136595009280), (Sum.inl 5299, 160213919040), (Sum.inl 5406, -197499957760), (Sum.inl 5408, -260822892960), (Sum.inl 5409, -986482306080), (Sum.inl 5423, -805612630080), (Sum.inl 5424, -183809159360), (Sum.inl 5425, -432941533760), (Sum.inl 5426, -134271040800), (Sum.inl 5427, 192181496160), (Sum.inl 5428, 483591381120), (Sum.inl 5429, -11563517120), (Sum.inl 5430, -143177913920), (Sum.inl 5431, -1109953513920), (Sum.inl 5432, -456361709440), (Sum.inl 5436, 229363571520), (Sum.inl 5438, 630697795200), (Sum.inl 5449, 389066200640)]

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

def originalBlock75 : Integer.Sparse OriginalKey := [(Sum.inl 2751, -32732670720), (Sum.inl 2773, 53989962240), (Sum.inl 2774, -90645302880), (Sum.inl 3109, 163572001920), (Sum.inl 3110, -92871236160), (Sum.inl 3229, 171064210560), (Sum.inl 3231, -19248180720), (Sum.inl 3526, 15404358800), (Sum.inl 3535, 41633775200), (Sum.inl 3541, 62008066480), (Sum.inl 3549, -10586607200), (Sum.inl 3584, -49540614480), (Sum.inl 3846, -140805663200), (Sum.inl 3854, -49077475480), (Sum.inl 3871, 59984395200), (Sum.inl 3881, -256088763600), (Sum.inl 3959, -241843442320), (Sum.inl 3976, -144865072880), (Sum.inl 3990, 114245799840), (Sum.inl 3995, 211191723280), (Sum.inl 3996, 26302040160), (Sum.inl 4002, -159417459120), (Sum.inl 4003, -13262269160), (Sum.inl 4004, 277437109200), (Sum.inl 4005, -17377408080), (Sum.inl 4006, -204446844240), (Sum.inl 4024, 134291832480), (Sum.inl 4028, -124444539240), (Sum.inl 4895, 684256842240), (Sum.inl 4901, -76992722880), (Sum.inl 5265, 61617435200), (Sum.inl 5266, 166535100800), (Sum.inl 5267, 248032265920), (Sum.inl 5268, -42346428800), (Sum.inl 5271, 654288007680), (Sum.inl 5275, -371484944640), (Sum.inl 5282, -130930682880), (Sum.inl 5299, 215959848960), (Sum.inl 5300, -560743669440), (Sum.inl 5410, 105208160640), (Sum.inl 5413, -817787376960), (Sum.inl 5424, 456983199360), (Sum.inl 5428, -53049076640), (Sum.inl 5429, -563222652800), (Sum.inl 5430, 239937580800), (Sum.inl 5436, -196309901920), (Sum.inl 5445, 537167329920), (Sum.inl 5446, -1991728823680), (Sum.inl 5448, -497778156960), (Sum.inl 5471, -579460291520), (Sum.inl 5472, -637669836480), (Sum.inl 5473, 844766893120), (Sum.inl 5474, -69509632320), (Sum.inl 5475, 1109748436800)]

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

def originalBlock76 : Integer.Sparse OriginalKey := [(Sum.inl 2708, 26420478720), (Sum.inl 2728, 32751053760), (Sum.inl 2729, 75397542720), (Sum.inl 2735, -41795249280), (Sum.inl 2750, 39902572800), (Sum.inl 2763, -170220652800), (Sum.inl 2781, -104137225920), (Sum.inl 3085, -170767914240), (Sum.inl 3086, 128688370560), (Sum.inl 3097, -138298757760), (Sum.inl 3119, 145494670080), (Sum.inl 3225, 5158261120), (Sum.inl 3227, -50386334880), (Sum.inl 3540, 7336967200), (Sum.inl 3572, -143659440000), (Sum.inl 3834, 11700642624), (Sum.inl 3840, -74677500000), (Sum.inl 3848, -68900767200), (Sum.inl 3866, 88699461120), (Sum.inl 3871, 36378677920), (Sum.inl 3872, -213667645200), (Sum.inl 3880, -92685692160), (Sum.inl 3881, -251085086160), (Sum.inl 3882, 19932687520), (Sum.inl 3883, 142548077280), (Sum.inl 3972, 156207899520), (Sum.inl 3976, -11069268480), (Sum.inl 3977, -9318353280), (Sum.inl 3978, -173815992000), (Sum.inl 3993, 4560264960), (Sum.inl 3994, 277266644640), (Sum.inl 3997, 24549885760), (Sum.inl 4888, -201545339520), (Sum.inl 4896, 20633044480), (Sum.inl 5173, -167180997120), (Sum.inl 5249, 105681914880), (Sum.inl 5256, -683071656960), (Sum.inl 5260, 544101351040), (Sum.inl 5263, 131004215040), (Sum.inl 5264, 301590170880), (Sum.inl 5281, 159610291200), (Sum.inl 5289, -1808715402240), (Sum.inl 5295, -416548903680), (Sum.inl 5304, 581978680320), (Sum.inl 5381, 46802570496), (Sum.inl 5382, 354797844480), (Sum.inl 5405, -37273413120), (Sum.inl 5411, 570192309120), (Sum.inl 5425, -1153380580800), (Sum.inl 5430, 494743240960), (Sum.inl 5438, 18241059840), (Sum.inl 5445, -370742768640), (Sum.inl 5446, -1004340344640), (Sum.inl 5447, 79730750080), (Sum.inl 5471, -44277073920), (Sum.inl 5478, 1109066578560), (Sum.inl 5480, -695263968000), (Sum.inl 5484, 98199543040)]

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

def originalBlock77 : Integer.Sparse OriginalKey := [(Sum.inl 2718, 90415507200), (Sum.inl 2719, 6312192000), (Sum.inl 2736, 39902572800), (Sum.inl 2737, -37074625440), (Sum.inl 3098, -35817134400), (Sum.inl 3289, -1174422320), (Sum.inl 3294, 1800137360), (Sum.inl 3296, -28075223520), (Sum.inl 3303, -15029351280), (Sum.inl 3306, -4970178000), (Sum.inl 3517, 80569291200), (Sum.inl 3557, -31543610640), (Sum.inl 3558, 231346835120), (Sum.inl 3565, 17151888960), (Sum.inl 3571, 71754163680), (Sum.inl 3572, -333860876800), (Sum.inl 3573, -73256630440), (Sum.inl 3584, 57327463280), (Sum.inl 3832, -20456109360), (Sum.inl 3842, 40201116000), (Sum.inl 3868, 90525826320), (Sum.inl 3869, -15685334800), (Sum.inl 3874, 56990279280), (Sum.inl 3877, 251942575840), (Sum.inl 3884, 101673310000), (Sum.inl 3954, -25002267840), (Sum.inl 3955, -96987695040), (Sum.inl 3959, -222331042080), (Sum.inl 3973, 96987695040), (Sum.inl 3978, -222656215200), (Sum.inl 4599, -4697689280), (Sum.inl 4603, 7200549440), (Sum.inl 4607, -112300894080), (Sum.inl 4616, -60117405120), (Sum.inl 4617, -148298501760), (Sum.inl 4620, -19880712000), (Sum.inl 5138, 322277164800), (Sum.inl 5144, -126174442560), (Sum.inl 5160, 925387340480), (Sum.inl 5161, 25248768000), (Sum.inl 5164, 68607555840), (Sum.inl 5255, 361662028800), (Sum.inl 5269, 159610291200), (Sum.inl 5281, 287016654720), (Sum.inl 5289, -1335443507200), (Sum.inl 5295, -143268537600), (Sum.inl 5299, -293026521760), (Sum.inl 5300, 229309853120), (Sum.inl 5379, -81824437440), (Sum.inl 5385, 362103305280), (Sum.inl 5414, -62741339200), (Sum.inl 5419, 160804464000), (Sum.inl 5429, 127952045760), (Sum.inl 5436, 1007770303360), (Sum.inl 5446, -482630928320), (Sum.inl 5461, 387950780160), (Sum.inl 5470, -387950780160), (Sum.inl 5480, -890624860800)]

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

def originalBlock78 : Integer.Sparse OriginalKey := [(Sum.inl 2664, 23608051200), (Sum.inl 2676, 12391456080), (Sum.inl 2677, 20479536000), (Sum.inl 2678, 97890662400), (Sum.inl 2680, 8725170240), (Sum.inl 2697, -28582650720), (Sum.inl 2698, -28844880000), (Sum.inl 2730, -65612324040), (Sum.inl 2731, 73703074320), (Sum.inl 2732, -102848410080), (Sum.inl 2734, -149969145600), (Sum.inl 2773, -416271120), (Sum.inl 2774, -88321265280), (Sum.inl 2775, -15470073480), (Sum.inl 2776, -14079306480), (Sum.inl 2778, -3120878880), (Sum.inl 3039, -158264635200), (Sum.inl 3225, 44975981600), (Sum.inl 3302, 2014495680), (Sum.inl 3523, -65633791200), (Sum.inl 3524, 5916834080), (Sum.inl 3529, 22988392800), (Sum.inl 3530, 61881626560), (Sum.inl 3537, 63279700800), (Sum.inl 3538, 31159570480), (Sum.inl 3542, -29434869600), (Sum.inl 3562, 63243540000), (Sum.inl 3565, 133109377360), (Sum.inl 3580, 2581495960), (Sum.inl 3881, -151040588880), (Sum.inl 3883, 172581972960), (Sum.inl 3960, 173815992000), (Sum.inl 4609, 8057982720), (Sum.inl 4896, 179903926400), (Sum.inl 4899, -12483515520), (Sum.inl 5139, -262535164800), (Sum.inl 5145, 252974160000), (Sum.inl 5147, 247526506240), (Sum.inl 5164, 532437509440), (Sum.inl 5184, 23667336320), (Sum.inl 5185, 91953571200), (Sum.inl 5187, 253118803200), (Sum.inl 5188, 124638281920), (Sum.inl 5189, -117739478400), (Sum.inl 5222, 94432204800), (Sum.inl 5231, 49565824320), (Sum.inl 5232, 81918144000), (Sum.inl 5233, 391562649600), (Sum.inl 5235, 34900680960), (Sum.inl 5243, -114330602880), (Sum.inl 5244, -115379520000), (Sum.inl 5265, -262449296160), (Sum.inl 5266, -338246243520), (Sum.inl 5267, -411393640320), (Sum.inl 5268, -599876582400), (Sum.inl 5282, 10325983840), (Sum.inl 5299, -1665084480), (Sum.inl 5300, -353285061120), (Sum.inl 5301, -61880293920), (Sum.inl 5302, -56317225920), (Sum.inl 5411, 690327891840), (Sum.inl 5446, -604162355520), (Sum.inl 5463, 695263968000)]

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

def originalBlock79 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 39516772800), (Sum.inl 2662, -40363279680), (Sum.inl 2673, 84249384000), (Sum.inl 2677, 35303490240), (Sum.inl 2678, -64673782080), (Sum.inl 2687, 72946361760), (Sum.inl 3038, 167739810240), (Sum.inl 3055, 118038269760), (Sum.inl 3223, 73844861120), (Sum.inl 3224, 93928209840), (Sum.inl 3524, -17400605280), (Sum.inl 3538, 4171087840), (Sum.inl 3570, 176570546880), (Sum.inl 3832, 10849510160), (Sum.inl 3833, 1828358280), (Sum.inl 3834, 156783781296), (Sum.inl 3840, 61332817120), (Sum.inl 3841, 97921657320), (Sum.inl 3854, 248493837600), (Sum.inl 3855, -100814408880), (Sum.inl 3856, 40021870200), (Sum.inl 3870, -55902749040), (Sum.inl 3871, 52916319280), (Sum.inl 3872, 31184084640), (Sum.inl 3873, -118378819600), (Sum.inl 3874, 74745834480), (Sum.inl 3877, 76682450400), (Sum.inl 3880, -82919052640), (Sum.inl 3882, -55872858880), (Sum.inl 3884, -18685629280), (Sum.inl 4889, 295379444480), (Sum.inl 4898, 375712839360), (Sum.inl 5184, -69602421120), (Sum.inl 5188, 16684351360), (Sum.inl 5198, 706282187520), (Sum.inl 5206, 291785447040), (Sum.inl 5219, 158067091200), (Sum.inl 5220, -161453118720), (Sum.inl 5229, 336997536000), (Sum.inl 5232, 141213960960), (Sum.inl 5233, -258695128320), (Sum.inl 5267, 670959240960), (Sum.inl 5300, 472153079040), (Sum.inl 5376, 7313433120), (Sum.inl 5379, 43398040640), (Sum.inl 5381, 627135125184), (Sum.inl 5412, 160087480800), (Sum.inl 5420, -223610996160), (Sum.inl 5421, -473515278400), (Sum.inl 5425, 370067607040), (Sum.inl 5426, 391686629280), (Sum.inl 5429, 298983337920), (Sum.inl 5430, 211665277120), (Sum.inl 5436, 1300705152000), (Sum.inl 5437, -403257635520), (Sum.inl 5445, -331676210560), (Sum.inl 5446, -74742517120), (Sum.inl 5447, -223491435520)]

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

def originalBlock8 : Integer.Sparse OriginalKey := [(Sum.inl 145, 98635539000), (Sum.inl 150, 155482908000), (Sum.inl 268, -49167224000), (Sum.inl 272, -21034456800), (Sum.inl 381, -23808436800), (Sum.inl 387, -41785320000), (Sum.inl 409, 145777817000), (Sum.inl 410, 23808436800), (Sum.inl 443, -51147672000), (Sum.inl 444, -113032272000), (Sum.inl 467, 21978144200), (Sum.inl 469, -101235026600), (Sum.inl 479, 49159200000), (Sum.inl 480, -195966264000), (Sum.inl 483, 87617129000), (Sum.inl 485, 24456750000), (Sum.inl 489, -4915920000), (Sum.inl 491, 6711290400), (Sum.inl 496, -17816880000), (Sum.inl 498, 109131048000), (Sum.inl 499, 30620004000), (Sum.inl 504, -21593270400), (Sum.inl 512, 24456750000), (Sum.inl 513, 22965003000), (Sum.inl 514, -24456750000), (Sum.inl 515, -22965003000), (Sum.inl 516, -54565524000), (Sum.inl 521, -4915920000), (Sum.inr 4, 4915920000)]

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

def originalBlock80 : Integer.Sparse OriginalKey := [(Sum.inl 2145, 19866199680), (Sum.inl 2146, -27682830720), (Sum.inl 2196, 20597398080), (Sum.inl 2197, 98777203200), (Sum.inl 2250, 28063444320), (Sum.inl 2251, 72601052160), (Sum.inl 2253, 107266045360), (Sum.inl 2255, 36502799040), (Sum.inl 2670, -114367811520), (Sum.inl 2676, 10651267200), (Sum.inl 2681, -70259291520), (Sum.inl 2682, -65159040000), (Sum.inl 2683, -79936891680), (Sum.inl 3037, 31541459520), (Sum.inl 3051, 122991876480), (Sum.inl 3052, 44837716800), (Sum.inl 3288, -4824040720), (Sum.inl 3295, -75840805840), (Sum.inl 3296, -220655614320), (Sum.inl 3516, 14680974880), (Sum.inl 3517, -33392949200), (Sum.inl 3539, 32205942360), (Sum.inl 3540, 78936544320), (Sum.inl 3541, 103267498800), (Sum.inl 3557, 31886642880), (Sum.inl 3835, 35162608800), (Sum.inl 3839, 148491963360), (Sum.inl 3842, -19207074240), (Sum.inl 3846, -49852232640), (Sum.inl 3847, -44657792160), (Sum.inl 3848, -26523501600), (Sum.inl 4589, -19296162880), (Sum.inl 4592, -303363223360), (Sum.inl 4607, -882622457280), (Sum.inl 4611, -319747566720), (Sum.inl 4680, 79464798720), (Sum.inl 4683, -110731322880), (Sum.inl 4816, 82389592320), (Sum.inl 4836, 395108812800), (Sum.inl 4852, 112253777280), (Sum.inl 4867, 290404208640), (Sum.inl 4891, 429064181440), (Sum.inl 4892, 146011196160), (Sum.inl 5129, 58723899520), (Sum.inl 5138, -133571796800), (Sum.inl 5140, -457471246080), (Sum.inl 5144, 127546571520), (Sum.inl 5151, -281037166080), (Sum.inl 5231, 42605068800), (Sum.inl 5236, -260636160000), (Sum.inl 5251, 128823769440), (Sum.inl 5260, 315746177280), (Sum.inl 5265, 126165838080), (Sum.inl 5267, 413069995200), (Sum.inl 5276, 179350867200), (Sum.inl 5299, 491967505920), (Sum.inl 5377, 140650435200), (Sum.inl 5406, -178631168640), (Sum.inl 5419, -76828296960), (Sum.inl 5425, 593967853440), (Sum.inl 5429, -199408930560), (Sum.inl 5430, -106094006400)]

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

def originalBlock81 : Integer.Sparse OriginalKey := [(Sum.inl 1511, -59653416480), (Sum.inl 1512, -48167756160), (Sum.inl 1513, 21474181440), (Sum.inl 1715, -93282494400), (Sum.inl 1716, 51191942400), (Sum.inl 2144, 19706327616), (Sum.inl 2171, -23608051200), (Sum.inl 2195, 45458951520), (Sum.inl 2252, 21803022720), (Sum.inl 2652, 108902126400), (Sum.inl 2653, -77090685120), (Sum.inl 2654, -1583273280), (Sum.inl 2655, 11023403520), (Sum.inl 2656, 65159040000), (Sum.inl 2657, 97278520320), (Sum.inl 2659, -112133076480), (Sum.inl 3016, -120295503360), (Sum.inl 3023, -154533336000), (Sum.inl 3024, 45165883200), (Sum.inl 3025, -97221541440), (Sum.inl 3221, -58291364928), (Sum.inl 3222, 27397679520), (Sum.inl 3258, 1965872184), (Sum.inl 3259, 243375339360), (Sum.inl 3463, -84480861360), (Sum.inl 3464, 22389196080), (Sum.inl 3509, 111263016744), (Sum.inl 3553, -30136375440), (Sum.inl 3761, -55422491760), (Sum.inl 3762, -57918681480), (Sum.inl 3802, -146618106000), (Sum.inl 3803, -249815111640), (Sum.inl 4154, -238613665920), (Sum.inl 4176, -192671024640), (Sum.inl 4179, 85896725760), (Sum.inl 4475, -373129977600), (Sum.inl 4500, 204767769600), (Sum.inl 4529, 7863488736), (Sum.inl 4545, 973501357440), (Sum.inl 4548, 389114081280), (Sum.inl 4665, 78825310464), (Sum.inl 4762, -94432204800), (Sum.inl 4803, 181835806080), (Sum.inl 4885, -145953368832), (Sum.inl 4891, 109590718080), (Sum.inl 4957, 445052066976), (Sum.inl 4963, -120545501760), (Sum.inl 4976, -448532305920), (Sum.inl 5035, 435608505600), (Sum.inl 5074, -337923445440), (Sum.inl 5086, 89556784320), (Sum.inl 5103, 180663532800), (Sum.inl 5116, 44093614080), (Sum.inl 5215, -308362740480), (Sum.inl 5216, -6333093120), (Sum.inl 5217, 260636160000), (Sum.inl 5254, -481182013440), (Sum.inl 5286, -618133344000), (Sum.inl 5287, -388886165760), (Sum.inl 5353, -221689967040), (Sum.inl 5360, -231674725920), (Sum.inl 5402, -586472424000), (Sum.inl 5407, -999260446560)]

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

def originalBlock82 : Integer.Sparse OriginalKey := [(Sum.inl 1510, -48604387680), (Sum.inl 1526, 86048565120), (Sum.inl 1667, -38744668320), (Sum.inl 1668, -29289765120), (Sum.inl 1713, -67829291760), (Sum.inl 1714, -145887997200), (Sum.inl 1740, 60804089920), (Sum.inl 2154, 33301422000), (Sum.inl 2158, -52044372480), (Sum.inl 2178, -70282894080), (Sum.inl 2213, 15724160040), (Sum.inl 2217, 124850719680), (Sum.inl 2274, 68215020240), (Sum.inl 2658, -846506880), (Sum.inl 3267, 4696238880), (Sum.inl 3271, -54920555760), (Sum.inl 3406, 8541086400), (Sum.inl 3407, 88892606880), (Sum.inl 3454, 154383516080), (Sum.inl 3476, 47107195560), (Sum.inl 3480, -41524809400), (Sum.inl 3508, -33321692640), (Sum.inl 3555, -152669552880), (Sum.inl 3556, -43730807040), (Sum.inl 3755, 23524214800), (Sum.inl 3759, -59248431360), (Sum.inl 3760, 206772988320), (Sum.inl 3761, -13199134080), (Sum.inl 3762, -34643013720), (Sum.inl 3763, 19207074240), (Sum.inl 3768, -16741642320), (Sum.inl 3772, -38735335280), (Sum.inl 4152, -194417550720), (Sum.inl 4188, 344194260480), (Sum.inl 4328, -154978673280), (Sum.inl 4345, -117159060480), (Sum.inl 4439, -271317167040), (Sum.inl 4459, -583551988800), (Sum.inl 4480, 243216359680), (Sum.inl 4533, 18784955520), (Sum.inl 4556, -219682223040), (Sum.inl 4668, 133205688000), (Sum.inl 4690, -208177489920), (Sum.inl 4768, -281131576320), (Sum.inl 4795, 62896640160), (Sum.inl 4821, 499402878720), (Sum.inl 4856, 272860080960), (Sum.inl 4931, 34164345600), (Sum.inl 4942, 355570427520), (Sum.inl 4945, -3386027520), (Sum.inl 4955, -133286770560), (Sum.inl 4966, -610678211520), (Sum.inl 5040, 617534064320), (Sum.inl 5067, 188428782240), (Sum.inl 5090, -166099237600), (Sum.inl 5112, -174923228160), (Sum.inl 5338, 94096859200), (Sum.inl 5339, 827091953280), (Sum.inl 5340, 76828296960), (Sum.inl 5348, -66966569280), (Sum.inl 5353, -52796536320), (Sum.inl 5359, -236993725440), (Sum.inl 5360, -138572054880), (Sum.inl 5361, -154941341120)]

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

def originalBlock83 : Integer.Sparse OriginalKey := [(Sum.inl 1522, 8689273200), (Sum.inl 1523, 24440506640), (Sum.inl 1678, 39641370240), (Sum.inl 1679, 75158508480), (Sum.inl 1682, 116686987200), (Sum.inl 1736, 46987459440), (Sum.inl 2155, 25571060400), (Sum.inl 2176, 6448516320), (Sum.inl 2681, 31168829520), (Sum.inl 2687, 249303360), (Sum.inl 2700, -6115859880), (Sum.inl 2706, 54421821120), (Sum.inl 2738, 57815945440), (Sum.inl 2744, 37314069920), (Sum.inl 2781, 4912046640), (Sum.inl 3268, -54421667240), (Sum.inl 3414, 8356094400), (Sum.inl 3415, -7644434160), (Sum.inl 3418, -9428064960), (Sum.inl 3452, 65164959920), (Sum.inl 3508, -4466670560), (Sum.inl 3509, 85165226856), (Sum.inl 3510, -28301606400), (Sum.inl 3511, -5759404800), (Sum.inl 3512, -83506716880), (Sum.inl 3557, 23588739440), (Sum.inl 3569, -29135184640), (Sum.inl 3570, -111901383360), (Sum.inl 3571, 85300658880), (Sum.inl 3572, -28910416160), (Sum.inl 3573, -2349687640), (Sum.inl 3584, -7881846960), (Sum.inl 4158, 34757092800), (Sum.inl 4160, 97762026560), (Sum.inl 4332, 158565480960), (Sum.inl 4334, 300634033920), (Sum.inl 4357, 466747948800), (Sum.inl 4444, 187949837760), (Sum.inl 4534, -217686668960), (Sum.inl 4669, 102284241600), (Sum.inl 4756, 25794065280), (Sum.inl 4933, 33424377600), (Sum.inl 4934, -30577736640), (Sum.inl 4951, -37712259840), (Sum.inl 4954, 260659839680), (Sum.inl 4955, -17866682240), (Sum.inl 4956, -113206425600), (Sum.inl 4957, 340660907424), (Sum.inl 4958, -23037619200), (Sum.inl 4959, -334026867520), (Sum.inl 5144, 94354957760), (Sum.inl 5150, -24463439520), (Sum.inl 5151, 124675318080), (Sum.inl 5197, -116540738560), (Sum.inl 5198, -447605533440), (Sum.inl 5205, 217687284480), (Sum.inl 5206, 997213440), (Sum.inl 5270, 231263781760), (Sum.inl 5276, 149256279680), (Sum.inl 5281, 341202635520), (Sum.inl 5289, -115641664640), (Sum.inl 5295, 19648186560), (Sum.inl 5299, -9398750560), (Sum.inl 5300, -31527387840)]

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

def originalBlock84 : Integer.Sparse OriginalKey := [(Sum.inl 2147, -13241985360), (Sum.inl 2153, -135136641600), (Sum.inl 2175, -66152373120), (Sum.inl 2201, -21855207840), (Sum.inl 2207, -8039874240), (Sum.inl 2259, -32556736560), (Sum.inl 3291, 25338206080), (Sum.inl 3302, -50478153360), (Sum.inl 3462, -63013829520), (Sum.inl 3463, 2985990720), (Sum.inl 3464, 58899945120), (Sum.inl 3480, -84110226760), (Sum.inl 3516, 17682887520), (Sum.inl 3519, -13314241320), (Sum.inl 3523, -212802172000), (Sum.inl 3524, -17029644480), (Sum.inl 3526, -24528769920), (Sum.inl 3530, 112442722560), (Sum.inl 3535, 15275984160), (Sum.inl 3537, 55271146720), (Sum.inl 3538, -2034772080), (Sum.inl 3539, 48308224200), (Sum.inl 3540, -67165112880), (Sum.inl 3541, -25307791360), (Sum.inl 3542, 19207074240), (Sum.inl 3543, -57578695560), (Sum.inl 3549, -17194545400), (Sum.inl 3562, 16155720480), (Sum.inl 3578, 295124194240), (Sum.inl 3579, 120925828800), (Sum.inl 3580, 18758213000), (Sum.inl 4591, 101352824320), (Sum.inl 4609, -201912613440), (Sum.inl 4664, -52967941440), (Sum.inl 4682, -540546566400), (Sum.inl 4761, -264609492480), (Sum.inl 4792, -87420831360), (Sum.inl 4817, -32159496960), (Sum.inl 4853, -130226946240), (Sum.inl 5042, -252055318080), (Sum.inl 5074, 11943962880), (Sum.inl 5086, 235599780480), (Sum.inl 5090, -336440907040), (Sum.inl 5128, -53256965280), (Sum.inl 5129, 70731550080), (Sum.inl 5139, -851208688000), (Sum.inl 5145, 64622881920), (Sum.inl 5147, 449770890240), (Sum.inl 5184, -68118577920), (Sum.inl 5187, 221084586880), (Sum.inl 5188, -8139088320), (Sum.inl 5189, 76828296960), (Sum.inl 5199, 1180496776960), (Sum.inl 5201, 483703315200), (Sum.inl 5251, 193232896800), (Sum.inl 5252, -230314782240), (Sum.inl 5260, -268660451520), (Sum.inl 5265, -98115079680), (Sum.inl 5266, 61103936640), (Sum.inl 5267, -101231165440), (Sum.inl 5268, -68778181600), (Sum.inl 5282, 75032852000)]

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

def originalBlock85 : Integer.Sparse OriginalKey := [(Sum.inl 1514, -17253001680), (Sum.inl 1520, 83076659520), (Sum.inl 1533, 33430043680), (Sum.inl 1670, -44732773560), (Sum.inl 1676, 11730552000), (Sum.inl 1689, 42334134120), (Sum.inl 1723, -50180808480), (Sum.inl 1729, 39601068160), (Sum.inl 2164, -18203620320), (Sum.inl 2181, -9899351640), (Sum.inl 2683, 4532419840), (Sum.inl 2702, 17425550160), (Sum.inl 3260, 41470746960), (Sum.inl 3266, 102678513360), (Sum.inl 3272, -13949930640), (Sum.inl 3406, 8815051200), (Sum.inl 3408, -52770777840), (Sum.inl 3413, -79464541920), (Sum.inl 3414, 1090620480), (Sum.inl 3415, -33818861040), (Sum.inl 3419, 21662031480), (Sum.inl 3451, 19791401920), (Sum.inl 3452, 61981314480), (Sum.inl 3458, 617189760), (Sum.inl 3461, 59248431360), (Sum.inl 3465, -19207074240), (Sum.inl 3466, -96553292760), (Sum.inl 3472, 13467990040), (Sum.inl 3474, -48784844320), (Sum.inl 3475, -123152322240), (Sum.inl 3476, 2248083000), (Sum.inl 4153, -69012006720), (Sum.inl 4161, 133720174720), (Sum.inl 4178, 332306638080), (Sum.inl 4327, -178931094240), (Sum.inl 4335, 169336536480), (Sum.inl 4347, 46922208000), (Sum.inl 4440, -200723233920), (Sum.inl 4476, 158404272640), (Sum.inl 4528, 165882987840), (Sum.inl 4535, -55799722560), (Sum.inl 4547, 410714053440), (Sum.inl 4600, 69702200640), (Sum.inl 4611, 18129679360), (Sum.inl 4670, -72814481280), (Sum.inl 4757, -39597406560), (Sum.inl 4930, -211083111360), (Sum.inl 4931, 35260204800), (Sum.inl 4933, 4362481920), (Sum.inl 4934, -135275444160), (Sum.inl 4935, 86648125920), (Sum.inl 4944, -317858167680), (Sum.inl 4954, 247925257920), (Sum.inl 4965, -492609288960), (Sum.inl 5034, 79165607680), (Sum.inl 5041, 2468759040), (Sum.inl 5043, -76828296960), (Sum.inl 5044, -195139377280), (Sum.inl 5065, -386213171040), (Sum.inl 5067, 8992332000), (Sum.inl 5085, 236993725440), (Sum.inl 5087, 53871960160)]

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

def originalBlock86 : Integer.Sparse OriginalKey := [(Sum.inl 1516, 12229556240), (Sum.inl 1672, -30751249440), (Sum.inl 2149, -39808563600), (Sum.inl 2172, -11048475840), (Sum.inl 2661, 5614752000), (Sum.inl 2662, 37829664000), (Sum.inl 2710, -1563432960), (Sum.inl 2724, -14164588800), (Sum.inl 2751, -37829664000), (Sum.inl 2753, -4411061760), (Sum.inl 2755, 34567384320), (Sum.inl 2763, 15559531200), (Sum.inl 3255, 28301606400), (Sum.inl 3258, -42685139784), (Sum.inl 3260, -10038288560), (Sum.inl 3261, 5759404800), (Sum.inl 3262, 52615829600), (Sum.inl 3267, -3263229280), (Sum.inl 3268, -4183807880), (Sum.inl 3272, -12420556560), (Sum.inl 3288, 9395255120), (Sum.inl 3289, 30723827920), (Sum.inl 3290, 15773304000), (Sum.inl 3291, -54640951680), (Sum.inl 3294, -40891467760), (Sum.inl 3295, -24878305840), (Sum.inl 3296, -4749425680), (Sum.inl 3297, -32053738400), (Sum.inl 3298, 20010395440), (Sum.inl 3302, 11529636880), (Sum.inl 4156, 48918224960), (Sum.inl 4330, -123004997760), (Sum.inl 4527, 113206425600), (Sum.inl 4528, -40153154240), (Sum.inl 4529, -170740559136), (Sum.inl 4530, 23037619200), (Sum.inl 4531, 210463318400), (Sum.inl 4532, -44193903360), (Sum.inl 4533, -13052917120), (Sum.inl 4534, -16735231520), (Sum.inl 4535, -49682226240), (Sum.inl 4536, -159234254400), (Sum.inl 4589, 37581020480), (Sum.inl 4590, 63093216000), (Sum.inl 4591, -218563806720), (Sum.inl 4592, -99513223360), (Sum.inl 4593, -128214953600), (Sum.inl 4594, 80041581760), (Sum.inl 4599, 122895311680), (Sum.inl 4603, -163565871040), (Sum.inl 4607, -18997702720), (Sum.inl 4609, 46118547520), (Sum.inl 4890, 138269537280), (Sum.inl 5219, 22459008000), (Sum.inl 5220, 151318656000), (Sum.inl 5251, -6253731840), (Sum.inl 5260, -56658355200), (Sum.inl 5282, -151318656000), (Sum.inl 5284, -17644247040), (Sum.inl 5289, 62238124800)]

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

def originalBlock87 : Integer.Sparse OriginalKey := [(Sum.inl 2669, 10373020800), (Sum.inl 2670, 5614752000), (Sum.inl 2682, 5186510400), (Sum.inl 2698, -56475672000), (Sum.inl 2706, 56475672000), (Sum.inl 3065, 41709844800), (Sum.inl 3078, 626512320), (Sum.inl 3088, -42336357120), (Sum.inl 3227, 506570400), (Sum.inl 3229, 128192524800), (Sum.inl 3517, 33408700800), (Sum.inl 3529, 41641183200), (Sum.inl 3537, 86075299200), (Sum.inl 3540, -7336967200), (Sum.inl 3569, 81289584000), (Sum.inl 3578, 76405896000), (Sum.inl 3840, -74677500000), (Sum.inl 3848, -38761696800), (Sum.inl 3873, -76405896000), (Sum.inl 3880, -122293680000), (Sum.inl 3954, 66389719680), (Sum.inl 3959, -56050135200), (Sum.inl 3972, -9717393600), (Sum.inl 3976, -81289584000), (Sum.inl 3977, -49533427200), (Sum.inl 3978, -15789352800), (Sum.inl 3990, 56715248160), (Sum.inl 3993, -19842213120), (Sum.inl 3994, -6462957600), (Sum.inl 3995, 122293680000), (Sum.inl 3996, -32626140000), (Sum.inl 3997, -13875116800), (Sum.inl 4888, 2026281600), (Sum.inl 4895, 512770099200), (Sum.inl 5138, 133634803200), (Sum.inl 5140, 22459008000), (Sum.inl 5185, 166564732800), (Sum.inl 5187, 344301196800), (Sum.inl 5197, 325158336000), (Sum.inl 5199, 305623584000), (Sum.inl 5205, 225902688000), (Sum.inl 5226, 41492083200), (Sum.inl 5236, 20746041600), (Sum.inl 5244, -225902688000), (Sum.inl 5250, 166839379200), (Sum.inl 5259, -169345428480), (Sum.inl 5260, -29347868800), (Sum.inl 5282, 2506049280), (Sum.inl 5405, -198133708800), (Sum.inl 5410, -130504560000), (Sum.inl 5421, -305623584000), (Sum.inl 5424, 226860992640), (Sum.inl 5425, -298710000000), (Sum.inl 5429, 265558878720), (Sum.inl 5430, -193916361600), (Sum.inl 5438, -79368852480), (Sum.inl 5445, -489174720000), (Sum.inl 5446, -224200540800), (Sum.inl 5471, -325158336000), (Sum.inl 5473, 489174720000), (Sum.inl 5478, -25851830400), (Sum.inl 5480, -63157411200), (Sum.inl 5484, -55500467200)]

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

def originalBlock88 : Integer.Sparse OriginalKey := [(Sum.inl 0, 140987363520), (Sum.inl 3, 192202411200), (Sum.inl 2697, 56475672000), (Sum.inl 2702, -56475672000), (Sum.inl 3064, -42474746880), (Sum.inl 3074, 50555669760), (Sum.inl 3075, 84811104000), (Sum.inl 3087, -22754900160), (Sum.inl 3099, -78356439360), (Sum.inl 3111, 50555669760), (Sum.inl 3223, 100765398400), (Sum.inl 3226, -118195249920), (Sum.inl 3228, 191985931200), (Sum.inl 3288, 3537700800), (Sum.inl 3289, 41004096000), (Sum.inl 3523, -48344200800), (Sum.inl 3526, -14366992320), (Sum.inl 3539, 94648080000), (Sum.inl 3542, -27995450400), (Sum.inl 3543, -47324040000), (Sum.inl 3839, 19033325280), (Sum.inl 3842, 17229204000), (Sum.inl 3846, -41004096000), (Sum.inl 3847, -63619065120), (Sum.inl 3848, -16509386400), (Sum.inl 3855, -47324040000), (Sum.inl 4026, -361568309760), (Sum.inl 4028, 34650547200), (Sum.inl 4034, 1255236480), (Sum.inl 4038, -12673492800), (Sum.inl 4083, 563949454080), (Sum.inl 4091, 768809644800), (Sum.inl 4589, 14150803200), (Sum.inl 4599, 164016384000), (Sum.inl 4600, -225902688000), (Sum.inl 4887, -472780999680), (Sum.inl 4889, 403061593600), (Sum.inl 4893, 767943724800), (Sum.inl 5139, -193376803200), (Sum.inl 5189, -111981801600), (Sum.inl 5243, 225902688000), (Sum.inl 5251, 208693332480), (Sum.inl 5252, -189296160000), (Sum.inl 5257, -91019600640), (Sum.inl 5265, -57467969280), (Sum.inl 5270, 339244416000), (Sum.inl 5273, 202222679040), (Sum.inl 5281, 202222679040), (Sum.inl 5290, -313425757440), (Sum.inl 5406, -254476260480), (Sum.inl 5408, -50693971200), (Sum.inl 5419, 68916816000), (Sum.inl 5425, 76133301120), (Sum.inl 5427, 5020945920), (Sum.inl 5429, -164016384000), (Sum.inl 5430, -66037545600), (Sum.inl 5431, -1446273239040), (Sum.inl 5437, -189296160000), (Sum.inl 5448, 138602188800)]

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

def originalBlock89 : Integer.Sparse OriginalKey := [(Sum.inl 1501, -16844256000), (Sum.inl 1502, -37829664000), (Sum.inl 1504, -31119062400), (Sum.inl 1508, 37829664000), (Sum.inl 1699, -6106736640), (Sum.inl 1700, -28414555200), (Sum.inl 1709, -7631160000), (Sum.inl 2140, -5614752000), (Sum.inl 2142, -37829664000), (Sum.inl 2187, 28414555200), (Sum.inl 2192, 2393825280), (Sum.inl 2232, 37829664000), (Sum.inl 2233, 6419160960), (Sum.inl 2235, 46994318640), (Sum.inl 2240, 10373020800), (Sum.inl 2688, 56475672000), (Sum.inl 2690, -56475672000), (Sum.inl 3058, 6893352000), (Sum.inl 3059, -49229709120), (Sum.inl 3221, -26084940672), (Sum.inl 3257, 157695480000), (Sum.inl 3290, 27259584000), (Sum.inl 3291, -11136233600), (Sum.inl 3294, -198699576000), (Sum.inl 3297, -18178405600), (Sum.inl 3510, -7075401600), (Sum.inl 3516, 11397799200), (Sum.inl 3535, -35628653280), (Sum.inl 3554, -157695480000), (Sum.inl 3832, 198699576000), (Sum.inl 3835, 15069535200), (Sum.inl 4024, 146133607680), (Sum.inl 4149, -67377024000), (Sum.inl 4150, -124476249600), (Sum.inl 4169, -151318656000), (Sum.inl 4173, 151318656000), (Sum.inl 4473, -24426946560), (Sum.inl 4474, -30524640000), (Sum.inl 4494, -113658220800), (Sum.inl 4540, 225902688000), (Sum.inl 4542, 630781920000), (Sum.inl 4590, 109038336000), (Sum.inl 4591, -44544934400), (Sum.inl 4593, -72713622400), (Sum.inl 4603, -794798304000), (Sum.inl 4663, -22459008000), (Sum.inl 4677, -151318656000), (Sum.inl 4815, 9575301120), (Sum.inl 4830, 113658220800), (Sum.inl 4851, 41492083200), (Sum.inl 4863, 151318656000), (Sum.inl 4885, -78663118848), (Sum.inl 4886, 187977274560), (Sum.inl 4956, -28301606400), (Sum.inl 4964, -630781920000), (Sum.inl 4975, -225902688000), (Sum.inl 5097, 27573408000), (Sum.inl 5129, 45591196800), (Sum.inl 5266, -142514613120), (Sum.inl 5277, -196918836480), (Sum.inl 5377, 60278140800), (Sum.inl 5379, 794798304000), (Sum.inl 5445, 584534430720)]

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

def originalBlock9 : Integer.Sparse OriginalKey := [(Sum.inl 147, -74048028800), (Sum.inl 153, -155482908000), (Sum.inl 244, 8378760000), (Sum.inl 248, -24611414400), (Sum.inl 249, 24611414400), (Sum.inl 330, -24456750000), (Sum.inl 333, 24456750000), (Sum.inl 337, -14553964800), (Sum.inl 346, 72382712400), (Sum.inl 390, 36869400000), (Sum.inl 394, -33682004400), (Sum.inl 395, 29089003800), (Sum.inl 402, 30311160000), (Sum.inl 410, -150492014000), (Sum.inl 420, 225013014400), (Sum.inl 446, -58510627200), (Sum.inl 447, 58466748000), (Sum.inl 456, 14865691200), (Sum.inl 459, 7276982400), (Sum.inl 470, -24456750000), (Sum.inl 483, -34411440000), (Sum.inl 484, -22965003000), (Sum.inl 487, 150480684000), (Sum.inl 491, 70344498000), (Sum.inl 493, 252078960000), (Sum.inl 494, 112434364800), (Sum.inl 496, -83664648000), (Sum.inl 503, -483511476000), (Sum.inr 5, 7785657600)]

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

def originalBlock90 : Integer.Sparse OriginalKey := [(Sum.inl 1505, 8422128000), (Sum.inl 1515, 15559531200), (Sum.inl 2148, -10373020800), (Sum.inl 3255, 7075401600), (Sum.inl 3261, 1439851200), (Sum.inl 3511, -1439851200), (Sum.inl 4151, 33688512000), (Sum.inl 4155, 62238124800), (Sum.inl 4527, 28301606400), (Sum.inl 4530, 5759404800), (Sum.inl 4666, -41492083200), (Sum.inl 4958, -5759404800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm0 : Integer.Sparse OriginalKey := [(Sum.inl 0, 445921053840)]

def originalTerm1 : Integer.Sparse OriginalKey := [(Sum.inl 1, 646978406640)]

def originalTerm2 : Integer.Sparse OriginalKey := [(Sum.inl 2, 74949359040)]

def originalTerm3 : Integer.Sparse OriginalKey := [(Sum.inl 3, 529189803840)]

def originalTerm4 : Integer.Sparse OriginalKey := [(Sum.inl 4, 1286762844080)]

def originalTerm5 : Integer.Sparse OriginalKey := [(Sum.inl 5, 215919309600)]

def originalTerm6 : Integer.Sparse OriginalKey := [(Sum.inl 6, 210023582400)]

def originalTerm7 : Integer.Sparse OriginalKey := [(Sum.inl 7, 175021876800)]

def originalTerm8 : Integer.Sparse OriginalKey := [(Sum.inl 8, -11590689600)]

def originalTerm9 : Integer.Sparse OriginalKey := [(Sum.inl 9, 11590689600)]

def originalTerm10 : Integer.Sparse OriginalKey := [(Sum.inl 10, 89720006400)]

def originalTerm11 : Integer.Sparse OriginalKey := [(Sum.inl 11, 89720006400)]

def originalTerm12 : Integer.Sparse OriginalKey := [(Sum.inl 12, -62888664000)]

def originalTerm13 : Integer.Sparse OriginalKey := [(Sum.inl 13, -26509586400)]

def originalTerm14 : Integer.Sparse OriginalKey := [(Sum.inl 14, -54397209600)]

def originalTerm15 : Integer.Sparse OriginalKey := [(Sum.inl 15, -89720006400)]

def originalTerm16 : Integer.Sparse OriginalKey := [(Sum.inl 16, 54397209600)]

def originalTerm17 : Integer.Sparse OriginalKey := [(Sum.inl 17, -16640095200)]

def originalTerm18 : Integer.Sparse OriginalKey := [(Sum.inl 18, -89720006400)]

def originalTerm19 : Integer.Sparse OriginalKey := [(Sum.inl 19, -37145028000)]

def originalTerm20 : Integer.Sparse OriginalKey := [(Sum.inl 20, 22854296400)]

def originalTerm21 : Integer.Sparse OriginalKey := [(Sum.inl 21, -49636036800)]

def originalTerm22 : Integer.Sparse OriginalKey := [(Sum.inl 22, -29183486400)]

def originalTerm23 : Integer.Sparse OriginalKey := [(Sum.inl 24, 49636036800)]

def originalTerm24 : Integer.Sparse OriginalKey := [(Sum.inl 26, 36906288000)]

def originalTerm25 : Integer.Sparse OriginalKey := [(Sum.inl 27, -15109920000)]

def originalTerm26 : Integer.Sparse OriginalKey := [(Sum.inl 28, 21023280000)]

def originalTerm27 : Integer.Sparse OriginalKey := [(Sum.inl 29, -21316464000)]

def originalTerm28 : Integer.Sparse OriginalKey := [(Sum.inl 30, 6635121600)]

def originalTerm29 : Integer.Sparse OriginalKey := [(Sum.inl 32, -33000508800)]

def originalTerm30 : Integer.Sparse OriginalKey := [(Sum.inl 33, -68618880000)]

def originalTerm31 : Integer.Sparse OriginalKey := [(Sum.inl 34, -7722801600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm32 : Integer.Sparse OriginalKey := [(Sum.inl 35, 53645860800)]

def originalTerm33 : Integer.Sparse OriginalKey := [(Sum.inl 36, 15109920000)]

def originalTerm34 : Integer.Sparse OriginalKey := [(Sum.inl 37, 33000508800)]

def originalTerm35 : Integer.Sparse OriginalKey := [(Sum.inl 38, 57050251200)]

def originalTerm36 : Integer.Sparse OriginalKey := [(Sum.inl 39, -27658401600)]

def originalTerm37 : Integer.Sparse OriginalKey := [(Sum.inl 40, 29615227200)]

def originalTerm38 : Integer.Sparse OriginalKey := [(Sum.inl 41, 4335177600)]

def originalTerm39 : Integer.Sparse OriginalKey := [(Sum.inl 42, -4855406400)]

def originalTerm40 : Integer.Sparse OriginalKey := [(Sum.inl 58, -265908600000)]

def originalTerm41 : Integer.Sparse OriginalKey := [(Sum.inl 59, -58574232000)]

def originalTerm42 : Integer.Sparse OriginalKey := [(Sum.inl 60, 55422432000)]

def originalTerm43 : Integer.Sparse OriginalKey := [(Sum.inl 63, 56534784000)]

def originalTerm44 : Integer.Sparse OriginalKey := [(Sum.inl 65, -45396547200)]

def originalTerm45 : Integer.Sparse OriginalKey := [(Sum.inl 66, -30264364800)]

def originalTerm46 : Integer.Sparse OriginalKey := [(Sum.inl 67, 61895664000)]

def originalTerm47 : Integer.Sparse OriginalKey := [(Sum.inl 68, 12604166400)]

def originalTerm48 : Integer.Sparse OriginalKey := [(Sum.inl 69, -56534784000)]

def originalTerm49 : Integer.Sparse OriginalKey := [(Sum.inl 70, -13697011200)]

def originalTerm50 : Integer.Sparse OriginalKey := [(Sum.inl 71, 19567080000)]

def originalTerm51 : Integer.Sparse OriginalKey := [(Sum.inl 72, -10987790400)]

def originalTerm52 : Integer.Sparse OriginalKey := [(Sum.inl 73, 2725992000)]

def originalTerm53 : Integer.Sparse OriginalKey := [(Sum.inl 74, 7706640000)]

def originalTerm54 : Integer.Sparse OriginalKey := [(Sum.inl 75, -7706640000)]

def originalTerm55 : Integer.Sparse OriginalKey := [(Sum.inl 76, -33000508800)]

def originalTerm56 : Integer.Sparse OriginalKey := [(Sum.inl 87, 189297187200)]

def originalTerm57 : Integer.Sparse OriginalKey := [(Sum.inl 88, 96879938400)]

def originalTerm58 : Integer.Sparse OriginalKey := [(Sum.inl 91, 49457467200)]

def originalTerm59 : Integer.Sparse OriginalKey := [(Sum.inl 93, -155449718400)]

def originalTerm60 : Integer.Sparse OriginalKey := [(Sum.inl 95, 30264364800)]

def originalTerm61 : Integer.Sparse OriginalKey := [(Sum.inl 96, 45396547200)]

def originalTerm62 : Integer.Sparse OriginalKey := [(Sum.inl 97, -11872209600)]

def originalTerm63 : Integer.Sparse OriginalKey := [(Sum.inl 98, 80728075200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm320 : Integer.Sparse OriginalKey := [(Sum.inl 408, 12245371200)]

def originalTerm321 : Integer.Sparse OriginalKey := [(Sum.inl 409, 325392359600)]

def originalTerm322 : Integer.Sparse OriginalKey := [(Sum.inl 410, -269816505200)]

def originalTerm323 : Integer.Sparse OriginalKey := [(Sum.inl 411, 62887622400)]

def originalTerm324 : Integer.Sparse OriginalKey := [(Sum.inl 412, -390136135200)]

def originalTerm325 : Integer.Sparse OriginalKey := [(Sum.inl 413, 2611036800)]

def originalTerm326 : Integer.Sparse OriginalKey := [(Sum.inl 414, -33234873600)]

def originalTerm327 : Integer.Sparse OriginalKey := [(Sum.inl 415, 48995640000)]

def originalTerm328 : Integer.Sparse OriginalKey := [(Sum.inl 416, -339802200000)]

def originalTerm329 : Integer.Sparse OriginalKey := [(Sum.inl 417, 30264364800)]

def originalTerm330 : Integer.Sparse OriginalKey := [(Sum.inl 418, 53645860800)]

def originalTerm331 : Integer.Sparse OriginalKey := [(Sum.inl 419, 69660840000)]

def originalTerm332 : Integer.Sparse OriginalKey := [(Sum.inl 420, 398629156800)]

def originalTerm333 : Integer.Sparse OriginalKey := [(Sum.inl 421, -81626716800)]

def originalTerm334 : Integer.Sparse OriginalKey := [(Sum.inl 422, 32362272000)]

def originalTerm335 : Integer.Sparse OriginalKey := [(Sum.inl 423, -76224000)]

def originalTerm336 : Integer.Sparse OriginalKey := [(Sum.inl 424, 71046268800)]

def originalTerm337 : Integer.Sparse OriginalKey := [(Sum.inl 426, 24456750000)]

def originalTerm338 : Integer.Sparse OriginalKey := [(Sum.inl 427, 362656380000)]

def originalTerm339 : Integer.Sparse OriginalKey := [(Sum.inl 428, 22965003000)]

def originalTerm340 : Integer.Sparse OriginalKey := [(Sum.inl 429, 39403584000)]

def originalTerm341 : Integer.Sparse OriginalKey := [(Sum.inl 432, -132933384000)]

def originalTerm342 : Integer.Sparse OriginalKey := [(Sum.inl 434, 414899520000)]

def originalTerm343 : Integer.Sparse OriginalKey := [(Sum.inl 435, -278136775000)]

def originalTerm344 : Integer.Sparse OriginalKey := [(Sum.inl 436, 22481664000)]

def originalTerm345 : Integer.Sparse OriginalKey := [(Sum.inl 437, -22405440000)]

def originalTerm346 : Integer.Sparse OriginalKey := [(Sum.inl 438, -295462521600)]

def originalTerm347 : Integer.Sparse OriginalKey := [(Sum.inl 439, -58510627200)]

def originalTerm348 : Integer.Sparse OriginalKey := [(Sum.inl 440, -20481206400)]

def originalTerm349 : Integer.Sparse OriginalKey := [(Sum.inl 443, -264447801600)]

def originalTerm350 : Integer.Sparse OriginalKey := [(Sum.inl 444, -113032272000)]

def originalTerm351 : Integer.Sparse OriginalKey := [(Sum.inl 446, -268490995200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm352 : Integer.Sparse OriginalKey := [(Sum.inl 447, 58466748000)]

def originalTerm353 : Integer.Sparse OriginalKey := [(Sum.inl 448, -8858596800)]

def originalTerm354 : Integer.Sparse OriginalKey := [(Sum.inl 449, 182073600000)]

def originalTerm355 : Integer.Sparse OriginalKey := [(Sum.inl 450, 13057142400)]

def originalTerm356 : Integer.Sparse OriginalKey := [(Sum.inl 451, 137360937600)]

def originalTerm357 : Integer.Sparse OriginalKey := [(Sum.inl 452, 104631547200)]

def originalTerm358 : Integer.Sparse OriginalKey := [(Sum.inl 455, 44597073600)]

def originalTerm359 : Integer.Sparse OriginalKey := [(Sum.inl 456, 14865691200)]

def originalTerm360 : Integer.Sparse OriginalKey := [(Sum.inl 458, -314148300000)]

def originalTerm361 : Integer.Sparse OriginalKey := [(Sum.inl 459, 7276982400)]

def originalTerm362 : Integer.Sparse OriginalKey := [(Sum.inl 461, -24456750000)]

def originalTerm363 : Integer.Sparse OriginalKey := [(Sum.inl 462, 29731382400)]

def originalTerm364 : Integer.Sparse OriginalKey := [(Sum.inl 463, -425229843600)]

def originalTerm365 : Integer.Sparse OriginalKey := [(Sum.inl 464, -52185958200)]

def originalTerm366 : Integer.Sparse OriginalKey := [(Sum.inl 465, -834214643200)]

def originalTerm367 : Integer.Sparse OriginalKey := [(Sum.inl 466, 24456750000)]

def originalTerm368 : Integer.Sparse OriginalKey := [(Sum.inl 467, 673907438800)]

def originalTerm369 : Integer.Sparse OriginalKey := [(Sum.inl 468, 288359812600)]

def originalTerm370 : Integer.Sparse OriginalKey := [(Sum.inl 469, 267478797400)]

def originalTerm371 : Integer.Sparse OriginalKey := [(Sum.inl 470, -24456750000)]

def originalTerm372 : Integer.Sparse OriginalKey := [(Sum.inl 471, -105157382400)]

def originalTerm373 : Integer.Sparse OriginalKey := [(Sum.inl 472, 26607974400)]

def originalTerm374 : Integer.Sparse OriginalKey := [(Sum.inl 475, -161540352000)]

def originalTerm375 : Integer.Sparse OriginalKey := [(Sum.inl 476, -24456750000)]

def originalTerm376 : Integer.Sparse OriginalKey := [(Sum.inl 478, 118976784000)]

def originalTerm377 : Integer.Sparse OriginalKey := [(Sum.inl 479, 919227600)]

def originalTerm378 : Integer.Sparse OriginalKey := [(Sum.inl 480, -179524686000)]

def originalTerm379 : Integer.Sparse OriginalKey := [(Sum.inl 481, -107015415600)]

def originalTerm380 : Integer.Sparse OriginalKey := [(Sum.inl 482, -22965003000)]

def originalTerm381 : Integer.Sparse OriginalKey := [(Sum.inl 483, -297942391000)]

def originalTerm382 : Integer.Sparse OriginalKey := [(Sum.inl 484, -21473256000)]

def originalTerm383 : Integer.Sparse OriginalKey := [(Sum.inl 485, 48913500000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm384 : Integer.Sparse OriginalKey := [(Sum.inl 486, 45930006000)]

def originalTerm385 : Integer.Sparse OriginalKey := [(Sum.inl 487, 548537410000)]

def originalTerm386 : Integer.Sparse OriginalKey := [(Sum.inl 488, -26607974400)]

def originalTerm387 : Integer.Sparse OriginalKey := [(Sum.inl 489, 3123408000)]

def originalTerm388 : Integer.Sparse OriginalKey := [(Sum.inl 490, -142388560800)]

def originalTerm389 : Integer.Sparse OriginalKey := [(Sum.inl 491, 614841568400)]

def originalTerm390 : Integer.Sparse OriginalKey := [(Sum.inl 492, -1021030200)]

def originalTerm391 : Integer.Sparse OriginalKey := [(Sum.inl 493, 252078960000)]

def originalTerm392 : Integer.Sparse OriginalKey := [(Sum.inl 494, 103827859200)]

def originalTerm393 : Integer.Sparse OriginalKey := [(Sum.inl 495, -29255313600)]

def originalTerm394 : Integer.Sparse OriginalKey := [(Sum.inl 496, -428061945600)]

def originalTerm395 : Integer.Sparse OriginalKey := [(Sum.inl 497, 24456750000)]

def originalTerm396 : Integer.Sparse OriginalKey := [(Sum.inl 498, 139239822000)]

def originalTerm397 : Integer.Sparse OriginalKey := [(Sum.inl 499, 45930006000)]

def originalTerm398 : Integer.Sparse OriginalKey := [(Sum.inl 500, -22965003000)]

def originalTerm399 : Integer.Sparse OriginalKey := [(Sum.inl 501, 73217623000)]

def originalTerm400 : Integer.Sparse OriginalKey := [(Sum.inl 502, -8155089600)]

def originalTerm401 : Integer.Sparse OriginalKey := [(Sum.inl 503, -717905798400)]

def originalTerm402 : Integer.Sparse OriginalKey := [(Sum.inl 504, 19380828000)]

def originalTerm403 : Integer.Sparse OriginalKey := [(Sum.inl 505, -36602335200)]

def originalTerm404 : Integer.Sparse OriginalKey := [(Sum.inl 506, -208692163200)]

def originalTerm405 : Integer.Sparse OriginalKey := [(Sum.inl 507, -81540043200)]

def originalTerm406 : Integer.Sparse OriginalKey := [(Sum.inl 508, -61727616000)]

def originalTerm407 : Integer.Sparse OriginalKey := [(Sum.inl 509, 185182848000)]

def originalTerm408 : Integer.Sparse OriginalKey := [(Sum.inl 510, -61727616000)]

def originalTerm409 : Integer.Sparse OriginalKey := [(Sum.inl 512, 24456750000)]

def originalTerm410 : Integer.Sparse OriginalKey := [(Sum.inl 513, 22965003000)]

def originalTerm411 : Integer.Sparse OriginalKey := [(Sum.inl 514, -69496302000)]

def originalTerm412 : Integer.Sparse OriginalKey := [(Sum.inl 515, -22965003000)]

def originalTerm413 : Integer.Sparse OriginalKey := [(Sum.inl 516, -32083860000)]

def originalTerm414 : Integer.Sparse OriginalKey := [(Sum.inl 517, -61727616000)]

def originalTerm415 : Integer.Sparse OriginalKey := [(Sum.inl 518, 22557888000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm416 : Integer.Sparse OriginalKey := [(Sum.inl 520, 175118889600)]

def originalTerm417 : Integer.Sparse OriginalKey := [(Sum.inl 521, -149287060800)]

def originalTerm418 : Integer.Sparse OriginalKey := [(Sum.inl 525, 26607974400)]

def originalTerm419 : Integer.Sparse OriginalKey := [(Sum.inl 526, -166607222400)]

def originalTerm420 : Integer.Sparse OriginalKey := [(Sum.inl 527, 87559444800)]

def originalTerm421 : Integer.Sparse OriginalKey := [(Sum.inl 528, 1165012800)]

def originalTerm422 : Integer.Sparse OriginalKey := [(Sum.inl 529, 26607974400)]

def originalTerm423 : Integer.Sparse OriginalKey := [(Sum.inl 530, 107665080000)]

def originalTerm424 : Integer.Sparse OriginalKey := [(Sum.inl 531, 175021876800)]

def originalTerm425 : Integer.Sparse OriginalKey := [(Sum.inl 532, -324211924800)]

def originalTerm426 : Integer.Sparse OriginalKey := [(Sum.inl 533, -25831828800)]

def originalTerm427 : Integer.Sparse OriginalKey := [(Sum.inl 577, -17391009600)]

def originalTerm428 : Integer.Sparse OriginalKey := [(Sum.inl 578, -60666854400)]

def originalTerm429 : Integer.Sparse OriginalKey := [(Sum.inl 579, 17391009600)]

def originalTerm430 : Integer.Sparse OriginalKey := [(Sum.inl 580, 23325720000)]

def originalTerm431 : Integer.Sparse OriginalKey := [(Sum.inl 581, 23321860800)]

def originalTerm432 : Integer.Sparse OriginalKey := [(Sum.inl 582, 16149292800)]

def originalTerm433 : Integer.Sparse OriginalKey := [(Sum.inl 583, 60666854400)]

def originalTerm434 : Integer.Sparse OriginalKey := [(Sum.inl 584, -3010183200)]

def originalTerm435 : Integer.Sparse OriginalKey := [(Sum.inl 585, -61808472000)]

def originalTerm436 : Integer.Sparse OriginalKey := [(Sum.inl 586, -23337297600)]

def originalTerm437 : Integer.Sparse OriginalKey := [(Sum.inl 587, 131568940800)]

def originalTerm438 : Integer.Sparse OriginalKey := [(Sum.inl 588, -25179842400)]

def originalTerm439 : Integer.Sparse OriginalKey := [(Sum.inl 589, -23333438400)]

def originalTerm440 : Integer.Sparse OriginalKey := [(Sum.inl 590, -14480793600)]

def originalTerm441 : Integer.Sparse OriginalKey := [(Sum.inl 591, 60910944000)]

def originalTerm442 : Integer.Sparse OriginalKey := [(Sum.inl 597, -758620800)]

def originalTerm443 : Integer.Sparse OriginalKey := [(Sum.inl 599, -32201481600)]

def originalTerm444 : Integer.Sparse OriginalKey := [(Sum.inl 600, 9158889600)]

def originalTerm445 : Integer.Sparse OriginalKey := [(Sum.inl 601, 758620800)]

def originalTerm446 : Integer.Sparse OriginalKey := [(Sum.inl 603, 14181249600)]

def originalTerm447 : Integer.Sparse OriginalKey := [(Sum.inl 604, 177820420800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm448 : Integer.Sparse OriginalKey := [(Sum.inl 605, -65216352000)]

def originalTerm449 : Integer.Sparse OriginalKey := [(Sum.inl 606, 38313403200)]

def originalTerm450 : Integer.Sparse OriginalKey := [(Sum.inl 607, 61158211200)]

def originalTerm451 : Integer.Sparse OriginalKey := [(Sum.inl 608, -28019308800)]

def originalTerm452 : Integer.Sparse OriginalKey := [(Sum.inl 610, -251788867200)]

def originalTerm453 : Integer.Sparse OriginalKey := [(Sum.inl 611, 488764281600)]

def originalTerm454 : Integer.Sparse OriginalKey := [(Sum.inl 612, -15534465600)]

def originalTerm455 : Integer.Sparse OriginalKey := [(Sum.inl 613, -69178903200)]

def originalTerm456 : Integer.Sparse OriginalKey := [(Sum.inl 614, 18020232000)]

def originalTerm457 : Integer.Sparse OriginalKey := [(Sum.inl 615, 47880720000)]

def originalTerm458 : Integer.Sparse OriginalKey := [(Sum.inl 616, -62880211200)]

def originalTerm459 : Integer.Sparse OriginalKey := [(Sum.inl 617, 79813992000)]

def originalTerm460 : Integer.Sparse OriginalKey := [(Sum.inl 618, 34213147200)]

def originalTerm461 : Integer.Sparse OriginalKey := [(Sum.inl 619, 84076771200)]

def originalTerm462 : Integer.Sparse OriginalKey := [(Sum.inl 620, 246315103200)]

def originalTerm463 : Integer.Sparse OriginalKey := [(Sum.inl 621, 9720763200)]

def originalTerm464 : Integer.Sparse OriginalKey := [(Sum.inl 622, -21797928000)]

def originalTerm465 : Integer.Sparse OriginalKey := [(Sum.inl 623, -33449788800)]

def originalTerm466 : Integer.Sparse OriginalKey := [(Sum.inl 624, -9654350400)]

def originalTerm467 : Integer.Sparse OriginalKey := [(Sum.inl 626, 106376856000)]

def originalTerm468 : Integer.Sparse OriginalKey := [(Sum.inl 627, -22862107200)]

def originalTerm469 : Integer.Sparse OriginalKey := [(Sum.inl 628, 9654350400)]

def originalTerm470 : Integer.Sparse OriginalKey := [(Sum.inl 629, 36039360000)]

def originalTerm471 : Integer.Sparse OriginalKey := [(Sum.inl 630, -36039360000)]

def originalTerm472 : Integer.Sparse OriginalKey := [(Sum.inl 631, -96217968000)]

def originalTerm473 : Integer.Sparse OriginalKey := [(Sum.inl 633, 122648020800)]

def originalTerm474 : Integer.Sparse OriginalKey := [(Sum.inl 634, -121776561600)]

def originalTerm475 : Integer.Sparse OriginalKey := [(Sum.inl 635, -50064960000)]

def originalTerm476 : Integer.Sparse OriginalKey := [(Sum.inl 636, -106301697600)]

def originalTerm477 : Integer.Sparse OriginalKey := [(Sum.inl 637, 133529400000)]

def originalTerm478 : Integer.Sparse OriginalKey := [(Sum.inl 638, 139214414400)]

def originalTerm479 : Integer.Sparse OriginalKey := [(Sum.inl 639, -93059640000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm480 : Integer.Sparse OriginalKey := [(Sum.inl 640, -133529400000)]

def originalTerm481 : Integer.Sparse OriginalKey := [(Sum.inl 641, 69128280000)]

def originalTerm482 : Integer.Sparse OriginalKey := [(Sum.inl 642, -208342694400)]

def originalTerm483 : Integer.Sparse OriginalKey := [(Sum.inl 643, 93059640000)]

def originalTerm484 : Integer.Sparse OriginalKey := [(Sum.inl 653, 23713099200)]

def originalTerm485 : Integer.Sparse OriginalKey := [(Sum.inl 654, 8398324800)]

def originalTerm486 : Integer.Sparse OriginalKey := [(Sum.inl 909, 230156186400)]

def originalTerm487 : Integer.Sparse OriginalKey := [(Sum.inl 911, 196881108000)]

def originalTerm488 : Integer.Sparse OriginalKey := [(Sum.inl 914, 216296064000)]

def originalTerm489 : Integer.Sparse OriginalKey := [(Sum.inl 922, 22401120000)]

def originalTerm490 : Integer.Sparse OriginalKey := [(Sum.inl 929, -25023835200)]

def originalTerm491 : Integer.Sparse OriginalKey := [(Sum.inl 930, -120195513600)]

def originalTerm492 : Integer.Sparse OriginalKey := [(Sum.inl 931, 22920076800)]

def originalTerm493 : Integer.Sparse OriginalKey := [(Sum.inl 932, -60632745600)]

def originalTerm494 : Integer.Sparse OriginalKey := [(Sum.inl 933, -22401120000)]

def originalTerm495 : Integer.Sparse OriginalKey := [(Sum.inl 934, 27859152000)]

def originalTerm496 : Integer.Sparse OriginalKey := [(Sum.inl 936, -93070348800)]

def originalTerm497 : Integer.Sparse OriginalKey := [(Sum.inl 937, -18342576000)]

def originalTerm498 : Integer.Sparse OriginalKey := [(Sum.inl 939, -150030254400)]

def originalTerm499 : Integer.Sparse OriginalKey := [(Sum.inl 940, -82667304000)]

def originalTerm500 : Integer.Sparse OriginalKey := [(Sum.inl 944, 152976600000)]

def originalTerm501 : Integer.Sparse OriginalKey := [(Sum.inl 945, 152976600000)]

def originalTerm502 : Integer.Sparse OriginalKey := [(Sum.inl 946, 131822880000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm64 : Integer.Sparse OriginalKey := [(Sum.inl 99, 105992251200)]

def originalTerm65 : Integer.Sparse OriginalKey := [(Sum.inl 100, -4669651200)]

def originalTerm66 : Integer.Sparse OriginalKey := [(Sum.inl 101, -25653120000)]

def originalTerm67 : Integer.Sparse OriginalKey := [(Sum.inl 102, -46276012800)]

def originalTerm68 : Integer.Sparse OriginalKey := [(Sum.inl 103, 25653120000)]

def originalTerm69 : Integer.Sparse OriginalKey := [(Sum.inl 104, 23138006400)]

def originalTerm70 : Integer.Sparse OriginalKey := [(Sum.inl 111, 8150452800)]

def originalTerm71 : Integer.Sparse OriginalKey := [(Sum.inl 112, -40276809600)]

def originalTerm72 : Integer.Sparse OriginalKey := [(Sum.inl 113, -4718736000)]

def originalTerm73 : Integer.Sparse OriginalKey := [(Sum.inl 114, -153660427200)]

def originalTerm74 : Integer.Sparse OriginalKey := [(Sum.inl 115, -114445105200)]

def originalTerm75 : Integer.Sparse OriginalKey := [(Sum.inl 116, 125961319200)]

def originalTerm76 : Integer.Sparse OriginalKey := [(Sum.inl 117, 50680622400)]

def originalTerm77 : Integer.Sparse OriginalKey := [(Sum.inl 118, 29731382400)]

def originalTerm78 : Integer.Sparse OriginalKey := [(Sum.inl 119, -353001600)]

def originalTerm79 : Integer.Sparse OriginalKey := [(Sum.inl 121, 29731382400)]

def originalTerm80 : Integer.Sparse OriginalKey := [(Sum.inl 122, -155482908000)]

def originalTerm81 : Integer.Sparse OriginalKey := [(Sum.inl 123, -4924267200)]

def originalTerm82 : Integer.Sparse OriginalKey := [(Sum.inl 124, 54967065600)]

def originalTerm83 : Integer.Sparse OriginalKey := [(Sum.inl 125, -7276982400)]

def originalTerm84 : Integer.Sparse OriginalKey := [(Sum.inl 126, 7276982400)]

def originalTerm85 : Integer.Sparse OriginalKey := [(Sum.inl 127, -117021254400)]

def originalTerm86 : Integer.Sparse OriginalKey := [(Sum.inl 129, -29255313600)]

def originalTerm87 : Integer.Sparse OriginalKey := [(Sum.inl 130, 155482908000)]

def originalTerm88 : Integer.Sparse OriginalKey := [(Sum.inl 131, -20785348800)]

def originalTerm89 : Integer.Sparse OriginalKey := [(Sum.inl 132, -29731382400)]

def originalTerm90 : Integer.Sparse OriginalKey := [(Sum.inl 133, -38619028800)]

def originalTerm91 : Integer.Sparse OriginalKey := [(Sum.inl 134, 14173675200)]

def originalTerm92 : Integer.Sparse OriginalKey := [(Sum.inl 139, 179893716000)]

def originalTerm93 : Integer.Sparse OriginalKey := [(Sum.inl 140, 152493757200)]

def originalTerm94 : Integer.Sparse OriginalKey := [(Sum.inl 142, -226590360000)]

def originalTerm95 : Integer.Sparse OriginalKey := [(Sum.inl 143, 18719664000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm959 : Integer.Sparse OriginalKey := [(Sum.inl 2556, -20279232000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm96 : Integer.Sparse OriginalKey := [(Sum.inl 145, -29521588800)]

def originalTerm97 : Integer.Sparse OriginalKey := [(Sum.inl 147, 105618892800)]

def originalTerm98 : Integer.Sparse OriginalKey := [(Sum.inl 148, -125285114400)]

def originalTerm99 : Integer.Sparse OriginalKey := [(Sum.inl 149, 141891912000)]

def originalTerm100 : Integer.Sparse OriginalKey := [(Sum.inl 150, 155482908000)]

def originalTerm101 : Integer.Sparse OriginalKey := [(Sum.inl 152, -29255313600)]

def originalTerm102 : Integer.Sparse OriginalKey := [(Sum.inl 153, -155482908000)]

def originalTerm103 : Integer.Sparse OriginalKey := [(Sum.inl 154, -7638192000)]

def originalTerm104 : Integer.Sparse OriginalKey := [(Sum.inl 155, -4660051200)]

def originalTerm105 : Integer.Sparse OriginalKey := [(Sum.inl 157, 112325131200)]

def originalTerm106 : Integer.Sparse OriginalKey := [(Sum.inl 159, -14173675200)]

def originalTerm107 : Integer.Sparse OriginalKey := [(Sum.inl 160, -57684297600)]

def originalTerm108 : Integer.Sparse OriginalKey := [(Sum.inl 161, -107665080000)]

def originalTerm109 : Integer.Sparse OriginalKey := [(Sum.inl 162, 81471988800)]

def originalTerm110 : Integer.Sparse OriginalKey := [(Sum.inl 163, 11590689600)]

def originalTerm111 : Integer.Sparse OriginalKey := [(Sum.inl 164, 114352617600)]

def originalTerm112 : Integer.Sparse OriginalKey := [(Sum.inl 165, 5942851200)]

def originalTerm113 : Integer.Sparse OriginalKey := [(Sum.inl 166, -174262449600)]

def originalTerm114 : Integer.Sparse OriginalKey := [(Sum.inl 167, -24632611200)]

def originalTerm115 : Integer.Sparse OriginalKey := [(Sum.inl 168, 57659644800)]

def originalTerm116 : Integer.Sparse OriginalKey := [(Sum.inl 169, -134580009600)]

def originalTerm117 : Integer.Sparse OriginalKey := [(Sum.inl 170, 14642695200)]

def originalTerm118 : Integer.Sparse OriginalKey := [(Sum.inl 171, 117325752000)]

def originalTerm119 : Integer.Sparse OriginalKey := [(Sum.inl 172, 49636036800)]

def originalTerm120 : Integer.Sparse OriginalKey := [(Sum.inl 173, -14848344000)]

def originalTerm121 : Integer.Sparse OriginalKey := [(Sum.inl 174, -6019252800)]

def originalTerm122 : Integer.Sparse OriginalKey := [(Sum.inl 175, 4781318400)]

def originalTerm123 : Integer.Sparse OriginalKey := [(Sum.inl 176, 23917920000)]

def originalTerm124 : Integer.Sparse OriginalKey := [(Sum.inl 177, 17204184000)]

def originalTerm125 : Integer.Sparse OriginalKey := [(Sum.inl 178, -115589558400)]

def originalTerm126 : Integer.Sparse OriginalKey := [(Sum.inl 179, -38900332800)]

def originalTerm127 : Integer.Sparse OriginalKey := [(Sum.inl 180, -17859355200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm960 : Integer.Sparse OriginalKey := [(Sum.inl 2557, -21995095200)]

def originalTerm961 : Integer.Sparse OriginalKey := [(Sum.inl 2558, 89053648800)]

def originalTerm962 : Integer.Sparse OriginalKey := [(Sum.inl 2560, -34782019200)]

def originalTerm963 : Integer.Sparse OriginalKey := [(Sum.inl 2561, -214800724800)]

def originalTerm964 : Integer.Sparse OriginalKey := [(Sum.inl 2566, 1455966000)]

def originalTerm965 : Integer.Sparse OriginalKey := [(Sum.inl 2569, -1455966000)]

def originalTerm966 : Integer.Sparse OriginalKey := [(Sum.inl 2573, 92375839200)]

def originalTerm967 : Integer.Sparse OriginalKey := [(Sum.inl 2575, 205472536800)]

def originalTerm968 : Integer.Sparse OriginalKey := [(Sum.inl 2587, 55524372000)]

def originalTerm969 : Integer.Sparse OriginalKey := [(Sum.inl 2589, -23344944000)]

def originalTerm970 : Integer.Sparse OriginalKey := [(Sum.inl 2590, 259541131200)]

def originalTerm971 : Integer.Sparse OriginalKey := [(Sum.inl 2591, -55524372000)]

def originalTerm972 : Integer.Sparse OriginalKey := [(Sum.inl 2600, 173434970400)]

def originalTerm973 : Integer.Sparse OriginalKey := [(Sum.inl 2603, 117060177600)]

def originalTerm974 : Integer.Sparse OriginalKey := [(Sum.inl 2614, 1455966000)]

def originalTerm975 : Integer.Sparse OriginalKey := [(Sum.inl 2617, -246669124000)]

def originalTerm976 : Integer.Sparse OriginalKey := [(Sum.inl 2618, 926675764000)]

def originalTerm977 : Integer.Sparse OriginalKey := [(Sum.inl 2620, 280773729200)]

def originalTerm978 : Integer.Sparse OriginalKey := [(Sum.inl 2631, -401664536000)]

def originalTerm979 : Integer.Sparse OriginalKey := [(Sum.inl 2632, -170188324000)]

def originalTerm980 : Integer.Sparse OriginalKey := [(Sum.inl 2633, 401664536000)]

def originalTerm981 : Integer.Sparse OriginalKey := [(Sum.inl 2635, 85094162000)]

def originalTerm982 : Integer.Sparse OriginalKey := [(Sum.inl 2641, 197147280000)]

def originalTerm983 : Integer.Sparse OriginalKey := [(Sum.inl 2643, 204270432000)]

def originalTerm984 : Integer.Sparse OriginalKey := [(Sum.inl 2652, 108902126400)]

def originalTerm985 : Integer.Sparse OriginalKey := [(Sum.inl 2653, -77090685120)]

def originalTerm986 : Integer.Sparse OriginalKey := [(Sum.inl 2654, -1583273280)]

def originalTerm987 : Integer.Sparse OriginalKey := [(Sum.inl 2655, 11023403520)]

def originalTerm988 : Integer.Sparse OriginalKey := [(Sum.inl 2656, 65159040000)]

def originalTerm989 : Integer.Sparse OriginalKey := [(Sum.inl 2657, 97278520320)]

def originalTerm990 : Integer.Sparse OriginalKey := [(Sum.inl 2658, -846506880)]

def originalTerm991 : Integer.Sparse OriginalKey := [(Sum.inl 2659, -112133076480)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm992 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 67590532800)]

def originalTerm993 : Integer.Sparse OriginalKey := [(Sum.inl 2662, -2533615680)]

def originalTerm994 : Integer.Sparse OriginalKey := [(Sum.inl 2664, 23608051200)]

def originalTerm995 : Integer.Sparse OriginalKey := [(Sum.inl 2669, 51865104000)]

def originalTerm996 : Integer.Sparse OriginalKey := [(Sum.inl 2670, -114367811520)]

def originalTerm997 : Integer.Sparse OriginalKey := [(Sum.inl 2673, 84249384000)]

def originalTerm998 : Integer.Sparse OriginalKey := [(Sum.inl 2676, 58395481920)]

def originalTerm999 : Integer.Sparse OriginalKey := [(Sum.inl 2677, 97285769280)]

def originalTerm1000 : Integer.Sparse OriginalKey := [(Sum.inl 2678, 33216880320)]

def originalTerm1001 : Integer.Sparse OriginalKey := [(Sum.inl 2680, 8725170240)]

def originalTerm1002 : Integer.Sparse OriginalKey := [(Sum.inl 2681, -8103403200)]

def originalTerm1003 : Integer.Sparse OriginalKey := [(Sum.inl 2682, -65159040000)]

def originalTerm1004 : Integer.Sparse OriginalKey := [(Sum.inl 2683, -72072555840)]

def originalTerm1005 : Integer.Sparse OriginalKey := [(Sum.inl 2687, 73195665120)]

def originalTerm1006 : Integer.Sparse OriginalKey := [(Sum.inl 2688, 56475672000)]

def originalTerm1007 : Integer.Sparse OriginalKey := [(Sum.inl 2690, -56475672000)]

def originalTerm1008 : Integer.Sparse OriginalKey := [(Sum.inl 2697, 17697953280)]

def originalTerm1009 : Integer.Sparse OriginalKey := [(Sum.inl 2698, -85320552000)]

def originalTerm1010 : Integer.Sparse OriginalKey := [(Sum.inl 2700, -11980787760)]

def originalTerm1011 : Integer.Sparse OriginalKey := [(Sum.inl 2702, -11246928960)]

def originalTerm1012 : Integer.Sparse OriginalKey := [(Sum.inl 2706, 110897493120)]

def originalTerm1013 : Integer.Sparse OriginalKey := [(Sum.inl 2707, -22523472000)]

def originalTerm1014 : Integer.Sparse OriginalKey := [(Sum.inl 2708, 57952011840)]

def originalTerm1015 : Integer.Sparse OriginalKey := [(Sum.inl 2709, 582075912000)]

def originalTerm1016 : Integer.Sparse OriginalKey := [(Sum.inl 2710, 100272275280)]

def originalTerm1017 : Integer.Sparse OriginalKey := [(Sum.inl 2712, 17804046000)]

def originalTerm1018 : Integer.Sparse OriginalKey := [(Sum.inl 2714, -498059928000)]

def originalTerm1019 : Integer.Sparse OriginalKey := [(Sum.inl 2716, 4757112000)]

def originalTerm1020 : Integer.Sparse OriginalKey := [(Sum.inl 2718, 70626419520)]

def originalTerm1021 : Integer.Sparse OriginalKey := [(Sum.inl 2719, 5042515200)]

def originalTerm1022 : Integer.Sparse OriginalKey := [(Sum.inl 2720, 348782546400)]

def originalTerm1023 : Integer.Sparse OriginalKey := [(Sum.inl 2721, -509212483200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1024 : Integer.Sparse OriginalKey := [(Sum.inl 2722, -1425447878400)]

def originalTerm1025 : Integer.Sparse OriginalKey := [(Sum.inl 2723, -163007496000)]

def originalTerm1026 : Integer.Sparse OriginalKey := [(Sum.inl 2724, 4026726720)]

def originalTerm1027 : Integer.Sparse OriginalKey := [(Sum.inl 2726, -583452000)]

def originalTerm1028 : Integer.Sparse OriginalKey := [(Sum.inl 2728, -111834753120)]

def originalTerm1029 : Integer.Sparse OriginalKey := [(Sum.inl 2729, 4268109120)]

def originalTerm1030 : Integer.Sparse OriginalKey := [(Sum.inl 2730, -144819820320)]

def originalTerm1031 : Integer.Sparse OriginalKey := [(Sum.inl 2731, 50275115760)]

def originalTerm1032 : Integer.Sparse OriginalKey := [(Sum.inl 2732, -103717799680)]

def originalTerm1033 : Integer.Sparse OriginalKey := [(Sum.inl 2734, 164032347040)]

def originalTerm1034 : Integer.Sparse OriginalKey := [(Sum.inl 2735, 89234675040)]

def originalTerm1035 : Integer.Sparse OriginalKey := [(Sum.inl 2736, 126876908160)]

def originalTerm1036 : Integer.Sparse OriginalKey := [(Sum.inl 2737, -5033704800)]

def originalTerm1037 : Integer.Sparse OriginalKey := [(Sum.inl 2738, 111679758960)]

def originalTerm1038 : Integer.Sparse OriginalKey := [(Sum.inl 2739, 22954528800)]

def originalTerm1039 : Integer.Sparse OriginalKey := [(Sum.inl 2740, -16921996800)]

def originalTerm1040 : Integer.Sparse OriginalKey := [(Sum.inl 2741, 576339384000)]

def originalTerm1041 : Integer.Sparse OriginalKey := [(Sum.inl 2742, 1237971955200)]

def originalTerm1042 : Integer.Sparse OriginalKey := [(Sum.inl 2743, 293832765600)]

def originalTerm1043 : Integer.Sparse OriginalKey := [(Sum.inl 2744, -611218105920)]

def originalTerm1044 : Integer.Sparse OriginalKey := [(Sum.inl 2745, -138282408000)]

def originalTerm1045 : Integer.Sparse OriginalKey := [(Sum.inl 2746, 138282408000)]

def originalTerm1046 : Integer.Sparse OriginalKey := [(Sum.inl 2747, -35781227520)]

def originalTerm1047 : Integer.Sparse OriginalKey := [(Sum.inl 2748, -90568526400)]

def originalTerm1048 : Integer.Sparse OriginalKey := [(Sum.inl 2750, 743788045680)]

def originalTerm1049 : Integer.Sparse OriginalKey := [(Sum.inl 2751, -751074989040)]

def originalTerm1050 : Integer.Sparse OriginalKey := [(Sum.inl 2753, -13849411200)]

def originalTerm1051 : Integer.Sparse OriginalKey := [(Sum.inl 2754, -131482856160)]

def originalTerm1052 : Integer.Sparse OriginalKey := [(Sum.inl 2755, 20120762880)]

def originalTerm1053 : Integer.Sparse OriginalKey := [(Sum.inl 2758, -215087481600)]

def originalTerm1054 : Integer.Sparse OriginalKey := [(Sum.inl 2759, -197879966400)]

def originalTerm1055 : Integer.Sparse OriginalKey := [(Sum.inl 2760, -11068343040)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1056 : Integer.Sparse OriginalKey := [(Sum.inl 2761, -27005613120)]

def originalTerm1057 : Integer.Sparse OriginalKey := [(Sum.inl 2763, -583548982560)]

def originalTerm1058 : Integer.Sparse OriginalKey := [(Sum.inl 2764, -633815145600)]

def originalTerm1059 : Integer.Sparse OriginalKey := [(Sum.inl 2765, 253382452800)]

def originalTerm1060 : Integer.Sparse OriginalKey := [(Sum.inl 2769, -605447161920)]

def originalTerm1061 : Integer.Sparse OriginalKey := [(Sum.inl 2771, -28722546720)]

def originalTerm1062 : Integer.Sparse OriginalKey := [(Sum.inl 2773, -204146488080)]

def originalTerm1063 : Integer.Sparse OriginalKey := [(Sum.inl 2774, 124653740400)]

def originalTerm1064 : Integer.Sparse OriginalKey := [(Sum.inl 2775, -14971544880)]

def originalTerm1065 : Integer.Sparse OriginalKey := [(Sum.inl 2776, -98609141760)]

def originalTerm1066 : Integer.Sparse OriginalKey := [(Sum.inl 2777, -125306354880)]

def originalTerm1067 : Integer.Sparse OriginalKey := [(Sum.inl 2778, -32302062720)]

def originalTerm1068 : Integer.Sparse OriginalKey := [(Sum.inl 2779, 27361002240)]

def originalTerm1069 : Integer.Sparse OriginalKey := [(Sum.inl 2780, -5820135840)]

def originalTerm1070 : Integer.Sparse OriginalKey := [(Sum.inl 2781, -259394784480)]

def originalTerm1071 : Integer.Sparse OriginalKey := [(Sum.inl 2782, -763917096000)]

def originalTerm1072 : Integer.Sparse OriginalKey := [(Sum.inl 2783, -327741403200)]

def originalTerm1073 : Integer.Sparse OriginalKey := [(Sum.inl 2789, -365301578880)]

def originalTerm1074 : Integer.Sparse OriginalKey := [(Sum.inl 2797, 287508036000)]

def originalTerm1075 : Integer.Sparse OriginalKey := [(Sum.inl 2798, -179487304800)]

def originalTerm1076 : Integer.Sparse OriginalKey := [(Sum.inl 2800, -106209801600)]

def originalTerm1077 : Integer.Sparse OriginalKey := [(Sum.inl 2801, -35637960000)]

def originalTerm1078 : Integer.Sparse OriginalKey := [(Sum.inl 2802, 127746492000)]

def originalTerm1079 : Integer.Sparse OriginalKey := [(Sum.inl 2803, 203471083200)]

def originalTerm1080 : Integer.Sparse OriginalKey := [(Sum.inl 2806, 11057040000)]

def originalTerm1081 : Integer.Sparse OriginalKey := [(Sum.inl 2807, 254279791200)]

def originalTerm1082 : Integer.Sparse OriginalKey := [(Sum.inl 2809, -43950276000)]

def originalTerm1083 : Integer.Sparse OriginalKey := [(Sum.inl 2810, -54492343200)]

def originalTerm1084 : Integer.Sparse OriginalKey := [(Sum.inl 2811, -91306568800)]

def originalTerm1085 : Integer.Sparse OriginalKey := [(Sum.inl 2812, 202893460800)]

def originalTerm1086 : Integer.Sparse OriginalKey := [(Sum.inl 2813, -15686486400)]

def originalTerm1087 : Integer.Sparse OriginalKey := [(Sum.inl 2814, -119057990400)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1088 : Integer.Sparse OriginalKey := [(Sum.inl 2815, 133211174400)]

def originalTerm1089 : Integer.Sparse OriginalKey := [(Sum.inl 2816, 26576592000)]

def originalTerm1090 : Integer.Sparse OriginalKey := [(Sum.inl 2817, -211901673600)]

def originalTerm1091 : Integer.Sparse OriginalKey := [(Sum.inl 2818, -153571207200)]

def originalTerm1092 : Integer.Sparse OriginalKey := [(Sum.inl 2819, 238183840000)]

def originalTerm1093 : Integer.Sparse OriginalKey := [(Sum.inl 2820, 33886166400)]

def originalTerm1094 : Integer.Sparse OriginalKey := [(Sum.inl 2821, -60127800000)]

def originalTerm1095 : Integer.Sparse OriginalKey := [(Sum.inl 2824, -308807652000)]

def originalTerm1096 : Integer.Sparse OriginalKey := [(Sum.inl 2826, -276589620000)]

def originalTerm1097 : Integer.Sparse OriginalKey := [(Sum.inl 2827, 165823320000)]

def originalTerm1098 : Integer.Sparse OriginalKey := [(Sum.inl 2846, 55524372000)]

def originalTerm1099 : Integer.Sparse OriginalKey := [(Sum.inl 2847, 150460056000)]

def originalTerm1100 : Integer.Sparse OriginalKey := [(Sum.inl 2848, -138074949600)]

def originalTerm1101 : Integer.Sparse OriginalKey := [(Sum.inl 2861, -91575132000)]

def originalTerm1102 : Integer.Sparse OriginalKey := [(Sum.inl 2862, -93724876800)]

def originalTerm1103 : Integer.Sparse OriginalKey := [(Sum.inl 2864, 35637960000)]

def originalTerm1104 : Integer.Sparse OriginalKey := [(Sum.inl 2865, -565714584000)]

def originalTerm1105 : Integer.Sparse OriginalKey := [(Sum.inl 2867, -178862902400)]

def originalTerm1106 : Integer.Sparse OriginalKey := [(Sum.inl 2868, 93724876800)]

def originalTerm1107 : Integer.Sparse OriginalKey := [(Sum.inl 2878, 265173914400)]

def originalTerm1108 : Integer.Sparse OriginalKey := [(Sum.inl 2879, -11057040000)]

def originalTerm1109 : Integer.Sparse OriginalKey := [(Sum.inl 2880, -47344773600)]

def originalTerm1110 : Integer.Sparse OriginalKey := [(Sum.inl 2881, 92224408800)]

def originalTerm1111 : Integer.Sparse OriginalKey := [(Sum.inl 2882, -265173914400)]

def originalTerm1112 : Integer.Sparse OriginalKey := [(Sum.inl 2884, 244866256800)]

def originalTerm1113 : Integer.Sparse OriginalKey := [(Sum.inl 2885, -104581640000)]

def originalTerm1114 : Integer.Sparse OriginalKey := [(Sum.inl 2886, 91306568800)]

def originalTerm1115 : Integer.Sparse OriginalKey := [(Sum.inl 2888, 220756252800)]

def originalTerm1116 : Integer.Sparse OriginalKey := [(Sum.inl 2889, 72408883200)]

def originalTerm1117 : Integer.Sparse OriginalKey := [(Sum.inl 2890, 36039360000)]

def originalTerm1118 : Integer.Sparse OriginalKey := [(Sum.inl 2892, 174490872000)]

def originalTerm1119 : Integer.Sparse OriginalKey := [(Sum.inl 2893, -28094251200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1120 : Integer.Sparse OriginalKey := [(Sum.inl 2895, -135693849600)]

def originalTerm1121 : Integer.Sparse OriginalKey := [(Sum.inl 2896, 104904806400)]

def originalTerm1122 : Integer.Sparse OriginalKey := [(Sum.inl 2898, -150460056000)]

def originalTerm1123 : Integer.Sparse OriginalKey := [(Sum.inl 2899, -259488537600)]

def originalTerm1124 : Integer.Sparse OriginalKey := [(Sum.inl 2900, 441407308000)]

def originalTerm1125 : Integer.Sparse OriginalKey := [(Sum.inl 2902, 364269600000)]

def originalTerm1126 : Integer.Sparse OriginalKey := [(Sum.inl 2916, -73295844000)]

def originalTerm1127 : Integer.Sparse OriginalKey := [(Sum.inl 2923, -9559209600)]

def originalTerm1128 : Integer.Sparse OriginalKey := [(Sum.inl 2924, 513032702400)]

def originalTerm1129 : Integer.Sparse OriginalKey := [(Sum.inl 2925, 183177100800)]

def originalTerm1130 : Integer.Sparse OriginalKey := [(Sum.inl 2928, 548480232000)]

def originalTerm1131 : Integer.Sparse OriginalKey := [(Sum.inl 2930, 171084873600)]

def originalTerm1132 : Integer.Sparse OriginalKey := [(Sum.inl 2931, 22050720000)]

def originalTerm1133 : Integer.Sparse OriginalKey := [(Sum.inl 2933, -437942044000)]

def originalTerm1134 : Integer.Sparse OriginalKey := [(Sum.inl 2942, -223213320000)]

def originalTerm1135 : Integer.Sparse OriginalKey := [(Sum.inl 2951, 902604232000)]

def originalTerm1136 : Integer.Sparse OriginalKey := [(Sum.inl 2952, -15186216000)]

def originalTerm1137 : Integer.Sparse OriginalKey := [(Sum.inl 2954, -238115980800)]

def originalTerm1138 : Integer.Sparse OriginalKey := [(Sum.inl 2955, -1058610796000)]

def originalTerm1139 : Integer.Sparse OriginalKey := [(Sum.inl 2964, -321303240000)]

def originalTerm1140 : Integer.Sparse OriginalKey := [(Sum.inl 2967, -424402320000)]

def originalTerm1141 : Integer.Sparse OriginalKey := [(Sum.inl 2979, -11215868000)]

def originalTerm1142 : Integer.Sparse OriginalKey := [(Sum.inl 2981, 17804046000)]

def originalTerm1143 : Integer.Sparse OriginalKey := [(Sum.inl 2984, 404016036000)]

def originalTerm1144 : Integer.Sparse OriginalKey := [(Sum.inl 3016, -120295503360)]

def originalTerm1145 : Integer.Sparse OriginalKey := [(Sum.inl 3023, -154533336000)]

def originalTerm1146 : Integer.Sparse OriginalKey := [(Sum.inl 3024, 45165883200)]

def originalTerm1147 : Integer.Sparse OriginalKey := [(Sum.inl 3025, -97221541440)]

def originalTerm1148 : Integer.Sparse OriginalKey := [(Sum.inl 3029, -342433200000)]

def originalTerm1149 : Integer.Sparse OriginalKey := [(Sum.inl 3030, -112236528000)]

def originalTerm1150 : Integer.Sparse OriginalKey := [(Sum.inl 3031, 122193288000)]

def originalTerm1151 : Integer.Sparse OriginalKey := [(Sum.inl 3032, 58921608000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1152 : Integer.Sparse OriginalKey := [(Sum.inl 3033, -112964961600)]

def originalTerm1153 : Integer.Sparse OriginalKey := [(Sum.inl 3036, 99295567200)]

def originalTerm1154 : Integer.Sparse OriginalKey := [(Sum.inl 3037, -344023459680)]

def originalTerm1155 : Integer.Sparse OriginalKey := [(Sum.inl 3038, 385200446720)]

def originalTerm1156 : Integer.Sparse OriginalKey := [(Sum.inl 3039, 247558604640)]

def originalTerm1157 : Integer.Sparse OriginalKey := [(Sum.inl 3040, 24432720000)]

def originalTerm1158 : Integer.Sparse OriginalKey := [(Sum.inl 3043, -68829976800)]

def originalTerm1159 : Integer.Sparse OriginalKey := [(Sum.inl 3044, -433249929600)]

def originalTerm1160 : Integer.Sparse OriginalKey := [(Sum.inl 3045, 121312444800)]

def originalTerm1161 : Integer.Sparse OriginalKey := [(Sum.inl 3046, 89440963200)]

def originalTerm1162 : Integer.Sparse OriginalKey := [(Sum.inl 3050, -117060177600)]

def originalTerm1163 : Integer.Sparse OriginalKey := [(Sum.inl 3051, 103819235840)]

def originalTerm1164 : Integer.Sparse OriginalKey := [(Sum.inl 3052, 211781925600)]

def originalTerm1165 : Integer.Sparse OriginalKey := [(Sum.inl 3053, -126760111200)]

def originalTerm1166 : Integer.Sparse OriginalKey := [(Sum.inl 3054, -169689468000)]

def originalTerm1167 : Integer.Sparse OriginalKey := [(Sum.inl 3055, 445281642400)]

def originalTerm1168 : Integer.Sparse OriginalKey := [(Sum.inl 3056, -107705304000)]

def originalTerm1169 : Integer.Sparse OriginalKey := [(Sum.inl 3058, 6893352000)]

def originalTerm1170 : Integer.Sparse OriginalKey := [(Sum.inl 3059, -49229709120)]

def originalTerm1171 : Integer.Sparse OriginalKey := [(Sum.inl 3062, -122193288000)]

def originalTerm1172 : Integer.Sparse OriginalKey := [(Sum.inl 3064, 195377116560)]

def originalTerm1173 : Integer.Sparse OriginalKey := [(Sum.inl 3065, 56050878720)]

def originalTerm1174 : Integer.Sparse OriginalKey := [(Sum.inl 3066, -149904950400)]

def originalTerm1175 : Integer.Sparse OriginalKey := [(Sum.inl 3068, -213921720000)]

def originalTerm1176 : Integer.Sparse OriginalKey := [(Sum.inl 3069, 44352960000)]

def originalTerm1177 : Integer.Sparse OriginalKey := [(Sum.inl 3073, 106869931200)]

def originalTerm1178 : Integer.Sparse OriginalKey := [(Sum.inl 3074, 413218543920)]

def originalTerm1179 : Integer.Sparse OriginalKey := [(Sum.inl 3075, -45627632640)]

def originalTerm1180 : Integer.Sparse OriginalKey := [(Sum.inl 3077, -434129625600)]

def originalTerm1181 : Integer.Sparse OriginalKey := [(Sum.inl 3078, 493361024400)]

def originalTerm1182 : Integer.Sparse OriginalKey := [(Sum.inl 3079, -326874033600)]

def originalTerm1183 : Integer.Sparse OriginalKey := [(Sum.inl 3083, -37634400000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1184 : Integer.Sparse OriginalKey := [(Sum.inl 3084, -1353997411200)]

def originalTerm1185 : Integer.Sparse OriginalKey := [(Sum.inl 3085, -133432956720)]

def originalTerm1186 : Integer.Sparse OriginalKey := [(Sum.inl 3086, -594078321600)]

def originalTerm1187 : Integer.Sparse OriginalKey := [(Sum.inl 3087, -101300161920)]

def originalTerm1188 : Integer.Sparse OriginalKey := [(Sum.inl 3088, -37712037120)]

def originalTerm1189 : Integer.Sparse OriginalKey := [(Sum.inl 3089, -150591744000)]

def originalTerm1190 : Integer.Sparse OriginalKey := [(Sum.inl 3092, -103421880000)]

def originalTerm1191 : Integer.Sparse OriginalKey := [(Sum.inl 3096, -286243718400)]

def originalTerm1192 : Integer.Sparse OriginalKey := [(Sum.inl 3097, 620022200400)]

def originalTerm1193 : Integer.Sparse OriginalKey := [(Sum.inl 3098, 914463197760)]

def originalTerm1194 : Integer.Sparse OriginalKey := [(Sum.inl 3099, -251656662720)]

def originalTerm1195 : Integer.Sparse OriginalKey := [(Sum.inl 3103, -72728407680)]

def originalTerm1196 : Integer.Sparse OriginalKey := [(Sum.inl 3108, 335499408000)]

def originalTerm1197 : Integer.Sparse OriginalKey := [(Sum.inl 3109, 265571789520)]

def originalTerm1198 : Integer.Sparse OriginalKey := [(Sum.inl 3110, 56641899840)]

def originalTerm1199 : Integer.Sparse OriginalKey := [(Sum.inl 3111, 201453184320)]

def originalTerm1200 : Integer.Sparse OriginalKey := [(Sum.inl 3112, 283262044320)]

def originalTerm1201 : Integer.Sparse OriginalKey := [(Sum.inl 3113, 99197019360)]

def originalTerm1202 : Integer.Sparse OriginalKey := [(Sum.inl 3114, 203623850880)]

def originalTerm1203 : Integer.Sparse OriginalKey := [(Sum.inl 3118, 179373787200)]

def originalTerm1204 : Integer.Sparse OriginalKey := [(Sum.inl 3119, 342434731440)]

def originalTerm1205 : Integer.Sparse OriginalKey := [(Sum.inl 3125, 10032668640)]

def originalTerm1206 : Integer.Sparse OriginalKey := [(Sum.inl 3127, -72062251200)]

def originalTerm1207 : Integer.Sparse OriginalKey := [(Sum.inl 3128, -21651192000)]

def originalTerm1208 : Integer.Sparse OriginalKey := [(Sum.inl 3129, -171148118400)]

def originalTerm1209 : Integer.Sparse OriginalKey := [(Sum.inl 3130, -76525828800)]

def originalTerm1210 : Integer.Sparse OriginalKey := [(Sum.inl 3131, -425560963200)]

def originalTerm1211 : Integer.Sparse OriginalKey := [(Sum.inl 3132, 21651192000)]

def originalTerm1212 : Integer.Sparse OriginalKey := [(Sum.inl 3133, -16387202400)]

def originalTerm1213 : Integer.Sparse OriginalKey := [(Sum.inl 3134, 251729265600)]

def originalTerm1214 : Integer.Sparse OriginalKey := [(Sum.inl 3136, 184248835200)]

def originalTerm1215 : Integer.Sparse OriginalKey := [(Sum.inl 3137, 133529400000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1216 : Integer.Sparse OriginalKey := [(Sum.inl 3138, 219537662400)]

def originalTerm1217 : Integer.Sparse OriginalKey := [(Sum.inl 3155, 79620278400)]

def originalTerm1218 : Integer.Sparse OriginalKey := [(Sum.inl 3156, -115587273600)]

def originalTerm1219 : Integer.Sparse OriginalKey := [(Sum.inl 3158, -79620278400)]

def originalTerm1220 : Integer.Sparse OriginalKey := [(Sum.inl 3161, 13808236800)]

def originalTerm1221 : Integer.Sparse OriginalKey := [(Sum.inl 3162, -166399216800)]

def originalTerm1222 : Integer.Sparse OriginalKey := [(Sum.inl 3163, 285355459200)]

def originalTerm1223 : Integer.Sparse OriginalKey := [(Sum.inl 3164, -254624500800)]

def originalTerm1224 : Integer.Sparse OriginalKey := [(Sum.inl 3170, 177138796800)]

def originalTerm1225 : Integer.Sparse OriginalKey := [(Sum.inl 3172, 254624500800)]

def originalTerm1226 : Integer.Sparse OriginalKey := [(Sum.inl 3174, -289204118400)]

def originalTerm1227 : Integer.Sparse OriginalKey := [(Sum.inl 3179, -233168486400)]

def originalTerm1228 : Integer.Sparse OriginalKey := [(Sum.inl 3180, -232689249600)]

def originalTerm1229 : Integer.Sparse OriginalKey := [(Sum.inl 3189, -31225200000)]

def originalTerm1230 : Integer.Sparse OriginalKey := [(Sum.inl 3196, 171867772800)]

def originalTerm1231 : Integer.Sparse OriginalKey := [(Sum.inl 3197, 50477025600)]

def originalTerm1232 : Integer.Sparse OriginalKey := [(Sum.inl 3198, 11144980800)]

def originalTerm1233 : Integer.Sparse OriginalKey := [(Sum.inl 3199, 183257613600)]

def originalTerm1234 : Integer.Sparse OriginalKey := [(Sum.inl 3202, 305008488000)]

def originalTerm1235 : Integer.Sparse OriginalKey := [(Sum.inl 3221, -344232948000)]

def originalTerm1236 : Integer.Sparse OriginalKey := [(Sum.inl 3222, -330612941280)]

def originalTerm1237 : Integer.Sparse OriginalKey := [(Sum.inl 3223, 107838659520)]

def originalTerm1238 : Integer.Sparse OriginalKey := [(Sum.inl 3224, 87094242240)]

def originalTerm1239 : Integer.Sparse OriginalKey := [(Sum.inl 3225, 45781599360)]

def originalTerm1240 : Integer.Sparse OriginalKey := [(Sum.inl 3226, -124558584240)]

def originalTerm1241 : Integer.Sparse OriginalKey := [(Sum.inl 3227, -76639881600)]

def originalTerm1242 : Integer.Sparse OriginalKey := [(Sum.inl 3228, 210077351040)]

def originalTerm1243 : Integer.Sparse OriginalKey := [(Sum.inl 3229, 668295156480)]

def originalTerm1244 : Integer.Sparse OriginalKey := [(Sum.inl 3230, 241012249680)]

def originalTerm1245 : Integer.Sparse OriginalKey := [(Sum.inl 3231, 65728133040)]

def originalTerm1246 : Integer.Sparse OriginalKey := [(Sum.inl 3255, 35377008000)]

def originalTerm1247 : Integer.Sparse OriginalKey := [(Sum.inl 3257, 157695480000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1248 : Integer.Sparse OriginalKey := [(Sum.inl 3258, -40719267600)]

def originalTerm1249 : Integer.Sparse OriginalKey := [(Sum.inl 3259, 243375339360)]

def originalTerm1250 : Integer.Sparse OriginalKey := [(Sum.inl 3260, 31432458400)]

def originalTerm1251 : Integer.Sparse OriginalKey := [(Sum.inl 3261, 7199256000)]

def originalTerm1252 : Integer.Sparse OriginalKey := [(Sum.inl 3262, 52615829600)]

def originalTerm1253 : Integer.Sparse OriginalKey := [(Sum.inl 3266, 102678513360)]

def originalTerm1254 : Integer.Sparse OriginalKey := [(Sum.inl 3267, 1433009600)]

def originalTerm1255 : Integer.Sparse OriginalKey := [(Sum.inl 3268, -58605475120)]

def originalTerm1256 : Integer.Sparse OriginalKey := [(Sum.inl 3271, -54920555760)]

def originalTerm1257 : Integer.Sparse OriginalKey := [(Sum.inl 3272, -26370487200)]

def originalTerm1258 : Integer.Sparse OriginalKey := [(Sum.inl 3288, 8108915200)]

def originalTerm1259 : Integer.Sparse OriginalKey := [(Sum.inl 3289, 70553501600)]

def originalTerm1260 : Integer.Sparse OriginalKey := [(Sum.inl 3290, 43032888000)]

def originalTerm1261 : Integer.Sparse OriginalKey := [(Sum.inl 3291, -40438979200)]

def originalTerm1262 : Integer.Sparse OriginalKey := [(Sum.inl 3294, -237790906400)]

def originalTerm1263 : Integer.Sparse OriginalKey := [(Sum.inl 3295, -100719111680)]

def originalTerm1264 : Integer.Sparse OriginalKey := [(Sum.inl 3296, -253480263520)]

def originalTerm1265 : Integer.Sparse OriginalKey := [(Sum.inl 3297, -50232144000)]

def originalTerm1266 : Integer.Sparse OriginalKey := [(Sum.inl 3298, 20010395440)]

def originalTerm1267 : Integer.Sparse OriginalKey := [(Sum.inl 3302, -36934020800)]

def originalTerm1268 : Integer.Sparse OriginalKey := [(Sum.inl 3303, -15029351280)]

def originalTerm1269 : Integer.Sparse OriginalKey := [(Sum.inl 3306, -4970178000)]

def originalTerm1270 : Integer.Sparse OriginalKey := [(Sum.inl 3365, 119640744000)]

def originalTerm1271 : Integer.Sparse OriginalKey := [(Sum.inl 3375, 17391009600)]

def originalTerm1272 : Integer.Sparse OriginalKey := [(Sum.inl 3376, -125853436800)]

def originalTerm1273 : Integer.Sparse OriginalKey := [(Sum.inl 3378, 131191286400)]

def originalTerm1274 : Integer.Sparse OriginalKey := [(Sum.inl 3379, -10091366400)]

def originalTerm1275 : Integer.Sparse OriginalKey := [(Sum.inl 3380, 65186582400)]

def originalTerm1276 : Integer.Sparse OriginalKey := [(Sum.inl 3388, 758620800)]

def originalTerm1277 : Integer.Sparse OriginalKey := [(Sum.inl 3390, -64490198400)]

def originalTerm1278 : Integer.Sparse OriginalKey := [(Sum.inl 3391, -104066668800)]

def originalTerm1279 : Integer.Sparse OriginalKey := [(Sum.inl 3392, -1517241600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm128 : Integer.Sparse OriginalKey := [(Sum.inl 181, 107818617600)]

def originalTerm129 : Integer.Sparse OriginalKey := [(Sum.inl 182, 240426432000)]

def originalTerm130 : Integer.Sparse OriginalKey := [(Sum.inl 183, 11384424000)]

def originalTerm131 : Integer.Sparse OriginalKey := [(Sum.inl 184, -39027840000)]

def originalTerm132 : Integer.Sparse OriginalKey := [(Sum.inl 185, -47681049600)]

def originalTerm133 : Integer.Sparse OriginalKey := [(Sum.inl 186, -49336550400)]

def originalTerm134 : Integer.Sparse OriginalKey := [(Sum.inl 187, -151369243200)]

def originalTerm135 : Integer.Sparse OriginalKey := [(Sum.inl 188, -18134899200)]

def originalTerm136 : Integer.Sparse OriginalKey := [(Sum.inl 189, -8433043200)]

def originalTerm137 : Integer.Sparse OriginalKey := [(Sum.inl 190, 8433043200)]

def originalTerm138 : Integer.Sparse OriginalKey := [(Sum.inl 191, 165345336000)]

def originalTerm139 : Integer.Sparse OriginalKey := [(Sum.inl 192, 198414403200)]

def originalTerm140 : Integer.Sparse OriginalKey := [(Sum.inl 193, 75033744000)]

def originalTerm141 : Integer.Sparse OriginalKey := [(Sum.inl 194, -2725992000)]

def originalTerm142 : Integer.Sparse OriginalKey := [(Sum.inl 195, -198414403200)]

def originalTerm143 : Integer.Sparse OriginalKey := [(Sum.inl 196, -87279115200)]

def originalTerm144 : Integer.Sparse OriginalKey := [(Sum.inl 197, -165345336000)]

def originalTerm145 : Integer.Sparse OriginalKey := [(Sum.inl 207, -56669328000)]

def originalTerm146 : Integer.Sparse OriginalKey := [(Sum.inl 208, -61895664000)]

def originalTerm147 : Integer.Sparse OriginalKey := [(Sum.inl 209, 31703544000)]

def originalTerm148 : Integer.Sparse OriginalKey := [(Sum.inl 210, 56534784000)]

def originalTerm149 : Integer.Sparse OriginalKey := [(Sum.inl 211, -422812800)]

def originalTerm150 : Integer.Sparse OriginalKey := [(Sum.inl 212, -66564864000)]

def originalTerm151 : Integer.Sparse OriginalKey := [(Sum.inl 213, 66564864000)]

def originalTerm152 : Integer.Sparse OriginalKey := [(Sum.inl 214, 7706640000)]

def originalTerm153 : Integer.Sparse OriginalKey := [(Sum.inl 218, -58574232000)]

def originalTerm154 : Integer.Sparse OriginalKey := [(Sum.inl 220, 6801955200)]

def originalTerm155 : Integer.Sparse OriginalKey := [(Sum.inl 221, -4937275200)]

def originalTerm156 : Integer.Sparse OriginalKey := [(Sum.inl 222, -6801955200)]

def originalTerm157 : Integer.Sparse OriginalKey := [(Sum.inl 223, -30264364800)]

def originalTerm158 : Integer.Sparse OriginalKey := [(Sum.inl 224, 52809926400)]

def originalTerm159 : Integer.Sparse OriginalKey := [(Sum.inl 225, 130712227200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1280 : Integer.Sparse OriginalKey := [(Sum.inl 3394, 173892648000)]

def originalTerm1281 : Integer.Sparse OriginalKey := [(Sum.inl 3395, 437319643200)]

def originalTerm1282 : Integer.Sparse OriginalKey := [(Sum.inl 3396, 277508563200)]

def originalTerm1283 : Integer.Sparse OriginalKey := [(Sum.inl 3397, -18187924800)]

def originalTerm1284 : Integer.Sparse OriginalKey := [(Sum.inl 3406, 17356137600)]

def originalTerm1285 : Integer.Sparse OriginalKey := [(Sum.inl 3407, 88892606880)]

def originalTerm1286 : Integer.Sparse OriginalKey := [(Sum.inl 3408, -52770777840)]

def originalTerm1287 : Integer.Sparse OriginalKey := [(Sum.inl 3413, -79464541920)]

def originalTerm1288 : Integer.Sparse OriginalKey := [(Sum.inl 3414, 9446714880)]

def originalTerm1289 : Integer.Sparse OriginalKey := [(Sum.inl 3415, -41463295200)]

def originalTerm1290 : Integer.Sparse OriginalKey := [(Sum.inl 3418, -9428064960)]

def originalTerm1291 : Integer.Sparse OriginalKey := [(Sum.inl 3419, 21662031480)]

def originalTerm1292 : Integer.Sparse OriginalKey := [(Sum.inl 3451, 19791401920)]

def originalTerm1293 : Integer.Sparse OriginalKey := [(Sum.inl 3452, 127146274400)]

def originalTerm1294 : Integer.Sparse OriginalKey := [(Sum.inl 3454, 154383516080)]

def originalTerm1295 : Integer.Sparse OriginalKey := [(Sum.inl 3458, 617189760)]

def originalTerm1296 : Integer.Sparse OriginalKey := [(Sum.inl 3461, 59248431360)]

def originalTerm1297 : Integer.Sparse OriginalKey := [(Sum.inl 3462, -63013829520)]

def originalTerm1298 : Integer.Sparse OriginalKey := [(Sum.inl 3463, -81494870640)]

def originalTerm1299 : Integer.Sparse OriginalKey := [(Sum.inl 3464, 81289141200)]

def originalTerm1300 : Integer.Sparse OriginalKey := [(Sum.inl 3465, -19207074240)]

def originalTerm1301 : Integer.Sparse OriginalKey := [(Sum.inl 3466, -96553292760)]

def originalTerm1302 : Integer.Sparse OriginalKey := [(Sum.inl 3472, 13467990040)]

def originalTerm1303 : Integer.Sparse OriginalKey := [(Sum.inl 3474, -48784844320)]

def originalTerm1304 : Integer.Sparse OriginalKey := [(Sum.inl 3475, -123152322240)]

def originalTerm1305 : Integer.Sparse OriginalKey := [(Sum.inl 3476, 49355278560)]

def originalTerm1306 : Integer.Sparse OriginalKey := [(Sum.inl 3480, -125635036160)]

def originalTerm1307 : Integer.Sparse OriginalKey := [(Sum.inl 3488, -11057040000)]

def originalTerm1308 : Integer.Sparse OriginalKey := [(Sum.inl 3493, 131802278400)]

def originalTerm1309 : Integer.Sparse OriginalKey := [(Sum.inl 3496, -215124470400)]

def originalTerm1310 : Integer.Sparse OriginalKey := [(Sum.inl 3497, -11057040000)]

def originalTerm1311 : Integer.Sparse OriginalKey := [(Sum.inl 3505, 207316608000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1312 : Integer.Sparse OriginalKey := [(Sum.inl 3506, -83633539200)]

def originalTerm1313 : Integer.Sparse OriginalKey := [(Sum.inl 3508, -37788363200)]

def originalTerm1314 : Integer.Sparse OriginalKey := [(Sum.inl 3509, 196428243600)]

def originalTerm1315 : Integer.Sparse OriginalKey := [(Sum.inl 3510, -35377008000)]

def originalTerm1316 : Integer.Sparse OriginalKey := [(Sum.inl 3511, -7199256000)]

def originalTerm1317 : Integer.Sparse OriginalKey := [(Sum.inl 3512, -83506716880)]

def originalTerm1318 : Integer.Sparse OriginalKey := [(Sum.inl 3516, 43761661600)]

def originalTerm1319 : Integer.Sparse OriginalKey := [(Sum.inl 3517, 80585042800)]

def originalTerm1320 : Integer.Sparse OriginalKey := [(Sum.inl 3519, -13314241320)]

def originalTerm1321 : Integer.Sparse OriginalKey := [(Sum.inl 3523, -326780164000)]

def originalTerm1322 : Integer.Sparse OriginalKey := [(Sum.inl 3524, -28513415680)]

def originalTerm1323 : Integer.Sparse OriginalKey := [(Sum.inl 3525, -185802336000)]

def originalTerm1324 : Integer.Sparse OriginalKey := [(Sum.inl 3526, -235138300640)]

def originalTerm1325 : Integer.Sparse OriginalKey := [(Sum.inl 3529, 64629576000)]

def originalTerm1326 : Integer.Sparse OriginalKey := [(Sum.inl 3530, 174324349120)]

def originalTerm1327 : Integer.Sparse OriginalKey := [(Sum.inl 3532, -42494037600)]

def originalTerm1328 : Integer.Sparse OriginalKey := [(Sum.inl 3533, -52501420800)]

def originalTerm1329 : Integer.Sparse OriginalKey := [(Sum.inl 3534, 693987007200)]

def originalTerm1330 : Integer.Sparse OriginalKey := [(Sum.inl 3535, 119379766880)]

def originalTerm1331 : Integer.Sparse OriginalKey := [(Sum.inl 3537, 204626146720)]

def originalTerm1332 : Integer.Sparse OriginalKey := [(Sum.inl 3538, 33295886240)]

def originalTerm1333 : Integer.Sparse OriginalKey := [(Sum.inl 3539, 175162246560)]

def originalTerm1334 : Integer.Sparse OriginalKey := [(Sum.inl 3540, 11771431440)]

def originalTerm1335 : Integer.Sparse OriginalKey := [(Sum.inl 3541, -71326750320)]

def originalTerm1336 : Integer.Sparse OriginalKey := [(Sum.inl 3542, -38223245760)]

def originalTerm1337 : Integer.Sparse OriginalKey := [(Sum.inl 3543, -104902735560)]

def originalTerm1338 : Integer.Sparse OriginalKey := [(Sum.inl 3544, -66142569600)]

def originalTerm1339 : Integer.Sparse OriginalKey := [(Sum.inl 3547, -3010183200)]

def originalTerm1340 : Integer.Sparse OriginalKey := [(Sum.inl 3548, -27346305600)]

def originalTerm1341 : Integer.Sparse OriginalKey := [(Sum.inl 3549, 33377058600)]

def originalTerm1342 : Integer.Sparse OriginalKey := [(Sum.inl 3553, -30136375440)]

def originalTerm1343 : Integer.Sparse OriginalKey := [(Sum.inl 3554, -157695480000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1344 : Integer.Sparse OriginalKey := [(Sum.inl 3555, -152669552880)]

def originalTerm1345 : Integer.Sparse OriginalKey := [(Sum.inl 3556, -43730807040)]

def originalTerm1346 : Integer.Sparse OriginalKey := [(Sum.inl 3557, 23931771680)]

def originalTerm1347 : Integer.Sparse OriginalKey := [(Sum.inl 3558, 231346835120)]

def originalTerm1348 : Integer.Sparse OriginalKey := [(Sum.inl 3562, 79399260480)]

def originalTerm1349 : Integer.Sparse OriginalKey := [(Sum.inl 3565, 150261266320)]

def originalTerm1350 : Integer.Sparse OriginalKey := [(Sum.inl 3569, 52154399360)]

def originalTerm1351 : Integer.Sparse OriginalKey := [(Sum.inl 3570, 64669163520)]

def originalTerm1352 : Integer.Sparse OriginalKey := [(Sum.inl 3571, 343575113760)]

def originalTerm1353 : Integer.Sparse OriginalKey := [(Sum.inl 3572, -446481833760)]

def originalTerm1354 : Integer.Sparse OriginalKey := [(Sum.inl 3573, 524292833680)]

def originalTerm1355 : Integer.Sparse OriginalKey := [(Sum.inl 3577, 123035280000)]

def originalTerm1356 : Integer.Sparse OriginalKey := [(Sum.inl 3578, 371530090240)]

def originalTerm1357 : Integer.Sparse OriginalKey := [(Sum.inl 3579, 120925828800)]

def originalTerm1358 : Integer.Sparse OriginalKey := [(Sum.inl 3580, 22098329760)]

def originalTerm1359 : Integer.Sparse OriginalKey := [(Sum.inl 3581, -5860713600)]

def originalTerm1360 : Integer.Sparse OriginalKey := [(Sum.inl 3582, 110520960000)]

def originalTerm1361 : Integer.Sparse OriginalKey := [(Sum.inl 3583, -316463486400)]

def originalTerm1362 : Integer.Sparse OriginalKey := [(Sum.inl 3584, 771015003440)]

def originalTerm1363 : Integer.Sparse OriginalKey := [(Sum.inl 3618, 31183603200)]

def originalTerm1364 : Integer.Sparse OriginalKey := [(Sum.inl 3619, -242715326400)]

def originalTerm1365 : Integer.Sparse OriginalKey := [(Sum.inl 3622, 362631684000)]

def originalTerm1366 : Integer.Sparse OriginalKey := [(Sum.inl 3623, -167999978400)]

def originalTerm1367 : Integer.Sparse OriginalKey := [(Sum.inl 3625, 97942315200)]

def originalTerm1368 : Integer.Sparse OriginalKey := [(Sum.inl 3626, 136381392000)]

def originalTerm1369 : Integer.Sparse OriginalKey := [(Sum.inl 3627, 197158603200)]

def originalTerm1370 : Integer.Sparse OriginalKey := [(Sum.inl 3628, -168406603200)]

def originalTerm1371 : Integer.Sparse OriginalKey := [(Sum.inl 3629, -380873188800)]

def originalTerm1372 : Integer.Sparse OriginalKey := [(Sum.inl 3632, -95925950400)]

def originalTerm1373 : Integer.Sparse OriginalKey := [(Sum.inl 3633, 469532373600)]

def originalTerm1374 : Integer.Sparse OriginalKey := [(Sum.inl 3635, -160502640000)]

def originalTerm1375 : Integer.Sparse OriginalKey := [(Sum.inl 3636, -33658200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1376 : Integer.Sparse OriginalKey := [(Sum.inl 3670, -94575744000)]

def originalTerm1377 : Integer.Sparse OriginalKey := [(Sum.inl 3671, 75932044800)]

def originalTerm1378 : Integer.Sparse OriginalKey := [(Sum.inl 3672, 213430944000)]

def originalTerm1379 : Integer.Sparse OriginalKey := [(Sum.inl 3673, -55524372000)]

def originalTerm1380 : Integer.Sparse OriginalKey := [(Sum.inl 3674, -89725020000)]

def originalTerm1381 : Integer.Sparse OriginalKey := [(Sum.inl 3676, 56859332000)]

def originalTerm1382 : Integer.Sparse OriginalKey := [(Sum.inl 3685, -17804046000)]

def originalTerm1383 : Integer.Sparse OriginalKey := [(Sum.inl 3689, 134453524800)]

def originalTerm1384 : Integer.Sparse OriginalKey := [(Sum.inl 3690, -72141828000)]

def originalTerm1385 : Integer.Sparse OriginalKey := [(Sum.inl 3692, -138607665600)]

def originalTerm1386 : Integer.Sparse OriginalKey := [(Sum.inl 3693, -47134248000)]

def originalTerm1387 : Integer.Sparse OriginalKey := [(Sum.inl 3694, -141289116000)]

def originalTerm1388 : Integer.Sparse OriginalKey := [(Sum.inl 3698, 95986680000)]

def originalTerm1389 : Integer.Sparse OriginalKey := [(Sum.inl 3699, 87531428000)]

def originalTerm1390 : Integer.Sparse OriginalKey := [(Sum.inl 3703, -169533650400)]

def originalTerm1391 : Integer.Sparse OriginalKey := [(Sum.inl 3705, 236959730400)]

def originalTerm1392 : Integer.Sparse OriginalKey := [(Sum.inl 3706, -281822836800)]

def originalTerm1393 : Integer.Sparse OriginalKey := [(Sum.inl 3708, 615399480000)]

def originalTerm1394 : Integer.Sparse OriginalKey := [(Sum.inl 3709, 207807660000)]

def originalTerm1395 : Integer.Sparse OriginalKey := [(Sum.inl 3710, 96277519200)]

def originalTerm1396 : Integer.Sparse OriginalKey := [(Sum.inl 3715, 299006860800)]

def originalTerm1397 : Integer.Sparse OriginalKey := [(Sum.inl 3719, 196632660000)]

def originalTerm1398 : Integer.Sparse OriginalKey := [(Sum.inl 3720, 181583924400)]

def originalTerm1399 : Integer.Sparse OriginalKey := [(Sum.inl 3721, 344179303200)]

def originalTerm1400 : Integer.Sparse OriginalKey := [(Sum.inl 3722, -696839493600)]

def originalTerm1401 : Integer.Sparse OriginalKey := [(Sum.inl 3723, 82140595200)]

def originalTerm1402 : Integer.Sparse OriginalKey := [(Sum.inl 3724, -343718712000)]

def originalTerm1403 : Integer.Sparse OriginalKey := [(Sum.inl 3730, 13252084800)]

def originalTerm1404 : Integer.Sparse OriginalKey := [(Sum.inl 3731, -119057990400)]

def originalTerm1405 : Integer.Sparse OriginalKey := [(Sum.inl 3732, -420588835200)]

def originalTerm1406 : Integer.Sparse OriginalKey := [(Sum.inl 3733, 34600506000)]

def originalTerm1407 : Integer.Sparse OriginalKey := [(Sum.inl 3755, 23524214800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1408 : Integer.Sparse OriginalKey := [(Sum.inl 3759, -59248431360)]

def originalTerm1409 : Integer.Sparse OriginalKey := [(Sum.inl 3760, 206772988320)]

def originalTerm1410 : Integer.Sparse OriginalKey := [(Sum.inl 3761, -68621625840)]

def originalTerm1411 : Integer.Sparse OriginalKey := [(Sum.inl 3762, -92561695200)]

def originalTerm1412 : Integer.Sparse OriginalKey := [(Sum.inl 3763, 19207074240)]

def originalTerm1413 : Integer.Sparse OriginalKey := [(Sum.inl 3768, -16741642320)]

def originalTerm1414 : Integer.Sparse OriginalKey := [(Sum.inl 3772, -38735335280)]

def originalTerm1415 : Integer.Sparse OriginalKey := [(Sum.inl 3779, -618756636000)]

def originalTerm1416 : Integer.Sparse OriginalKey := [(Sum.inl 3780, 119432460000)]

def originalTerm1417 : Integer.Sparse OriginalKey := [(Sum.inl 3781, 46382980800)]

def originalTerm1418 : Integer.Sparse OriginalKey := [(Sum.inl 3782, -118356528000)]

def originalTerm1419 : Integer.Sparse OriginalKey := [(Sum.inl 3783, 33982476000)]

def originalTerm1420 : Integer.Sparse OriginalKey := [(Sum.inl 3786, 149531803200)]

def originalTerm1421 : Integer.Sparse OriginalKey := [(Sum.inl 3787, -435689292000)]

def originalTerm1422 : Integer.Sparse OriginalKey := [(Sum.inl 3788, 72775010400)]

def originalTerm1423 : Integer.Sparse OriginalKey := [(Sum.inl 3789, 38323598400)]

def originalTerm1424 : Integer.Sparse OriginalKey := [(Sum.inl 3800, 708338680000)]

def originalTerm1425 : Integer.Sparse OriginalKey := [(Sum.inl 3801, -350268487200)]

def originalTerm1426 : Integer.Sparse OriginalKey := [(Sum.inl 3802, -146618106000)]

def originalTerm1427 : Integer.Sparse OriginalKey := [(Sum.inl 3803, -184571517240)]

def originalTerm1428 : Integer.Sparse OriginalKey := [(Sum.inl 3805, 139812619200)]

def originalTerm1429 : Integer.Sparse OriginalKey := [(Sum.inl 3806, 17804046000)]

def originalTerm1430 : Integer.Sparse OriginalKey := [(Sum.inl 3807, 1132317305600)]

def originalTerm1431 : Integer.Sparse OriginalKey := [(Sum.inl 3808, 264601304000)]

def originalTerm1432 : Integer.Sparse OriginalKey := [(Sum.inl 3809, -758696139200)]

def originalTerm1433 : Integer.Sparse OriginalKey := [(Sum.inl 3812, 268433312400)]

def originalTerm1434 : Integer.Sparse OriginalKey := [(Sum.inl 3813, -848678449200)]

def originalTerm1435 : Integer.Sparse OriginalKey := [(Sum.inl 3814, -482207276000)]

def originalTerm1436 : Integer.Sparse OriginalKey := [(Sum.inl 3816, -47231206800)]

def originalTerm1437 : Integer.Sparse OriginalKey := [(Sum.inl 3817, 658070393200)]

def originalTerm1438 : Integer.Sparse OriginalKey := [(Sum.inl 3819, 55524372000)]

def originalTerm1439 : Integer.Sparse OriginalKey := [(Sum.inl 3826, -216104352000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1440 : Integer.Sparse OriginalKey := [(Sum.inl 3827, -724574936000)]

def originalTerm1441 : Integer.Sparse OriginalKey := [(Sum.inl 3832, 189092976800)]

def originalTerm1442 : Integer.Sparse OriginalKey := [(Sum.inl 3833, 1828358280)]

def originalTerm1443 : Integer.Sparse OriginalKey := [(Sum.inl 3834, 168484423920)]

def originalTerm1444 : Integer.Sparse OriginalKey := [(Sum.inl 3835, 50232144000)]

def originalTerm1445 : Integer.Sparse OriginalKey := [(Sum.inl 3837, -524285438400)]

def originalTerm1446 : Integer.Sparse OriginalKey := [(Sum.inl 3838, 484870084000)]

def originalTerm1447 : Integer.Sparse OriginalKey := [(Sum.inl 3839, 342342707440)]

def originalTerm1448 : Integer.Sparse OriginalKey := [(Sum.inl 3840, 838872379120)]

def originalTerm1449 : Integer.Sparse OriginalKey := [(Sum.inl 3841, -541060433280)]

def originalTerm1450 : Integer.Sparse OriginalKey := [(Sum.inl 3842, 38223245760)]

def originalTerm1451 : Integer.Sparse OriginalKey := [(Sum.inl 3843, 181484989200)]

def originalTerm1452 : Integer.Sparse OriginalKey := [(Sum.inl 3844, 17804046000)]

def originalTerm1453 : Integer.Sparse OriginalKey := [(Sum.inl 3845, -914200380400)]

def originalTerm1454 : Integer.Sparse OriginalKey := [(Sum.inl 3846, -322821933840)]

def originalTerm1455 : Integer.Sparse OriginalKey := [(Sum.inl 3847, -197314821280)]

def originalTerm1456 : Integer.Sparse OriginalKey := [(Sum.inl 3848, -263200062000)]

def originalTerm1457 : Integer.Sparse OriginalKey := [(Sum.inl 3849, -24616340400)]

def originalTerm1458 : Integer.Sparse OriginalKey := [(Sum.inl 3850, -212077721600)]

def originalTerm1459 : Integer.Sparse OriginalKey := [(Sum.inl 3854, -24238911880)]

def originalTerm1460 : Integer.Sparse OriginalKey := [(Sum.inl 3855, -148138448880)]

def originalTerm1461 : Integer.Sparse OriginalKey := [(Sum.inl 3856, -42546809360)]

def originalTerm1462 : Integer.Sparse OriginalKey := [(Sum.inl 3857, 126799420800)]

def originalTerm1463 : Integer.Sparse OriginalKey := [(Sum.inl 3866, 88699461120)]

def originalTerm1464 : Integer.Sparse OriginalKey := [(Sum.inl 3868, 90525826320)]

def originalTerm1465 : Integer.Sparse OriginalKey := [(Sum.inl 3869, -15685334800)]

def originalTerm1466 : Integer.Sparse OriginalKey := [(Sum.inl 3870, -55902749040)]

def originalTerm1467 : Integer.Sparse OriginalKey := [(Sum.inl 3871, 307088268400)]

def originalTerm1468 : Integer.Sparse OriginalKey := [(Sum.inl 3872, -157035924800)]

def originalTerm1469 : Integer.Sparse OriginalKey := [(Sum.inl 3873, -194784715600)]

def originalTerm1470 : Integer.Sparse OriginalKey := [(Sum.inl 3874, -105372182640)]

def originalTerm1471 : Integer.Sparse OriginalKey := [(Sum.inl 3875, -318033073200)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1472 : Integer.Sparse OriginalKey := [(Sum.inl 3876, -210083776800)]

def originalTerm1473 : Integer.Sparse OriginalKey := [(Sum.inl 3877, 177223146720)]

def originalTerm1474 : Integer.Sparse OriginalKey := [(Sum.inl 3880, 384714611200)]

def originalTerm1475 : Integer.Sparse OriginalKey := [(Sum.inl 3881, 8303689360)]

def originalTerm1476 : Integer.Sparse OriginalKey := [(Sum.inl 3882, -35940171360)]

def originalTerm1477 : Integer.Sparse OriginalKey := [(Sum.inl 3883, 332230229280)]

def originalTerm1478 : Integer.Sparse OriginalKey := [(Sum.inl 3884, 606630423920)]

def originalTerm1479 : Integer.Sparse OriginalKey := [(Sum.inl 3885, 217596428400)]

def originalTerm1480 : Integer.Sparse OriginalKey := [(Sum.inl 3886, 125789293600)]

def originalTerm1481 : Integer.Sparse OriginalKey := [(Sum.inl 3899, 256774710000)]

def originalTerm1482 : Integer.Sparse OriginalKey := [(Sum.inl 3901, -830998876800)]

def originalTerm1483 : Integer.Sparse OriginalKey := [(Sum.inl 3902, 141289116000)]

def originalTerm1484 : Integer.Sparse OriginalKey := [(Sum.inl 3903, -802636111200)]

def originalTerm1485 : Integer.Sparse OriginalKey := [(Sum.inl 3904, 188055000000)]

def originalTerm1486 : Integer.Sparse OriginalKey := [(Sum.inl 3905, 148702010400)]

def originalTerm1487 : Integer.Sparse OriginalKey := [(Sum.inl 3906, -183275148000)]

def originalTerm1488 : Integer.Sparse OriginalKey := [(Sum.inl 3907, 544735072800)]

def originalTerm1489 : Integer.Sparse OriginalKey := [(Sum.inl 3908, 173690028000)]

def originalTerm1490 : Integer.Sparse OriginalKey := [(Sum.inl 3909, -163224006000)]

def originalTerm1491 : Integer.Sparse OriginalKey := [(Sum.inl 3910, 369051456000)]

def originalTerm1492 : Integer.Sparse OriginalKey := [(Sum.inl 3913, 927484934400)]

def originalTerm1493 : Integer.Sparse OriginalKey := [(Sum.inl 3922, 93724876800)]

def originalTerm1494 : Integer.Sparse OriginalKey := [(Sum.inl 3945, -807270528000)]

def originalTerm1495 : Integer.Sparse OriginalKey := [(Sum.inl 3946, -154125170400)]

def originalTerm1496 : Integer.Sparse OriginalKey := [(Sum.inl 3949, -207319388000)]

def originalTerm1497 : Integer.Sparse OriginalKey := [(Sum.inl 3953, 875034992000)]

def originalTerm1498 : Integer.Sparse OriginalKey := [(Sum.inl 3954, 308430780160)]

def originalTerm1499 : Integer.Sparse OriginalKey := [(Sum.inl 3955, -96987695040)]

def originalTerm1500 : Integer.Sparse OriginalKey := [(Sum.inl 3956, 154125170400)]

def originalTerm1501 : Integer.Sparse OriginalKey := [(Sum.inl 3957, -270960944400)]

def originalTerm1502 : Integer.Sparse OriginalKey := [(Sum.inl 3958, -421788356000)]

def originalTerm1503 : Integer.Sparse OriginalKey := [(Sum.inl 3959, -607012113600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1504 : Integer.Sparse OriginalKey := [(Sum.inl 3960, 173815992000)]

def originalTerm1505 : Integer.Sparse OriginalKey := [(Sum.inl 3961, 246102416400)]

def originalTerm1506 : Integer.Sparse OriginalKey := [(Sum.inl 3962, 109392596400)]

def originalTerm1507 : Integer.Sparse OriginalKey := [(Sum.inl 3963, -336453507600)]

def originalTerm1508 : Integer.Sparse OriginalKey := [(Sum.inl 3964, -299102709600)]

def originalTerm1509 : Integer.Sparse OriginalKey := [(Sum.inl 3972, 234057866640)]

def originalTerm1510 : Integer.Sparse OriginalKey := [(Sum.inl 3973, 96987695040)]

def originalTerm1511 : Integer.Sparse OriginalKey := [(Sum.inl 3974, 1379766741600)]

def originalTerm1512 : Integer.Sparse OriginalKey := [(Sum.inl 3976, -237223925360)]

def originalTerm1513 : Integer.Sparse OriginalKey := [(Sum.inl 3977, -50798292400)]

def originalTerm1514 : Integer.Sparse OriginalKey := [(Sum.inl 3978, -505986436800)]

def originalTerm1515 : Integer.Sparse OriginalKey := [(Sum.inl 3983, -39488424000)]

def originalTerm1516 : Integer.Sparse OriginalKey := [(Sum.inl 3990, 125008758160)]

def originalTerm1517 : Integer.Sparse OriginalKey := [(Sum.inl 3993, 142392500640)]

def originalTerm1518 : Integer.Sparse OriginalKey := [(Sum.inl 3994, 270803687040)]

def originalTerm1519 : Integer.Sparse OriginalKey := [(Sum.inl 3995, 333485403280)]

def originalTerm1520 : Integer.Sparse OriginalKey := [(Sum.inl 3996, 154429053200)]

def originalTerm1521 : Integer.Sparse OriginalKey := [(Sum.inl 3997, 10674768960)]

def originalTerm1522 : Integer.Sparse OriginalKey := [(Sum.inl 4002, -159417459120)]

def originalTerm1523 : Integer.Sparse OriginalKey := [(Sum.inl 4003, 107635576120)]

def originalTerm1524 : Integer.Sparse OriginalKey := [(Sum.inl 4004, 277437109200)]

def originalTerm1525 : Integer.Sparse OriginalKey := [(Sum.inl 4005, -17377408080)]

def originalTerm1526 : Integer.Sparse OriginalKey := [(Sum.inl 4006, -234053418480)]

def originalTerm1527 : Integer.Sparse OriginalKey := [(Sum.inl 4008, 47344773600)]

def originalTerm1528 : Integer.Sparse OriginalKey := [(Sum.inl 4010, -1101001082400)]

def originalTerm1529 : Integer.Sparse OriginalKey := [(Sum.inl 4022, 326025590400)]

def originalTerm1530 : Integer.Sparse OriginalKey := [(Sum.inl 4024, 193923518160)]

def originalTerm1531 : Integer.Sparse OriginalKey := [(Sum.inl 4025, -179099749200)]

def originalTerm1532 : Integer.Sparse OriginalKey := [(Sum.inl 4026, -639056688240)]

def originalTerm1533 : Integer.Sparse OriginalKey := [(Sum.inl 4027, -114090427360)]

def originalTerm1534 : Integer.Sparse OriginalKey := [(Sum.inl 4028, -89793992040)]

def originalTerm1535 : Integer.Sparse OriginalKey := [(Sum.inl 4030, 97266550160)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1536 : Integer.Sparse OriginalKey := [(Sum.inl 4032, -201403157520)]

def originalTerm1537 : Integer.Sparse OriginalKey := [(Sum.inl 4034, 49300610520)]

def originalTerm1538 : Integer.Sparse OriginalKey := [(Sum.inl 4035, -364852742920)]

def originalTerm1539 : Integer.Sparse OriginalKey := [(Sum.inl 4038, -77879216040)]

def originalTerm1540 : Integer.Sparse OriginalKey := [(Sum.inl 4044, -68343328800)]

def originalTerm1541 : Integer.Sparse OriginalKey := [(Sum.inl 4046, -223478112000)]

def originalTerm1542 : Integer.Sparse OriginalKey := [(Sum.inl 4047, -101105690400)]

def originalTerm1543 : Integer.Sparse OriginalKey := [(Sum.inl 4048, 385046460000)]

def originalTerm1544 : Integer.Sparse OriginalKey := [(Sum.inl 4049, 120339007200)]

def originalTerm1545 : Integer.Sparse OriginalKey := [(Sum.inl 4083, 1088531700960)]

def originalTerm1546 : Integer.Sparse OriginalKey := [(Sum.inl 4084, 1517274716160)]

def originalTerm1547 : Integer.Sparse OriginalKey := [(Sum.inl 4085, 66834365760)]

def originalTerm1548 : Integer.Sparse OriginalKey := [(Sum.inl 4091, 1890211336560)]

def originalTerm1549 : Integer.Sparse OriginalKey := [(Sum.inl 4092, 2187808831520)]

def originalTerm1550 : Integer.Sparse OriginalKey := [(Sum.inl 4149, -112295040000)]

def originalTerm1551 : Integer.Sparse OriginalKey := [(Sum.inl 4150, -207460416000)]

def originalTerm1552 : Integer.Sparse OriginalKey := [(Sum.inl 4151, 112295040000)]

def originalTerm1553 : Integer.Sparse OriginalKey := [(Sum.inl 4152, -235057334400)]

def originalTerm1554 : Integer.Sparse OriginalKey := [(Sum.inl 4153, 29671128960)]

def originalTerm1555 : Integer.Sparse OriginalKey := [(Sum.inl 4154, -304345777920)]

def originalTerm1556 : Integer.Sparse OriginalKey := [(Sum.inl 4155, 207460416000)]

def originalTerm1557 : Integer.Sparse OriginalKey := [(Sum.inl 4156, 162893239680)]

def originalTerm1558 : Integer.Sparse OriginalKey := [(Sum.inl 4157, -12304784640)]

def originalTerm1559 : Integer.Sparse OriginalKey := [(Sum.inl 4158, 148667141760)]

def originalTerm1560 : Integer.Sparse OriginalKey := [(Sum.inl 4159, 54580154880)]

def originalTerm1561 : Integer.Sparse OriginalKey := [(Sum.inl 4160, 210315515520)]

def originalTerm1562 : Integer.Sparse OriginalKey := [(Sum.inl 4161, 396171185280)]

def originalTerm1563 : Integer.Sparse OriginalKey := [(Sum.inl 4162, -20242454400)]

def originalTerm1564 : Integer.Sparse OriginalKey := [(Sum.inl 4163, 9785615040)]

def originalTerm1565 : Integer.Sparse OriginalKey := [(Sum.inl 4169, -151318656000)]

def originalTerm1566 : Integer.Sparse OriginalKey := [(Sum.inl 4173, 151318656000)]

def originalTerm1567 : Integer.Sparse OriginalKey := [(Sum.inl 4176, -192671024640)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1568 : Integer.Sparse OriginalKey := [(Sum.inl 4178, 332306638080)]

def originalTerm1569 : Integer.Sparse OriginalKey := [(Sum.inl 4179, 85896725760)]

def originalTerm1570 : Integer.Sparse OriginalKey := [(Sum.inl 4184, -19033818240)]

def originalTerm1571 : Integer.Sparse OriginalKey := [(Sum.inl 4188, 344194260480)]

def originalTerm1572 : Integer.Sparse OriginalKey := [(Sum.inl 4189, 31817389440)]

def originalTerm1573 : Integer.Sparse OriginalKey := [(Sum.inl 4193, -2585122560)]

def originalTerm1574 : Integer.Sparse OriginalKey := [(Sum.inl 4327, -78148407360)]

def originalTerm1575 : Integer.Sparse OriginalKey := [(Sum.inl 4328, -115956314880)]

def originalTerm1576 : Integer.Sparse OriginalKey := [(Sum.inl 4330, -65419488000)]

def originalTerm1577 : Integer.Sparse OriginalKey := [(Sum.inl 4331, 64271667840)]

def originalTerm1578 : Integer.Sparse OriginalKey := [(Sum.inl 4332, 297571752960)]

def originalTerm1579 : Integer.Sparse OriginalKey := [(Sum.inl 4333, 138776738880)]

def originalTerm1580 : Integer.Sparse OriginalKey := [(Sum.inl 4334, 446985415680)]

def originalTerm1581 : Integer.Sparse OriginalKey := [(Sum.inl 4335, 389778008640)]

def originalTerm1582 : Integer.Sparse OriginalKey := [(Sum.inl 4336, 96839819520)]

def originalTerm1583 : Integer.Sparse OriginalKey := [(Sum.inl 4345, -117159060480)]

def originalTerm1584 : Integer.Sparse OriginalKey := [(Sum.inl 4347, 46922208000)]

def originalTerm1585 : Integer.Sparse OriginalKey := [(Sum.inl 4353, 83927070720)]

def originalTerm1586 : Integer.Sparse OriginalKey := [(Sum.inl 4357, 466747948800)]

def originalTerm1587 : Integer.Sparse OriginalKey := [(Sum.inl 4358, 94411576320)]

def originalTerm1588 : Integer.Sparse OriginalKey := [(Sum.inl 4362, -12841920000)]

def originalTerm1589 : Integer.Sparse OriginalKey := [(Sum.inl 4363, 58484689920)]

def originalTerm1590 : Integer.Sparse OriginalKey := [(Sum.inl 4364, 213444518400)]

def originalTerm1591 : Integer.Sparse OriginalKey := [(Sum.inl 4365, 62024705280)]

def originalTerm1592 : Integer.Sparse OriginalKey := [(Sum.inl 4366, -505306265280)]

def originalTerm1593 : Integer.Sparse OriginalKey := [(Sum.inl 4367, -163889655360)]

def originalTerm1594 : Integer.Sparse OriginalKey := [(Sum.inl 4368, -512307939840)]

def originalTerm1595 : Integer.Sparse OriginalKey := [(Sum.inl 4369, 147377145600)]

def originalTerm1596 : Integer.Sparse OriginalKey := [(Sum.inl 4370, 182600444160)]

def originalTerm1597 : Integer.Sparse OriginalKey := [(Sum.inl 4371, 12674346240)]

def originalTerm1598 : Integer.Sparse OriginalKey := [(Sum.inl 4372, -10165504320)]

def originalTerm1599 : Integer.Sparse OriginalKey := [(Sum.inl 4373, 244822030080)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm160 : Integer.Sparse OriginalKey := [(Sum.inl 227, -108132292800)]

def originalTerm161 : Integer.Sparse OriginalKey := [(Sum.inl 228, 115226812800)]

def originalTerm162 : Integer.Sparse OriginalKey := [(Sum.inl 229, -25653120000)]

def originalTerm163 : Integer.Sparse OriginalKey := [(Sum.inl 232, -115774934400)]

def originalTerm164 : Integer.Sparse OriginalKey := [(Sum.inl 234, 115774934400)]

def originalTerm165 : Integer.Sparse OriginalKey := [(Sum.inl 235, -63525398400)]

def originalTerm166 : Integer.Sparse OriginalKey := [(Sum.inl 236, 51687412800)]

def originalTerm167 : Integer.Sparse OriginalKey := [(Sum.inl 238, 134580009600)]

def originalTerm168 : Integer.Sparse OriginalKey := [(Sum.inl 239, 131652259200)]

def originalTerm169 : Integer.Sparse OriginalKey := [(Sum.inl 240, -221372265600)]

def originalTerm170 : Integer.Sparse OriginalKey := [(Sum.inl 242, -49636036800)]

def originalTerm171 : Integer.Sparse OriginalKey := [(Sum.inl 243, -20806603200)]

def originalTerm172 : Integer.Sparse OriginalKey := [(Sum.inl 244, 8378760000)]

def originalTerm173 : Integer.Sparse OriginalKey := [(Sum.inl 245, -11384424000)]

def originalTerm174 : Integer.Sparse OriginalKey := [(Sum.inl 246, 7403280000)]

def originalTerm175 : Integer.Sparse OriginalKey := [(Sum.inl 247, -29402040000)]

def originalTerm176 : Integer.Sparse OriginalKey := [(Sum.inl 248, 287325532800)]

def originalTerm177 : Integer.Sparse OriginalKey := [(Sum.inl 249, -230565844800)]

def originalTerm178 : Integer.Sparse OriginalKey := [(Sum.inl 250, -74818108800)]

def originalTerm179 : Integer.Sparse OriginalKey := [(Sum.inl 251, -41171371200)]

def originalTerm180 : Integer.Sparse OriginalKey := [(Sum.inl 252, 26825856000)]

def originalTerm181 : Integer.Sparse OriginalKey := [(Sum.inl 253, -19684944000)]

def originalTerm182 : Integer.Sparse OriginalKey := [(Sum.inl 254, 19684944000)]

def originalTerm183 : Integer.Sparse OriginalKey := [(Sum.inl 255, 58283520000)]

def originalTerm184 : Integer.Sparse OriginalKey := [(Sum.inl 256, -58283520000)]

def originalTerm185 : Integer.Sparse OriginalKey := [(Sum.inl 257, -11590689600)]

def originalTerm186 : Integer.Sparse OriginalKey := [(Sum.inl 258, 96879938400)]

def originalTerm187 : Integer.Sparse OriginalKey := [(Sum.inl 259, -31116316800)]

def originalTerm188 : Integer.Sparse OriginalKey := [(Sum.inl 260, 108132292800)]

def originalTerm189 : Integer.Sparse OriginalKey := [(Sum.inl 261, 21165844800)]

def originalTerm190 : Integer.Sparse OriginalKey := [(Sum.inl 262, -11272780800)]

def originalTerm191 : Integer.Sparse OriginalKey := [(Sum.inl 263, -150222969600)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1600 : Integer.Sparse OriginalKey := [(Sum.inl 4374, 467138775360)]

def originalTerm1601 : Integer.Sparse OriginalKey := [(Sum.inl 4375, -917178240)]

def originalTerm1602 : Integer.Sparse OriginalKey := [(Sum.inl 4439, -359231590080)]

def originalTerm1603 : Integer.Sparse OriginalKey := [(Sum.inl 4440, -511427777280)]

def originalTerm1604 : Integer.Sparse OriginalKey := [(Sum.inl 4442, -58912594560)]

def originalTerm1605 : Integer.Sparse OriginalKey := [(Sum.inl 4444, 261458013120)]

def originalTerm1606 : Integer.Sparse OriginalKey := [(Sum.inl 4445, -76765761600)]

def originalTerm1607 : Integer.Sparse OriginalKey := [(Sum.inl 4459, -662120709120)]

def originalTerm1608 : Integer.Sparse OriginalKey := [(Sum.inl 4464, -294411287040)]

def originalTerm1609 : Integer.Sparse OriginalKey := [(Sum.inl 4473, -95936947200)]

def originalTerm1610 : Integer.Sparse OriginalKey := [(Sum.inl 4474, -213736550400)]

def originalTerm1611 : Integer.Sparse OriginalKey := [(Sum.inl 4475, -227344561920)]

def originalTerm1612 : Integer.Sparse OriginalKey := [(Sum.inl 4476, 398876632320)]

def originalTerm1613 : Integer.Sparse OriginalKey := [(Sum.inl 4478, -378877136640)]

def originalTerm1614 : Integer.Sparse OriginalKey := [(Sum.inl 4480, 481057612800)]

def originalTerm1615 : Integer.Sparse OriginalKey := [(Sum.inl 4481, -50412508800)]

def originalTerm1616 : Integer.Sparse OriginalKey := [(Sum.inl 4494, -113658220800)]

def originalTerm1617 : Integer.Sparse OriginalKey := [(Sum.inl 4500, 204767769600)]

def originalTerm1618 : Integer.Sparse OriginalKey := [(Sum.inl 4508, -118817832960)]

def originalTerm1619 : Integer.Sparse OriginalKey := [(Sum.inl 4527, 141508032000)]

def originalTerm1620 : Integer.Sparse OriginalKey := [(Sum.inl 4528, 125729833600)]

def originalTerm1621 : Integer.Sparse OriginalKey := [(Sum.inl 4529, -162877070400)]

def originalTerm1622 : Integer.Sparse OriginalKey := [(Sum.inl 4530, 28797024000)]

def originalTerm1623 : Integer.Sparse OriginalKey := [(Sum.inl 4531, 210463318400)]

def originalTerm1624 : Integer.Sparse OriginalKey := [(Sum.inl 4532, -115495484160)]

def originalTerm1625 : Integer.Sparse OriginalKey := [(Sum.inl 4533, 5732038400)]

def originalTerm1626 : Integer.Sparse OriginalKey := [(Sum.inl 4534, -234421900480)]

def originalTerm1627 : Integer.Sparse OriginalKey := [(Sum.inl 4535, -105481948800)]

def originalTerm1628 : Integer.Sparse OriginalKey := [(Sum.inl 4536, -375136661760)]

def originalTerm1629 : Integer.Sparse OriginalKey := [(Sum.inl 4540, 225902688000)]

def originalTerm1630 : Integer.Sparse OriginalKey := [(Sum.inl 4542, 630781920000)]

def originalTerm1631 : Integer.Sparse OriginalKey := [(Sum.inl 4545, 973501357440)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1632 : Integer.Sparse OriginalKey := [(Sum.inl 4547, 410714053440)]

def originalTerm1633 : Integer.Sparse OriginalKey := [(Sum.inl 4548, 389114081280)]

def originalTerm1634 : Integer.Sparse OriginalKey := [(Sum.inl 4552, -310764126720)]

def originalTerm1635 : Integer.Sparse OriginalKey := [(Sum.inl 4556, -219682223040)]

def originalTerm1636 : Integer.Sparse OriginalKey := [(Sum.inl 4560, -30372842880)]

def originalTerm1637 : Integer.Sparse OriginalKey := [(Sum.inl 4589, 32435660800)]

def originalTerm1638 : Integer.Sparse OriginalKey := [(Sum.inl 4590, 172131552000)]

def originalTerm1639 : Integer.Sparse OriginalKey := [(Sum.inl 4591, -161755916800)]

def originalTerm1640 : Integer.Sparse OriginalKey := [(Sum.inl 4592, -402876446720)]

def originalTerm1641 : Integer.Sparse OriginalKey := [(Sum.inl 4593, -200928576000)]

def originalTerm1642 : Integer.Sparse OriginalKey := [(Sum.inl 4594, 80041581760)]

def originalTerm1643 : Integer.Sparse OriginalKey := [(Sum.inl 4599, 282214006400)]

def originalTerm1644 : Integer.Sparse OriginalKey := [(Sum.inl 4600, -44987715840)]

def originalTerm1645 : Integer.Sparse OriginalKey := [(Sum.inl 4603, -951163625600)]

def originalTerm1646 : Integer.Sparse OriginalKey := [(Sum.inl 4607, -1013921054080)]

def originalTerm1647 : Integer.Sparse OriginalKey := [(Sum.inl 4609, -147736083200)]

def originalTerm1648 : Integer.Sparse OriginalKey := [(Sum.inl 4611, -288290223360)]

def originalTerm1649 : Integer.Sparse OriginalKey := [(Sum.inl 4616, -60117405120)]

def originalTerm1650 : Integer.Sparse OriginalKey := [(Sum.inl 4617, -20134819200)]

def originalTerm1651 : Integer.Sparse OriginalKey := [(Sum.inl 4620, -19880712000)]

def originalTerm1652 : Integer.Sparse OriginalKey := [(Sum.inl 4626, -23280543360)]

def originalTerm1653 : Integer.Sparse OriginalKey := [(Sum.inl 4663, -112295040000)]

def originalTerm1654 : Integer.Sparse OriginalKey := [(Sum.inl 4664, -148871425920)]

def originalTerm1655 : Integer.Sparse OriginalKey := [(Sum.inl 4665, 131271494400)]

def originalTerm1656 : Integer.Sparse OriginalKey := [(Sum.inl 4666, -207460416000)]

def originalTerm1657 : Integer.Sparse OriginalKey := [(Sum.inl 4667, 37237167360)]

def originalTerm1658 : Integer.Sparse OriginalKey := [(Sum.inl 4668, 44198745600)]

def originalTerm1659 : Integer.Sparse OriginalKey := [(Sum.inl 4669, -21242365440)]

def originalTerm1660 : Integer.Sparse OriginalKey := [(Sum.inl 4670, -434089534080)]

def originalTerm1661 : Integer.Sparse OriginalKey := [(Sum.inl 4671, 48991797120)]

def originalTerm1662 : Integer.Sparse OriginalKey := [(Sum.inl 4677, -151318656000)]

def originalTerm1663 : Integer.Sparse OriginalKey := [(Sum.inl 4680, 79464798720)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1664 : Integer.Sparse OriginalKey := [(Sum.inl 4682, -540546566400)]

def originalTerm1665 : Integer.Sparse OriginalKey := [(Sum.inl 4683, -110731322880)]

def originalTerm1666 : Integer.Sparse OriginalKey := [(Sum.inl 4687, 115116775680)]

def originalTerm1667 : Integer.Sparse OriginalKey := [(Sum.inl 4690, -208177489920)]

def originalTerm1668 : Integer.Sparse OriginalKey := [(Sum.inl 4694, 11142213120)]

def originalTerm1669 : Integer.Sparse OriginalKey := [(Sum.inl 4695, 55507422720)]

def originalTerm1670 : Integer.Sparse OriginalKey := [(Sum.inl 4696, 124090010880)]

def originalTerm1671 : Integer.Sparse OriginalKey := [(Sum.inl 4697, -1269361920)]

def originalTerm1672 : Integer.Sparse OriginalKey := [(Sum.inl 4698, -301964455680)]

def originalTerm1673 : Integer.Sparse OriginalKey := [(Sum.inl 4699, -325434385920)]

def originalTerm1674 : Integer.Sparse OriginalKey := [(Sum.inl 4700, -239670885120)]

def originalTerm1675 : Integer.Sparse OriginalKey := [(Sum.inl 4701, 37906233600)]

def originalTerm1676 : Integer.Sparse OriginalKey := [(Sum.inl 4702, 8610336000)]

def originalTerm1677 : Integer.Sparse OriginalKey := [(Sum.inl 4703, 65957376000)]

def originalTerm1678 : Integer.Sparse OriginalKey := [(Sum.inl 4704, 162749950080)]

def originalTerm1679 : Integer.Sparse OriginalKey := [(Sum.inl 4705, 149138972160)]

def originalTerm1680 : Integer.Sparse OriginalKey := [(Sum.inl 4756, -110498737920)]

def originalTerm1681 : Integer.Sparse OriginalKey := [(Sum.inl 4757, -263706450240)]

def originalTerm1682 : Integer.Sparse OriginalKey := [(Sum.inl 4761, -264609492480)]

def originalTerm1683 : Integer.Sparse OriginalKey := [(Sum.inl 4762, -94432204800)]

def originalTerm1684 : Integer.Sparse OriginalKey := [(Sum.inl 4765, 40698343680)]

def originalTerm1685 : Integer.Sparse OriginalKey := [(Sum.inl 4768, -281131576320)]

def originalTerm1686 : Integer.Sparse OriginalKey := [(Sum.inl 4771, -56945998080)]

def originalTerm1687 : Integer.Sparse OriginalKey := [(Sum.inl 4772, -186910251840)]

def originalTerm1688 : Integer.Sparse OriginalKey := [(Sum.inl 4773, 53872270080)]

def originalTerm1689 : Integer.Sparse OriginalKey := [(Sum.inl 4774, -56306315520)]

def originalTerm1690 : Integer.Sparse OriginalKey := [(Sum.inl 4775, 331497966720)]

def originalTerm1691 : Integer.Sparse OriginalKey := [(Sum.inl 4776, 363339598080)]

def originalTerm1692 : Integer.Sparse OriginalKey := [(Sum.inl 4777, 48373755840)]

def originalTerm1693 : Integer.Sparse OriginalKey := [(Sum.inl 4792, -102976493760)]

def originalTerm1694 : Integer.Sparse OriginalKey := [(Sum.inl 4793, 57835932480)]

def originalTerm1695 : Integer.Sparse OriginalKey := [(Sum.inl 4795, -17477638080)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1696 : Integer.Sparse OriginalKey := [(Sum.inl 4803, 242581313280)]

def originalTerm1697 : Integer.Sparse OriginalKey := [(Sum.inl 4808, 180619656960)]

def originalTerm1698 : Integer.Sparse OriginalKey := [(Sum.inl 4815, 271188357120)]

def originalTerm1699 : Integer.Sparse OriginalKey := [(Sum.inl 4816, 443451939840)]

def originalTerm1700 : Integer.Sparse OriginalKey := [(Sum.inl 4817, -114350376960)]

def originalTerm1701 : Integer.Sparse OriginalKey := [(Sum.inl 4819, -257546534400)]

def originalTerm1702 : Integer.Sparse OriginalKey := [(Sum.inl 4821, 649213578240)]

def originalTerm1703 : Integer.Sparse OriginalKey := [(Sum.inl 4830, 113658220800)]

def originalTerm1704 : Integer.Sparse OriginalKey := [(Sum.inl 4836, 395108812800)]

def originalTerm1705 : Integer.Sparse OriginalKey := [(Sum.inl 4844, -282051233280)]

def originalTerm1706 : Integer.Sparse OriginalKey := [(Sum.inl 4851, -97054932480)]

def originalTerm1707 : Integer.Sparse OriginalKey := [(Sum.inl 4852, 678856307520)]

def originalTerm1708 : Integer.Sparse OriginalKey := [(Sum.inl 4853, -237404645760)]

def originalTerm1709 : Integer.Sparse OriginalKey := [(Sum.inl 4856, 1268404749120)]

def originalTerm1710 : Integer.Sparse OriginalKey := [(Sum.inl 4863, 87755258880)]

def originalTerm1711 : Integer.Sparse OriginalKey := [(Sum.inl 4867, 669275692800)]

def originalTerm1712 : Integer.Sparse OriginalKey := [(Sum.inl 4872, -34919706240)]

def originalTerm1713 : Integer.Sparse OriginalKey := [(Sum.inl 4878, 561502936320)]

def originalTerm1714 : Integer.Sparse OriginalKey := [(Sum.inl 4879, 1548138385920)]

def originalTerm1715 : Integer.Sparse OriginalKey := [(Sum.inl 4880, 422910792960)]

def originalTerm1716 : Integer.Sparse OriginalKey := [(Sum.inl 4881, 261134428800)]

def originalTerm1717 : Integer.Sparse OriginalKey := [(Sum.inl 4884, 509737645440)]

def originalTerm1718 : Integer.Sparse OriginalKey := [(Sum.inl 4885, -29065285440)]

def originalTerm1719 : Integer.Sparse OriginalKey := [(Sum.inl 4886, 589092636480)]

def originalTerm1720 : Integer.Sparse OriginalKey := [(Sum.inl 4887, -498234336960)]

def originalTerm1721 : Integer.Sparse OriginalKey := [(Sum.inl 4888, -306559526400)]

def originalTerm1722 : Integer.Sparse OriginalKey := [(Sum.inl 4889, 431354638080)]

def originalTerm1723 : Integer.Sparse OriginalKey := [(Sum.inl 4890, 80483051520)]

def originalTerm1724 : Integer.Sparse OriginalKey := [(Sum.inl 4891, 1048584366720)]

def originalTerm1725 : Integer.Sparse OriginalKey := [(Sum.inl 4892, 166751726400)]

def originalTerm1726 : Integer.Sparse OriginalKey := [(Sum.inl 4893, 840309404160)]

def originalTerm1727 : Integer.Sparse OriginalKey := [(Sum.inl 4894, 964048998720)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1728 : Integer.Sparse OriginalKey := [(Sum.inl 4895, 2673180625920)]

def originalTerm1729 : Integer.Sparse OriginalKey := [(Sum.inl 4896, 183126397440)]

def originalTerm1730 : Integer.Sparse OriginalKey := [(Sum.inl 4897, 814495403520)]

def originalTerm1731 : Integer.Sparse OriginalKey := [(Sum.inl 4898, 348376968960)]

def originalTerm1732 : Integer.Sparse OriginalKey := [(Sum.inl 4899, -129208250880)]

def originalTerm1733 : Integer.Sparse OriginalKey := [(Sum.inl 4900, -43787496960)]

def originalTerm1734 : Integer.Sparse OriginalKey := [(Sum.inl 4901, 262912532160)]

def originalTerm1735 : Integer.Sparse OriginalKey := [(Sum.inl 4930, -211083111360)]

def originalTerm1736 : Integer.Sparse OriginalKey := [(Sum.inl 4931, 69424550400)]

def originalTerm1737 : Integer.Sparse OriginalKey := [(Sum.inl 4933, 37786859520)]

def originalTerm1738 : Integer.Sparse OriginalKey := [(Sum.inl 4934, -165853180800)]

def originalTerm1739 : Integer.Sparse OriginalKey := [(Sum.inl 4935, 86648125920)]

def originalTerm1740 : Integer.Sparse OriginalKey := [(Sum.inl 4942, 355570427520)]

def originalTerm1741 : Integer.Sparse OriginalKey := [(Sum.inl 4944, -317858167680)]

def originalTerm1742 : Integer.Sparse OriginalKey := [(Sum.inl 4945, -3386027520)]

def originalTerm1743 : Integer.Sparse OriginalKey := [(Sum.inl 4951, -37712259840)]

def originalTerm1744 : Integer.Sparse OriginalKey := [(Sum.inl 4954, 508585097600)]

def originalTerm1745 : Integer.Sparse OriginalKey := [(Sum.inl 4955, -151153452800)]

def originalTerm1746 : Integer.Sparse OriginalKey := [(Sum.inl 4956, -141508032000)]

def originalTerm1747 : Integer.Sparse OriginalKey := [(Sum.inl 4957, 785712974400)]

def originalTerm1748 : Integer.Sparse OriginalKey := [(Sum.inl 4958, -28797024000)]

def originalTerm1749 : Integer.Sparse OriginalKey := [(Sum.inl 4959, -334026867520)]

def originalTerm1750 : Integer.Sparse OriginalKey := [(Sum.inl 4963, -120545501760)]

def originalTerm1751 : Integer.Sparse OriginalKey := [(Sum.inl 4964, -630781920000)]

def originalTerm1752 : Integer.Sparse OriginalKey := [(Sum.inl 4965, -492609288960)]

def originalTerm1753 : Integer.Sparse OriginalKey := [(Sum.inl 4966, -610678211520)]

def originalTerm1754 : Integer.Sparse OriginalKey := [(Sum.inl 4975, -225902688000)]

def originalTerm1755 : Integer.Sparse OriginalKey := [(Sum.inl 4976, -448532305920)]

def originalTerm1756 : Integer.Sparse OriginalKey := [(Sum.inl 5034, 79165607680)]

def originalTerm1757 : Integer.Sparse OriginalKey := [(Sum.inl 5035, 435608505600)]

def originalTerm1758 : Integer.Sparse OriginalKey := [(Sum.inl 5040, 617534064320)]

def originalTerm1759 : Integer.Sparse OriginalKey := [(Sum.inl 5041, 2468759040)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1760 : Integer.Sparse OriginalKey := [(Sum.inl 5042, -252055318080)]

def originalTerm1761 : Integer.Sparse OriginalKey := [(Sum.inl 5043, -76828296960)]

def originalTerm1762 : Integer.Sparse OriginalKey := [(Sum.inl 5044, -195139377280)]

def originalTerm1763 : Integer.Sparse OriginalKey := [(Sum.inl 5065, -386213171040)]

def originalTerm1764 : Integer.Sparse OriginalKey := [(Sum.inl 5067, 197421114240)]

def originalTerm1765 : Integer.Sparse OriginalKey := [(Sum.inl 5074, -325979482560)]

def originalTerm1766 : Integer.Sparse OriginalKey := [(Sum.inl 5085, 236993725440)]

def originalTerm1767 : Integer.Sparse OriginalKey := [(Sum.inl 5086, 325156564800)]

def originalTerm1768 : Integer.Sparse OriginalKey := [(Sum.inl 5087, 53871960160)]

def originalTerm1769 : Integer.Sparse OriginalKey := [(Sum.inl 5090, -502540144640)]

def originalTerm1770 : Integer.Sparse OriginalKey := [(Sum.inl 5097, 27573408000)]

def originalTerm1771 : Integer.Sparse OriginalKey := [(Sum.inl 5103, 180663532800)]

def originalTerm1772 : Integer.Sparse OriginalKey := [(Sum.inl 5112, -174923228160)]

def originalTerm1773 : Integer.Sparse OriginalKey := [(Sum.inl 5116, 44093614080)]

def originalTerm1774 : Integer.Sparse OriginalKey := [(Sum.inl 5128, -53256965280)]

def originalTerm1775 : Integer.Sparse OriginalKey := [(Sum.inl 5129, 175046646400)]

def originalTerm1776 : Integer.Sparse OriginalKey := [(Sum.inl 5138, 322340171200)]

def originalTerm1777 : Integer.Sparse OriginalKey := [(Sum.inl 5139, -1307120656000)]

def originalTerm1778 : Integer.Sparse OriginalKey := [(Sum.inl 5140, -457471246080)]

def originalTerm1779 : Integer.Sparse OriginalKey := [(Sum.inl 5144, 95727086720)]

def originalTerm1780 : Integer.Sparse OriginalKey := [(Sum.inl 5145, 317597041920)]

def originalTerm1781 : Integer.Sparse OriginalKey := [(Sum.inl 5147, 697297396480)]

def originalTerm1782 : Integer.Sparse OriginalKey := [(Sum.inl 5150, -47923151040)]

def originalTerm1783 : Integer.Sparse OriginalKey := [(Sum.inl 5151, -32413612800)]

def originalTerm1784 : Integer.Sparse OriginalKey := [(Sum.inl 5160, 925387340480)]

def originalTerm1785 : Integer.Sparse OriginalKey := [(Sum.inl 5161, 20170060800)]

def originalTerm1786 : Integer.Sparse OriginalKey := [(Sum.inl 5164, 601045065280)]

def originalTerm1787 : Integer.Sparse OriginalKey := [(Sum.inl 5173, 356938700160)]

def originalTerm1788 : Integer.Sparse OriginalKey := [(Sum.inl 5175, -108022452480)]

def originalTerm1789 : Integer.Sparse OriginalKey := [(Sum.inl 5184, -114053662720)]

def originalTerm1790 : Integer.Sparse OriginalKey := [(Sum.inl 5185, 258518304000)]

def originalTerm1791 : Integer.Sparse OriginalKey := [(Sum.inl 5187, 818504586880)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1792 : Integer.Sparse OriginalKey := [(Sum.inl 5188, 133183544960)]

def originalTerm1793 : Integer.Sparse OriginalKey := [(Sum.inl 5189, -152892983040)]

def originalTerm1794 : Integer.Sparse OriginalKey := [(Sum.inl 5197, 208617597440)]

def originalTerm1795 : Integer.Sparse OriginalKey := [(Sum.inl 5198, 258676654080)]

def originalTerm1796 : Integer.Sparse OriginalKey := [(Sum.inl 5199, 1486120360960)]

def originalTerm1797 : Integer.Sparse OriginalKey := [(Sum.inl 5201, 483703315200)]

def originalTerm1798 : Integer.Sparse OriginalKey := [(Sum.inl 5205, 443589972480)]

def originalTerm1799 : Integer.Sparse OriginalKey := [(Sum.inl 5206, 292782660480)]

def originalTerm1800 : Integer.Sparse OriginalKey := [(Sum.inl 5215, -308362740480)]

def originalTerm1801 : Integer.Sparse OriginalKey := [(Sum.inl 5216, -6333093120)]

def originalTerm1802 : Integer.Sparse OriginalKey := [(Sum.inl 5217, 260636160000)]

def originalTerm1803 : Integer.Sparse OriginalKey := [(Sum.inl 5219, 270362131200)]

def originalTerm1804 : Integer.Sparse OriginalKey := [(Sum.inl 5220, -10134462720)]

def originalTerm1805 : Integer.Sparse OriginalKey := [(Sum.inl 5222, 94432204800)]

def originalTerm1806 : Integer.Sparse OriginalKey := [(Sum.inl 5226, 207460416000)]

def originalTerm1807 : Integer.Sparse OriginalKey := [(Sum.inl 5229, 336997536000)]

def originalTerm1808 : Integer.Sparse OriginalKey := [(Sum.inl 5231, 233581927680)]

def originalTerm1809 : Integer.Sparse OriginalKey := [(Sum.inl 5232, 389143077120)]

def originalTerm1810 : Integer.Sparse OriginalKey := [(Sum.inl 5233, 132867521280)]

def originalTerm1811 : Integer.Sparse OriginalKey := [(Sum.inl 5235, 34900680960)]

def originalTerm1812 : Integer.Sparse OriginalKey := [(Sum.inl 5236, -260636160000)]

def originalTerm1813 : Integer.Sparse OriginalKey := [(Sum.inl 5243, 70791813120)]

def originalTerm1814 : Integer.Sparse OriginalKey := [(Sum.inl 5244, -341282208000)]

def originalTerm1815 : Integer.Sparse OriginalKey := [(Sum.inl 5249, 231808047360)]

def originalTerm1816 : Integer.Sparse OriginalKey := [(Sum.inl 5250, 224203514880)]

def originalTerm1817 : Integer.Sparse OriginalKey := [(Sum.inl 5251, 552966633600)]

def originalTerm1818 : Integer.Sparse OriginalKey := [(Sum.inl 5252, -419610942240)]

def originalTerm1819 : Integer.Sparse OriginalKey := [(Sum.inl 5254, -481182013440)]

def originalTerm1820 : Integer.Sparse OriginalKey := [(Sum.inl 5255, 282505678080)]

def originalTerm1821 : Integer.Sparse OriginalKey := [(Sum.inl 5256, -533731826880)]

def originalTerm1822 : Integer.Sparse OriginalKey := [(Sum.inl 5257, -405200647680)]

def originalTerm1823 : Integer.Sparse OriginalKey := [(Sum.inl 5258, -602366976000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1824 : Integer.Sparse OriginalKey := [(Sum.inl 5259, -150848148480)]

def originalTerm1825 : Integer.Sparse OriginalKey := [(Sum.inl 5260, 242563717440)]

def originalTerm1826 : Integer.Sparse OriginalKey := [(Sum.inl 5263, -447339012480)]

def originalTerm1827 : Integer.Sparse OriginalKey := [(Sum.inl 5264, 17072436480)]

def originalTerm1828 : Integer.Sparse OriginalKey := [(Sum.inl 5265, -672144100160)]

def originalTerm1829 : Integer.Sparse OriginalKey := [(Sum.inl 5266, -631483415680)]

def originalTerm1830 : Integer.Sparse OriginalKey := [(Sum.inl 5267, -751298493120)]

def originalTerm1831 : Integer.Sparse OriginalKey := [(Sum.inl 5268, -821471679840)]

def originalTerm1832 : Integer.Sparse OriginalKey := [(Sum.inl 5269, 507507632640)]

def originalTerm1833 : Integer.Sparse OriginalKey := [(Sum.inl 5270, 634775394240)]

def originalTerm1834 : Integer.Sparse OriginalKey := [(Sum.inl 5271, 1062287158080)]

def originalTerm1835 : Integer.Sparse OriginalKey := [(Sum.inl 5272, 396788077440)]

def originalTerm1836 : Integer.Sparse OriginalKey := [(Sum.inl 5273, 805812737280)]

def originalTerm1837 : Integer.Sparse OriginalKey := [(Sum.inl 5274, 1133048177280)]

def originalTerm1838 : Integer.Sparse OriginalKey := [(Sum.inl 5275, 226567599360)]

def originalTerm1839 : Integer.Sparse OriginalKey := [(Sum.inl 5276, -1284013286400)]

def originalTerm1840 : Integer.Sparse OriginalKey := [(Sum.inl 5277, -196918836480)]

def originalTerm1841 : Integer.Sparse OriginalKey := [(Sum.inl 5278, -143124910080)]

def originalTerm1842 : Integer.Sparse OriginalKey := [(Sum.inl 5279, -362274105600)]

def originalTerm1843 : Integer.Sparse OriginalKey := [(Sum.inl 5281, 1832812314240)]

def originalTerm1844 : Integer.Sparse OriginalKey := [(Sum.inl 5282, -325873806720)]

def originalTerm1845 : Integer.Sparse OriginalKey := [(Sum.inl 5284, -55397644800)]

def originalTerm1846 : Integer.Sparse OriginalKey := [(Sum.inl 5286, -618133344000)]

def originalTerm1847 : Integer.Sparse OriginalKey := [(Sum.inl 5287, -388886165760)]

def originalTerm1848 : Integer.Sparse OriginalKey := [(Sum.inl 5288, -44273372160)]

def originalTerm1849 : Integer.Sparse OriginalKey := [(Sum.inl 5289, -5072517324480)]

def originalTerm1850 : Integer.Sparse OriginalKey := [(Sum.inl 5290, -1006626650880)]

def originalTerm1851 : Integer.Sparse OriginalKey := [(Sum.inl 5291, -290913630720)]

def originalTerm1852 : Integer.Sparse OriginalKey := [(Sum.inl 5295, -2402373567360)]

def originalTerm1853 : Integer.Sparse OriginalKey := [(Sum.inl 5297, -114890186880)]

def originalTerm1854 : Integer.Sparse OriginalKey := [(Sum.inl 5299, -262209237440)]

def originalTerm1855 : Integer.Sparse OriginalKey := [(Sum.inl 5300, -506358543040)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1856 : Integer.Sparse OriginalKey := [(Sum.inl 5301, -59886179520)]

def originalTerm1857 : Integer.Sparse OriginalKey := [(Sum.inl 5302, -394436567040)]

def originalTerm1858 : Integer.Sparse OriginalKey := [(Sum.inl 5303, 109444008960)]

def originalTerm1859 : Integer.Sparse OriginalKey := [(Sum.inl 5304, 1369738925760)]

def originalTerm1860 : Integer.Sparse OriginalKey := [(Sum.inl 5305, 40130674560)]

def originalTerm1861 : Integer.Sparse OriginalKey := [(Sum.inl 5311, -479717118720)]

def originalTerm1862 : Integer.Sparse OriginalKey := [(Sum.inl 5338, 94096859200)]

def originalTerm1863 : Integer.Sparse OriginalKey := [(Sum.inl 5339, 827091953280)]

def originalTerm1864 : Integer.Sparse OriginalKey := [(Sum.inl 5340, 76828296960)]

def originalTerm1865 : Integer.Sparse OriginalKey := [(Sum.inl 5348, -66966569280)]

def originalTerm1866 : Integer.Sparse OriginalKey := [(Sum.inl 5353, -274486503360)]

def originalTerm1867 : Integer.Sparse OriginalKey := [(Sum.inl 5359, -236993725440)]

def originalTerm1868 : Integer.Sparse OriginalKey := [(Sum.inl 5360, -370246780800)]

def originalTerm1869 : Integer.Sparse OriginalKey := [(Sum.inl 5361, -154941341120)]

def originalTerm1870 : Integer.Sparse OriginalKey := [(Sum.inl 5376, 7313433120)]

def originalTerm1871 : Integer.Sparse OriginalKey := [(Sum.inl 5377, 200928576000)]

def originalTerm1872 : Integer.Sparse OriginalKey := [(Sum.inl 5379, 756371907200)]

def originalTerm1873 : Integer.Sparse OriginalKey := [(Sum.inl 5381, 673937695680)]

def originalTerm1874 : Integer.Sparse OriginalKey := [(Sum.inl 5382, 354797844480)]

def originalTerm1875 : Integer.Sparse OriginalKey := [(Sum.inl 5385, 362103305280)]

def originalTerm1876 : Integer.Sparse OriginalKey := [(Sum.inl 5402, -586472424000)]

def originalTerm1877 : Integer.Sparse OriginalKey := [(Sum.inl 5405, -203193169600)]

def originalTerm1878 : Integer.Sparse OriginalKey := [(Sum.inl 5406, -789259285120)]

def originalTerm1879 : Integer.Sparse OriginalKey := [(Sum.inl 5407, -999260446560)]

def originalTerm1880 : Integer.Sparse OriginalKey := [(Sum.inl 5408, -311516864160)]

def originalTerm1881 : Integer.Sparse OriginalKey := [(Sum.inl 5409, -1459410971680)]

def originalTerm1882 : Integer.Sparse OriginalKey := [(Sum.inl 5410, 617716212800)]

def originalTerm1883 : Integer.Sparse OriginalKey := [(Sum.inl 5411, 1328920917120)]

def originalTerm1884 : Integer.Sparse OriginalKey := [(Sum.inl 5412, -170187237440)]

def originalTerm1885 : Integer.Sparse OriginalKey := [(Sum.inl 5413, -936213673920)]

def originalTerm1886 : Integer.Sparse OriginalKey := [(Sum.inl 5414, -62741339200)]

def originalTerm1887 : Integer.Sparse OriginalKey := [(Sum.inl 5419, 152892983040)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm1888 : Integer.Sparse OriginalKey := [(Sum.inl 5420, -223610996160)]

def originalTerm1889 : Integer.Sparse OriginalKey := [(Sum.inl 5421, -779138862400)]

def originalTerm1890 : Integer.Sparse OriginalKey := [(Sum.inl 5423, -805612630080)]

def originalTerm1891 : Integer.Sparse OriginalKey := [(Sum.inl 5424, 500035032640)]

def originalTerm1892 : Integer.Sparse OriginalKey := [(Sum.inl 5425, -844863352960)]

def originalTerm1893 : Integer.Sparse OriginalKey := [(Sum.inl 5426, 257415588480)]

def originalTerm1894 : Integer.Sparse OriginalKey := [(Sum.inl 5427, 197202442080)]

def originalTerm1895 : Integer.Sparse OriginalKey := [(Sum.inl 5428, 430542304480)]

def originalTerm1896 : Integer.Sparse OriginalKey := [(Sum.inl 5429, -245717222080)]

def originalTerm1897 : Integer.Sparse OriginalKey := [(Sum.inl 5430, 437120271360)]

def originalTerm1898 : Integer.Sparse OriginalKey := [(Sum.inl 5431, -2556226752960)]

def originalTerm1899 : Integer.Sparse OriginalKey := [(Sum.inl 5432, -456361709440)]

def originalTerm1900 : Integer.Sparse OriginalKey := [(Sum.inl 5436, 2341529124960)]

def originalTerm1901 : Integer.Sparse OriginalKey := [(Sum.inl 5437, -592553795520)]

def originalTerm1902 : Integer.Sparse OriginalKey := [(Sum.inl 5438, 569570002560)]

def originalTerm1903 : Integer.Sparse OriginalKey := [(Sum.inl 5445, -69891938560)]

def originalTerm1904 : Integer.Sparse OriginalKey := [(Sum.inl 5446, -4381805510080)]

def originalTerm1905 : Integer.Sparse OriginalKey := [(Sum.inl 5447, -143760685440)]

def originalTerm1906 : Integer.Sparse OriginalKey := [(Sum.inl 5448, -359175968160)]

def originalTerm1907 : Integer.Sparse OriginalKey := [(Sum.inl 5449, 389066200640)]

def originalTerm1908 : Integer.Sparse OriginalKey := [(Sum.inl 5461, 387950780160)]

def originalTerm1909 : Integer.Sparse OriginalKey := [(Sum.inl 5463, 695263968000)]

def originalTerm1910 : Integer.Sparse OriginalKey := [(Sum.inl 5470, -387950780160)]

def originalTerm1911 : Integer.Sparse OriginalKey := [(Sum.inl 5471, -948895701440)]

def originalTerm1912 : Integer.Sparse OriginalKey := [(Sum.inl 5472, -637669836480)]

def originalTerm1913 : Integer.Sparse OriginalKey := [(Sum.inl 5473, 1333941613120)]

def originalTerm1914 : Integer.Sparse OriginalKey := [(Sum.inl 5474, -69509632320)]

def originalTerm1915 : Integer.Sparse OriginalKey := [(Sum.inl 5475, 1109748436800)]

def originalTerm1916 : Integer.Sparse OriginalKey := [(Sum.inl 5478, 1083214748160)]

def originalTerm1917 : Integer.Sparse OriginalKey := [(Sum.inl 5480, -1649046240000)]

def originalTerm1918 : Integer.Sparse OriginalKey := [(Sum.inl 5484, 42699075840)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm192 : Integer.Sparse OriginalKey := [(Sum.inl 264, -42855824400)]

def originalTerm193 : Integer.Sparse OriginalKey := [(Sum.inl 265, -194185209600)]

def originalTerm194 : Integer.Sparse OriginalKey := [(Sum.inl 266, -208967479200)]

def originalTerm195 : Integer.Sparse OriginalKey := [(Sum.inl 267, 57745742400)]

def originalTerm196 : Integer.Sparse OriginalKey := [(Sum.inl 268, -160248340800)]

def originalTerm197 : Integer.Sparse OriginalKey := [(Sum.inl 269, 179454536400)]

def originalTerm198 : Integer.Sparse OriginalKey := [(Sum.inl 270, -38061417600)]

def originalTerm199 : Integer.Sparse OriginalKey := [(Sum.inl 271, 15419606400)]

def originalTerm200 : Integer.Sparse OriginalKey := [(Sum.inl 272, 53783652000)]

def originalTerm201 : Integer.Sparse OriginalKey := [(Sum.inl 275, -574616001600)]

def originalTerm202 : Integer.Sparse OriginalKey := [(Sum.inl 277, 530018928000)]

def originalTerm203 : Integer.Sparse OriginalKey := [(Sum.inl 278, 256488794400)]

def originalTerm204 : Integer.Sparse OriginalKey := [(Sum.inl 279, -153198993600)]

def originalTerm205 : Integer.Sparse OriginalKey := [(Sum.inl 280, 314148300000)]

def originalTerm206 : Integer.Sparse OriginalKey := [(Sum.inl 281, 106974828000)]

def originalTerm207 : Integer.Sparse OriginalKey := [(Sum.inl 282, -421123128000)]

def originalTerm208 : Integer.Sparse OriginalKey := [(Sum.inl 283, 8424604800)]

def originalTerm209 : Integer.Sparse OriginalKey := [(Sum.inl 285, -300814920000)]

def originalTerm210 : Integer.Sparse OriginalKey := [(Sum.inl 286, -71193873600)]

def originalTerm211 : Integer.Sparse OriginalKey := [(Sum.inl 287, -8424604800)]

def originalTerm212 : Integer.Sparse OriginalKey := [(Sum.inl 288, -16911316800)]

def originalTerm213 : Integer.Sparse OriginalKey := [(Sum.inl 289, -227990496000)]

def originalTerm214 : Integer.Sparse OriginalKey := [(Sum.inl 290, -15407899200)]

def originalTerm215 : Integer.Sparse OriginalKey := [(Sum.inl 291, 48837120000)]

def originalTerm216 : Integer.Sparse OriginalKey := [(Sum.inl 292, 24456750000)]

def originalTerm217 : Integer.Sparse OriginalKey := [(Sum.inl 293, -48760896000)]

def originalTerm218 : Integer.Sparse OriginalKey := [(Sum.inl 294, -3891744000)]

def originalTerm219 : Integer.Sparse OriginalKey := [(Sum.inl 295, 44597073600)]

def originalTerm220 : Integer.Sparse OriginalKey := [(Sum.inl 296, -24456750000)]

def originalTerm221 : Integer.Sparse OriginalKey := [(Sum.inl 297, -48508080000)]

def originalTerm222 : Integer.Sparse OriginalKey := [(Sum.inl 298, -24456750000)]

def originalTerm223 : Integer.Sparse OriginalKey := [(Sum.inl 299, 22965003000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm224 : Integer.Sparse OriginalKey := [(Sum.inl 300, -45930006000)]

def originalTerm225 : Integer.Sparse OriginalKey := [(Sum.inl 301, 9509760000)]

def originalTerm226 : Integer.Sparse OriginalKey := [(Sum.inl 303, -58346880000)]

def originalTerm227 : Integer.Sparse OriginalKey := [(Sum.inl 305, 3891744000)]

def originalTerm228 : Integer.Sparse OriginalKey := [(Sum.inl 306, 349236480000)]

def originalTerm229 : Integer.Sparse OriginalKey := [(Sum.inl 308, -70687015000)]

def originalTerm230 : Integer.Sparse OriginalKey := [(Sum.inl 309, 141374030000)]

def originalTerm231 : Integer.Sparse OriginalKey := [(Sum.inl 310, -71395008000)]

def originalTerm232 : Integer.Sparse OriginalKey := [(Sum.inl 312, 71318784000)]

def originalTerm233 : Integer.Sparse OriginalKey := [(Sum.inl 313, 38407920000)]

def originalTerm234 : Integer.Sparse OriginalKey := [(Sum.inl 314, 14865691200)]

def originalTerm235 : Integer.Sparse OriginalKey := [(Sum.inl 316, 54779121600)]

def originalTerm236 : Integer.Sparse OriginalKey := [(Sum.inl 317, 7276982400)]

def originalTerm237 : Integer.Sparse OriginalKey := [(Sum.inl 319, 58441910400)]

def originalTerm238 : Integer.Sparse OriginalKey := [(Sum.inl 321, -8606505600)]

def originalTerm239 : Integer.Sparse OriginalKey := [(Sum.inl 322, 24456750000)]

def originalTerm240 : Integer.Sparse OriginalKey := [(Sum.inl 323, -24456750000)]

def originalTerm241 : Integer.Sparse OriginalKey := [(Sum.inl 324, -23181379200)]

def originalTerm242 : Integer.Sparse OriginalKey := [(Sum.inl 325, 9433536000)]

def originalTerm243 : Integer.Sparse OriginalKey := [(Sum.inl 326, 3891744000)]

def originalTerm244 : Integer.Sparse OriginalKey := [(Sum.inl 327, 62887622400)]

def originalTerm245 : Integer.Sparse OriginalKey := [(Sum.inl 328, 20227392000)]

def originalTerm246 : Integer.Sparse OriginalKey := [(Sum.inl 330, -24456750000)]

def originalTerm247 : Integer.Sparse OriginalKey := [(Sum.inl 332, 300814920000)]

def originalTerm248 : Integer.Sparse OriginalKey := [(Sum.inl 333, 24456750000)]

def originalTerm249 : Integer.Sparse OriginalKey := [(Sum.inl 334, 28470672000)]

def originalTerm250 : Integer.Sparse OriginalKey := [(Sum.inl 335, 105157382400)]

def originalTerm251 : Integer.Sparse OriginalKey := [(Sum.inl 336, -30333369600)]

def originalTerm252 : Integer.Sparse OriginalKey := [(Sum.inl 337, -14553964800)]

def originalTerm253 : Integer.Sparse OriginalKey := [(Sum.inl 339, -50432774400)]

def originalTerm254 : Integer.Sparse OriginalKey := [(Sum.inl 340, 66564864000)]

def originalTerm255 : Integer.Sparse OriginalKey := [(Sum.inl 341, -40754464800)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm256 : Integer.Sparse OriginalKey := [(Sum.inl 342, -41502110400)]

def originalTerm257 : Integer.Sparse OriginalKey := [(Sum.inl 343, -187518960000)]

def originalTerm258 : Integer.Sparse OriginalKey := [(Sum.inl 344, 1862697600)]

def originalTerm259 : Integer.Sparse OriginalKey := [(Sum.inl 345, 24456750000)]

def originalTerm260 : Integer.Sparse OriginalKey := [(Sum.inl 346, 143637052800)]

def originalTerm261 : Integer.Sparse OriginalKey := [(Sum.inl 347, -24456750000)]

def originalTerm262 : Integer.Sparse OriginalKey := [(Sum.inl 348, 213949656000)]

def originalTerm263 : Integer.Sparse OriginalKey := [(Sum.inl 349, 24456750000)]

def originalTerm264 : Integer.Sparse OriginalKey := [(Sum.inl 350, -106974828000)]

def originalTerm265 : Integer.Sparse OriginalKey := [(Sum.inl 351, -8424604800)]

def originalTerm266 : Integer.Sparse OriginalKey := [(Sum.inl 352, 8424604800)]

def originalTerm267 : Integer.Sparse OriginalKey := [(Sum.inl 353, -252078960000)]

def originalTerm268 : Integer.Sparse OriginalKey := [(Sum.inl 354, -7006603200)]

def originalTerm269 : Integer.Sparse OriginalKey := [(Sum.inl 355, 250865448000)]

def originalTerm270 : Integer.Sparse OriginalKey := [(Sum.inl 356, -21835584000)]

def originalTerm271 : Integer.Sparse OriginalKey := [(Sum.inl 357, 11590689600)]

def originalTerm272 : Integer.Sparse OriginalKey := [(Sum.inl 358, 49636036800)]

def originalTerm273 : Integer.Sparse OriginalKey := [(Sum.inl 359, -11431929600)]

def originalTerm274 : Integer.Sparse OriginalKey := [(Sum.inl 360, -20806603200)]

def originalTerm275 : Integer.Sparse OriginalKey := [(Sum.inl 361, -75431952000)]

def originalTerm276 : Integer.Sparse OriginalKey := [(Sum.inl 362, -99272073600)]

def originalTerm277 : Integer.Sparse OriginalKey := [(Sum.inl 363, 24632611200)]

def originalTerm278 : Integer.Sparse OriginalKey := [(Sum.inl 364, -160104676800)]

def originalTerm279 : Integer.Sparse OriginalKey := [(Sum.inl 365, -1691913600)]

def originalTerm280 : Integer.Sparse OriginalKey := [(Sum.inl 366, -81153576000)]

def originalTerm281 : Integer.Sparse OriginalKey := [(Sum.inl 367, 11431929600)]

def originalTerm282 : Integer.Sparse OriginalKey := [(Sum.inl 368, 15441432000)]

def originalTerm283 : Integer.Sparse OriginalKey := [(Sum.inl 369, 63471868800)]

def originalTerm284 : Integer.Sparse OriginalKey := [(Sum.inl 371, -183047308800)]

def originalTerm285 : Integer.Sparse OriginalKey := [(Sum.inl 373, -12511904400)]

def originalTerm286 : Integer.Sparse OriginalKey := [(Sum.inl 374, -52185958200)]

def originalTerm287 : Integer.Sparse OriginalKey := [(Sum.inl 375, 66564864000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalTerm288 : Integer.Sparse OriginalKey := [(Sum.inl 376, -51597508800)]

def originalTerm289 : Integer.Sparse OriginalKey := [(Sum.inl 377, 23015644800)]

def originalTerm290 : Integer.Sparse OriginalKey := [(Sum.inl 378, 124381440000)]

def originalTerm291 : Integer.Sparse OriginalKey := [(Sum.inl 379, 9509760000)]

def originalTerm292 : Integer.Sparse OriginalKey := [(Sum.inl 380, -66564864000)]

def originalTerm293 : Integer.Sparse OriginalKey := [(Sum.inl 381, -31515076800)]

def originalTerm294 : Integer.Sparse OriginalKey := [(Sum.inl 382, 47059776000)]

def originalTerm295 : Integer.Sparse OriginalKey := [(Sum.inl 383, -62325840000)]

def originalTerm296 : Integer.Sparse OriginalKey := [(Sum.inl 384, 8161930000)]

def originalTerm297 : Integer.Sparse OriginalKey := [(Sum.inl 385, -3210302600)]

def originalTerm298 : Integer.Sparse OriginalKey := [(Sum.inl 386, 89073590400)]

def originalTerm299 : Integer.Sparse OriginalKey := [(Sum.inl 387, 452687524800)]

def originalTerm300 : Integer.Sparse OriginalKey := [(Sum.inl 388, -51481564800)]

def originalTerm301 : Integer.Sparse OriginalKey := [(Sum.inl 389, -26509586400)]

def originalTerm302 : Integer.Sparse OriginalKey := [(Sum.inl 390, -147766358400)]

def originalTerm303 : Integer.Sparse OriginalKey := [(Sum.inl 391, 61446981600)]

def originalTerm304 : Integer.Sparse OriginalKey := [(Sum.inl 392, 2611036800)]

def originalTerm305 : Integer.Sparse OriginalKey := [(Sum.inl 393, 41502110400)]

def originalTerm306 : Integer.Sparse OriginalKey := [(Sum.inl 394, -34498076400)]

def originalTerm307 : Integer.Sparse OriginalKey := [(Sum.inl 395, 95566042800)]

def originalTerm308 : Integer.Sparse OriginalKey := [(Sum.inl 396, -30264364800)]

def originalTerm309 : Integer.Sparse OriginalKey := [(Sum.inl 397, 39432067200)]

def originalTerm310 : Integer.Sparse OriginalKey := [(Sum.inl 398, -38407920000)]

def originalTerm311 : Integer.Sparse OriginalKey := [(Sum.inl 399, -5222073600)]

def originalTerm312 : Integer.Sparse OriginalKey := [(Sum.inl 400, -77996793600)]

def originalTerm313 : Integer.Sparse OriginalKey := [(Sum.inl 401, 20806603200)]

def originalTerm314 : Integer.Sparse OriginalKey := [(Sum.inl 402, -318925320000)]

def originalTerm315 : Integer.Sparse OriginalKey := [(Sum.inl 403, 24989534400)]

def originalTerm316 : Integer.Sparse OriginalKey := [(Sum.inl 404, -56389747200)]

def originalTerm317 : Integer.Sparse OriginalKey := [(Sum.inl 405, 262864046400)]

def originalTerm318 : Integer.Sparse OriginalKey := [(Sum.inl 406, -283613472000)]

def originalTerm319 : Integer.Sparse OriginalKey := [(Sum.inl 407, -89814871200)]

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

def originalMerge0 : Integer.Sparse OriginalKey := originalTerm1 ++ originalTerm2

def originalMerge1 : Integer.Sparse OriginalKey := originalTerm0 ++ originalMerge0

def originalMerge2 : Integer.Sparse OriginalKey := originalTerm3 ++ originalTerm4

def originalMerge3 : Integer.Sparse OriginalKey := originalTerm5 ++ originalTerm6

def originalMerge4 : Integer.Sparse OriginalKey := originalMerge2 ++ originalMerge3

def originalMerge5 : Integer.Sparse OriginalKey := originalMerge1 ++ originalMerge4

def originalMerge6 : Integer.Sparse OriginalKey := originalTerm8 ++ originalTerm9

def originalMerge7 : Integer.Sparse OriginalKey := originalTerm7 ++ originalMerge6

def originalMerge8 : Integer.Sparse OriginalKey := originalTerm10 ++ originalTerm11

def originalMerge9 : Integer.Sparse OriginalKey := originalTerm12 ++ originalTerm13

def originalMerge10 : Integer.Sparse OriginalKey := originalMerge8 ++ originalMerge9

def originalMerge11 : Integer.Sparse OriginalKey := originalMerge7 ++ originalMerge10

def originalMerge12 : Integer.Sparse OriginalKey := originalMerge5 ++ originalMerge11

def originalMerge13 : Integer.Sparse OriginalKey := originalTerm15 ++ originalTerm16

def originalMerge14 : Integer.Sparse OriginalKey := originalTerm14 ++ originalMerge13

def originalMerge15 : Integer.Sparse OriginalKey := originalTerm17 ++ originalTerm18

def originalMerge16 : Integer.Sparse OriginalKey := originalTerm19 ++ originalTerm20

def originalMerge17 : Integer.Sparse OriginalKey := originalMerge15 ++ originalMerge16

def originalMerge18 : Integer.Sparse OriginalKey := originalMerge14 ++ originalMerge17

def originalMerge19 : Integer.Sparse OriginalKey := originalTerm21 ++ originalTerm22

def originalMerge20 : Integer.Sparse OriginalKey := originalTerm23 ++ originalTerm24

def originalMerge21 : Integer.Sparse OriginalKey := originalMerge19 ++ originalMerge20

def originalMerge22 : Integer.Sparse OriginalKey := originalTerm25 ++ originalTerm26

def originalMerge23 : Integer.Sparse OriginalKey := originalTerm27 ++ originalTerm28

def originalMerge24 : Integer.Sparse OriginalKey := originalMerge22 ++ originalMerge23

def originalMerge25 : Integer.Sparse OriginalKey := originalMerge21 ++ originalMerge24

def originalMerge26 : Integer.Sparse OriginalKey := originalMerge18 ++ originalMerge25

def originalMerge27 : Integer.Sparse OriginalKey := originalMerge12 ++ originalMerge26

def originalMerge28 : Integer.Sparse OriginalKey := originalTerm30 ++ originalTerm31

def originalMerge29 : Integer.Sparse OriginalKey := originalTerm29 ++ originalMerge28

def originalMerge30 : Integer.Sparse OriginalKey := originalTerm32 ++ originalTerm33

def originalMerge31 : Integer.Sparse OriginalKey := originalTerm34 ++ originalTerm35

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge32 : Integer.Sparse OriginalKey := originalMerge30 ++ originalMerge31

def originalMerge33 : Integer.Sparse OriginalKey := originalMerge29 ++ originalMerge32

def originalMerge34 : Integer.Sparse OriginalKey := originalTerm36 ++ originalTerm37

def originalMerge35 : Integer.Sparse OriginalKey := originalTerm38 ++ originalTerm39

def originalMerge36 : Integer.Sparse OriginalKey := originalMerge34 ++ originalMerge35

def originalMerge37 : Integer.Sparse OriginalKey := originalTerm40 ++ originalTerm41

def originalMerge38 : Integer.Sparse OriginalKey := originalTerm42 ++ originalTerm43

def originalMerge39 : Integer.Sparse OriginalKey := originalMerge37 ++ originalMerge38

def originalMerge40 : Integer.Sparse OriginalKey := originalMerge36 ++ originalMerge39

def originalMerge41 : Integer.Sparse OriginalKey := originalMerge33 ++ originalMerge40

def originalMerge42 : Integer.Sparse OriginalKey := originalTerm45 ++ originalTerm46

def originalMerge43 : Integer.Sparse OriginalKey := originalTerm44 ++ originalMerge42

def originalMerge44 : Integer.Sparse OriginalKey := originalTerm47 ++ originalTerm48

def originalMerge45 : Integer.Sparse OriginalKey := originalTerm49 ++ originalTerm50

def originalMerge46 : Integer.Sparse OriginalKey := originalMerge44 ++ originalMerge45

def originalMerge47 : Integer.Sparse OriginalKey := originalMerge43 ++ originalMerge46

def originalMerge48 : Integer.Sparse OriginalKey := originalTerm51 ++ originalTerm52

def originalMerge49 : Integer.Sparse OriginalKey := originalTerm53 ++ originalTerm54

def originalMerge50 : Integer.Sparse OriginalKey := originalMerge48 ++ originalMerge49

def originalMerge51 : Integer.Sparse OriginalKey := originalTerm55 ++ originalTerm56

def originalMerge52 : Integer.Sparse OriginalKey := originalTerm57 ++ originalTerm58

def originalMerge53 : Integer.Sparse OriginalKey := originalMerge51 ++ originalMerge52

def originalMerge54 : Integer.Sparse OriginalKey := originalMerge50 ++ originalMerge53

def originalMerge55 : Integer.Sparse OriginalKey := originalMerge47 ++ originalMerge54

def originalMerge56 : Integer.Sparse OriginalKey := originalMerge41 ++ originalMerge55

def originalMerge57 : Integer.Sparse OriginalKey := originalMerge27 ++ originalMerge56

def originalMerge58 : Integer.Sparse OriginalKey := originalTerm60 ++ originalTerm61

def originalMerge59 : Integer.Sparse OriginalKey := originalTerm59 ++ originalMerge58

def originalMerge60 : Integer.Sparse OriginalKey := originalTerm62 ++ originalTerm63

def originalMerge61 : Integer.Sparse OriginalKey := originalTerm64 ++ originalTerm65

def originalMerge62 : Integer.Sparse OriginalKey := originalMerge60 ++ originalMerge61

def originalMerge63 : Integer.Sparse OriginalKey := originalMerge59 ++ originalMerge62

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge64 : Integer.Sparse OriginalKey := originalTerm66 ++ originalTerm67

def originalMerge65 : Integer.Sparse OriginalKey := originalTerm68 ++ originalTerm69

def originalMerge66 : Integer.Sparse OriginalKey := originalMerge64 ++ originalMerge65

def originalMerge67 : Integer.Sparse OriginalKey := originalTerm70 ++ originalTerm71

def originalMerge68 : Integer.Sparse OriginalKey := originalTerm72 ++ originalTerm73

def originalMerge69 : Integer.Sparse OriginalKey := originalMerge67 ++ originalMerge68

def originalMerge70 : Integer.Sparse OriginalKey := originalMerge66 ++ originalMerge69

def originalMerge71 : Integer.Sparse OriginalKey := originalMerge63 ++ originalMerge70

def originalMerge72 : Integer.Sparse OriginalKey := originalTerm75 ++ originalTerm76

def originalMerge73 : Integer.Sparse OriginalKey := originalTerm74 ++ originalMerge72

def originalMerge74 : Integer.Sparse OriginalKey := originalTerm77 ++ originalTerm78

def originalMerge75 : Integer.Sparse OriginalKey := originalTerm79 ++ originalTerm80

def originalMerge76 : Integer.Sparse OriginalKey := originalMerge74 ++ originalMerge75

def originalMerge77 : Integer.Sparse OriginalKey := originalMerge73 ++ originalMerge76

def originalMerge78 : Integer.Sparse OriginalKey := originalTerm81 ++ originalTerm82

def originalMerge79 : Integer.Sparse OriginalKey := originalTerm83 ++ originalTerm84

def originalMerge80 : Integer.Sparse OriginalKey := originalMerge78 ++ originalMerge79

def originalMerge81 : Integer.Sparse OriginalKey := originalTerm85 ++ originalTerm86

def originalMerge82 : Integer.Sparse OriginalKey := originalTerm87 ++ originalTerm88

def originalMerge83 : Integer.Sparse OriginalKey := originalMerge81 ++ originalMerge82

def originalMerge84 : Integer.Sparse OriginalKey := originalMerge80 ++ originalMerge83

def originalMerge85 : Integer.Sparse OriginalKey := originalMerge77 ++ originalMerge84

def originalMerge86 : Integer.Sparse OriginalKey := originalMerge71 ++ originalMerge85

def originalMerge87 : Integer.Sparse OriginalKey := originalTerm90 ++ originalTerm91

def originalMerge88 : Integer.Sparse OriginalKey := originalTerm89 ++ originalMerge87

def originalMerge89 : Integer.Sparse OriginalKey := originalTerm92 ++ originalTerm93

def originalMerge90 : Integer.Sparse OriginalKey := originalTerm94 ++ originalTerm95

def originalMerge91 : Integer.Sparse OriginalKey := originalMerge89 ++ originalMerge90

def originalMerge92 : Integer.Sparse OriginalKey := originalMerge88 ++ originalMerge91

def originalMerge93 : Integer.Sparse OriginalKey := originalTerm96 ++ originalTerm97

def originalMerge94 : Integer.Sparse OriginalKey := originalTerm98 ++ originalTerm99

def originalMerge95 : Integer.Sparse OriginalKey := originalMerge93 ++ originalMerge94

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

def originalMerge96 : Integer.Sparse OriginalKey := originalTerm100 ++ originalTerm101

def originalMerge97 : Integer.Sparse OriginalKey := originalTerm102 ++ originalTerm103

def originalMerge98 : Integer.Sparse OriginalKey := originalMerge96 ++ originalMerge97

def originalMerge99 : Integer.Sparse OriginalKey := originalMerge95 ++ originalMerge98

def originalMerge100 : Integer.Sparse OriginalKey := originalMerge92 ++ originalMerge99

def originalMerge101 : Integer.Sparse OriginalKey := originalTerm105 ++ originalTerm106

def originalMerge102 : Integer.Sparse OriginalKey := originalTerm104 ++ originalMerge101

def originalMerge103 : Integer.Sparse OriginalKey := originalTerm107 ++ originalTerm108

def originalMerge104 : Integer.Sparse OriginalKey := originalTerm109 ++ originalTerm110

def originalMerge105 : Integer.Sparse OriginalKey := originalMerge103 ++ originalMerge104

def originalMerge106 : Integer.Sparse OriginalKey := originalMerge102 ++ originalMerge105

def originalMerge107 : Integer.Sparse OriginalKey := originalTerm111 ++ originalTerm112

def originalMerge108 : Integer.Sparse OriginalKey := originalTerm113 ++ originalTerm114

def originalMerge109 : Integer.Sparse OriginalKey := originalMerge107 ++ originalMerge108

def originalMerge110 : Integer.Sparse OriginalKey := originalTerm115 ++ originalTerm116

def originalMerge111 : Integer.Sparse OriginalKey := originalTerm117 ++ originalTerm118

def originalMerge112 : Integer.Sparse OriginalKey := originalMerge110 ++ originalMerge111

def originalMerge113 : Integer.Sparse OriginalKey := originalMerge109 ++ originalMerge112

def originalMerge114 : Integer.Sparse OriginalKey := originalMerge106 ++ originalMerge113

def originalMerge115 : Integer.Sparse OriginalKey := originalMerge100 ++ originalMerge114

def originalMerge116 : Integer.Sparse OriginalKey := originalMerge86 ++ originalMerge115

def originalMerge117 : Integer.Sparse OriginalKey := originalMerge57 ++ originalMerge116

def originalMerge118 : Integer.Sparse OriginalKey := originalTerm120 ++ originalTerm121

def originalMerge119 : Integer.Sparse OriginalKey := originalTerm119 ++ originalMerge118

def originalMerge120 : Integer.Sparse OriginalKey := originalTerm122 ++ originalTerm123

def originalMerge121 : Integer.Sparse OriginalKey := originalTerm124 ++ originalTerm125

def originalMerge122 : Integer.Sparse OriginalKey := originalMerge120 ++ originalMerge121

def originalMerge123 : Integer.Sparse OriginalKey := originalMerge119 ++ originalMerge122

def originalMerge124 : Integer.Sparse OriginalKey := originalTerm126 ++ originalTerm127

def originalMerge125 : Integer.Sparse OriginalKey := originalTerm128 ++ originalTerm129

def originalMerge126 : Integer.Sparse OriginalKey := originalMerge124 ++ originalMerge125

def originalMerge127 : Integer.Sparse OriginalKey := originalTerm130 ++ originalTerm131

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

def originalMerge128 : Integer.Sparse OriginalKey := originalTerm132 ++ originalTerm133

def originalMerge129 : Integer.Sparse OriginalKey := originalMerge127 ++ originalMerge128

def originalMerge130 : Integer.Sparse OriginalKey := originalMerge126 ++ originalMerge129

def originalMerge131 : Integer.Sparse OriginalKey := originalMerge123 ++ originalMerge130

def originalMerge132 : Integer.Sparse OriginalKey := originalTerm135 ++ originalTerm136

def originalMerge133 : Integer.Sparse OriginalKey := originalTerm134 ++ originalMerge132

def originalMerge134 : Integer.Sparse OriginalKey := originalTerm137 ++ originalTerm138

def originalMerge135 : Integer.Sparse OriginalKey := originalTerm139 ++ originalTerm140

def originalMerge136 : Integer.Sparse OriginalKey := originalMerge134 ++ originalMerge135

def originalMerge137 : Integer.Sparse OriginalKey := originalMerge133 ++ originalMerge136

def originalMerge138 : Integer.Sparse OriginalKey := originalTerm141 ++ originalTerm142

def originalMerge139 : Integer.Sparse OriginalKey := originalTerm143 ++ originalTerm144

def originalMerge140 : Integer.Sparse OriginalKey := originalMerge138 ++ originalMerge139

def originalMerge141 : Integer.Sparse OriginalKey := originalTerm145 ++ originalTerm146

def originalMerge142 : Integer.Sparse OriginalKey := originalTerm147 ++ originalTerm148

def originalMerge143 : Integer.Sparse OriginalKey := originalMerge141 ++ originalMerge142

def originalMerge144 : Integer.Sparse OriginalKey := originalMerge140 ++ originalMerge143

def originalMerge145 : Integer.Sparse OriginalKey := originalMerge137 ++ originalMerge144

def originalMerge146 : Integer.Sparse OriginalKey := originalMerge131 ++ originalMerge145

def originalMerge147 : Integer.Sparse OriginalKey := originalTerm150 ++ originalTerm151

def originalMerge148 : Integer.Sparse OriginalKey := originalTerm149 ++ originalMerge147

def originalMerge149 : Integer.Sparse OriginalKey := originalTerm152 ++ originalTerm153

def originalMerge150 : Integer.Sparse OriginalKey := originalTerm154 ++ originalTerm155

def originalMerge151 : Integer.Sparse OriginalKey := originalMerge149 ++ originalMerge150

def originalMerge152 : Integer.Sparse OriginalKey := originalMerge148 ++ originalMerge151

def originalMerge153 : Integer.Sparse OriginalKey := originalTerm156 ++ originalTerm157

def originalMerge154 : Integer.Sparse OriginalKey := originalTerm158 ++ originalTerm159

def originalMerge155 : Integer.Sparse OriginalKey := originalMerge153 ++ originalMerge154

def originalMerge156 : Integer.Sparse OriginalKey := originalTerm160 ++ originalTerm161

def originalMerge157 : Integer.Sparse OriginalKey := originalTerm162 ++ originalTerm163

def originalMerge158 : Integer.Sparse OriginalKey := originalMerge156 ++ originalMerge157

def originalMerge159 : Integer.Sparse OriginalKey := originalMerge155 ++ originalMerge158

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge160 : Integer.Sparse OriginalKey := originalMerge152 ++ originalMerge159

def originalMerge161 : Integer.Sparse OriginalKey := originalTerm165 ++ originalTerm166

def originalMerge162 : Integer.Sparse OriginalKey := originalTerm164 ++ originalMerge161

def originalMerge163 : Integer.Sparse OriginalKey := originalTerm167 ++ originalTerm168

def originalMerge164 : Integer.Sparse OriginalKey := originalTerm169 ++ originalTerm170

def originalMerge165 : Integer.Sparse OriginalKey := originalMerge163 ++ originalMerge164

def originalMerge166 : Integer.Sparse OriginalKey := originalMerge162 ++ originalMerge165

def originalMerge167 : Integer.Sparse OriginalKey := originalTerm171 ++ originalTerm172

def originalMerge168 : Integer.Sparse OriginalKey := originalTerm173 ++ originalTerm174

def originalMerge169 : Integer.Sparse OriginalKey := originalMerge167 ++ originalMerge168

def originalMerge170 : Integer.Sparse OriginalKey := originalTerm175 ++ originalTerm176

def originalMerge171 : Integer.Sparse OriginalKey := originalTerm177 ++ originalTerm178

def originalMerge172 : Integer.Sparse OriginalKey := originalMerge170 ++ originalMerge171

def originalMerge173 : Integer.Sparse OriginalKey := originalMerge169 ++ originalMerge172

def originalMerge174 : Integer.Sparse OriginalKey := originalMerge166 ++ originalMerge173

def originalMerge175 : Integer.Sparse OriginalKey := originalMerge160 ++ originalMerge174

def originalMerge176 : Integer.Sparse OriginalKey := originalMerge146 ++ originalMerge175

def originalMerge177 : Integer.Sparse OriginalKey := originalTerm180 ++ originalTerm181

def originalMerge178 : Integer.Sparse OriginalKey := originalTerm179 ++ originalMerge177

def originalMerge179 : Integer.Sparse OriginalKey := originalTerm182 ++ originalTerm183

def originalMerge180 : Integer.Sparse OriginalKey := originalTerm184 ++ originalTerm185

def originalMerge181 : Integer.Sparse OriginalKey := originalMerge179 ++ originalMerge180

def originalMerge182 : Integer.Sparse OriginalKey := originalMerge178 ++ originalMerge181

def originalMerge183 : Integer.Sparse OriginalKey := originalTerm186 ++ originalTerm187

def originalMerge184 : Integer.Sparse OriginalKey := originalTerm188 ++ originalTerm189

def originalMerge185 : Integer.Sparse OriginalKey := originalMerge183 ++ originalMerge184

def originalMerge186 : Integer.Sparse OriginalKey := originalTerm190 ++ originalTerm191

def originalMerge187 : Integer.Sparse OriginalKey := originalTerm192 ++ originalTerm193

def originalMerge188 : Integer.Sparse OriginalKey := originalMerge186 ++ originalMerge187

def originalMerge189 : Integer.Sparse OriginalKey := originalMerge185 ++ originalMerge188

def originalMerge190 : Integer.Sparse OriginalKey := originalMerge182 ++ originalMerge189

def originalMerge191 : Integer.Sparse OriginalKey := originalTerm195 ++ originalTerm196

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge192 : Integer.Sparse OriginalKey := originalTerm194 ++ originalMerge191

def originalMerge193 : Integer.Sparse OriginalKey := originalTerm197 ++ originalTerm198

def originalMerge194 : Integer.Sparse OriginalKey := originalTerm199 ++ originalTerm200

def originalMerge195 : Integer.Sparse OriginalKey := originalMerge193 ++ originalMerge194

def originalMerge196 : Integer.Sparse OriginalKey := originalMerge192 ++ originalMerge195

def originalMerge197 : Integer.Sparse OriginalKey := originalTerm201 ++ originalTerm202

def originalMerge198 : Integer.Sparse OriginalKey := originalTerm203 ++ originalTerm204

def originalMerge199 : Integer.Sparse OriginalKey := originalMerge197 ++ originalMerge198

def originalMerge200 : Integer.Sparse OriginalKey := originalTerm205 ++ originalTerm206

def originalMerge201 : Integer.Sparse OriginalKey := originalTerm207 ++ originalTerm208

def originalMerge202 : Integer.Sparse OriginalKey := originalMerge200 ++ originalMerge201

def originalMerge203 : Integer.Sparse OriginalKey := originalMerge199 ++ originalMerge202

def originalMerge204 : Integer.Sparse OriginalKey := originalMerge196 ++ originalMerge203

def originalMerge205 : Integer.Sparse OriginalKey := originalMerge190 ++ originalMerge204

def originalMerge206 : Integer.Sparse OriginalKey := originalTerm210 ++ originalTerm211

def originalMerge207 : Integer.Sparse OriginalKey := originalTerm209 ++ originalMerge206

def originalMerge208 : Integer.Sparse OriginalKey := originalTerm212 ++ originalTerm213

def originalMerge209 : Integer.Sparse OriginalKey := originalTerm214 ++ originalTerm215

def originalMerge210 : Integer.Sparse OriginalKey := originalMerge208 ++ originalMerge209

def originalMerge211 : Integer.Sparse OriginalKey := originalMerge207 ++ originalMerge210

def originalMerge212 : Integer.Sparse OriginalKey := originalTerm216 ++ originalTerm217

def originalMerge213 : Integer.Sparse OriginalKey := originalTerm218 ++ originalTerm219

def originalMerge214 : Integer.Sparse OriginalKey := originalMerge212 ++ originalMerge213

def originalMerge215 : Integer.Sparse OriginalKey := originalTerm220 ++ originalTerm221

def originalMerge216 : Integer.Sparse OriginalKey := originalTerm222 ++ originalTerm223

def originalMerge217 : Integer.Sparse OriginalKey := originalMerge215 ++ originalMerge216

def originalMerge218 : Integer.Sparse OriginalKey := originalMerge214 ++ originalMerge217

def originalMerge219 : Integer.Sparse OriginalKey := originalMerge211 ++ originalMerge218

def originalMerge220 : Integer.Sparse OriginalKey := originalTerm225 ++ originalTerm226

def originalMerge221 : Integer.Sparse OriginalKey := originalTerm224 ++ originalMerge220

def originalMerge222 : Integer.Sparse OriginalKey := originalTerm227 ++ originalTerm228

def originalMerge223 : Integer.Sparse OriginalKey := originalTerm229 ++ originalTerm230

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge224 : Integer.Sparse OriginalKey := originalMerge222 ++ originalMerge223

def originalMerge225 : Integer.Sparse OriginalKey := originalMerge221 ++ originalMerge224

def originalMerge226 : Integer.Sparse OriginalKey := originalTerm231 ++ originalTerm232

def originalMerge227 : Integer.Sparse OriginalKey := originalTerm233 ++ originalTerm234

def originalMerge228 : Integer.Sparse OriginalKey := originalMerge226 ++ originalMerge227

def originalMerge229 : Integer.Sparse OriginalKey := originalTerm235 ++ originalTerm236

def originalMerge230 : Integer.Sparse OriginalKey := originalTerm237 ++ originalTerm238

def originalMerge231 : Integer.Sparse OriginalKey := originalMerge229 ++ originalMerge230

def originalMerge232 : Integer.Sparse OriginalKey := originalMerge228 ++ originalMerge231

def originalMerge233 : Integer.Sparse OriginalKey := originalMerge225 ++ originalMerge232

def originalMerge234 : Integer.Sparse OriginalKey := originalMerge219 ++ originalMerge233

def originalMerge235 : Integer.Sparse OriginalKey := originalMerge205 ++ originalMerge234

def originalMerge236 : Integer.Sparse OriginalKey := originalMerge176 ++ originalMerge235

def originalMerge237 : Integer.Sparse OriginalKey := originalMerge117 ++ originalMerge236

def originalMerge238 : Integer.Sparse OriginalKey := originalTerm240 ++ originalTerm241

def originalMerge239 : Integer.Sparse OriginalKey := originalTerm239 ++ originalMerge238

def originalMerge240 : Integer.Sparse OriginalKey := originalTerm242 ++ originalTerm243

def originalMerge241 : Integer.Sparse OriginalKey := originalTerm244 ++ originalTerm245

def originalMerge242 : Integer.Sparse OriginalKey := originalMerge240 ++ originalMerge241

def originalMerge243 : Integer.Sparse OriginalKey := originalMerge239 ++ originalMerge242

def originalMerge244 : Integer.Sparse OriginalKey := originalTerm246 ++ originalTerm247

def originalMerge245 : Integer.Sparse OriginalKey := originalTerm248 ++ originalTerm249

def originalMerge246 : Integer.Sparse OriginalKey := originalMerge244 ++ originalMerge245

def originalMerge247 : Integer.Sparse OriginalKey := originalTerm250 ++ originalTerm251

def originalMerge248 : Integer.Sparse OriginalKey := originalTerm252 ++ originalTerm253

def originalMerge249 : Integer.Sparse OriginalKey := originalMerge247 ++ originalMerge248

def originalMerge250 : Integer.Sparse OriginalKey := originalMerge246 ++ originalMerge249

def originalMerge251 : Integer.Sparse OriginalKey := originalMerge243 ++ originalMerge250

def originalMerge252 : Integer.Sparse OriginalKey := originalTerm255 ++ originalTerm256

def originalMerge253 : Integer.Sparse OriginalKey := originalTerm254 ++ originalMerge252

def originalMerge254 : Integer.Sparse OriginalKey := originalTerm257 ++ originalTerm258

def originalMerge255 : Integer.Sparse OriginalKey := originalTerm259 ++ originalTerm260

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge256 : Integer.Sparse OriginalKey := originalMerge254 ++ originalMerge255

def originalMerge257 : Integer.Sparse OriginalKey := originalMerge253 ++ originalMerge256

def originalMerge258 : Integer.Sparse OriginalKey := originalTerm261 ++ originalTerm262

def originalMerge259 : Integer.Sparse OriginalKey := originalTerm263 ++ originalTerm264

def originalMerge260 : Integer.Sparse OriginalKey := originalMerge258 ++ originalMerge259

def originalMerge261 : Integer.Sparse OriginalKey := originalTerm265 ++ originalTerm266

def originalMerge262 : Integer.Sparse OriginalKey := originalTerm267 ++ originalTerm268

def originalMerge263 : Integer.Sparse OriginalKey := originalMerge261 ++ originalMerge262

def originalMerge264 : Integer.Sparse OriginalKey := originalMerge260 ++ originalMerge263

def originalMerge265 : Integer.Sparse OriginalKey := originalMerge257 ++ originalMerge264

def originalMerge266 : Integer.Sparse OriginalKey := originalMerge251 ++ originalMerge265

def originalMerge267 : Integer.Sparse OriginalKey := originalTerm270 ++ originalTerm271

def originalMerge268 : Integer.Sparse OriginalKey := originalTerm269 ++ originalMerge267

def originalMerge269 : Integer.Sparse OriginalKey := originalTerm272 ++ originalTerm273

def originalMerge270 : Integer.Sparse OriginalKey := originalTerm274 ++ originalTerm275

def originalMerge271 : Integer.Sparse OriginalKey := originalMerge269 ++ originalMerge270

def originalMerge272 : Integer.Sparse OriginalKey := originalMerge268 ++ originalMerge271

def originalMerge273 : Integer.Sparse OriginalKey := originalTerm276 ++ originalTerm277

def originalMerge274 : Integer.Sparse OriginalKey := originalTerm278 ++ originalTerm279

def originalMerge275 : Integer.Sparse OriginalKey := originalMerge273 ++ originalMerge274

def originalMerge276 : Integer.Sparse OriginalKey := originalTerm280 ++ originalTerm281

def originalMerge277 : Integer.Sparse OriginalKey := originalTerm282 ++ originalTerm283

def originalMerge278 : Integer.Sparse OriginalKey := originalMerge276 ++ originalMerge277

def originalMerge279 : Integer.Sparse OriginalKey := originalMerge275 ++ originalMerge278

def originalMerge280 : Integer.Sparse OriginalKey := originalMerge272 ++ originalMerge279

def originalMerge281 : Integer.Sparse OriginalKey := originalTerm285 ++ originalTerm286

def originalMerge282 : Integer.Sparse OriginalKey := originalTerm284 ++ originalMerge281

def originalMerge283 : Integer.Sparse OriginalKey := originalTerm287 ++ originalTerm288

def originalMerge284 : Integer.Sparse OriginalKey := originalTerm289 ++ originalTerm290

def originalMerge285 : Integer.Sparse OriginalKey := originalMerge283 ++ originalMerge284

def originalMerge286 : Integer.Sparse OriginalKey := originalMerge282 ++ originalMerge285

def originalMerge287 : Integer.Sparse OriginalKey := originalTerm291 ++ originalTerm292

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge288 : Integer.Sparse OriginalKey := originalTerm293 ++ originalTerm294

def originalMerge289 : Integer.Sparse OriginalKey := originalMerge287 ++ originalMerge288

def originalMerge290 : Integer.Sparse OriginalKey := originalTerm295 ++ originalTerm296

def originalMerge291 : Integer.Sparse OriginalKey := originalTerm297 ++ originalTerm298

def originalMerge292 : Integer.Sparse OriginalKey := originalMerge290 ++ originalMerge291

def originalMerge293 : Integer.Sparse OriginalKey := originalMerge289 ++ originalMerge292

def originalMerge294 : Integer.Sparse OriginalKey := originalMerge286 ++ originalMerge293

def originalMerge295 : Integer.Sparse OriginalKey := originalMerge280 ++ originalMerge294

def originalMerge296 : Integer.Sparse OriginalKey := originalMerge266 ++ originalMerge295

def originalMerge297 : Integer.Sparse OriginalKey := originalTerm300 ++ originalTerm301

def originalMerge298 : Integer.Sparse OriginalKey := originalTerm299 ++ originalMerge297

def originalMerge299 : Integer.Sparse OriginalKey := originalTerm302 ++ originalTerm303

def originalMerge300 : Integer.Sparse OriginalKey := originalTerm304 ++ originalTerm305

def originalMerge301 : Integer.Sparse OriginalKey := originalMerge299 ++ originalMerge300

def originalMerge302 : Integer.Sparse OriginalKey := originalMerge298 ++ originalMerge301

def originalMerge303 : Integer.Sparse OriginalKey := originalTerm306 ++ originalTerm307

def originalMerge304 : Integer.Sparse OriginalKey := originalTerm308 ++ originalTerm309

def originalMerge305 : Integer.Sparse OriginalKey := originalMerge303 ++ originalMerge304

def originalMerge306 : Integer.Sparse OriginalKey := originalTerm310 ++ originalTerm311

def originalMerge307 : Integer.Sparse OriginalKey := originalTerm312 ++ originalTerm313

def originalMerge308 : Integer.Sparse OriginalKey := originalMerge306 ++ originalMerge307

def originalMerge309 : Integer.Sparse OriginalKey := originalMerge305 ++ originalMerge308

def originalMerge310 : Integer.Sparse OriginalKey := originalMerge302 ++ originalMerge309

def originalMerge311 : Integer.Sparse OriginalKey := originalTerm315 ++ originalTerm316

def originalMerge312 : Integer.Sparse OriginalKey := originalTerm314 ++ originalMerge311

def originalMerge313 : Integer.Sparse OriginalKey := originalTerm317 ++ originalTerm318

def originalMerge314 : Integer.Sparse OriginalKey := originalTerm319 ++ originalTerm320

def originalMerge315 : Integer.Sparse OriginalKey := originalMerge313 ++ originalMerge314

def originalMerge316 : Integer.Sparse OriginalKey := originalMerge312 ++ originalMerge315

def originalMerge317 : Integer.Sparse OriginalKey := originalTerm321 ++ originalTerm322

def originalMerge318 : Integer.Sparse OriginalKey := originalTerm323 ++ originalTerm324

def originalMerge319 : Integer.Sparse OriginalKey := originalMerge317 ++ originalMerge318

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge320 : Integer.Sparse OriginalKey := originalTerm325 ++ originalTerm326

def originalMerge321 : Integer.Sparse OriginalKey := originalTerm327 ++ originalTerm328

def originalMerge322 : Integer.Sparse OriginalKey := originalMerge320 ++ originalMerge321

def originalMerge323 : Integer.Sparse OriginalKey := originalMerge319 ++ originalMerge322

def originalMerge324 : Integer.Sparse OriginalKey := originalMerge316 ++ originalMerge323

def originalMerge325 : Integer.Sparse OriginalKey := originalMerge310 ++ originalMerge324

def originalMerge326 : Integer.Sparse OriginalKey := originalTerm330 ++ originalTerm331

def originalMerge327 : Integer.Sparse OriginalKey := originalTerm329 ++ originalMerge326

def originalMerge328 : Integer.Sparse OriginalKey := originalTerm332 ++ originalTerm333

def originalMerge329 : Integer.Sparse OriginalKey := originalTerm334 ++ originalTerm335

def originalMerge330 : Integer.Sparse OriginalKey := originalMerge328 ++ originalMerge329

def originalMerge331 : Integer.Sparse OriginalKey := originalMerge327 ++ originalMerge330

def originalMerge332 : Integer.Sparse OriginalKey := originalTerm336 ++ originalTerm337

def originalMerge333 : Integer.Sparse OriginalKey := originalTerm338 ++ originalTerm339

def originalMerge334 : Integer.Sparse OriginalKey := originalMerge332 ++ originalMerge333

def originalMerge335 : Integer.Sparse OriginalKey := originalTerm340 ++ originalTerm341

def originalMerge336 : Integer.Sparse OriginalKey := originalTerm342 ++ originalTerm343

def originalMerge337 : Integer.Sparse OriginalKey := originalMerge335 ++ originalMerge336

def originalMerge338 : Integer.Sparse OriginalKey := originalMerge334 ++ originalMerge337

def originalMerge339 : Integer.Sparse OriginalKey := originalMerge331 ++ originalMerge338

def originalMerge340 : Integer.Sparse OriginalKey := originalTerm345 ++ originalTerm346

def originalMerge341 : Integer.Sparse OriginalKey := originalTerm344 ++ originalMerge340

def originalMerge342 : Integer.Sparse OriginalKey := originalTerm347 ++ originalTerm348

def originalMerge343 : Integer.Sparse OriginalKey := originalTerm349 ++ originalTerm350

def originalMerge344 : Integer.Sparse OriginalKey := originalMerge342 ++ originalMerge343

def originalMerge345 : Integer.Sparse OriginalKey := originalMerge341 ++ originalMerge344

def originalMerge346 : Integer.Sparse OriginalKey := originalTerm351 ++ originalTerm352

def originalMerge347 : Integer.Sparse OriginalKey := originalTerm353 ++ originalTerm354

def originalMerge348 : Integer.Sparse OriginalKey := originalMerge346 ++ originalMerge347

def originalMerge349 : Integer.Sparse OriginalKey := originalTerm355 ++ originalTerm356

def originalMerge350 : Integer.Sparse OriginalKey := originalTerm357 ++ originalTerm358

def originalMerge351 : Integer.Sparse OriginalKey := originalMerge349 ++ originalMerge350

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge352 : Integer.Sparse OriginalKey := originalMerge348 ++ originalMerge351

def originalMerge353 : Integer.Sparse OriginalKey := originalMerge345 ++ originalMerge352

def originalMerge354 : Integer.Sparse OriginalKey := originalMerge339 ++ originalMerge353

def originalMerge355 : Integer.Sparse OriginalKey := originalMerge325 ++ originalMerge354

def originalMerge356 : Integer.Sparse OriginalKey := originalMerge296 ++ originalMerge355

def originalMerge357 : Integer.Sparse OriginalKey := originalTerm360 ++ originalTerm361

def originalMerge358 : Integer.Sparse OriginalKey := originalTerm359 ++ originalMerge357

def originalMerge359 : Integer.Sparse OriginalKey := originalTerm362 ++ originalTerm363

def originalMerge360 : Integer.Sparse OriginalKey := originalTerm364 ++ originalTerm365

def originalMerge361 : Integer.Sparse OriginalKey := originalMerge359 ++ originalMerge360

def originalMerge362 : Integer.Sparse OriginalKey := originalMerge358 ++ originalMerge361

def originalMerge363 : Integer.Sparse OriginalKey := originalTerm366 ++ originalTerm367

def originalMerge364 : Integer.Sparse OriginalKey := originalTerm368 ++ originalTerm369

def originalMerge365 : Integer.Sparse OriginalKey := originalMerge363 ++ originalMerge364

def originalMerge366 : Integer.Sparse OriginalKey := originalTerm370 ++ originalTerm371

def originalMerge367 : Integer.Sparse OriginalKey := originalTerm372 ++ originalTerm373

def originalMerge368 : Integer.Sparse OriginalKey := originalMerge366 ++ originalMerge367

def originalMerge369 : Integer.Sparse OriginalKey := originalMerge365 ++ originalMerge368

def originalMerge370 : Integer.Sparse OriginalKey := originalMerge362 ++ originalMerge369

def originalMerge371 : Integer.Sparse OriginalKey := originalTerm375 ++ originalTerm376

def originalMerge372 : Integer.Sparse OriginalKey := originalTerm374 ++ originalMerge371

def originalMerge373 : Integer.Sparse OriginalKey := originalTerm377 ++ originalTerm378

def originalMerge374 : Integer.Sparse OriginalKey := originalTerm379 ++ originalTerm380

def originalMerge375 : Integer.Sparse OriginalKey := originalMerge373 ++ originalMerge374

def originalMerge376 : Integer.Sparse OriginalKey := originalMerge372 ++ originalMerge375

def originalMerge377 : Integer.Sparse OriginalKey := originalTerm381 ++ originalTerm382

def originalMerge378 : Integer.Sparse OriginalKey := originalTerm383 ++ originalTerm384

def originalMerge379 : Integer.Sparse OriginalKey := originalMerge377 ++ originalMerge378

def originalMerge380 : Integer.Sparse OriginalKey := originalTerm385 ++ originalTerm386

def originalMerge381 : Integer.Sparse OriginalKey := originalTerm387 ++ originalTerm388

def originalMerge382 : Integer.Sparse OriginalKey := originalMerge380 ++ originalMerge381

def originalMerge383 : Integer.Sparse OriginalKey := originalMerge379 ++ originalMerge382

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge384 : Integer.Sparse OriginalKey := originalMerge376 ++ originalMerge383

def originalMerge385 : Integer.Sparse OriginalKey := originalMerge370 ++ originalMerge384

def originalMerge386 : Integer.Sparse OriginalKey := originalTerm390 ++ originalTerm391

def originalMerge387 : Integer.Sparse OriginalKey := originalTerm389 ++ originalMerge386

def originalMerge388 : Integer.Sparse OriginalKey := originalTerm392 ++ originalTerm393

def originalMerge389 : Integer.Sparse OriginalKey := originalTerm394 ++ originalTerm395

def originalMerge390 : Integer.Sparse OriginalKey := originalMerge388 ++ originalMerge389

def originalMerge391 : Integer.Sparse OriginalKey := originalMerge387 ++ originalMerge390

def originalMerge392 : Integer.Sparse OriginalKey := originalTerm396 ++ originalTerm397

def originalMerge393 : Integer.Sparse OriginalKey := originalTerm398 ++ originalTerm399

def originalMerge394 : Integer.Sparse OriginalKey := originalMerge392 ++ originalMerge393

def originalMerge395 : Integer.Sparse OriginalKey := originalTerm400 ++ originalTerm401

def originalMerge396 : Integer.Sparse OriginalKey := originalTerm402 ++ originalTerm403

def originalMerge397 : Integer.Sparse OriginalKey := originalMerge395 ++ originalMerge396

def originalMerge398 : Integer.Sparse OriginalKey := originalMerge394 ++ originalMerge397

def originalMerge399 : Integer.Sparse OriginalKey := originalMerge391 ++ originalMerge398

def originalMerge400 : Integer.Sparse OriginalKey := originalTerm405 ++ originalTerm406

def originalMerge401 : Integer.Sparse OriginalKey := originalTerm404 ++ originalMerge400

def originalMerge402 : Integer.Sparse OriginalKey := originalTerm407 ++ originalTerm408

def originalMerge403 : Integer.Sparse OriginalKey := originalTerm409 ++ originalTerm410

def originalMerge404 : Integer.Sparse OriginalKey := originalMerge402 ++ originalMerge403

def originalMerge405 : Integer.Sparse OriginalKey := originalMerge401 ++ originalMerge404

def originalMerge406 : Integer.Sparse OriginalKey := originalTerm411 ++ originalTerm412

def originalMerge407 : Integer.Sparse OriginalKey := originalTerm413 ++ originalTerm414

def originalMerge408 : Integer.Sparse OriginalKey := originalMerge406 ++ originalMerge407

def originalMerge409 : Integer.Sparse OriginalKey := originalTerm415 ++ originalTerm416

def originalMerge410 : Integer.Sparse OriginalKey := originalTerm417 ++ originalTerm418

def originalMerge411 : Integer.Sparse OriginalKey := originalMerge409 ++ originalMerge410

def originalMerge412 : Integer.Sparse OriginalKey := originalMerge408 ++ originalMerge411

def originalMerge413 : Integer.Sparse OriginalKey := originalMerge405 ++ originalMerge412

def originalMerge414 : Integer.Sparse OriginalKey := originalMerge399 ++ originalMerge413

def originalMerge415 : Integer.Sparse OriginalKey := originalMerge385 ++ originalMerge414

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge416 : Integer.Sparse OriginalKey := originalTerm420 ++ originalTerm421

def originalMerge417 : Integer.Sparse OriginalKey := originalTerm419 ++ originalMerge416

def originalMerge418 : Integer.Sparse OriginalKey := originalTerm422 ++ originalTerm423

def originalMerge419 : Integer.Sparse OriginalKey := originalTerm424 ++ originalTerm425

def originalMerge420 : Integer.Sparse OriginalKey := originalMerge418 ++ originalMerge419

def originalMerge421 : Integer.Sparse OriginalKey := originalMerge417 ++ originalMerge420

def originalMerge422 : Integer.Sparse OriginalKey := originalTerm426 ++ originalTerm427

def originalMerge423 : Integer.Sparse OriginalKey := originalTerm428 ++ originalTerm429

def originalMerge424 : Integer.Sparse OriginalKey := originalMerge422 ++ originalMerge423

def originalMerge425 : Integer.Sparse OriginalKey := originalTerm430 ++ originalTerm431

def originalMerge426 : Integer.Sparse OriginalKey := originalTerm432 ++ originalTerm433

def originalMerge427 : Integer.Sparse OriginalKey := originalMerge425 ++ originalMerge426

def originalMerge428 : Integer.Sparse OriginalKey := originalMerge424 ++ originalMerge427

def originalMerge429 : Integer.Sparse OriginalKey := originalMerge421 ++ originalMerge428

def originalMerge430 : Integer.Sparse OriginalKey := originalTerm435 ++ originalTerm436

def originalMerge431 : Integer.Sparse OriginalKey := originalTerm434 ++ originalMerge430

def originalMerge432 : Integer.Sparse OriginalKey := originalTerm437 ++ originalTerm438

def originalMerge433 : Integer.Sparse OriginalKey := originalTerm439 ++ originalTerm440

def originalMerge434 : Integer.Sparse OriginalKey := originalMerge432 ++ originalMerge433

def originalMerge435 : Integer.Sparse OriginalKey := originalMerge431 ++ originalMerge434

def originalMerge436 : Integer.Sparse OriginalKey := originalTerm441 ++ originalTerm442

def originalMerge437 : Integer.Sparse OriginalKey := originalTerm443 ++ originalTerm444

def originalMerge438 : Integer.Sparse OriginalKey := originalMerge436 ++ originalMerge437

def originalMerge439 : Integer.Sparse OriginalKey := originalTerm445 ++ originalTerm446

def originalMerge440 : Integer.Sparse OriginalKey := originalTerm447 ++ originalTerm448

def originalMerge441 : Integer.Sparse OriginalKey := originalMerge439 ++ originalMerge440

def originalMerge442 : Integer.Sparse OriginalKey := originalMerge438 ++ originalMerge441

def originalMerge443 : Integer.Sparse OriginalKey := originalMerge435 ++ originalMerge442

def originalMerge444 : Integer.Sparse OriginalKey := originalMerge429 ++ originalMerge443

def originalMerge445 : Integer.Sparse OriginalKey := originalTerm450 ++ originalTerm451

def originalMerge446 : Integer.Sparse OriginalKey := originalTerm449 ++ originalMerge445

def originalMerge447 : Integer.Sparse OriginalKey := originalTerm452 ++ originalTerm453

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge448 : Integer.Sparse OriginalKey := originalTerm454 ++ originalTerm455

def originalMerge449 : Integer.Sparse OriginalKey := originalMerge447 ++ originalMerge448

def originalMerge450 : Integer.Sparse OriginalKey := originalMerge446 ++ originalMerge449

def originalMerge451 : Integer.Sparse OriginalKey := originalTerm456 ++ originalTerm457

def originalMerge452 : Integer.Sparse OriginalKey := originalTerm458 ++ originalTerm459

def originalMerge453 : Integer.Sparse OriginalKey := originalMerge451 ++ originalMerge452

def originalMerge454 : Integer.Sparse OriginalKey := originalTerm460 ++ originalTerm461

def originalMerge455 : Integer.Sparse OriginalKey := originalTerm462 ++ originalTerm463

def originalMerge456 : Integer.Sparse OriginalKey := originalMerge454 ++ originalMerge455

def originalMerge457 : Integer.Sparse OriginalKey := originalMerge453 ++ originalMerge456

def originalMerge458 : Integer.Sparse OriginalKey := originalMerge450 ++ originalMerge457

def originalMerge459 : Integer.Sparse OriginalKey := originalTerm465 ++ originalTerm466

def originalMerge460 : Integer.Sparse OriginalKey := originalTerm464 ++ originalMerge459

def originalMerge461 : Integer.Sparse OriginalKey := originalTerm467 ++ originalTerm468

def originalMerge462 : Integer.Sparse OriginalKey := originalTerm469 ++ originalTerm470

def originalMerge463 : Integer.Sparse OriginalKey := originalMerge461 ++ originalMerge462

def originalMerge464 : Integer.Sparse OriginalKey := originalMerge460 ++ originalMerge463

def originalMerge465 : Integer.Sparse OriginalKey := originalTerm471 ++ originalTerm472

def originalMerge466 : Integer.Sparse OriginalKey := originalTerm473 ++ originalTerm474

def originalMerge467 : Integer.Sparse OriginalKey := originalMerge465 ++ originalMerge466

def originalMerge468 : Integer.Sparse OriginalKey := originalTerm475 ++ originalTerm476

def originalMerge469 : Integer.Sparse OriginalKey := originalTerm477 ++ originalTerm478

def originalMerge470 : Integer.Sparse OriginalKey := originalMerge468 ++ originalMerge469

def originalMerge471 : Integer.Sparse OriginalKey := originalMerge467 ++ originalMerge470

def originalMerge472 : Integer.Sparse OriginalKey := originalMerge464 ++ originalMerge471

def originalMerge473 : Integer.Sparse OriginalKey := originalMerge458 ++ originalMerge472

def originalMerge474 : Integer.Sparse OriginalKey := originalMerge444 ++ originalMerge473

def originalMerge475 : Integer.Sparse OriginalKey := originalMerge415 ++ originalMerge474

def originalMerge476 : Integer.Sparse OriginalKey := originalMerge356 ++ originalMerge475

def originalMerge477 : Integer.Sparse OriginalKey := originalMerge237 ++ originalMerge476

def originalMerge478 : Integer.Sparse OriginalKey := originalTerm480 ++ originalTerm481

def originalMerge479 : Integer.Sparse OriginalKey := originalTerm479 ++ originalMerge478

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge480 : Integer.Sparse OriginalKey := originalTerm482 ++ originalTerm483

def originalMerge481 : Integer.Sparse OriginalKey := originalTerm484 ++ originalTerm485

def originalMerge482 : Integer.Sparse OriginalKey := originalMerge480 ++ originalMerge481

def originalMerge483 : Integer.Sparse OriginalKey := originalMerge479 ++ originalMerge482

def originalMerge484 : Integer.Sparse OriginalKey := originalTerm486 ++ originalTerm487

def originalMerge485 : Integer.Sparse OriginalKey := originalTerm488 ++ originalTerm489

def originalMerge486 : Integer.Sparse OriginalKey := originalMerge484 ++ originalMerge485

def originalMerge487 : Integer.Sparse OriginalKey := originalTerm490 ++ originalTerm491

def originalMerge488 : Integer.Sparse OriginalKey := originalTerm492 ++ originalTerm493

def originalMerge489 : Integer.Sparse OriginalKey := originalMerge487 ++ originalMerge488

def originalMerge490 : Integer.Sparse OriginalKey := originalMerge486 ++ originalMerge489

def originalMerge491 : Integer.Sparse OriginalKey := originalMerge483 ++ originalMerge490

def originalMerge492 : Integer.Sparse OriginalKey := originalTerm495 ++ originalTerm496

def originalMerge493 : Integer.Sparse OriginalKey := originalTerm494 ++ originalMerge492

def originalMerge494 : Integer.Sparse OriginalKey := originalTerm497 ++ originalTerm498

def originalMerge495 : Integer.Sparse OriginalKey := originalTerm499 ++ originalTerm500

def originalMerge496 : Integer.Sparse OriginalKey := originalMerge494 ++ originalMerge495

def originalMerge497 : Integer.Sparse OriginalKey := originalMerge493 ++ originalMerge496

def originalMerge498 : Integer.Sparse OriginalKey := originalTerm501 ++ originalTerm502

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge958 : Integer.Sparse OriginalKey := originalTerm960 ++ originalTerm961

def originalMerge959 : Integer.Sparse OriginalKey := originalTerm959 ++ originalMerge958

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge960 : Integer.Sparse OriginalKey := originalTerm962 ++ originalTerm963

def originalMerge961 : Integer.Sparse OriginalKey := originalTerm964 ++ originalTerm965

def originalMerge962 : Integer.Sparse OriginalKey := originalMerge960 ++ originalMerge961

def originalMerge963 : Integer.Sparse OriginalKey := originalMerge959 ++ originalMerge962

def originalMerge964 : Integer.Sparse OriginalKey := originalTerm966 ++ originalTerm967

def originalMerge965 : Integer.Sparse OriginalKey := originalTerm968 ++ originalTerm969

def originalMerge966 : Integer.Sparse OriginalKey := originalMerge964 ++ originalMerge965

def originalMerge967 : Integer.Sparse OriginalKey := originalTerm970 ++ originalTerm971

def originalMerge968 : Integer.Sparse OriginalKey := originalTerm972 ++ originalTerm973

def originalMerge969 : Integer.Sparse OriginalKey := originalMerge967 ++ originalMerge968

def originalMerge970 : Integer.Sparse OriginalKey := originalMerge966 ++ originalMerge969

def originalMerge971 : Integer.Sparse OriginalKey := originalMerge963 ++ originalMerge970

def originalMerge972 : Integer.Sparse OriginalKey := originalTerm975 ++ originalTerm976

def originalMerge973 : Integer.Sparse OriginalKey := originalTerm974 ++ originalMerge972

def originalMerge974 : Integer.Sparse OriginalKey := originalTerm977 ++ originalTerm978

def originalMerge975 : Integer.Sparse OriginalKey := originalTerm979 ++ originalTerm980

def originalMerge976 : Integer.Sparse OriginalKey := originalMerge974 ++ originalMerge975

def originalMerge977 : Integer.Sparse OriginalKey := originalMerge973 ++ originalMerge976

def originalMerge978 : Integer.Sparse OriginalKey := originalTerm981 ++ originalTerm982

def originalMerge979 : Integer.Sparse OriginalKey := originalTerm983 ++ originalTerm984

def originalMerge980 : Integer.Sparse OriginalKey := originalMerge978 ++ originalMerge979

def originalMerge981 : Integer.Sparse OriginalKey := originalTerm985 ++ originalTerm986

def originalMerge982 : Integer.Sparse OriginalKey := originalTerm987 ++ originalTerm988

def originalMerge983 : Integer.Sparse OriginalKey := originalMerge981 ++ originalMerge982

def originalMerge984 : Integer.Sparse OriginalKey := originalMerge980 ++ originalMerge983

def originalMerge985 : Integer.Sparse OriginalKey := originalMerge977 ++ originalMerge984

def originalMerge986 : Integer.Sparse OriginalKey := originalMerge971 ++ originalMerge985

def originalMerge987 : Integer.Sparse OriginalKey := originalTerm990 ++ originalTerm991

def originalMerge988 : Integer.Sparse OriginalKey := originalTerm989 ++ originalMerge987

def originalMerge989 : Integer.Sparse OriginalKey := originalTerm992 ++ originalTerm993

def originalMerge990 : Integer.Sparse OriginalKey := originalTerm994 ++ originalTerm995

def originalMerge991 : Integer.Sparse OriginalKey := originalMerge989 ++ originalMerge990

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

def originalMerge992 : Integer.Sparse OriginalKey := originalMerge988 ++ originalMerge991

def originalMerge993 : Integer.Sparse OriginalKey := originalTerm996 ++ originalTerm997

def originalMerge994 : Integer.Sparse OriginalKey := originalTerm998 ++ originalTerm999

def originalMerge995 : Integer.Sparse OriginalKey := originalMerge993 ++ originalMerge994

def originalMerge996 : Integer.Sparse OriginalKey := originalTerm1000 ++ originalTerm1001

def originalMerge997 : Integer.Sparse OriginalKey := originalTerm1002 ++ originalTerm1003

def originalMerge998 : Integer.Sparse OriginalKey := originalMerge996 ++ originalMerge997

def originalMerge999 : Integer.Sparse OriginalKey := originalMerge995 ++ originalMerge998

def originalMerge1000 : Integer.Sparse OriginalKey := originalMerge992 ++ originalMerge999

def originalMerge1001 : Integer.Sparse OriginalKey := originalTerm1005 ++ originalTerm1006

def originalMerge1002 : Integer.Sparse OriginalKey := originalTerm1004 ++ originalMerge1001

def originalMerge1003 : Integer.Sparse OriginalKey := originalTerm1007 ++ originalTerm1008

def originalMerge1004 : Integer.Sparse OriginalKey := originalTerm1009 ++ originalTerm1010

def originalMerge1005 : Integer.Sparse OriginalKey := originalMerge1003 ++ originalMerge1004

def originalMerge1006 : Integer.Sparse OriginalKey := originalMerge1002 ++ originalMerge1005

def originalMerge1007 : Integer.Sparse OriginalKey := originalTerm1011 ++ originalTerm1012

def originalMerge1008 : Integer.Sparse OriginalKey := originalTerm1013 ++ originalTerm1014

def originalMerge1009 : Integer.Sparse OriginalKey := originalMerge1007 ++ originalMerge1008

def originalMerge1010 : Integer.Sparse OriginalKey := originalTerm1015 ++ originalTerm1016

def originalMerge1011 : Integer.Sparse OriginalKey := originalTerm1017 ++ originalTerm1018

def originalMerge1012 : Integer.Sparse OriginalKey := originalMerge1010 ++ originalMerge1011

def originalMerge1013 : Integer.Sparse OriginalKey := originalMerge1009 ++ originalMerge1012

def originalMerge1014 : Integer.Sparse OriginalKey := originalMerge1006 ++ originalMerge1013

def originalMerge1015 : Integer.Sparse OriginalKey := originalMerge1000 ++ originalMerge1014

def originalMerge1016 : Integer.Sparse OriginalKey := originalMerge986 ++ originalMerge1015

def originalMerge1017 : Integer.Sparse OriginalKey := originalTerm1020 ++ originalTerm1021

def originalMerge1018 : Integer.Sparse OriginalKey := originalTerm1019 ++ originalMerge1017

def originalMerge1019 : Integer.Sparse OriginalKey := originalTerm1022 ++ originalTerm1023

def originalMerge1020 : Integer.Sparse OriginalKey := originalTerm1024 ++ originalTerm1025

def originalMerge1021 : Integer.Sparse OriginalKey := originalMerge1019 ++ originalMerge1020

def originalMerge1022 : Integer.Sparse OriginalKey := originalMerge1018 ++ originalMerge1021

def originalMerge1023 : Integer.Sparse OriginalKey := originalTerm1026 ++ originalTerm1027

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

def originalMerge1024 : Integer.Sparse OriginalKey := originalTerm1028 ++ originalTerm1029

def originalMerge1025 : Integer.Sparse OriginalKey := originalMerge1023 ++ originalMerge1024

def originalMerge1026 : Integer.Sparse OriginalKey := originalTerm1030 ++ originalTerm1031

def originalMerge1027 : Integer.Sparse OriginalKey := originalTerm1032 ++ originalTerm1033

def originalMerge1028 : Integer.Sparse OriginalKey := originalMerge1026 ++ originalMerge1027

def originalMerge1029 : Integer.Sparse OriginalKey := originalMerge1025 ++ originalMerge1028

def originalMerge1030 : Integer.Sparse OriginalKey := originalMerge1022 ++ originalMerge1029

def originalMerge1031 : Integer.Sparse OriginalKey := originalTerm1035 ++ originalTerm1036

def originalMerge1032 : Integer.Sparse OriginalKey := originalTerm1034 ++ originalMerge1031

def originalMerge1033 : Integer.Sparse OriginalKey := originalTerm1037 ++ originalTerm1038

def originalMerge1034 : Integer.Sparse OriginalKey := originalTerm1039 ++ originalTerm1040

def originalMerge1035 : Integer.Sparse OriginalKey := originalMerge1033 ++ originalMerge1034

def originalMerge1036 : Integer.Sparse OriginalKey := originalMerge1032 ++ originalMerge1035

def originalMerge1037 : Integer.Sparse OriginalKey := originalTerm1041 ++ originalTerm1042

def originalMerge1038 : Integer.Sparse OriginalKey := originalTerm1043 ++ originalTerm1044

def originalMerge1039 : Integer.Sparse OriginalKey := originalMerge1037 ++ originalMerge1038

def originalMerge1040 : Integer.Sparse OriginalKey := originalTerm1045 ++ originalTerm1046

def originalMerge1041 : Integer.Sparse OriginalKey := originalTerm1047 ++ originalTerm1048

def originalMerge1042 : Integer.Sparse OriginalKey := originalMerge1040 ++ originalMerge1041

def originalMerge1043 : Integer.Sparse OriginalKey := originalMerge1039 ++ originalMerge1042

def originalMerge1044 : Integer.Sparse OriginalKey := originalMerge1036 ++ originalMerge1043

def originalMerge1045 : Integer.Sparse OriginalKey := originalMerge1030 ++ originalMerge1044

def originalMerge1046 : Integer.Sparse OriginalKey := originalTerm1050 ++ originalTerm1051

def originalMerge1047 : Integer.Sparse OriginalKey := originalTerm1049 ++ originalMerge1046

def originalMerge1048 : Integer.Sparse OriginalKey := originalTerm1052 ++ originalTerm1053

def originalMerge1049 : Integer.Sparse OriginalKey := originalTerm1054 ++ originalTerm1055

def originalMerge1050 : Integer.Sparse OriginalKey := originalMerge1048 ++ originalMerge1049

def originalMerge1051 : Integer.Sparse OriginalKey := originalMerge1047 ++ originalMerge1050

def originalMerge1052 : Integer.Sparse OriginalKey := originalTerm1056 ++ originalTerm1057

def originalMerge1053 : Integer.Sparse OriginalKey := originalTerm1058 ++ originalTerm1059

def originalMerge1054 : Integer.Sparse OriginalKey := originalMerge1052 ++ originalMerge1053

def originalMerge1055 : Integer.Sparse OriginalKey := originalTerm1060 ++ originalTerm1061

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

def originalMerge1056 : Integer.Sparse OriginalKey := originalTerm1062 ++ originalTerm1063

def originalMerge1057 : Integer.Sparse OriginalKey := originalMerge1055 ++ originalMerge1056

def originalMerge1058 : Integer.Sparse OriginalKey := originalMerge1054 ++ originalMerge1057

def originalMerge1059 : Integer.Sparse OriginalKey := originalMerge1051 ++ originalMerge1058

def originalMerge1060 : Integer.Sparse OriginalKey := originalTerm1065 ++ originalTerm1066

def originalMerge1061 : Integer.Sparse OriginalKey := originalTerm1064 ++ originalMerge1060

def originalMerge1062 : Integer.Sparse OriginalKey := originalTerm1067 ++ originalTerm1068

def originalMerge1063 : Integer.Sparse OriginalKey := originalTerm1069 ++ originalTerm1070

def originalMerge1064 : Integer.Sparse OriginalKey := originalMerge1062 ++ originalMerge1063

def originalMerge1065 : Integer.Sparse OriginalKey := originalMerge1061 ++ originalMerge1064

def originalMerge1066 : Integer.Sparse OriginalKey := originalTerm1071 ++ originalTerm1072

def originalMerge1067 : Integer.Sparse OriginalKey := originalTerm1073 ++ originalTerm1074

def originalMerge1068 : Integer.Sparse OriginalKey := originalMerge1066 ++ originalMerge1067

def originalMerge1069 : Integer.Sparse OriginalKey := originalTerm1075 ++ originalTerm1076

def originalMerge1070 : Integer.Sparse OriginalKey := originalTerm1077 ++ originalTerm1078

def originalMerge1071 : Integer.Sparse OriginalKey := originalMerge1069 ++ originalMerge1070

def originalMerge1072 : Integer.Sparse OriginalKey := originalMerge1068 ++ originalMerge1071

def originalMerge1073 : Integer.Sparse OriginalKey := originalMerge1065 ++ originalMerge1072

def originalMerge1074 : Integer.Sparse OriginalKey := originalMerge1059 ++ originalMerge1073

def originalMerge1075 : Integer.Sparse OriginalKey := originalMerge1045 ++ originalMerge1074

def originalMerge1076 : Integer.Sparse OriginalKey := originalMerge1016 ++ originalMerge1075

def originalMerge1077 : Integer.Sparse OriginalKey := originalTerm1080 ++ originalTerm1081

def originalMerge1078 : Integer.Sparse OriginalKey := originalTerm1079 ++ originalMerge1077

def originalMerge1079 : Integer.Sparse OriginalKey := originalTerm1082 ++ originalTerm1083

def originalMerge1080 : Integer.Sparse OriginalKey := originalTerm1084 ++ originalTerm1085

def originalMerge1081 : Integer.Sparse OriginalKey := originalMerge1079 ++ originalMerge1080

def originalMerge1082 : Integer.Sparse OriginalKey := originalMerge1078 ++ originalMerge1081

def originalMerge1083 : Integer.Sparse OriginalKey := originalTerm1086 ++ originalTerm1087

def originalMerge1084 : Integer.Sparse OriginalKey := originalTerm1088 ++ originalTerm1089

def originalMerge1085 : Integer.Sparse OriginalKey := originalMerge1083 ++ originalMerge1084

def originalMerge1086 : Integer.Sparse OriginalKey := originalTerm1090 ++ originalTerm1091

def originalMerge1087 : Integer.Sparse OriginalKey := originalTerm1092 ++ originalTerm1093

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

def originalMerge1088 : Integer.Sparse OriginalKey := originalMerge1086 ++ originalMerge1087

def originalMerge1089 : Integer.Sparse OriginalKey := originalMerge1085 ++ originalMerge1088

def originalMerge1090 : Integer.Sparse OriginalKey := originalMerge1082 ++ originalMerge1089

def originalMerge1091 : Integer.Sparse OriginalKey := originalTerm1095 ++ originalTerm1096

def originalMerge1092 : Integer.Sparse OriginalKey := originalTerm1094 ++ originalMerge1091

def originalMerge1093 : Integer.Sparse OriginalKey := originalTerm1097 ++ originalTerm1098

def originalMerge1094 : Integer.Sparse OriginalKey := originalTerm1099 ++ originalTerm1100

def originalMerge1095 : Integer.Sparse OriginalKey := originalMerge1093 ++ originalMerge1094

def originalMerge1096 : Integer.Sparse OriginalKey := originalMerge1092 ++ originalMerge1095

def originalMerge1097 : Integer.Sparse OriginalKey := originalTerm1101 ++ originalTerm1102

def originalMerge1098 : Integer.Sparse OriginalKey := originalTerm1103 ++ originalTerm1104

def originalMerge1099 : Integer.Sparse OriginalKey := originalMerge1097 ++ originalMerge1098

def originalMerge1100 : Integer.Sparse OriginalKey := originalTerm1105 ++ originalTerm1106

def originalMerge1101 : Integer.Sparse OriginalKey := originalTerm1107 ++ originalTerm1108

def originalMerge1102 : Integer.Sparse OriginalKey := originalMerge1100 ++ originalMerge1101

def originalMerge1103 : Integer.Sparse OriginalKey := originalMerge1099 ++ originalMerge1102

def originalMerge1104 : Integer.Sparse OriginalKey := originalMerge1096 ++ originalMerge1103

def originalMerge1105 : Integer.Sparse OriginalKey := originalMerge1090 ++ originalMerge1104

def originalMerge1106 : Integer.Sparse OriginalKey := originalTerm1110 ++ originalTerm1111

def originalMerge1107 : Integer.Sparse OriginalKey := originalTerm1109 ++ originalMerge1106

def originalMerge1108 : Integer.Sparse OriginalKey := originalTerm1112 ++ originalTerm1113

def originalMerge1109 : Integer.Sparse OriginalKey := originalTerm1114 ++ originalTerm1115

def originalMerge1110 : Integer.Sparse OriginalKey := originalMerge1108 ++ originalMerge1109

def originalMerge1111 : Integer.Sparse OriginalKey := originalMerge1107 ++ originalMerge1110

def originalMerge1112 : Integer.Sparse OriginalKey := originalTerm1116 ++ originalTerm1117

def originalMerge1113 : Integer.Sparse OriginalKey := originalTerm1118 ++ originalTerm1119

def originalMerge1114 : Integer.Sparse OriginalKey := originalMerge1112 ++ originalMerge1113

def originalMerge1115 : Integer.Sparse OriginalKey := originalTerm1120 ++ originalTerm1121

def originalMerge1116 : Integer.Sparse OriginalKey := originalTerm1122 ++ originalTerm1123

def originalMerge1117 : Integer.Sparse OriginalKey := originalMerge1115 ++ originalMerge1116

def originalMerge1118 : Integer.Sparse OriginalKey := originalMerge1114 ++ originalMerge1117

def originalMerge1119 : Integer.Sparse OriginalKey := originalMerge1111 ++ originalMerge1118

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

def originalMerge1120 : Integer.Sparse OriginalKey := originalTerm1125 ++ originalTerm1126

def originalMerge1121 : Integer.Sparse OriginalKey := originalTerm1124 ++ originalMerge1120

def originalMerge1122 : Integer.Sparse OriginalKey := originalTerm1127 ++ originalTerm1128

def originalMerge1123 : Integer.Sparse OriginalKey := originalTerm1129 ++ originalTerm1130

def originalMerge1124 : Integer.Sparse OriginalKey := originalMerge1122 ++ originalMerge1123

def originalMerge1125 : Integer.Sparse OriginalKey := originalMerge1121 ++ originalMerge1124

def originalMerge1126 : Integer.Sparse OriginalKey := originalTerm1131 ++ originalTerm1132

def originalMerge1127 : Integer.Sparse OriginalKey := originalTerm1133 ++ originalTerm1134

def originalMerge1128 : Integer.Sparse OriginalKey := originalMerge1126 ++ originalMerge1127

def originalMerge1129 : Integer.Sparse OriginalKey := originalTerm1135 ++ originalTerm1136

def originalMerge1130 : Integer.Sparse OriginalKey := originalTerm1137 ++ originalTerm1138

def originalMerge1131 : Integer.Sparse OriginalKey := originalMerge1129 ++ originalMerge1130

def originalMerge1132 : Integer.Sparse OriginalKey := originalMerge1128 ++ originalMerge1131

def originalMerge1133 : Integer.Sparse OriginalKey := originalMerge1125 ++ originalMerge1132

def originalMerge1134 : Integer.Sparse OriginalKey := originalMerge1119 ++ originalMerge1133

def originalMerge1135 : Integer.Sparse OriginalKey := originalMerge1105 ++ originalMerge1134

def originalMerge1136 : Integer.Sparse OriginalKey := originalTerm1140 ++ originalTerm1141

def originalMerge1137 : Integer.Sparse OriginalKey := originalTerm1139 ++ originalMerge1136

def originalMerge1138 : Integer.Sparse OriginalKey := originalTerm1142 ++ originalTerm1143

def originalMerge1139 : Integer.Sparse OriginalKey := originalTerm1144 ++ originalTerm1145

def originalMerge1140 : Integer.Sparse OriginalKey := originalMerge1138 ++ originalMerge1139

def originalMerge1141 : Integer.Sparse OriginalKey := originalMerge1137 ++ originalMerge1140

def originalMerge1142 : Integer.Sparse OriginalKey := originalTerm1146 ++ originalTerm1147

def originalMerge1143 : Integer.Sparse OriginalKey := originalTerm1148 ++ originalTerm1149

def originalMerge1144 : Integer.Sparse OriginalKey := originalMerge1142 ++ originalMerge1143

def originalMerge1145 : Integer.Sparse OriginalKey := originalTerm1150 ++ originalTerm1151

def originalMerge1146 : Integer.Sparse OriginalKey := originalTerm1152 ++ originalTerm1153

def originalMerge1147 : Integer.Sparse OriginalKey := originalMerge1145 ++ originalMerge1146

def originalMerge1148 : Integer.Sparse OriginalKey := originalMerge1144 ++ originalMerge1147

def originalMerge1149 : Integer.Sparse OriginalKey := originalMerge1141 ++ originalMerge1148

def originalMerge1150 : Integer.Sparse OriginalKey := originalTerm1155 ++ originalTerm1156

def originalMerge1151 : Integer.Sparse OriginalKey := originalTerm1154 ++ originalMerge1150

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

def originalMerge1152 : Integer.Sparse OriginalKey := originalTerm1157 ++ originalTerm1158

def originalMerge1153 : Integer.Sparse OriginalKey := originalTerm1159 ++ originalTerm1160

def originalMerge1154 : Integer.Sparse OriginalKey := originalMerge1152 ++ originalMerge1153

def originalMerge1155 : Integer.Sparse OriginalKey := originalMerge1151 ++ originalMerge1154

def originalMerge1156 : Integer.Sparse OriginalKey := originalTerm1161 ++ originalTerm1162

def originalMerge1157 : Integer.Sparse OriginalKey := originalTerm1163 ++ originalTerm1164

def originalMerge1158 : Integer.Sparse OriginalKey := originalMerge1156 ++ originalMerge1157

def originalMerge1159 : Integer.Sparse OriginalKey := originalTerm1165 ++ originalTerm1166

def originalMerge1160 : Integer.Sparse OriginalKey := originalTerm1167 ++ originalTerm1168

def originalMerge1161 : Integer.Sparse OriginalKey := originalMerge1159 ++ originalMerge1160

def originalMerge1162 : Integer.Sparse OriginalKey := originalMerge1158 ++ originalMerge1161

def originalMerge1163 : Integer.Sparse OriginalKey := originalMerge1155 ++ originalMerge1162

def originalMerge1164 : Integer.Sparse OriginalKey := originalMerge1149 ++ originalMerge1163

def originalMerge1165 : Integer.Sparse OriginalKey := originalTerm1170 ++ originalTerm1171

def originalMerge1166 : Integer.Sparse OriginalKey := originalTerm1169 ++ originalMerge1165

def originalMerge1167 : Integer.Sparse OriginalKey := originalTerm1172 ++ originalTerm1173

def originalMerge1168 : Integer.Sparse OriginalKey := originalTerm1174 ++ originalTerm1175

def originalMerge1169 : Integer.Sparse OriginalKey := originalMerge1167 ++ originalMerge1168

def originalMerge1170 : Integer.Sparse OriginalKey := originalMerge1166 ++ originalMerge1169

def originalMerge1171 : Integer.Sparse OriginalKey := originalTerm1176 ++ originalTerm1177

def originalMerge1172 : Integer.Sparse OriginalKey := originalTerm1178 ++ originalTerm1179

def originalMerge1173 : Integer.Sparse OriginalKey := originalMerge1171 ++ originalMerge1172

def originalMerge1174 : Integer.Sparse OriginalKey := originalTerm1180 ++ originalTerm1181

def originalMerge1175 : Integer.Sparse OriginalKey := originalTerm1182 ++ originalTerm1183

def originalMerge1176 : Integer.Sparse OriginalKey := originalMerge1174 ++ originalMerge1175

def originalMerge1177 : Integer.Sparse OriginalKey := originalMerge1173 ++ originalMerge1176

def originalMerge1178 : Integer.Sparse OriginalKey := originalMerge1170 ++ originalMerge1177

def originalMerge1179 : Integer.Sparse OriginalKey := originalTerm1185 ++ originalTerm1186

def originalMerge1180 : Integer.Sparse OriginalKey := originalTerm1184 ++ originalMerge1179

def originalMerge1181 : Integer.Sparse OriginalKey := originalTerm1187 ++ originalTerm1188

def originalMerge1182 : Integer.Sparse OriginalKey := originalTerm1189 ++ originalTerm1190

def originalMerge1183 : Integer.Sparse OriginalKey := originalMerge1181 ++ originalMerge1182

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

def originalMerge1184 : Integer.Sparse OriginalKey := originalMerge1180 ++ originalMerge1183

def originalMerge1185 : Integer.Sparse OriginalKey := originalTerm1191 ++ originalTerm1192

def originalMerge1186 : Integer.Sparse OriginalKey := originalTerm1193 ++ originalTerm1194

def originalMerge1187 : Integer.Sparse OriginalKey := originalMerge1185 ++ originalMerge1186

def originalMerge1188 : Integer.Sparse OriginalKey := originalTerm1195 ++ originalTerm1196

def originalMerge1189 : Integer.Sparse OriginalKey := originalTerm1197 ++ originalTerm1198

def originalMerge1190 : Integer.Sparse OriginalKey := originalMerge1188 ++ originalMerge1189

def originalMerge1191 : Integer.Sparse OriginalKey := originalMerge1187 ++ originalMerge1190

def originalMerge1192 : Integer.Sparse OriginalKey := originalMerge1184 ++ originalMerge1191

def originalMerge1193 : Integer.Sparse OriginalKey := originalMerge1178 ++ originalMerge1192

def originalMerge1194 : Integer.Sparse OriginalKey := originalMerge1164 ++ originalMerge1193

def originalMerge1195 : Integer.Sparse OriginalKey := originalMerge1135 ++ originalMerge1194

def originalMerge1196 : Integer.Sparse OriginalKey := originalMerge1076 ++ originalMerge1195

def originalMerge1197 : Integer.Sparse OriginalKey := originalTerm1200 ++ originalTerm1201

def originalMerge1198 : Integer.Sparse OriginalKey := originalTerm1199 ++ originalMerge1197

def originalMerge1199 : Integer.Sparse OriginalKey := originalTerm1202 ++ originalTerm1203

def originalMerge1200 : Integer.Sparse OriginalKey := originalTerm1204 ++ originalTerm1205

def originalMerge1201 : Integer.Sparse OriginalKey := originalMerge1199 ++ originalMerge1200

def originalMerge1202 : Integer.Sparse OriginalKey := originalMerge1198 ++ originalMerge1201

def originalMerge1203 : Integer.Sparse OriginalKey := originalTerm1206 ++ originalTerm1207

def originalMerge1204 : Integer.Sparse OriginalKey := originalTerm1208 ++ originalTerm1209

def originalMerge1205 : Integer.Sparse OriginalKey := originalMerge1203 ++ originalMerge1204

def originalMerge1206 : Integer.Sparse OriginalKey := originalTerm1210 ++ originalTerm1211

def originalMerge1207 : Integer.Sparse OriginalKey := originalTerm1212 ++ originalTerm1213

def originalMerge1208 : Integer.Sparse OriginalKey := originalMerge1206 ++ originalMerge1207

def originalMerge1209 : Integer.Sparse OriginalKey := originalMerge1205 ++ originalMerge1208

def originalMerge1210 : Integer.Sparse OriginalKey := originalMerge1202 ++ originalMerge1209

def originalMerge1211 : Integer.Sparse OriginalKey := originalTerm1215 ++ originalTerm1216

def originalMerge1212 : Integer.Sparse OriginalKey := originalTerm1214 ++ originalMerge1211

def originalMerge1213 : Integer.Sparse OriginalKey := originalTerm1217 ++ originalTerm1218

def originalMerge1214 : Integer.Sparse OriginalKey := originalTerm1219 ++ originalTerm1220

def originalMerge1215 : Integer.Sparse OriginalKey := originalMerge1213 ++ originalMerge1214

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

def originalMerge1216 : Integer.Sparse OriginalKey := originalMerge1212 ++ originalMerge1215

def originalMerge1217 : Integer.Sparse OriginalKey := originalTerm1221 ++ originalTerm1222

def originalMerge1218 : Integer.Sparse OriginalKey := originalTerm1223 ++ originalTerm1224

def originalMerge1219 : Integer.Sparse OriginalKey := originalMerge1217 ++ originalMerge1218

def originalMerge1220 : Integer.Sparse OriginalKey := originalTerm1225 ++ originalTerm1226

def originalMerge1221 : Integer.Sparse OriginalKey := originalTerm1227 ++ originalTerm1228

def originalMerge1222 : Integer.Sparse OriginalKey := originalMerge1220 ++ originalMerge1221

def originalMerge1223 : Integer.Sparse OriginalKey := originalMerge1219 ++ originalMerge1222

def originalMerge1224 : Integer.Sparse OriginalKey := originalMerge1216 ++ originalMerge1223

def originalMerge1225 : Integer.Sparse OriginalKey := originalMerge1210 ++ originalMerge1224

def originalMerge1226 : Integer.Sparse OriginalKey := originalTerm1230 ++ originalTerm1231

def originalMerge1227 : Integer.Sparse OriginalKey := originalTerm1229 ++ originalMerge1226

def originalMerge1228 : Integer.Sparse OriginalKey := originalTerm1232 ++ originalTerm1233

def originalMerge1229 : Integer.Sparse OriginalKey := originalTerm1234 ++ originalTerm1235

def originalMerge1230 : Integer.Sparse OriginalKey := originalMerge1228 ++ originalMerge1229

def originalMerge1231 : Integer.Sparse OriginalKey := originalMerge1227 ++ originalMerge1230

def originalMerge1232 : Integer.Sparse OriginalKey := originalTerm1236 ++ originalTerm1237

def originalMerge1233 : Integer.Sparse OriginalKey := originalTerm1238 ++ originalTerm1239

def originalMerge1234 : Integer.Sparse OriginalKey := originalMerge1232 ++ originalMerge1233

def originalMerge1235 : Integer.Sparse OriginalKey := originalTerm1240 ++ originalTerm1241

def originalMerge1236 : Integer.Sparse OriginalKey := originalTerm1242 ++ originalTerm1243

def originalMerge1237 : Integer.Sparse OriginalKey := originalMerge1235 ++ originalMerge1236

def originalMerge1238 : Integer.Sparse OriginalKey := originalMerge1234 ++ originalMerge1237

def originalMerge1239 : Integer.Sparse OriginalKey := originalMerge1231 ++ originalMerge1238

def originalMerge1240 : Integer.Sparse OriginalKey := originalTerm1245 ++ originalTerm1246

def originalMerge1241 : Integer.Sparse OriginalKey := originalTerm1244 ++ originalMerge1240

def originalMerge1242 : Integer.Sparse OriginalKey := originalTerm1247 ++ originalTerm1248

def originalMerge1243 : Integer.Sparse OriginalKey := originalTerm1249 ++ originalTerm1250

def originalMerge1244 : Integer.Sparse OriginalKey := originalMerge1242 ++ originalMerge1243

def originalMerge1245 : Integer.Sparse OriginalKey := originalMerge1241 ++ originalMerge1244

def originalMerge1246 : Integer.Sparse OriginalKey := originalTerm1251 ++ originalTerm1252

def originalMerge1247 : Integer.Sparse OriginalKey := originalTerm1253 ++ originalTerm1254

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

def originalMerge1248 : Integer.Sparse OriginalKey := originalMerge1246 ++ originalMerge1247

def originalMerge1249 : Integer.Sparse OriginalKey := originalTerm1255 ++ originalTerm1256

def originalMerge1250 : Integer.Sparse OriginalKey := originalTerm1257 ++ originalTerm1258

def originalMerge1251 : Integer.Sparse OriginalKey := originalMerge1249 ++ originalMerge1250

def originalMerge1252 : Integer.Sparse OriginalKey := originalMerge1248 ++ originalMerge1251

def originalMerge1253 : Integer.Sparse OriginalKey := originalMerge1245 ++ originalMerge1252

def originalMerge1254 : Integer.Sparse OriginalKey := originalMerge1239 ++ originalMerge1253

def originalMerge1255 : Integer.Sparse OriginalKey := originalMerge1225 ++ originalMerge1254

def originalMerge1256 : Integer.Sparse OriginalKey := originalTerm1260 ++ originalTerm1261

def originalMerge1257 : Integer.Sparse OriginalKey := originalTerm1259 ++ originalMerge1256

def originalMerge1258 : Integer.Sparse OriginalKey := originalTerm1262 ++ originalTerm1263

def originalMerge1259 : Integer.Sparse OriginalKey := originalTerm1264 ++ originalTerm1265

def originalMerge1260 : Integer.Sparse OriginalKey := originalMerge1258 ++ originalMerge1259

def originalMerge1261 : Integer.Sparse OriginalKey := originalMerge1257 ++ originalMerge1260

def originalMerge1262 : Integer.Sparse OriginalKey := originalTerm1266 ++ originalTerm1267

def originalMerge1263 : Integer.Sparse OriginalKey := originalTerm1268 ++ originalTerm1269

def originalMerge1264 : Integer.Sparse OriginalKey := originalMerge1262 ++ originalMerge1263

def originalMerge1265 : Integer.Sparse OriginalKey := originalTerm1270 ++ originalTerm1271

def originalMerge1266 : Integer.Sparse OriginalKey := originalTerm1272 ++ originalTerm1273

def originalMerge1267 : Integer.Sparse OriginalKey := originalMerge1265 ++ originalMerge1266

def originalMerge1268 : Integer.Sparse OriginalKey := originalMerge1264 ++ originalMerge1267

def originalMerge1269 : Integer.Sparse OriginalKey := originalMerge1261 ++ originalMerge1268

def originalMerge1270 : Integer.Sparse OriginalKey := originalTerm1275 ++ originalTerm1276

def originalMerge1271 : Integer.Sparse OriginalKey := originalTerm1274 ++ originalMerge1270

def originalMerge1272 : Integer.Sparse OriginalKey := originalTerm1277 ++ originalTerm1278

def originalMerge1273 : Integer.Sparse OriginalKey := originalTerm1279 ++ originalTerm1280

def originalMerge1274 : Integer.Sparse OriginalKey := originalMerge1272 ++ originalMerge1273

def originalMerge1275 : Integer.Sparse OriginalKey := originalMerge1271 ++ originalMerge1274

def originalMerge1276 : Integer.Sparse OriginalKey := originalTerm1281 ++ originalTerm1282

def originalMerge1277 : Integer.Sparse OriginalKey := originalTerm1283 ++ originalTerm1284

def originalMerge1278 : Integer.Sparse OriginalKey := originalMerge1276 ++ originalMerge1277

def originalMerge1279 : Integer.Sparse OriginalKey := originalTerm1285 ++ originalTerm1286

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

def originalMerge1280 : Integer.Sparse OriginalKey := originalTerm1287 ++ originalTerm1288

def originalMerge1281 : Integer.Sparse OriginalKey := originalMerge1279 ++ originalMerge1280

def originalMerge1282 : Integer.Sparse OriginalKey := originalMerge1278 ++ originalMerge1281

def originalMerge1283 : Integer.Sparse OriginalKey := originalMerge1275 ++ originalMerge1282

def originalMerge1284 : Integer.Sparse OriginalKey := originalMerge1269 ++ originalMerge1283

def originalMerge1285 : Integer.Sparse OriginalKey := originalTerm1290 ++ originalTerm1291

def originalMerge1286 : Integer.Sparse OriginalKey := originalTerm1289 ++ originalMerge1285

def originalMerge1287 : Integer.Sparse OriginalKey := originalTerm1292 ++ originalTerm1293

def originalMerge1288 : Integer.Sparse OriginalKey := originalTerm1294 ++ originalTerm1295

def originalMerge1289 : Integer.Sparse OriginalKey := originalMerge1287 ++ originalMerge1288

def originalMerge1290 : Integer.Sparse OriginalKey := originalMerge1286 ++ originalMerge1289

def originalMerge1291 : Integer.Sparse OriginalKey := originalTerm1296 ++ originalTerm1297

def originalMerge1292 : Integer.Sparse OriginalKey := originalTerm1298 ++ originalTerm1299

def originalMerge1293 : Integer.Sparse OriginalKey := originalMerge1291 ++ originalMerge1292

def originalMerge1294 : Integer.Sparse OriginalKey := originalTerm1300 ++ originalTerm1301

def originalMerge1295 : Integer.Sparse OriginalKey := originalTerm1302 ++ originalTerm1303

def originalMerge1296 : Integer.Sparse OriginalKey := originalMerge1294 ++ originalMerge1295

def originalMerge1297 : Integer.Sparse OriginalKey := originalMerge1293 ++ originalMerge1296

def originalMerge1298 : Integer.Sparse OriginalKey := originalMerge1290 ++ originalMerge1297

def originalMerge1299 : Integer.Sparse OriginalKey := originalTerm1305 ++ originalTerm1306

def originalMerge1300 : Integer.Sparse OriginalKey := originalTerm1304 ++ originalMerge1299

def originalMerge1301 : Integer.Sparse OriginalKey := originalTerm1307 ++ originalTerm1308

def originalMerge1302 : Integer.Sparse OriginalKey := originalTerm1309 ++ originalTerm1310

def originalMerge1303 : Integer.Sparse OriginalKey := originalMerge1301 ++ originalMerge1302

def originalMerge1304 : Integer.Sparse OriginalKey := originalMerge1300 ++ originalMerge1303

def originalMerge1305 : Integer.Sparse OriginalKey := originalTerm1311 ++ originalTerm1312

def originalMerge1306 : Integer.Sparse OriginalKey := originalTerm1313 ++ originalTerm1314

def originalMerge1307 : Integer.Sparse OriginalKey := originalMerge1305 ++ originalMerge1306

def originalMerge1308 : Integer.Sparse OriginalKey := originalTerm1315 ++ originalTerm1316

def originalMerge1309 : Integer.Sparse OriginalKey := originalTerm1317 ++ originalTerm1318

def originalMerge1310 : Integer.Sparse OriginalKey := originalMerge1308 ++ originalMerge1309

def originalMerge1311 : Integer.Sparse OriginalKey := originalMerge1307 ++ originalMerge1310

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

def originalMerge1312 : Integer.Sparse OriginalKey := originalMerge1304 ++ originalMerge1311

def originalMerge1313 : Integer.Sparse OriginalKey := originalMerge1298 ++ originalMerge1312

def originalMerge1314 : Integer.Sparse OriginalKey := originalMerge1284 ++ originalMerge1313

def originalMerge1315 : Integer.Sparse OriginalKey := originalMerge1255 ++ originalMerge1314

def originalMerge1316 : Integer.Sparse OriginalKey := originalTerm1320 ++ originalTerm1321

def originalMerge1317 : Integer.Sparse OriginalKey := originalTerm1319 ++ originalMerge1316

def originalMerge1318 : Integer.Sparse OriginalKey := originalTerm1322 ++ originalTerm1323

def originalMerge1319 : Integer.Sparse OriginalKey := originalTerm1324 ++ originalTerm1325

def originalMerge1320 : Integer.Sparse OriginalKey := originalMerge1318 ++ originalMerge1319

def originalMerge1321 : Integer.Sparse OriginalKey := originalMerge1317 ++ originalMerge1320

def originalMerge1322 : Integer.Sparse OriginalKey := originalTerm1326 ++ originalTerm1327

def originalMerge1323 : Integer.Sparse OriginalKey := originalTerm1328 ++ originalTerm1329

def originalMerge1324 : Integer.Sparse OriginalKey := originalMerge1322 ++ originalMerge1323

def originalMerge1325 : Integer.Sparse OriginalKey := originalTerm1330 ++ originalTerm1331

def originalMerge1326 : Integer.Sparse OriginalKey := originalTerm1332 ++ originalTerm1333

def originalMerge1327 : Integer.Sparse OriginalKey := originalMerge1325 ++ originalMerge1326

def originalMerge1328 : Integer.Sparse OriginalKey := originalMerge1324 ++ originalMerge1327

def originalMerge1329 : Integer.Sparse OriginalKey := originalMerge1321 ++ originalMerge1328

def originalMerge1330 : Integer.Sparse OriginalKey := originalTerm1335 ++ originalTerm1336

def originalMerge1331 : Integer.Sparse OriginalKey := originalTerm1334 ++ originalMerge1330

def originalMerge1332 : Integer.Sparse OriginalKey := originalTerm1337 ++ originalTerm1338

def originalMerge1333 : Integer.Sparse OriginalKey := originalTerm1339 ++ originalTerm1340

def originalMerge1334 : Integer.Sparse OriginalKey := originalMerge1332 ++ originalMerge1333

def originalMerge1335 : Integer.Sparse OriginalKey := originalMerge1331 ++ originalMerge1334

def originalMerge1336 : Integer.Sparse OriginalKey := originalTerm1341 ++ originalTerm1342

def originalMerge1337 : Integer.Sparse OriginalKey := originalTerm1343 ++ originalTerm1344

def originalMerge1338 : Integer.Sparse OriginalKey := originalMerge1336 ++ originalMerge1337

def originalMerge1339 : Integer.Sparse OriginalKey := originalTerm1345 ++ originalTerm1346

def originalMerge1340 : Integer.Sparse OriginalKey := originalTerm1347 ++ originalTerm1348

def originalMerge1341 : Integer.Sparse OriginalKey := originalMerge1339 ++ originalMerge1340

def originalMerge1342 : Integer.Sparse OriginalKey := originalMerge1338 ++ originalMerge1341

def originalMerge1343 : Integer.Sparse OriginalKey := originalMerge1335 ++ originalMerge1342

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

def originalMerge1344 : Integer.Sparse OriginalKey := originalMerge1329 ++ originalMerge1343

def originalMerge1345 : Integer.Sparse OriginalKey := originalTerm1350 ++ originalTerm1351

def originalMerge1346 : Integer.Sparse OriginalKey := originalTerm1349 ++ originalMerge1345

def originalMerge1347 : Integer.Sparse OriginalKey := originalTerm1352 ++ originalTerm1353

def originalMerge1348 : Integer.Sparse OriginalKey := originalTerm1354 ++ originalTerm1355

def originalMerge1349 : Integer.Sparse OriginalKey := originalMerge1347 ++ originalMerge1348

def originalMerge1350 : Integer.Sparse OriginalKey := originalMerge1346 ++ originalMerge1349

def originalMerge1351 : Integer.Sparse OriginalKey := originalTerm1356 ++ originalTerm1357

def originalMerge1352 : Integer.Sparse OriginalKey := originalTerm1358 ++ originalTerm1359

def originalMerge1353 : Integer.Sparse OriginalKey := originalMerge1351 ++ originalMerge1352

def originalMerge1354 : Integer.Sparse OriginalKey := originalTerm1360 ++ originalTerm1361

def originalMerge1355 : Integer.Sparse OriginalKey := originalTerm1362 ++ originalTerm1363

def originalMerge1356 : Integer.Sparse OriginalKey := originalMerge1354 ++ originalMerge1355

def originalMerge1357 : Integer.Sparse OriginalKey := originalMerge1353 ++ originalMerge1356

def originalMerge1358 : Integer.Sparse OriginalKey := originalMerge1350 ++ originalMerge1357

def originalMerge1359 : Integer.Sparse OriginalKey := originalTerm1365 ++ originalTerm1366

def originalMerge1360 : Integer.Sparse OriginalKey := originalTerm1364 ++ originalMerge1359

def originalMerge1361 : Integer.Sparse OriginalKey := originalTerm1367 ++ originalTerm1368

def originalMerge1362 : Integer.Sparse OriginalKey := originalTerm1369 ++ originalTerm1370

def originalMerge1363 : Integer.Sparse OriginalKey := originalMerge1361 ++ originalMerge1362

def originalMerge1364 : Integer.Sparse OriginalKey := originalMerge1360 ++ originalMerge1363

def originalMerge1365 : Integer.Sparse OriginalKey := originalTerm1371 ++ originalTerm1372

def originalMerge1366 : Integer.Sparse OriginalKey := originalTerm1373 ++ originalTerm1374

def originalMerge1367 : Integer.Sparse OriginalKey := originalMerge1365 ++ originalMerge1366

def originalMerge1368 : Integer.Sparse OriginalKey := originalTerm1375 ++ originalTerm1376

def originalMerge1369 : Integer.Sparse OriginalKey := originalTerm1377 ++ originalTerm1378

def originalMerge1370 : Integer.Sparse OriginalKey := originalMerge1368 ++ originalMerge1369

def originalMerge1371 : Integer.Sparse OriginalKey := originalMerge1367 ++ originalMerge1370

def originalMerge1372 : Integer.Sparse OriginalKey := originalMerge1364 ++ originalMerge1371

def originalMerge1373 : Integer.Sparse OriginalKey := originalMerge1358 ++ originalMerge1372

def originalMerge1374 : Integer.Sparse OriginalKey := originalMerge1344 ++ originalMerge1373

def originalMerge1375 : Integer.Sparse OriginalKey := originalTerm1380 ++ originalTerm1381

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

def originalMerge1376 : Integer.Sparse OriginalKey := originalTerm1379 ++ originalMerge1375

def originalMerge1377 : Integer.Sparse OriginalKey := originalTerm1382 ++ originalTerm1383

def originalMerge1378 : Integer.Sparse OriginalKey := originalTerm1384 ++ originalTerm1385

def originalMerge1379 : Integer.Sparse OriginalKey := originalMerge1377 ++ originalMerge1378

def originalMerge1380 : Integer.Sparse OriginalKey := originalMerge1376 ++ originalMerge1379

def originalMerge1381 : Integer.Sparse OriginalKey := originalTerm1386 ++ originalTerm1387

def originalMerge1382 : Integer.Sparse OriginalKey := originalTerm1388 ++ originalTerm1389

def originalMerge1383 : Integer.Sparse OriginalKey := originalMerge1381 ++ originalMerge1382

def originalMerge1384 : Integer.Sparse OriginalKey := originalTerm1390 ++ originalTerm1391

def originalMerge1385 : Integer.Sparse OriginalKey := originalTerm1392 ++ originalTerm1393

def originalMerge1386 : Integer.Sparse OriginalKey := originalMerge1384 ++ originalMerge1385

def originalMerge1387 : Integer.Sparse OriginalKey := originalMerge1383 ++ originalMerge1386

def originalMerge1388 : Integer.Sparse OriginalKey := originalMerge1380 ++ originalMerge1387

def originalMerge1389 : Integer.Sparse OriginalKey := originalTerm1395 ++ originalTerm1396

def originalMerge1390 : Integer.Sparse OriginalKey := originalTerm1394 ++ originalMerge1389

def originalMerge1391 : Integer.Sparse OriginalKey := originalTerm1397 ++ originalTerm1398

def originalMerge1392 : Integer.Sparse OriginalKey := originalTerm1399 ++ originalTerm1400

def originalMerge1393 : Integer.Sparse OriginalKey := originalMerge1391 ++ originalMerge1392

def originalMerge1394 : Integer.Sparse OriginalKey := originalMerge1390 ++ originalMerge1393

def originalMerge1395 : Integer.Sparse OriginalKey := originalTerm1401 ++ originalTerm1402

def originalMerge1396 : Integer.Sparse OriginalKey := originalTerm1403 ++ originalTerm1404

def originalMerge1397 : Integer.Sparse OriginalKey := originalMerge1395 ++ originalMerge1396

def originalMerge1398 : Integer.Sparse OriginalKey := originalTerm1405 ++ originalTerm1406

def originalMerge1399 : Integer.Sparse OriginalKey := originalTerm1407 ++ originalTerm1408

def originalMerge1400 : Integer.Sparse OriginalKey := originalMerge1398 ++ originalMerge1399

def originalMerge1401 : Integer.Sparse OriginalKey := originalMerge1397 ++ originalMerge1400

def originalMerge1402 : Integer.Sparse OriginalKey := originalMerge1394 ++ originalMerge1401

def originalMerge1403 : Integer.Sparse OriginalKey := originalMerge1388 ++ originalMerge1402

def originalMerge1404 : Integer.Sparse OriginalKey := originalTerm1410 ++ originalTerm1411

def originalMerge1405 : Integer.Sparse OriginalKey := originalTerm1409 ++ originalMerge1404

def originalMerge1406 : Integer.Sparse OriginalKey := originalTerm1412 ++ originalTerm1413

def originalMerge1407 : Integer.Sparse OriginalKey := originalTerm1414 ++ originalTerm1415

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

def originalMerge1408 : Integer.Sparse OriginalKey := originalMerge1406 ++ originalMerge1407

def originalMerge1409 : Integer.Sparse OriginalKey := originalMerge1405 ++ originalMerge1408

def originalMerge1410 : Integer.Sparse OriginalKey := originalTerm1416 ++ originalTerm1417

def originalMerge1411 : Integer.Sparse OriginalKey := originalTerm1418 ++ originalTerm1419

def originalMerge1412 : Integer.Sparse OriginalKey := originalMerge1410 ++ originalMerge1411

def originalMerge1413 : Integer.Sparse OriginalKey := originalTerm1420 ++ originalTerm1421

def originalMerge1414 : Integer.Sparse OriginalKey := originalTerm1422 ++ originalTerm1423

def originalMerge1415 : Integer.Sparse OriginalKey := originalMerge1413 ++ originalMerge1414

def originalMerge1416 : Integer.Sparse OriginalKey := originalMerge1412 ++ originalMerge1415

def originalMerge1417 : Integer.Sparse OriginalKey := originalMerge1409 ++ originalMerge1416

def originalMerge1418 : Integer.Sparse OriginalKey := originalTerm1425 ++ originalTerm1426

def originalMerge1419 : Integer.Sparse OriginalKey := originalTerm1424 ++ originalMerge1418

def originalMerge1420 : Integer.Sparse OriginalKey := originalTerm1427 ++ originalTerm1428

def originalMerge1421 : Integer.Sparse OriginalKey := originalTerm1429 ++ originalTerm1430

def originalMerge1422 : Integer.Sparse OriginalKey := originalMerge1420 ++ originalMerge1421

def originalMerge1423 : Integer.Sparse OriginalKey := originalMerge1419 ++ originalMerge1422

def originalMerge1424 : Integer.Sparse OriginalKey := originalTerm1431 ++ originalTerm1432

def originalMerge1425 : Integer.Sparse OriginalKey := originalTerm1433 ++ originalTerm1434

def originalMerge1426 : Integer.Sparse OriginalKey := originalMerge1424 ++ originalMerge1425

def originalMerge1427 : Integer.Sparse OriginalKey := originalTerm1435 ++ originalTerm1436

def originalMerge1428 : Integer.Sparse OriginalKey := originalTerm1437 ++ originalTerm1438

def originalMerge1429 : Integer.Sparse OriginalKey := originalMerge1427 ++ originalMerge1428

def originalMerge1430 : Integer.Sparse OriginalKey := originalMerge1426 ++ originalMerge1429

def originalMerge1431 : Integer.Sparse OriginalKey := originalMerge1423 ++ originalMerge1430

def originalMerge1432 : Integer.Sparse OriginalKey := originalMerge1417 ++ originalMerge1431

def originalMerge1433 : Integer.Sparse OriginalKey := originalMerge1403 ++ originalMerge1432

def originalMerge1434 : Integer.Sparse OriginalKey := originalMerge1374 ++ originalMerge1433

def originalMerge1435 : Integer.Sparse OriginalKey := originalMerge1315 ++ originalMerge1434

def originalMerge1436 : Integer.Sparse OriginalKey := originalMerge1196 ++ originalMerge1435

def originalMerge1437 : Integer.Sparse OriginalKey := originalTerm1440 ++ originalTerm1441

def originalMerge1438 : Integer.Sparse OriginalKey := originalTerm1439 ++ originalMerge1437

def originalMerge1439 : Integer.Sparse OriginalKey := originalTerm1442 ++ originalTerm1443

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1440 : Integer.Sparse OriginalKey := originalTerm1444 ++ originalTerm1445

def originalMerge1441 : Integer.Sparse OriginalKey := originalMerge1439 ++ originalMerge1440

def originalMerge1442 : Integer.Sparse OriginalKey := originalMerge1438 ++ originalMerge1441

def originalMerge1443 : Integer.Sparse OriginalKey := originalTerm1446 ++ originalTerm1447

def originalMerge1444 : Integer.Sparse OriginalKey := originalTerm1448 ++ originalTerm1449

def originalMerge1445 : Integer.Sparse OriginalKey := originalMerge1443 ++ originalMerge1444

def originalMerge1446 : Integer.Sparse OriginalKey := originalTerm1450 ++ originalTerm1451

def originalMerge1447 : Integer.Sparse OriginalKey := originalTerm1452 ++ originalTerm1453

def originalMerge1448 : Integer.Sparse OriginalKey := originalMerge1446 ++ originalMerge1447

def originalMerge1449 : Integer.Sparse OriginalKey := originalMerge1445 ++ originalMerge1448

def originalMerge1450 : Integer.Sparse OriginalKey := originalMerge1442 ++ originalMerge1449

def originalMerge1451 : Integer.Sparse OriginalKey := originalTerm1455 ++ originalTerm1456

def originalMerge1452 : Integer.Sparse OriginalKey := originalTerm1454 ++ originalMerge1451

def originalMerge1453 : Integer.Sparse OriginalKey := originalTerm1457 ++ originalTerm1458

def originalMerge1454 : Integer.Sparse OriginalKey := originalTerm1459 ++ originalTerm1460

def originalMerge1455 : Integer.Sparse OriginalKey := originalMerge1453 ++ originalMerge1454

def originalMerge1456 : Integer.Sparse OriginalKey := originalMerge1452 ++ originalMerge1455

def originalMerge1457 : Integer.Sparse OriginalKey := originalTerm1461 ++ originalTerm1462

def originalMerge1458 : Integer.Sparse OriginalKey := originalTerm1463 ++ originalTerm1464

def originalMerge1459 : Integer.Sparse OriginalKey := originalMerge1457 ++ originalMerge1458

def originalMerge1460 : Integer.Sparse OriginalKey := originalTerm1465 ++ originalTerm1466

def originalMerge1461 : Integer.Sparse OriginalKey := originalTerm1467 ++ originalTerm1468

def originalMerge1462 : Integer.Sparse OriginalKey := originalMerge1460 ++ originalMerge1461

def originalMerge1463 : Integer.Sparse OriginalKey := originalMerge1459 ++ originalMerge1462

def originalMerge1464 : Integer.Sparse OriginalKey := originalMerge1456 ++ originalMerge1463

def originalMerge1465 : Integer.Sparse OriginalKey := originalMerge1450 ++ originalMerge1464

def originalMerge1466 : Integer.Sparse OriginalKey := originalTerm1470 ++ originalTerm1471

def originalMerge1467 : Integer.Sparse OriginalKey := originalTerm1469 ++ originalMerge1466

def originalMerge1468 : Integer.Sparse OriginalKey := originalTerm1472 ++ originalTerm1473

def originalMerge1469 : Integer.Sparse OriginalKey := originalTerm1474 ++ originalTerm1475

def originalMerge1470 : Integer.Sparse OriginalKey := originalMerge1468 ++ originalMerge1469

def originalMerge1471 : Integer.Sparse OriginalKey := originalMerge1467 ++ originalMerge1470

end MUB6.Certificate.MixedTargetSemantics

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

def originalMerge1472 : Integer.Sparse OriginalKey := originalTerm1476 ++ originalTerm1477

def originalMerge1473 : Integer.Sparse OriginalKey := originalTerm1478 ++ originalTerm1479

def originalMerge1474 : Integer.Sparse OriginalKey := originalMerge1472 ++ originalMerge1473

def originalMerge1475 : Integer.Sparse OriginalKey := originalTerm1480 ++ originalTerm1481

def originalMerge1476 : Integer.Sparse OriginalKey := originalTerm1482 ++ originalTerm1483

def originalMerge1477 : Integer.Sparse OriginalKey := originalMerge1475 ++ originalMerge1476

def originalMerge1478 : Integer.Sparse OriginalKey := originalMerge1474 ++ originalMerge1477

def originalMerge1479 : Integer.Sparse OriginalKey := originalMerge1471 ++ originalMerge1478

def originalMerge1480 : Integer.Sparse OriginalKey := originalTerm1485 ++ originalTerm1486

def originalMerge1481 : Integer.Sparse OriginalKey := originalTerm1484 ++ originalMerge1480

def originalMerge1482 : Integer.Sparse OriginalKey := originalTerm1487 ++ originalTerm1488

def originalMerge1483 : Integer.Sparse OriginalKey := originalTerm1489 ++ originalTerm1490

def originalMerge1484 : Integer.Sparse OriginalKey := originalMerge1482 ++ originalMerge1483

def originalMerge1485 : Integer.Sparse OriginalKey := originalMerge1481 ++ originalMerge1484

def originalMerge1486 : Integer.Sparse OriginalKey := originalTerm1491 ++ originalTerm1492

def originalMerge1487 : Integer.Sparse OriginalKey := originalTerm1493 ++ originalTerm1494

def originalMerge1488 : Integer.Sparse OriginalKey := originalMerge1486 ++ originalMerge1487

def originalMerge1489 : Integer.Sparse OriginalKey := originalTerm1495 ++ originalTerm1496

def originalMerge1490 : Integer.Sparse OriginalKey := originalTerm1497 ++ originalTerm1498

def originalMerge1491 : Integer.Sparse OriginalKey := originalMerge1489 ++ originalMerge1490

def originalMerge1492 : Integer.Sparse OriginalKey := originalMerge1488 ++ originalMerge1491

def originalMerge1493 : Integer.Sparse OriginalKey := originalMerge1485 ++ originalMerge1492

def originalMerge1494 : Integer.Sparse OriginalKey := originalMerge1479 ++ originalMerge1493

def originalMerge1495 : Integer.Sparse OriginalKey := originalMerge1465 ++ originalMerge1494

def originalMerge1496 : Integer.Sparse OriginalKey := originalTerm1500 ++ originalTerm1501

def originalMerge1497 : Integer.Sparse OriginalKey := originalTerm1499 ++ originalMerge1496

def originalMerge1498 : Integer.Sparse OriginalKey := originalTerm1502 ++ originalTerm1503

def originalMerge1499 : Integer.Sparse OriginalKey := originalTerm1504 ++ originalTerm1505

def originalMerge1500 : Integer.Sparse OriginalKey := originalMerge1498 ++ originalMerge1499

def originalMerge1501 : Integer.Sparse OriginalKey := originalMerge1497 ++ originalMerge1500

def originalMerge1502 : Integer.Sparse OriginalKey := originalTerm1506 ++ originalTerm1507

def originalMerge1503 : Integer.Sparse OriginalKey := originalTerm1508 ++ originalTerm1509

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1504 : Integer.Sparse OriginalKey := originalMerge1502 ++ originalMerge1503

def originalMerge1505 : Integer.Sparse OriginalKey := originalTerm1510 ++ originalTerm1511

def originalMerge1506 : Integer.Sparse OriginalKey := originalTerm1512 ++ originalTerm1513

def originalMerge1507 : Integer.Sparse OriginalKey := originalMerge1505 ++ originalMerge1506

def originalMerge1508 : Integer.Sparse OriginalKey := originalMerge1504 ++ originalMerge1507

def originalMerge1509 : Integer.Sparse OriginalKey := originalMerge1501 ++ originalMerge1508

def originalMerge1510 : Integer.Sparse OriginalKey := originalTerm1515 ++ originalTerm1516

def originalMerge1511 : Integer.Sparse OriginalKey := originalTerm1514 ++ originalMerge1510

def originalMerge1512 : Integer.Sparse OriginalKey := originalTerm1517 ++ originalTerm1518

def originalMerge1513 : Integer.Sparse OriginalKey := originalTerm1519 ++ originalTerm1520

def originalMerge1514 : Integer.Sparse OriginalKey := originalMerge1512 ++ originalMerge1513

def originalMerge1515 : Integer.Sparse OriginalKey := originalMerge1511 ++ originalMerge1514

def originalMerge1516 : Integer.Sparse OriginalKey := originalTerm1521 ++ originalTerm1522

def originalMerge1517 : Integer.Sparse OriginalKey := originalTerm1523 ++ originalTerm1524

def originalMerge1518 : Integer.Sparse OriginalKey := originalMerge1516 ++ originalMerge1517

def originalMerge1519 : Integer.Sparse OriginalKey := originalTerm1525 ++ originalTerm1526

def originalMerge1520 : Integer.Sparse OriginalKey := originalTerm1527 ++ originalTerm1528

def originalMerge1521 : Integer.Sparse OriginalKey := originalMerge1519 ++ originalMerge1520

def originalMerge1522 : Integer.Sparse OriginalKey := originalMerge1518 ++ originalMerge1521

def originalMerge1523 : Integer.Sparse OriginalKey := originalMerge1515 ++ originalMerge1522

def originalMerge1524 : Integer.Sparse OriginalKey := originalMerge1509 ++ originalMerge1523

def originalMerge1525 : Integer.Sparse OriginalKey := originalTerm1530 ++ originalTerm1531

def originalMerge1526 : Integer.Sparse OriginalKey := originalTerm1529 ++ originalMerge1525

def originalMerge1527 : Integer.Sparse OriginalKey := originalTerm1532 ++ originalTerm1533

def originalMerge1528 : Integer.Sparse OriginalKey := originalTerm1534 ++ originalTerm1535

def originalMerge1529 : Integer.Sparse OriginalKey := originalMerge1527 ++ originalMerge1528

def originalMerge1530 : Integer.Sparse OriginalKey := originalMerge1526 ++ originalMerge1529

def originalMerge1531 : Integer.Sparse OriginalKey := originalTerm1536 ++ originalTerm1537

def originalMerge1532 : Integer.Sparse OriginalKey := originalTerm1538 ++ originalTerm1539

def originalMerge1533 : Integer.Sparse OriginalKey := originalMerge1531 ++ originalMerge1532

def originalMerge1534 : Integer.Sparse OriginalKey := originalTerm1540 ++ originalTerm1541

def originalMerge1535 : Integer.Sparse OriginalKey := originalTerm1542 ++ originalTerm1543

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1536 : Integer.Sparse OriginalKey := originalMerge1534 ++ originalMerge1535

def originalMerge1537 : Integer.Sparse OriginalKey := originalMerge1533 ++ originalMerge1536

def originalMerge1538 : Integer.Sparse OriginalKey := originalMerge1530 ++ originalMerge1537

def originalMerge1539 : Integer.Sparse OriginalKey := originalTerm1545 ++ originalTerm1546

def originalMerge1540 : Integer.Sparse OriginalKey := originalTerm1544 ++ originalMerge1539

def originalMerge1541 : Integer.Sparse OriginalKey := originalTerm1547 ++ originalTerm1548

def originalMerge1542 : Integer.Sparse OriginalKey := originalTerm1549 ++ originalTerm1550

def originalMerge1543 : Integer.Sparse OriginalKey := originalMerge1541 ++ originalMerge1542

def originalMerge1544 : Integer.Sparse OriginalKey := originalMerge1540 ++ originalMerge1543

def originalMerge1545 : Integer.Sparse OriginalKey := originalTerm1551 ++ originalTerm1552

def originalMerge1546 : Integer.Sparse OriginalKey := originalTerm1553 ++ originalTerm1554

def originalMerge1547 : Integer.Sparse OriginalKey := originalMerge1545 ++ originalMerge1546

def originalMerge1548 : Integer.Sparse OriginalKey := originalTerm1555 ++ originalTerm1556

def originalMerge1549 : Integer.Sparse OriginalKey := originalTerm1557 ++ originalTerm1558

def originalMerge1550 : Integer.Sparse OriginalKey := originalMerge1548 ++ originalMerge1549

def originalMerge1551 : Integer.Sparse OriginalKey := originalMerge1547 ++ originalMerge1550

def originalMerge1552 : Integer.Sparse OriginalKey := originalMerge1544 ++ originalMerge1551

def originalMerge1553 : Integer.Sparse OriginalKey := originalMerge1538 ++ originalMerge1552

def originalMerge1554 : Integer.Sparse OriginalKey := originalMerge1524 ++ originalMerge1553

def originalMerge1555 : Integer.Sparse OriginalKey := originalMerge1495 ++ originalMerge1554

def originalMerge1556 : Integer.Sparse OriginalKey := originalTerm1560 ++ originalTerm1561

def originalMerge1557 : Integer.Sparse OriginalKey := originalTerm1559 ++ originalMerge1556

def originalMerge1558 : Integer.Sparse OriginalKey := originalTerm1562 ++ originalTerm1563

def originalMerge1559 : Integer.Sparse OriginalKey := originalTerm1564 ++ originalTerm1565

def originalMerge1560 : Integer.Sparse OriginalKey := originalMerge1558 ++ originalMerge1559

def originalMerge1561 : Integer.Sparse OriginalKey := originalMerge1557 ++ originalMerge1560

def originalMerge1562 : Integer.Sparse OriginalKey := originalTerm1566 ++ originalTerm1567

def originalMerge1563 : Integer.Sparse OriginalKey := originalTerm1568 ++ originalTerm1569

def originalMerge1564 : Integer.Sparse OriginalKey := originalMerge1562 ++ originalMerge1563

def originalMerge1565 : Integer.Sparse OriginalKey := originalTerm1570 ++ originalTerm1571

def originalMerge1566 : Integer.Sparse OriginalKey := originalTerm1572 ++ originalTerm1573

def originalMerge1567 : Integer.Sparse OriginalKey := originalMerge1565 ++ originalMerge1566

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1568 : Integer.Sparse OriginalKey := originalMerge1564 ++ originalMerge1567

def originalMerge1569 : Integer.Sparse OriginalKey := originalMerge1561 ++ originalMerge1568

def originalMerge1570 : Integer.Sparse OriginalKey := originalTerm1575 ++ originalTerm1576

def originalMerge1571 : Integer.Sparse OriginalKey := originalTerm1574 ++ originalMerge1570

def originalMerge1572 : Integer.Sparse OriginalKey := originalTerm1577 ++ originalTerm1578

def originalMerge1573 : Integer.Sparse OriginalKey := originalTerm1579 ++ originalTerm1580

def originalMerge1574 : Integer.Sparse OriginalKey := originalMerge1572 ++ originalMerge1573

def originalMerge1575 : Integer.Sparse OriginalKey := originalMerge1571 ++ originalMerge1574

def originalMerge1576 : Integer.Sparse OriginalKey := originalTerm1581 ++ originalTerm1582

def originalMerge1577 : Integer.Sparse OriginalKey := originalTerm1583 ++ originalTerm1584

def originalMerge1578 : Integer.Sparse OriginalKey := originalMerge1576 ++ originalMerge1577

def originalMerge1579 : Integer.Sparse OriginalKey := originalTerm1585 ++ originalTerm1586

def originalMerge1580 : Integer.Sparse OriginalKey := originalTerm1587 ++ originalTerm1588

def originalMerge1581 : Integer.Sparse OriginalKey := originalMerge1579 ++ originalMerge1580

def originalMerge1582 : Integer.Sparse OriginalKey := originalMerge1578 ++ originalMerge1581

def originalMerge1583 : Integer.Sparse OriginalKey := originalMerge1575 ++ originalMerge1582

def originalMerge1584 : Integer.Sparse OriginalKey := originalMerge1569 ++ originalMerge1583

def originalMerge1585 : Integer.Sparse OriginalKey := originalTerm1590 ++ originalTerm1591

def originalMerge1586 : Integer.Sparse OriginalKey := originalTerm1589 ++ originalMerge1585

def originalMerge1587 : Integer.Sparse OriginalKey := originalTerm1592 ++ originalTerm1593

def originalMerge1588 : Integer.Sparse OriginalKey := originalTerm1594 ++ originalTerm1595

def originalMerge1589 : Integer.Sparse OriginalKey := originalMerge1587 ++ originalMerge1588

def originalMerge1590 : Integer.Sparse OriginalKey := originalMerge1586 ++ originalMerge1589

def originalMerge1591 : Integer.Sparse OriginalKey := originalTerm1596 ++ originalTerm1597

def originalMerge1592 : Integer.Sparse OriginalKey := originalTerm1598 ++ originalTerm1599

def originalMerge1593 : Integer.Sparse OriginalKey := originalMerge1591 ++ originalMerge1592

def originalMerge1594 : Integer.Sparse OriginalKey := originalTerm1600 ++ originalTerm1601

def originalMerge1595 : Integer.Sparse OriginalKey := originalTerm1602 ++ originalTerm1603

def originalMerge1596 : Integer.Sparse OriginalKey := originalMerge1594 ++ originalMerge1595

def originalMerge1597 : Integer.Sparse OriginalKey := originalMerge1593 ++ originalMerge1596

def originalMerge1598 : Integer.Sparse OriginalKey := originalMerge1590 ++ originalMerge1597

def originalMerge1599 : Integer.Sparse OriginalKey := originalTerm1605 ++ originalTerm1606

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1600 : Integer.Sparse OriginalKey := originalTerm1604 ++ originalMerge1599

def originalMerge1601 : Integer.Sparse OriginalKey := originalTerm1607 ++ originalTerm1608

def originalMerge1602 : Integer.Sparse OriginalKey := originalTerm1609 ++ originalTerm1610

def originalMerge1603 : Integer.Sparse OriginalKey := originalMerge1601 ++ originalMerge1602

def originalMerge1604 : Integer.Sparse OriginalKey := originalMerge1600 ++ originalMerge1603

def originalMerge1605 : Integer.Sparse OriginalKey := originalTerm1611 ++ originalTerm1612

def originalMerge1606 : Integer.Sparse OriginalKey := originalTerm1613 ++ originalTerm1614

def originalMerge1607 : Integer.Sparse OriginalKey := originalMerge1605 ++ originalMerge1606

def originalMerge1608 : Integer.Sparse OriginalKey := originalTerm1615 ++ originalTerm1616

def originalMerge1609 : Integer.Sparse OriginalKey := originalTerm1617 ++ originalTerm1618

def originalMerge1610 : Integer.Sparse OriginalKey := originalMerge1608 ++ originalMerge1609

def originalMerge1611 : Integer.Sparse OriginalKey := originalMerge1607 ++ originalMerge1610

def originalMerge1612 : Integer.Sparse OriginalKey := originalMerge1604 ++ originalMerge1611

def originalMerge1613 : Integer.Sparse OriginalKey := originalMerge1598 ++ originalMerge1612

def originalMerge1614 : Integer.Sparse OriginalKey := originalMerge1584 ++ originalMerge1613

def originalMerge1615 : Integer.Sparse OriginalKey := originalTerm1620 ++ originalTerm1621

def originalMerge1616 : Integer.Sparse OriginalKey := originalTerm1619 ++ originalMerge1615

def originalMerge1617 : Integer.Sparse OriginalKey := originalTerm1622 ++ originalTerm1623

def originalMerge1618 : Integer.Sparse OriginalKey := originalTerm1624 ++ originalTerm1625

def originalMerge1619 : Integer.Sparse OriginalKey := originalMerge1617 ++ originalMerge1618

def originalMerge1620 : Integer.Sparse OriginalKey := originalMerge1616 ++ originalMerge1619

def originalMerge1621 : Integer.Sparse OriginalKey := originalTerm1626 ++ originalTerm1627

def originalMerge1622 : Integer.Sparse OriginalKey := originalTerm1628 ++ originalTerm1629

def originalMerge1623 : Integer.Sparse OriginalKey := originalMerge1621 ++ originalMerge1622

def originalMerge1624 : Integer.Sparse OriginalKey := originalTerm1630 ++ originalTerm1631

def originalMerge1625 : Integer.Sparse OriginalKey := originalTerm1632 ++ originalTerm1633

def originalMerge1626 : Integer.Sparse OriginalKey := originalMerge1624 ++ originalMerge1625

def originalMerge1627 : Integer.Sparse OriginalKey := originalMerge1623 ++ originalMerge1626

def originalMerge1628 : Integer.Sparse OriginalKey := originalMerge1620 ++ originalMerge1627

def originalMerge1629 : Integer.Sparse OriginalKey := originalTerm1635 ++ originalTerm1636

def originalMerge1630 : Integer.Sparse OriginalKey := originalTerm1634 ++ originalMerge1629

def originalMerge1631 : Integer.Sparse OriginalKey := originalTerm1637 ++ originalTerm1638

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1632 : Integer.Sparse OriginalKey := originalTerm1639 ++ originalTerm1640

def originalMerge1633 : Integer.Sparse OriginalKey := originalMerge1631 ++ originalMerge1632

def originalMerge1634 : Integer.Sparse OriginalKey := originalMerge1630 ++ originalMerge1633

def originalMerge1635 : Integer.Sparse OriginalKey := originalTerm1641 ++ originalTerm1642

def originalMerge1636 : Integer.Sparse OriginalKey := originalTerm1643 ++ originalTerm1644

def originalMerge1637 : Integer.Sparse OriginalKey := originalMerge1635 ++ originalMerge1636

def originalMerge1638 : Integer.Sparse OriginalKey := originalTerm1645 ++ originalTerm1646

def originalMerge1639 : Integer.Sparse OriginalKey := originalTerm1647 ++ originalTerm1648

def originalMerge1640 : Integer.Sparse OriginalKey := originalMerge1638 ++ originalMerge1639

def originalMerge1641 : Integer.Sparse OriginalKey := originalMerge1637 ++ originalMerge1640

def originalMerge1642 : Integer.Sparse OriginalKey := originalMerge1634 ++ originalMerge1641

def originalMerge1643 : Integer.Sparse OriginalKey := originalMerge1628 ++ originalMerge1642

def originalMerge1644 : Integer.Sparse OriginalKey := originalTerm1650 ++ originalTerm1651

def originalMerge1645 : Integer.Sparse OriginalKey := originalTerm1649 ++ originalMerge1644

def originalMerge1646 : Integer.Sparse OriginalKey := originalTerm1652 ++ originalTerm1653

def originalMerge1647 : Integer.Sparse OriginalKey := originalTerm1654 ++ originalTerm1655

def originalMerge1648 : Integer.Sparse OriginalKey := originalMerge1646 ++ originalMerge1647

def originalMerge1649 : Integer.Sparse OriginalKey := originalMerge1645 ++ originalMerge1648

def originalMerge1650 : Integer.Sparse OriginalKey := originalTerm1656 ++ originalTerm1657

def originalMerge1651 : Integer.Sparse OriginalKey := originalTerm1658 ++ originalTerm1659

def originalMerge1652 : Integer.Sparse OriginalKey := originalMerge1650 ++ originalMerge1651

def originalMerge1653 : Integer.Sparse OriginalKey := originalTerm1660 ++ originalTerm1661

def originalMerge1654 : Integer.Sparse OriginalKey := originalTerm1662 ++ originalTerm1663

def originalMerge1655 : Integer.Sparse OriginalKey := originalMerge1653 ++ originalMerge1654

def originalMerge1656 : Integer.Sparse OriginalKey := originalMerge1652 ++ originalMerge1655

def originalMerge1657 : Integer.Sparse OriginalKey := originalMerge1649 ++ originalMerge1656

def originalMerge1658 : Integer.Sparse OriginalKey := originalTerm1665 ++ originalTerm1666

def originalMerge1659 : Integer.Sparse OriginalKey := originalTerm1664 ++ originalMerge1658

def originalMerge1660 : Integer.Sparse OriginalKey := originalTerm1667 ++ originalTerm1668

def originalMerge1661 : Integer.Sparse OriginalKey := originalTerm1669 ++ originalTerm1670

def originalMerge1662 : Integer.Sparse OriginalKey := originalMerge1660 ++ originalMerge1661

def originalMerge1663 : Integer.Sparse OriginalKey := originalMerge1659 ++ originalMerge1662

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1664 : Integer.Sparse OriginalKey := originalTerm1671 ++ originalTerm1672

def originalMerge1665 : Integer.Sparse OriginalKey := originalTerm1673 ++ originalTerm1674

def originalMerge1666 : Integer.Sparse OriginalKey := originalMerge1664 ++ originalMerge1665

def originalMerge1667 : Integer.Sparse OriginalKey := originalTerm1675 ++ originalTerm1676

def originalMerge1668 : Integer.Sparse OriginalKey := originalTerm1677 ++ originalTerm1678

def originalMerge1669 : Integer.Sparse OriginalKey := originalMerge1667 ++ originalMerge1668

def originalMerge1670 : Integer.Sparse OriginalKey := originalMerge1666 ++ originalMerge1669

def originalMerge1671 : Integer.Sparse OriginalKey := originalMerge1663 ++ originalMerge1670

def originalMerge1672 : Integer.Sparse OriginalKey := originalMerge1657 ++ originalMerge1671

def originalMerge1673 : Integer.Sparse OriginalKey := originalMerge1643 ++ originalMerge1672

def originalMerge1674 : Integer.Sparse OriginalKey := originalMerge1614 ++ originalMerge1673

def originalMerge1675 : Integer.Sparse OriginalKey := originalMerge1555 ++ originalMerge1674

def originalMerge1676 : Integer.Sparse OriginalKey := originalTerm1680 ++ originalTerm1681

def originalMerge1677 : Integer.Sparse OriginalKey := originalTerm1679 ++ originalMerge1676

def originalMerge1678 : Integer.Sparse OriginalKey := originalTerm1682 ++ originalTerm1683

def originalMerge1679 : Integer.Sparse OriginalKey := originalTerm1684 ++ originalTerm1685

def originalMerge1680 : Integer.Sparse OriginalKey := originalMerge1678 ++ originalMerge1679

def originalMerge1681 : Integer.Sparse OriginalKey := originalMerge1677 ++ originalMerge1680

def originalMerge1682 : Integer.Sparse OriginalKey := originalTerm1686 ++ originalTerm1687

def originalMerge1683 : Integer.Sparse OriginalKey := originalTerm1688 ++ originalTerm1689

def originalMerge1684 : Integer.Sparse OriginalKey := originalMerge1682 ++ originalMerge1683

def originalMerge1685 : Integer.Sparse OriginalKey := originalTerm1690 ++ originalTerm1691

def originalMerge1686 : Integer.Sparse OriginalKey := originalTerm1692 ++ originalTerm1693

def originalMerge1687 : Integer.Sparse OriginalKey := originalMerge1685 ++ originalMerge1686

def originalMerge1688 : Integer.Sparse OriginalKey := originalMerge1684 ++ originalMerge1687

def originalMerge1689 : Integer.Sparse OriginalKey := originalMerge1681 ++ originalMerge1688

def originalMerge1690 : Integer.Sparse OriginalKey := originalTerm1695 ++ originalTerm1696

def originalMerge1691 : Integer.Sparse OriginalKey := originalTerm1694 ++ originalMerge1690

def originalMerge1692 : Integer.Sparse OriginalKey := originalTerm1697 ++ originalTerm1698

def originalMerge1693 : Integer.Sparse OriginalKey := originalTerm1699 ++ originalTerm1700

def originalMerge1694 : Integer.Sparse OriginalKey := originalMerge1692 ++ originalMerge1693

def originalMerge1695 : Integer.Sparse OriginalKey := originalMerge1691 ++ originalMerge1694

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1696 : Integer.Sparse OriginalKey := originalTerm1701 ++ originalTerm1702

def originalMerge1697 : Integer.Sparse OriginalKey := originalTerm1703 ++ originalTerm1704

def originalMerge1698 : Integer.Sparse OriginalKey := originalMerge1696 ++ originalMerge1697

def originalMerge1699 : Integer.Sparse OriginalKey := originalTerm1705 ++ originalTerm1706

def originalMerge1700 : Integer.Sparse OriginalKey := originalTerm1707 ++ originalTerm1708

def originalMerge1701 : Integer.Sparse OriginalKey := originalMerge1699 ++ originalMerge1700

def originalMerge1702 : Integer.Sparse OriginalKey := originalMerge1698 ++ originalMerge1701

def originalMerge1703 : Integer.Sparse OriginalKey := originalMerge1695 ++ originalMerge1702

def originalMerge1704 : Integer.Sparse OriginalKey := originalMerge1689 ++ originalMerge1703

def originalMerge1705 : Integer.Sparse OriginalKey := originalTerm1710 ++ originalTerm1711

def originalMerge1706 : Integer.Sparse OriginalKey := originalTerm1709 ++ originalMerge1705

def originalMerge1707 : Integer.Sparse OriginalKey := originalTerm1712 ++ originalTerm1713

def originalMerge1708 : Integer.Sparse OriginalKey := originalTerm1714 ++ originalTerm1715

def originalMerge1709 : Integer.Sparse OriginalKey := originalMerge1707 ++ originalMerge1708

def originalMerge1710 : Integer.Sparse OriginalKey := originalMerge1706 ++ originalMerge1709

def originalMerge1711 : Integer.Sparse OriginalKey := originalTerm1716 ++ originalTerm1717

def originalMerge1712 : Integer.Sparse OriginalKey := originalTerm1718 ++ originalTerm1719

def originalMerge1713 : Integer.Sparse OriginalKey := originalMerge1711 ++ originalMerge1712

def originalMerge1714 : Integer.Sparse OriginalKey := originalTerm1720 ++ originalTerm1721

def originalMerge1715 : Integer.Sparse OriginalKey := originalTerm1722 ++ originalTerm1723

def originalMerge1716 : Integer.Sparse OriginalKey := originalMerge1714 ++ originalMerge1715

def originalMerge1717 : Integer.Sparse OriginalKey := originalMerge1713 ++ originalMerge1716

def originalMerge1718 : Integer.Sparse OriginalKey := originalMerge1710 ++ originalMerge1717

def originalMerge1719 : Integer.Sparse OriginalKey := originalTerm1725 ++ originalTerm1726

def originalMerge1720 : Integer.Sparse OriginalKey := originalTerm1724 ++ originalMerge1719

def originalMerge1721 : Integer.Sparse OriginalKey := originalTerm1727 ++ originalTerm1728

def originalMerge1722 : Integer.Sparse OriginalKey := originalTerm1729 ++ originalTerm1730

def originalMerge1723 : Integer.Sparse OriginalKey := originalMerge1721 ++ originalMerge1722

def originalMerge1724 : Integer.Sparse OriginalKey := originalMerge1720 ++ originalMerge1723

def originalMerge1725 : Integer.Sparse OriginalKey := originalTerm1731 ++ originalTerm1732

def originalMerge1726 : Integer.Sparse OriginalKey := originalTerm1733 ++ originalTerm1734

def originalMerge1727 : Integer.Sparse OriginalKey := originalMerge1725 ++ originalMerge1726

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1728 : Integer.Sparse OriginalKey := originalTerm1735 ++ originalTerm1736

def originalMerge1729 : Integer.Sparse OriginalKey := originalTerm1737 ++ originalTerm1738

def originalMerge1730 : Integer.Sparse OriginalKey := originalMerge1728 ++ originalMerge1729

def originalMerge1731 : Integer.Sparse OriginalKey := originalMerge1727 ++ originalMerge1730

def originalMerge1732 : Integer.Sparse OriginalKey := originalMerge1724 ++ originalMerge1731

def originalMerge1733 : Integer.Sparse OriginalKey := originalMerge1718 ++ originalMerge1732

def originalMerge1734 : Integer.Sparse OriginalKey := originalMerge1704 ++ originalMerge1733

def originalMerge1735 : Integer.Sparse OriginalKey := originalTerm1740 ++ originalTerm1741

def originalMerge1736 : Integer.Sparse OriginalKey := originalTerm1739 ++ originalMerge1735

def originalMerge1737 : Integer.Sparse OriginalKey := originalTerm1742 ++ originalTerm1743

def originalMerge1738 : Integer.Sparse OriginalKey := originalTerm1744 ++ originalTerm1745

def originalMerge1739 : Integer.Sparse OriginalKey := originalMerge1737 ++ originalMerge1738

def originalMerge1740 : Integer.Sparse OriginalKey := originalMerge1736 ++ originalMerge1739

def originalMerge1741 : Integer.Sparse OriginalKey := originalTerm1746 ++ originalTerm1747

def originalMerge1742 : Integer.Sparse OriginalKey := originalTerm1748 ++ originalTerm1749

def originalMerge1743 : Integer.Sparse OriginalKey := originalMerge1741 ++ originalMerge1742

def originalMerge1744 : Integer.Sparse OriginalKey := originalTerm1750 ++ originalTerm1751

def originalMerge1745 : Integer.Sparse OriginalKey := originalTerm1752 ++ originalTerm1753

def originalMerge1746 : Integer.Sparse OriginalKey := originalMerge1744 ++ originalMerge1745

def originalMerge1747 : Integer.Sparse OriginalKey := originalMerge1743 ++ originalMerge1746

def originalMerge1748 : Integer.Sparse OriginalKey := originalMerge1740 ++ originalMerge1747

def originalMerge1749 : Integer.Sparse OriginalKey := originalTerm1755 ++ originalTerm1756

def originalMerge1750 : Integer.Sparse OriginalKey := originalTerm1754 ++ originalMerge1749

def originalMerge1751 : Integer.Sparse OriginalKey := originalTerm1757 ++ originalTerm1758

def originalMerge1752 : Integer.Sparse OriginalKey := originalTerm1759 ++ originalTerm1760

def originalMerge1753 : Integer.Sparse OriginalKey := originalMerge1751 ++ originalMerge1752

def originalMerge1754 : Integer.Sparse OriginalKey := originalMerge1750 ++ originalMerge1753

def originalMerge1755 : Integer.Sparse OriginalKey := originalTerm1761 ++ originalTerm1762

def originalMerge1756 : Integer.Sparse OriginalKey := originalTerm1763 ++ originalTerm1764

def originalMerge1757 : Integer.Sparse OriginalKey := originalMerge1755 ++ originalMerge1756

def originalMerge1758 : Integer.Sparse OriginalKey := originalTerm1765 ++ originalTerm1766

def originalMerge1759 : Integer.Sparse OriginalKey := originalTerm1767 ++ originalTerm1768

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1760 : Integer.Sparse OriginalKey := originalMerge1758 ++ originalMerge1759

def originalMerge1761 : Integer.Sparse OriginalKey := originalMerge1757 ++ originalMerge1760

def originalMerge1762 : Integer.Sparse OriginalKey := originalMerge1754 ++ originalMerge1761

def originalMerge1763 : Integer.Sparse OriginalKey := originalMerge1748 ++ originalMerge1762

def originalMerge1764 : Integer.Sparse OriginalKey := originalTerm1770 ++ originalTerm1771

def originalMerge1765 : Integer.Sparse OriginalKey := originalTerm1769 ++ originalMerge1764

def originalMerge1766 : Integer.Sparse OriginalKey := originalTerm1772 ++ originalTerm1773

def originalMerge1767 : Integer.Sparse OriginalKey := originalTerm1774 ++ originalTerm1775

def originalMerge1768 : Integer.Sparse OriginalKey := originalMerge1766 ++ originalMerge1767

def originalMerge1769 : Integer.Sparse OriginalKey := originalMerge1765 ++ originalMerge1768

def originalMerge1770 : Integer.Sparse OriginalKey := originalTerm1776 ++ originalTerm1777

def originalMerge1771 : Integer.Sparse OriginalKey := originalTerm1778 ++ originalTerm1779

def originalMerge1772 : Integer.Sparse OriginalKey := originalMerge1770 ++ originalMerge1771

def originalMerge1773 : Integer.Sparse OriginalKey := originalTerm1780 ++ originalTerm1781

def originalMerge1774 : Integer.Sparse OriginalKey := originalTerm1782 ++ originalTerm1783

def originalMerge1775 : Integer.Sparse OriginalKey := originalMerge1773 ++ originalMerge1774

def originalMerge1776 : Integer.Sparse OriginalKey := originalMerge1772 ++ originalMerge1775

def originalMerge1777 : Integer.Sparse OriginalKey := originalMerge1769 ++ originalMerge1776

def originalMerge1778 : Integer.Sparse OriginalKey := originalTerm1785 ++ originalTerm1786

def originalMerge1779 : Integer.Sparse OriginalKey := originalTerm1784 ++ originalMerge1778

def originalMerge1780 : Integer.Sparse OriginalKey := originalTerm1787 ++ originalTerm1788

def originalMerge1781 : Integer.Sparse OriginalKey := originalTerm1789 ++ originalTerm1790

def originalMerge1782 : Integer.Sparse OriginalKey := originalMerge1780 ++ originalMerge1781

def originalMerge1783 : Integer.Sparse OriginalKey := originalMerge1779 ++ originalMerge1782

def originalMerge1784 : Integer.Sparse OriginalKey := originalTerm1791 ++ originalTerm1792

def originalMerge1785 : Integer.Sparse OriginalKey := originalTerm1793 ++ originalTerm1794

def originalMerge1786 : Integer.Sparse OriginalKey := originalMerge1784 ++ originalMerge1785

def originalMerge1787 : Integer.Sparse OriginalKey := originalTerm1795 ++ originalTerm1796

def originalMerge1788 : Integer.Sparse OriginalKey := originalTerm1797 ++ originalTerm1798

def originalMerge1789 : Integer.Sparse OriginalKey := originalMerge1787 ++ originalMerge1788

def originalMerge1790 : Integer.Sparse OriginalKey := originalMerge1786 ++ originalMerge1789

def originalMerge1791 : Integer.Sparse OriginalKey := originalMerge1783 ++ originalMerge1790

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1792 : Integer.Sparse OriginalKey := originalMerge1777 ++ originalMerge1791

def originalMerge1793 : Integer.Sparse OriginalKey := originalMerge1763 ++ originalMerge1792

def originalMerge1794 : Integer.Sparse OriginalKey := originalMerge1734 ++ originalMerge1793

def originalMerge1795 : Integer.Sparse OriginalKey := originalTerm1800 ++ originalTerm1801

def originalMerge1796 : Integer.Sparse OriginalKey := originalTerm1799 ++ originalMerge1795

def originalMerge1797 : Integer.Sparse OriginalKey := originalTerm1802 ++ originalTerm1803

def originalMerge1798 : Integer.Sparse OriginalKey := originalTerm1804 ++ originalTerm1805

def originalMerge1799 : Integer.Sparse OriginalKey := originalMerge1797 ++ originalMerge1798

def originalMerge1800 : Integer.Sparse OriginalKey := originalMerge1796 ++ originalMerge1799

def originalMerge1801 : Integer.Sparse OriginalKey := originalTerm1806 ++ originalTerm1807

def originalMerge1802 : Integer.Sparse OriginalKey := originalTerm1808 ++ originalTerm1809

def originalMerge1803 : Integer.Sparse OriginalKey := originalMerge1801 ++ originalMerge1802

def originalMerge1804 : Integer.Sparse OriginalKey := originalTerm1810 ++ originalTerm1811

def originalMerge1805 : Integer.Sparse OriginalKey := originalTerm1812 ++ originalTerm1813

def originalMerge1806 : Integer.Sparse OriginalKey := originalMerge1804 ++ originalMerge1805

def originalMerge1807 : Integer.Sparse OriginalKey := originalMerge1803 ++ originalMerge1806

def originalMerge1808 : Integer.Sparse OriginalKey := originalMerge1800 ++ originalMerge1807

def originalMerge1809 : Integer.Sparse OriginalKey := originalTerm1815 ++ originalTerm1816

def originalMerge1810 : Integer.Sparse OriginalKey := originalTerm1814 ++ originalMerge1809

def originalMerge1811 : Integer.Sparse OriginalKey := originalTerm1817 ++ originalTerm1818

def originalMerge1812 : Integer.Sparse OriginalKey := originalTerm1819 ++ originalTerm1820

def originalMerge1813 : Integer.Sparse OriginalKey := originalMerge1811 ++ originalMerge1812

def originalMerge1814 : Integer.Sparse OriginalKey := originalMerge1810 ++ originalMerge1813

def originalMerge1815 : Integer.Sparse OriginalKey := originalTerm1821 ++ originalTerm1822

def originalMerge1816 : Integer.Sparse OriginalKey := originalTerm1823 ++ originalTerm1824

def originalMerge1817 : Integer.Sparse OriginalKey := originalMerge1815 ++ originalMerge1816

def originalMerge1818 : Integer.Sparse OriginalKey := originalTerm1825 ++ originalTerm1826

def originalMerge1819 : Integer.Sparse OriginalKey := originalTerm1827 ++ originalTerm1828

def originalMerge1820 : Integer.Sparse OriginalKey := originalMerge1818 ++ originalMerge1819

def originalMerge1821 : Integer.Sparse OriginalKey := originalMerge1817 ++ originalMerge1820

def originalMerge1822 : Integer.Sparse OriginalKey := originalMerge1814 ++ originalMerge1821

def originalMerge1823 : Integer.Sparse OriginalKey := originalMerge1808 ++ originalMerge1822

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1824 : Integer.Sparse OriginalKey := originalTerm1830 ++ originalTerm1831

def originalMerge1825 : Integer.Sparse OriginalKey := originalTerm1829 ++ originalMerge1824

def originalMerge1826 : Integer.Sparse OriginalKey := originalTerm1832 ++ originalTerm1833

def originalMerge1827 : Integer.Sparse OriginalKey := originalTerm1834 ++ originalTerm1835

def originalMerge1828 : Integer.Sparse OriginalKey := originalMerge1826 ++ originalMerge1827

def originalMerge1829 : Integer.Sparse OriginalKey := originalMerge1825 ++ originalMerge1828

def originalMerge1830 : Integer.Sparse OriginalKey := originalTerm1836 ++ originalTerm1837

def originalMerge1831 : Integer.Sparse OriginalKey := originalTerm1838 ++ originalTerm1839

def originalMerge1832 : Integer.Sparse OriginalKey := originalMerge1830 ++ originalMerge1831

def originalMerge1833 : Integer.Sparse OriginalKey := originalTerm1840 ++ originalTerm1841

def originalMerge1834 : Integer.Sparse OriginalKey := originalTerm1842 ++ originalTerm1843

def originalMerge1835 : Integer.Sparse OriginalKey := originalMerge1833 ++ originalMerge1834

def originalMerge1836 : Integer.Sparse OriginalKey := originalMerge1832 ++ originalMerge1835

def originalMerge1837 : Integer.Sparse OriginalKey := originalMerge1829 ++ originalMerge1836

def originalMerge1838 : Integer.Sparse OriginalKey := originalTerm1845 ++ originalTerm1846

def originalMerge1839 : Integer.Sparse OriginalKey := originalTerm1844 ++ originalMerge1838

def originalMerge1840 : Integer.Sparse OriginalKey := originalTerm1847 ++ originalTerm1848

def originalMerge1841 : Integer.Sparse OriginalKey := originalTerm1849 ++ originalTerm1850

def originalMerge1842 : Integer.Sparse OriginalKey := originalMerge1840 ++ originalMerge1841

def originalMerge1843 : Integer.Sparse OriginalKey := originalMerge1839 ++ originalMerge1842

def originalMerge1844 : Integer.Sparse OriginalKey := originalTerm1851 ++ originalTerm1852

def originalMerge1845 : Integer.Sparse OriginalKey := originalTerm1853 ++ originalTerm1854

def originalMerge1846 : Integer.Sparse OriginalKey := originalMerge1844 ++ originalMerge1845

def originalMerge1847 : Integer.Sparse OriginalKey := originalTerm1855 ++ originalTerm1856

def originalMerge1848 : Integer.Sparse OriginalKey := originalTerm1857 ++ originalTerm1858

def originalMerge1849 : Integer.Sparse OriginalKey := originalMerge1847 ++ originalMerge1848

def originalMerge1850 : Integer.Sparse OriginalKey := originalMerge1846 ++ originalMerge1849

def originalMerge1851 : Integer.Sparse OriginalKey := originalMerge1843 ++ originalMerge1850

def originalMerge1852 : Integer.Sparse OriginalKey := originalMerge1837 ++ originalMerge1851

def originalMerge1853 : Integer.Sparse OriginalKey := originalMerge1823 ++ originalMerge1852

def originalMerge1854 : Integer.Sparse OriginalKey := originalTerm1860 ++ originalTerm1861

def originalMerge1855 : Integer.Sparse OriginalKey := originalTerm1859 ++ originalMerge1854

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1856 : Integer.Sparse OriginalKey := originalTerm1862 ++ originalTerm1863

def originalMerge1857 : Integer.Sparse OriginalKey := originalTerm1864 ++ originalTerm1865

def originalMerge1858 : Integer.Sparse OriginalKey := originalMerge1856 ++ originalMerge1857

def originalMerge1859 : Integer.Sparse OriginalKey := originalMerge1855 ++ originalMerge1858

def originalMerge1860 : Integer.Sparse OriginalKey := originalTerm1866 ++ originalTerm1867

def originalMerge1861 : Integer.Sparse OriginalKey := originalTerm1868 ++ originalTerm1869

def originalMerge1862 : Integer.Sparse OriginalKey := originalMerge1860 ++ originalMerge1861

def originalMerge1863 : Integer.Sparse OriginalKey := originalTerm1870 ++ originalTerm1871

def originalMerge1864 : Integer.Sparse OriginalKey := originalTerm1872 ++ originalTerm1873

def originalMerge1865 : Integer.Sparse OriginalKey := originalMerge1863 ++ originalMerge1864

def originalMerge1866 : Integer.Sparse OriginalKey := originalMerge1862 ++ originalMerge1865

def originalMerge1867 : Integer.Sparse OriginalKey := originalMerge1859 ++ originalMerge1866

def originalMerge1868 : Integer.Sparse OriginalKey := originalTerm1875 ++ originalTerm1876

def originalMerge1869 : Integer.Sparse OriginalKey := originalTerm1874 ++ originalMerge1868

def originalMerge1870 : Integer.Sparse OriginalKey := originalTerm1877 ++ originalTerm1878

def originalMerge1871 : Integer.Sparse OriginalKey := originalTerm1879 ++ originalTerm1880

def originalMerge1872 : Integer.Sparse OriginalKey := originalMerge1870 ++ originalMerge1871

def originalMerge1873 : Integer.Sparse OriginalKey := originalMerge1869 ++ originalMerge1872

def originalMerge1874 : Integer.Sparse OriginalKey := originalTerm1881 ++ originalTerm1882

def originalMerge1875 : Integer.Sparse OriginalKey := originalTerm1883 ++ originalTerm1884

def originalMerge1876 : Integer.Sparse OriginalKey := originalMerge1874 ++ originalMerge1875

def originalMerge1877 : Integer.Sparse OriginalKey := originalTerm1885 ++ originalTerm1886

def originalMerge1878 : Integer.Sparse OriginalKey := originalTerm1887 ++ originalTerm1888

def originalMerge1879 : Integer.Sparse OriginalKey := originalMerge1877 ++ originalMerge1878

def originalMerge1880 : Integer.Sparse OriginalKey := originalMerge1876 ++ originalMerge1879

def originalMerge1881 : Integer.Sparse OriginalKey := originalMerge1873 ++ originalMerge1880

def originalMerge1882 : Integer.Sparse OriginalKey := originalMerge1867 ++ originalMerge1881

def originalMerge1883 : Integer.Sparse OriginalKey := originalTerm1890 ++ originalTerm1891

def originalMerge1884 : Integer.Sparse OriginalKey := originalTerm1889 ++ originalMerge1883

def originalMerge1885 : Integer.Sparse OriginalKey := originalTerm1892 ++ originalTerm1893

def originalMerge1886 : Integer.Sparse OriginalKey := originalTerm1894 ++ originalTerm1895

def originalMerge1887 : Integer.Sparse OriginalKey := originalMerge1885 ++ originalMerge1886

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

def originalMerge1888 : Integer.Sparse OriginalKey := originalMerge1884 ++ originalMerge1887

def originalMerge1889 : Integer.Sparse OriginalKey := originalTerm1896 ++ originalTerm1897

def originalMerge1890 : Integer.Sparse OriginalKey := originalTerm1898 ++ originalTerm1899

def originalMerge1891 : Integer.Sparse OriginalKey := originalMerge1889 ++ originalMerge1890

def originalMerge1892 : Integer.Sparse OriginalKey := originalTerm1900 ++ originalTerm1901

def originalMerge1893 : Integer.Sparse OriginalKey := originalTerm1902 ++ originalTerm1903

def originalMerge1894 : Integer.Sparse OriginalKey := originalMerge1892 ++ originalMerge1893

def originalMerge1895 : Integer.Sparse OriginalKey := originalMerge1891 ++ originalMerge1894

def originalMerge1896 : Integer.Sparse OriginalKey := originalMerge1888 ++ originalMerge1895

def originalMerge1897 : Integer.Sparse OriginalKey := originalTerm1905 ++ originalTerm1906

def originalMerge1898 : Integer.Sparse OriginalKey := originalTerm1904 ++ originalMerge1897

def originalMerge1899 : Integer.Sparse OriginalKey := originalTerm1907 ++ originalTerm1908

def originalMerge1900 : Integer.Sparse OriginalKey := originalTerm1909 ++ originalTerm1910

def originalMerge1901 : Integer.Sparse OriginalKey := originalMerge1899 ++ originalMerge1900

def originalMerge1902 : Integer.Sparse OriginalKey := originalMerge1898 ++ originalMerge1901

def originalMerge1903 : Integer.Sparse OriginalKey := originalTerm1911 ++ originalTerm1912

def originalMerge1904 : Integer.Sparse OriginalKey := originalTerm1913 ++ originalTerm1914

def originalMerge1905 : Integer.Sparse OriginalKey := originalMerge1903 ++ originalMerge1904

def originalMerge1906 : Integer.Sparse OriginalKey := originalTerm1915 ++ originalTerm1916

def originalMerge1907 : Integer.Sparse OriginalKey := originalTerm1917 ++ originalTerm1918

def originalMerge1908 : Integer.Sparse OriginalKey := originalMerge1906 ++ originalMerge1907

def originalMerge1909 : Integer.Sparse OriginalKey := originalMerge1905 ++ originalMerge1908

def originalMerge1910 : Integer.Sparse OriginalKey := originalMerge1902 ++ originalMerge1909

def originalMerge1911 : Integer.Sparse OriginalKey := originalMerge1896 ++ originalMerge1910

def originalMerge1912 : Integer.Sparse OriginalKey := originalMerge1882 ++ originalMerge1911

def originalMerge1913 : Integer.Sparse OriginalKey := originalMerge1853 ++ originalMerge1912

def originalMerge1914 : Integer.Sparse OriginalKey := originalMerge1794 ++ originalMerge1913

def originalMerge1915 : Integer.Sparse OriginalKey := originalMerge1675 ++ originalMerge1914

def originalMerge1916 : Integer.Sparse OriginalKey := originalMerge1436 ++ originalMerge1915

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


