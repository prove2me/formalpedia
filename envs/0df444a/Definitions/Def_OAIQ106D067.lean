-- Prove2me | Definitions.Def_OAIQ106D067
-- name    : OAIQ106D067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:30:19.947573+00:00
-- url     : https://prove2.me/theorems/d978e1da-191a-4552-86d8-da4e4f5f5a02
-- title:
--   Definitions bundle OAIQ106D067 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1472 declarations of OpenAI's Lean: 1472 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw9484step0`, `OAI.MUB6.Certificate.PairSemantics.raw9485`, `OAI.MUB6.Certificate.PairSemantics.raw9485step0`, `OAI.MUB6.Certificate.PairSemantics.raw9486`, `OAI.MUB6.Certificate.PairSemantics.raw9486step0`, `OAI.MUB6.Certificate.PairSemantics.raw9487`, `OAI.MUB6.Certificate.PairSemantics.raw9487step0`, `OAI.MUB6.Certificate.PairSemantics.raw9488`, `OAI.MUB6.Certificate.PairSemantics.raw9488step0`, `OAI.MUB6.Certificate.PairSemantics.raw9489`, `OAI.MUB6.Certificate.PairSemantics.raw9489step0`, `OAI.MUB6.Certificate.PairSemantics.raw949`, `OAI.MUB6.Certificate.PairSemantics.raw9490`, `OAI.MUB6.Certificate.PairSemantics.raw9490step0`, `OAI.MUB6.Certificate.PairSemantics.raw9491`, `OAI.MUB6.Certificate.PairSemantics.raw9491step0`, `OAI.MUB6.Certificate.PairSemantics.raw9492`, `OAI.MUB6.Certificate.PairSemantics.raw9492step0`, `OAI.MUB6.Certificate.PairSemantics.raw9493`, `OAI.MUB6.Certificate.PairSemantics.raw9493step0`, `OAI.MUB6.Certificate.PairSemantics.raw9494`, `OAI.MUB6.Certificate.PairSemantics.raw9494step0`, `OAI.MUB6.Certificate.PairSemantics.raw9495`, `OAI.MUB6.Certificate.PairSemantics.raw9495step0`, `OAI.MUB6.Certificate.PairSemantics.raw9496`, `OAI.MUB6.Certificate.PairSemantics.raw9496step0`, `OAI.MUB6.Certificate.PairSemantics.raw9497`, `OAI.MUB6.Certificate.PairSemantics.raw9497step0`, `OAI.MUB6.Certificate.PairSemantics.raw9498`, `OAI.MUB6.Certificate.PairSemantics.raw9498step0`, `OAI.MUB6.Certificate.PairSemantics.raw9499`, `OAI.MUB6.Certificate.PairSemantics.raw9499step0`, `OAI.MUB6.Certificate.PairSemantics.raw949step0`, `OAI.MUB6.Certificate.PairSemantics.raw94step0`, `OAI.MUB6.Certificate.PairSemantics.raw94step1`, `OAI.MUB6.Certificate.PairSemantics.raw95`, `OAI.MUB6.Certificate.PairSemantics.raw950`, `OAI.MUB6.Certificate.PairSemantics.raw9500`, `OAI.MUB6.Certificate.PairSemantics.raw9500step0`, `OAI.MUB6.Certificate.PairSemantics.raw9501` and 1432 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Gram`, `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical29`, `MutuallyUnbiased_PairSemantics_Canonical296`, `MutuallyUnbiased_PairSemantics_Canonical297`, `MutuallyUnbiased_PairSemantics_Canonical298`, `MutuallyUnbiased_PairSemantics_Canonical299`, `MutuallyUnbiased_PairSemantics_Canonical3`, `MutuallyUnbiased_PairSemantics_Canonical30`, `MutuallyUnbiased_PairSemantics_Canonical300`, `MutuallyUnbiased_PairSemantics_Canonical301`, `MutuallyUnbiased_PairSemantics_Canonical302`, `MutuallyUnbiased_PairSemantics_Canonical303`, `MutuallyUnbiased_PairSemantics_Canonical304`, `MutuallyUnbiased_PairSemantics_Canonical305`, `MutuallyUnbiased_PairSemantics_Canonical306`, `MutuallyUnbiased_PairSemantics_Canonical307`, `MutuallyUnbiased_PairSemantics_Canonical308`, `MutuallyUnbiased_PairSemantics_Canonical309`, `MutuallyUnbiased_PairSemantics_Canonical31`, `MutuallyUnbiased_PairSemantics_Canonical310`, `MutuallyUnbiased_PairSemantics_Canonical311`, `MutuallyUnbiased_PairSemantics_Canonical312`, `MutuallyUnbiased_PairSources_Data`, `MutuallyUnbiased_PairTargets_ExtraPermutations`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D140`; the statements `OAI.MUB6.Certificate.GramData.Block3.entry_0_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_26` and `OAI.MUB6.Certificate.GramData.Block3.gram`; the proofs of `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical110`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical111`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical112`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical113`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical114`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical115`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical116`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical117`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical119`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical120`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical121`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical123`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical125`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical126`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical35`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical4`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical5`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical56`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical57`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical58`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical59`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical60`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical61`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical62`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical90` and `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical91`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact rational Gram witnesses

A unit lower triangular matrix and a positive rational diagonal certify a real
matrix's positive definiteness. The large numerical checks can therefore be
split into separate rational identities for individual matrix entries.
-/
namespace MUB6.Certificate

open Matrix
open scoped BigOperators

/-- Complete a table of strict lower triangular entries with unit diagonal. -/
def lowerUnit {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j < i then entries i j else if i = j then 1 else 0

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw9step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw94step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw94step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw95 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw95step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw95step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw950 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

def raw953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw955 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def raw956 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

def raw957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw958 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def raw959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical296
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9484step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9485 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, -1, 4], ![2, -1, 1, -2]]

def raw9485step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw9486 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 0, -1]]

def raw9486step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9487 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9487step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw9488 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 0, 0]]

def raw9488step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9489 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, -1, 1]]

def raw9489step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9490 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -2, 2]]

def raw9490step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9491 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1], ![-2, -1, 2, 1]]

def raw9491step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9492 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 1, 2]]

def raw9492step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9493 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9493step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9494 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0], ![-2, -2, 2, 2]]

def raw9494step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9495 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 1, 3]]

def raw9495step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9496 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9496step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw9497 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw9497step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9498 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9498step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw9499 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9499step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9500 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![1, -1, 1, -1]]

def raw9500step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9501 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 0, 0]]

def raw9501step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9502 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 1, 0]]

def raw9502step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9503 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1]]

def raw9503step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical297
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9504 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1]]

def raw9504step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw9505 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9505step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9506 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9506step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9507 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9507step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9508 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -2, 3], ![1, -2, 2, -1]]

def raw9508step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9509 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 1, 0]]

def raw9509step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9510 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 0, 1]]

def raw9510step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9511 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![0, -1, -2, 3]]

def raw9511step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![-1, -2, 3]]

def raw9511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw9512 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -2, 0, 2]]

def raw9512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![-2, 0, 2]]

def raw9512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw9513 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9513step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9513step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9514 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9514step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9514step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9515 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9515step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9515step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9516 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9516step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9517 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9517step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9517step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw9518 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9518step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9518step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw9519 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9519step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9520 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9520step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9520step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw9521 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9521step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9521step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw9522 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9522step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9523 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9523step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9523step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9524 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9524step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9524step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9525 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 2, 1, -3]]

def raw9525step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9526 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 0, -2]]

def raw9526step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9527 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -2, 3], ![-1, 2, 2, -3]]

def raw9527step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 2, -3], ![1, -2, -2, 3]]

def raw9527step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9528 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 1, -2]]

def raw9528step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -1, 2]]

def raw9528step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9529 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9529step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9530 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9530step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9530step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9531 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9531step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9531step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9532 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9532step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9533 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 2, 1, -3]]

def raw9533step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3], ![0, -2, -1, 3]]

def raw9533step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw9534 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 0, -2]]

def raw9534step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9535 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2]]

def raw9535step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw9535step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical298
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9536 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 2, -3]]

def raw9536step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def raw9536step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9537 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9537step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9537step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9538 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 0, -1]]

def raw9538step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, 0, 1]]

def raw9538step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9539 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9539step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9539step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9540 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![-2, -1, 2, 1]]

def raw9540step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9541 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9541step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9542 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9542step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9542step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9543 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 0, -1]]

def raw9543step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, 0, 1]]

def raw9543step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9544 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -2, 3], ![-2, 2, 2, -2]]

def raw9544step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw9544step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9545 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 1, -1]]

def raw9545step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw9545step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9546 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9546step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9546step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9547 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 1, 2]]

def raw9547step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9548 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9548step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9549 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, -1, 0, 0], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw9549step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw9549step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9550 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 2, -2, 2]]

def raw9550step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw9551 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9551step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9552 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![1, -1, 0, 0]]

def raw9552step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, -2, 1, 0]]

def raw9552step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw9553 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def raw9553step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def raw9554 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, -1, 0, 1]]

def raw9554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1]]

def raw9554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw9555 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![0, -1, -2, 3]]

def raw9555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw9555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw9556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9556step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -2, 0, 1]]

def raw9557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -2, 0, 2]]

def raw9558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]

def raw9558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw9559 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9559step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9560 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9560step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9561 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9561step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw9562 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9562step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw9563 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9563step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9564 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9564step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw9565 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9565step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 0, -3, 4]]

def raw9565step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw9566 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9566step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw9567 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9567step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical299
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9568 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9568step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw9569 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 3, -4]]

def raw9569step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw9570 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 3, -3]]

def raw9570step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw9571 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3]]

def raw9571step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9572 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9572step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9573 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9573step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9573step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9574 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9574step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9574step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9575 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9575step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9576 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9576step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9577 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9577step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9578 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9578step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9579 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9579step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw9580 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9580step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9581 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9581step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9582 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9582step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9583 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9583step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw9584 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9584step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9585 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9585step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9586 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9586step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9587 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9587step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9588 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9588step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw9589 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9589step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9590 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4]]

def raw9590step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9591 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9591step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9591step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9592 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9592step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9593 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3]]

def raw9593step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9594 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4]]

def raw9594step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9595 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 0, 3, -3]]

def raw9595step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, 0, -3, 3]]

def raw9595step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw9596 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9596step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9597 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9597step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9598 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9598step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9599 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2]]

def raw9599step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw96 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]

def raw96step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]

def raw96step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw97 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw97step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw97step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw98 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]

def raw98step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]

def raw98step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw99 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]

def raw99step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]

def raw99step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw960 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def raw961 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, -1, 0], ![1, 4, -5]]

def raw961step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, -1, 4], ![5, 0, -5]]

def raw961step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 5, -5], ![1, -2, 1]]

def raw962 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 0, -1], ![1, 3, -4]]

def raw962step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 0, 3], ![5, -1, -4]]

def raw962step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def raw963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

def raw964 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 2, -3], ![1, 1, -2]]

def raw964step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

def raw965 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 3, -4], ![1, 0, -1]]

def raw965step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![5, -4, -1]]

def raw965step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

def raw966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw967 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw968 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw968step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw969step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw970 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw972 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw974step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, -1, 1], ![5, -1, 0, -4]]

def raw974step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw975step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw976 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw977step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, 0, 0], ![5, -1, -1, -3]]

def raw978step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw979 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw979step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, 1, -1], ![5, -1, -2, -2]]

def raw980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw981 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw981step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw984step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 2, -1, 0], ![5, -2, 0, -3]]

def raw984step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![1, -2, 1, 0], ![-5, 2, 0, 3]]

def raw984step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -2, 0, 1]]

def raw985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw987 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw987step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw988 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw988step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 2, 0, -1], ![5, -2, -1, -2]]

def raw988step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw989step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw991step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical300
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9600 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw9600step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9601 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw9601step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw9602 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9602step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9602step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9603 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9603step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9604 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9604step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9605 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9605step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9606 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9606step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw9607 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9607step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9608 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -2, -1, 2]]

def raw9608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 1, -2], ![-1, 0, 2, -1], ![1, -1, -2, 2]]

def raw9608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw9609 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9609step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9609step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9610 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9610step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9610step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9611 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9611step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9612 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9612step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9613 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9613step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9614 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9614step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9615 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9615step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw9616 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9616step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9617 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9617step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9618 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9618step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9619 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9619step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9619step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9620 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9620step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9620step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9621 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def raw9621step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9622 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def raw9622step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9623 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 0, 2, -3]]

def raw9623step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw9624 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 1, -2]]

def raw9624step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -1, 2]]

def raw9624step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9625 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9625step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw9626 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 1, -1]]

def raw9626step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 1, -1, 1]]

def raw9626step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw9627 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 2, 0]]

def raw9627step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9628 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9628step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9628step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9629 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 2, 1]]

def raw9629step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9630 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9630step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9631 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def raw9631step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical301
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9632 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def raw9632step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw9633 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def raw9633step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9634 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def raw9634step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9635 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, -1, 2], ![-2, 0, 3, -1]]

def raw9635step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9636 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 2, 0]]

def raw9636step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw9637 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0], ![-2, -1, 2, 1]]

def raw9637step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9638 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def raw9638step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9639 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def raw9639step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9640 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, -1, 4], ![1, -1, 2, -2]]

def raw9640step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw9641 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 1, -1]]

def raw9641step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![-1, 1, -1, 1]]

def raw9641step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9642 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9642step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9643 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -2, 3]]

def raw9643step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw9644 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 0, 0], ![-2, -1, 1, 2]]

def raw9644step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9645 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3]]

def raw9645step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3]]

def raw9645step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw9646 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0], ![-2, -2, 2, 2]]

def raw9646step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9647 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9647step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9648 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -2, 0, 2]]

def raw9648step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 2, 0, -2]]

def raw9648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2]]

def raw9648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw9649 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9649step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9649step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9650 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9650step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9651 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9651step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9652 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9652step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw9653 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9653step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9653step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9654 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9654step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9654step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9655 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9655step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9656 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def raw9656step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -1, -2, 3]]

def raw9656step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9657 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def raw9657step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9658 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9658step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9659 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2]]

def raw9659step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw9659step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9660 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, 0, 3, -3]]

def raw9660step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9661 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 2, -2]]

def raw9661step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9662 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def raw9662step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9663 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def raw9663step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical302
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9664 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9664step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3], ![0, -1, -2, 3]]

def raw9664step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9665 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2]]

def raw9665step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9666 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 2, -1]]

def raw9666step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9667 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 3, -3]]

def raw9667step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw9668 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def raw9668step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -1, -2, 2]]

def raw9668step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9669 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def raw9669step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9670 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 1, 2, -3]]

def raw9670step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9671 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 1, -2]]

def raw9671step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3], ![0, -1, -1, 2]]

def raw9671step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw9672 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9672step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9672step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw9673 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 1, -1]]

def raw9673step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -1, -1, 1]]

def raw9673step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9674 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -2, 3], ![-2, 1, 3, -2]]

def raw9674step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9675 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 2, -1]]

def raw9675step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def raw9675step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9676 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9676step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw9677 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9677step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9678 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9678step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9679 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9679step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw9680 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def raw9680step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9681 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def raw9681step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9682 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def raw9682step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9683 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def raw9683step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9684 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, -2, 3, -1]]

def raw9684step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9685 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 2, 0]]

def raw9685step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw9686 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -2, 2, 1]]

def raw9686step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9687 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 1, 2]]

def raw9687step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9688 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, -1, 3], ![-2, 1, 3, -2]]

def raw9688step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9689 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 2, -1]]

def raw9689step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![0, 2, 0, -2], ![2, -1, -2, 1]]

def raw9689step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9690 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 1, 0]]

def raw9690step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw9691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def raw9691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw9692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw9692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def raw9692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw9693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw9693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def raw9693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw9694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw9694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def raw9694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw9695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical303
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw9696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def raw9696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw9697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw9697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw9697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw9698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw9698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw9698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw9698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw9699 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

def raw9699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1]]

def raw9699step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw9699step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw9700 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9700step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9700step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9701 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9701step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9701step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9702 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9702step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9702step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9703 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9703step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9703step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw9704 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9704step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9704step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9704step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9705 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9705step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9705step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9705step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9706 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9706step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9706step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9706step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9707 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9707step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9707step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9708 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9708step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9708step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9709 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9709step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9709step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9710 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9710step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9710step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9710step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw9711 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9711step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9711step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9712 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9712step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9712step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9713 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9713step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9713step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9713step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9714 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9714step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9714step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9714step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9715 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9715step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9715step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9715step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9716 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9716step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9716step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9717 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9717step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9717step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9717step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9718 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9718step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9718step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9719 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9719step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9719step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw9719step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9720 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9720step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9720step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw9721 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9721step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9721step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9721step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw9722 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9722step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, -1, -2]]

def raw9722step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, -1, -2]]

def raw9722step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9723 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9723step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9723step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9724 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9724step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9724step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9725 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9725step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9725step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, -1, -2, 2]]

def raw9725step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9726 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9726step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2]]

def raw9726step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, -1, -2]]

def raw9726step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9727 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9727step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9727step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical304
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9728 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9728step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9728step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9729 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9729step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9729step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9730 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9730step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2], ![2, 2, 0, -4]]

def raw9730step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2], ![2, 2, 0, -4]]

def raw9730step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw9731 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9731step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9731step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw9732 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9732step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9732step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9733 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9733step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw9733step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw9733step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9734 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9734step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9734step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9735 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-5, 2, 1, 2], ![5, -2, -2, -1]]

def raw9735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -5, 5], ![0, 2, -2], ![1, 1, -2], ![-1, 2, -1]]

def raw9735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def raw9736 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-4, 2, 1, 1], ![4, -2, -2, 0]]

def raw9736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw9736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -2, 2], ![-1, -1, 2], ![1, -1, 0]]

def raw9736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw9737 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-4, 3, 1, 0], ![4, -3, -2, 1]]

def raw9737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![1, 1, -2], ![-1, 0, 1]]

def raw9737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -3, 3], ![-1, -1, 2], ![1, 0, -1]]

def raw9737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw9738 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 2, -2, 3], ![3, -2, 1, -2]]

def raw9738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, -2, 1], ![-1, 3, -2]]

def raw9738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw9739 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 2, 1, 0], ![3, -2, -2, 1]]

def raw9739step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw9739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![-1, -1, 2], ![1, 0, -1]]

def raw9739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9740 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 3, -2, 2], ![3, -3, 1, -1]]

def raw9740step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![1, -2, 1], ![-1, 2, -1]]

def raw9740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw9741 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-3, 3, 1, -1], ![3, -3, -2, 2]]

def raw9741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![1, 1, -2], ![-1, -1, 2]]

def raw9741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw9742 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![2, 2, -2, -2]]

def raw9742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw9742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw9743 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![2, -2, 1, -1]]

def raw9743step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![-1, 2, -1]]

def raw9743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw9744 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 1, -1], ![2, -2, -2, 2]]

def raw9744step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw9744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw9745 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 3, -2, 1], ![2, -3, 1, 0]]

def raw9745step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![1, -2, 1], ![-1, 1, 0]]

def raw9745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![-1, 2, -1], ![1, -1, 0]]

def raw9745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9746 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 4, -2, 0], ![2, -4, 1, 1]]

def raw9746step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![1, -2, 1], ![-1, 0, 1]]

def raw9746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -4, 4], ![-1, 2, -1], ![1, 0, -1]]

def raw9746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw9747 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -3, 1, 3], ![1, 3, -2, -2]]

def raw9747step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![1, 1, -2], ![-1, 3, -2]]

def raw9747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def raw9748 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -3, 3, 1], ![1, 3, -4, 0]]

def raw9748step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -3, 3], ![1, 3, -4], ![-1, 1, 0]]

def raw9748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 3, -3], ![-1, -3, 4], ![1, -1, 0]]

def raw9748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

def raw9749 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![1, 2, -2, -1]]

def raw9749step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw9749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw9750 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 2, 1], ![1, 2, -3, 0]]

def raw9750step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw9750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw9750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw9751 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 3, 0], ![1, 2, -4, 1]]

def raw9751step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![-1, 0, 1]]

def raw9751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-1, -3, 4], ![1, 0, -1]]

def raw9751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw9752 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9753 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def raw9753step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![-1, 1, 1, -1]]

def raw9753step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9754 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9755 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw9755step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![-1, 0, -2, 3]]

def raw9755step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![-1, -1, 0, 2], ![1, 0, 2, -3]]

def raw9755step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw9756 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9756step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw9756step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw9757 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, -2, 1, 0]]

def raw9757step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![-1, 1, 0]]

def raw9757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0]]

def raw9757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw9758 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

def raw9758step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw9758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw9759 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 3, -2, 0], ![1, -3, 1, 1]]

def raw9759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![-1, 0, 1]]

def raw9759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![-1, 2, -1], ![1, 0, -1]]

def raw9759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical305
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9760 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 4, -3, 0], ![1, -4, 2, 1]]

def raw9760step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![1, -3, 2], ![-1, 0, 1]]

def raw9760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -4, 4], ![-1, 3, -2], ![1, 0, -1]]

def raw9760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def raw9761 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 4, -2, -1], ![1, -4, 1, 2]]

def raw9761step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![-1, -1, 2]]

def raw9761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def raw9762 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9762step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9763 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9763step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9764 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9764step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9765 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9765step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9766 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9766step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9766step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9767 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9767step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9767step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw9768 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9768step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9768step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1], ![2, 1, 0, -3]]

def raw9768step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9769 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9769step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9769step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 0, 0, 2], ![2, 2, 0, -4]]

def raw9769step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9770 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9770step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9770step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw9770step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9771 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9771step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9772 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9772step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9772step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw9773 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9773step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9774 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9774step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9774step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1], ![2, 2, 0, -4]]

def raw9774step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw9775 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9775step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9775step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw9776 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9776step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw9777 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9777step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9777step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw9777step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9778 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9778step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9778step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9778step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9779 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9779step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9779step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, -2, 0, 2], ![2, 1, 0, -3]]

def raw9779step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9780 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9780step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9780step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw9781 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9781step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9781step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![2, 1, 0, -3]]

def raw9781step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9782 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9782step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9782step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9783 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9783step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw9784 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, -1, -1, 1]]

def raw9784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1], ![-1, -1, 1, 1]]

def raw9784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw9785 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9785step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9786 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -2, -2, 3]]

def raw9786step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw9786step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw9787 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9787step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw9788 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9788step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9788step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9789 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9789step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9789step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9790 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def raw9790step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw9791 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def raw9791step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical306
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9792 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, -1, 2], ![2, -2, -2, 2]]

def raw9792step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw9793 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -3, 3]]

def raw9793step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw9794 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 1, -2, 3]]

def raw9794step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw9795 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -3, 4]]

def raw9795step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw9796 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, -2, 1, 0]]

def raw9796step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw9797 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, -2, 1, 1]]

def raw9797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![-2, 1, 1]]

def raw9797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw9798 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9798step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9799 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9799step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw9800 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9800step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw9801 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9801step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9802 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9802step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw9803 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, -1, -1, 2]]

def raw9803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2]]

def raw9803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw9804 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9804step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9805 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, -1, 4], ![2, -1, 1, -2]]

def raw9805step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw9806 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 0, -1]]

def raw9806step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw9807 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def raw9807step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw9808 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def raw9808step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw9809 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def raw9809step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw9810 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -2, 4], ![2, -2, 1, -1]]

def raw9810step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw9811 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 0, 0]]

def raw9811step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9812 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9812step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9813 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9813step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9814 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9814step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9815 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, -1, 4]]

def raw9815step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9816 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9816step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9817 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, -1, 5]]

def raw9817step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw9818 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def raw9818step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw9819 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw9819step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw9820 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9820step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9821 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3]]

def raw9821step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw9822 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, 0, 3]]

def raw9822step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9823 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9823step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical307
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9824 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9824step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, -2, -2, 3]]

def raw9825step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw9826 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def raw9826step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9827 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def raw9827step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9828 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def raw9828step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9829 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def raw9829step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9830 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, -1, 1]]

def raw9830step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw9831 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -2, 2]]

def raw9831step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -2, 4]]

def raw9832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def raw9832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw9833 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 0, -1, 3]]

def raw9833step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw9834 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw9834step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9835 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1], ![-2, -1, 0, 3]]

def raw9835step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw9836 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, -1, 4]]

def raw9836step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw9837 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0], ![-2, -2, 0, 4]]

def raw9837step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw9838 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, -1, 5]]

def raw9838step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw9839 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def raw9839step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9840 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw9840step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw9841 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, -1, 2]]

def raw9841step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9842 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -2, 3]]

def raw9842step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9843 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1], ![-2, -1, -1, 4]]

def raw9843step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9844 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -2, 5]]

def raw9844step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9845 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def raw9845step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9846 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![-2, -2, 0, 4]]

def raw9846step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9847 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, -1, 5]]

def raw9847step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9848 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -2, -2, 4]]

def raw9848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![-2, -2, 4]]

def raw9848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw9849 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9849step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9849step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw9850 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9850step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9851 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9851step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw9851step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw9852 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9852step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9853 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9853step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9854 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def raw9854step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![1, -2, -1, 2]]

def raw9854step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw9855 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def raw9855step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9856 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -2, 4], ![-1, 2, 1, -2]]

def raw9856step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 2, -4], ![1, -2, -1, 2]]

def raw9856step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw9857 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 0, -1]]

def raw9857step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![1, -2, 0, 1]]

def raw9857step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9858 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw9858step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw9858step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9859 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def raw9859step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9860 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def raw9860step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9861 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, -1, 0], ![-1, -1, -1, 3]]

def raw9861step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw9861step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw9862 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw9862step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9863 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -2, 0], ![-2, -1, 0, 3]]

def raw9863step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9864 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, -1, 4]]

def raw9864step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9865 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -2, 5]]

def raw9865step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9866 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9866step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9867 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9867step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9868 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9868step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9869 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9869step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9870 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9870step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9871 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9871step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9872 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9872step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw9873 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9873step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9873step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw9874 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9874step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9875 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw9875step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw9876 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, -1, 4], ![1, 0, 2, -3]]

def raw9876step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw9877 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 1, -2]]

def raw9877step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw9878 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9878step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9879 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9879step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1]]

def raw9879step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9880 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9880step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9881 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def raw9881step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw9882 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def raw9882step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9883 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def raw9883step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9884 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -2, 4], ![1, -1, 2, -2]]

def raw9884step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw9885 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 1, -1]]

def raw9885step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw9886 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1]]

def raw9886step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw9887 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2]]

def raw9887step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9888 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9888step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9889 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3]]

def raw9889step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 1, 0, -3]]

def raw9889step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9890 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9890step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9891 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9891step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, 2, 1, -2]]

def raw9891step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9892 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2]]

def raw9892step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9893 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9893step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9894 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9894step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9895 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9895step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9896 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9896step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9897 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9897step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9898 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def raw9898step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw9899 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 1, 2, -3]]

def raw9899step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw9900 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2]]

def raw9900step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw9901 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def raw9901step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9902 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, 1, 2, -3]]

def raw9902step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9903 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2]]

def raw9903step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9904 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def raw9904step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9905 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -2, 4], ![-1, 1, 2, -2]]

def raw9905step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw9906 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 1, -1]]

def raw9906step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9907 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9907step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw9908 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9908step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9909 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9909step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw9910 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9910step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw9910step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9911 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -2, -2, 3]]

def raw9911step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![-1, -1, -1, 3]]

def raw9911step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw9912 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9912step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9913 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9913step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw9914 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9914step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, 2, 1, -2]]

def raw9914step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9915 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9915step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9916 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9916step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw9917 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -2, -1, 3]]

def raw9917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3]]

def raw9917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw9918 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def raw9918step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw9919 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def raw9919step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![-1, 2, 0, -1], ![5, -2, -1, -2]]

def raw992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def raw994step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw995 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 2, -4]]

def raw997step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![-1, -1, 0, 2], ![5, 0, -1, -4]]

def raw997step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![1, 1, 0, -2], ![-5, 0, 1, 4]]

def raw997step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 4, -5]]

def raw998 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw999step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9920 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 1, 2]]

def raw9920step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw9921 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3]]

def raw9921step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3]]

def raw9921step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw9922 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, -1, 4]]

def raw9922step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9923 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -2, 5]]

def raw9923step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw9924 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def raw9924step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw9925 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def raw9925step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9926 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def raw9926step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9927 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, -2, -1, 2]]

def raw9927step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9928 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -2, 3]]

def raw9928step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw9929 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -2, 1, 3]]

def raw9929step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9930 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 0, 4]]

def raw9930step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![2, 2, 0, -4]]

def raw9930step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw9931 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, -1, 5]]

def raw9931step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw9932 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9932step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9933 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9933step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw9934 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw9934step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9935 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def raw9935step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9936 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw9936step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw9937 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw9937step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9938 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 1, 0], ![-2, 1, -2, 3]]

def raw9938step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw9939 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -3, 4]]

def raw9939step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9940 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9940step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9941 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9941step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw9942 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def raw9942step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw9943 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def raw9943step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw9943step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9944 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![-1, -2, 0, 3]]

def raw9944step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw9944step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw9945 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, -1, 4]]

def raw9945step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw9946 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, -1, 2]]

def raw9946step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9947 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -2, 3]]

def raw9947step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw9948 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -3, 2, 0], ![-1, 3, -3, 1]]

def raw9948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![-1, 0, 1]]

def raw9948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![-1, -2, 3], ![1, 0, -1]]

def raw9948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw9949 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -2, 2, -1], ![-1, 2, -3, 2]]

def raw9949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![-1, -1, 2]]

def raw9949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-1, -2, 3], ![1, 1, -2]]

def raw9949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw9950 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, -3, 1, 0], ![-2, 3, -2, 1]]

def raw9950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![-1, 0, 1]]

def raw9950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-1, -1, 2], ![1, 0, -1]]

def raw9950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw9951 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, -2, 1, -1], ![-2, 2, -2, 2]]

def raw9951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![-1, -1, 2]]

def raw9951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9952 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 2, -1, 3], ![4, -2, -1, -1]]

def raw9952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![2, -1, -1], ![-2, 3, -1]]

def raw9952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw9953 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 2, 0, 2], ![4, -2, -2, 0]]

def raw9953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![2, 0, -2], ![-2, 2, 0]]

def raw9953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw9954 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 3, -1, 2], ![4, -3, -1, 0]]

def raw9954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![2, -1, -1], ![-2, 2, 0]]

def raw9954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw9955 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-4, 3, 0, 1], ![4, -3, -2, 1]]

def raw9955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![0, 3, -3], ![2, 0, -2], ![-2, 1, 1]]

def raw9955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -3, 3], ![-2, 0, 2], ![2, -1, -1]]

def raw9955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw9956 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 2, -1, 2], ![3, -2, -1, 0]]

def raw9956step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![2, -1, -1], ![-2, 2, 0]]

def raw9956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9957 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 2, 0, 1], ![3, -2, -2, 1]]

def raw9957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 2, -2], ![2, 0, -2], ![-2, 1, 1]]

def raw9957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![-2, 0, 2], ![2, -1, -1]]

def raw9957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9958 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 3, -1, 1], ![3, -3, -1, 1]]

def raw9958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![2, -1, -1], ![-2, 1, 1]]

def raw9958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw9959 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 3, 0, 0], ![3, -3, -2, 2]]

def raw9959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![2, 0, -2], ![-2, 0, 2]]

def raw9959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw9960 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-3, 4, -2, 1], ![3, -4, 0, 1]]

def raw9960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 4, -4], ![2, -2, 0], ![-2, 1, 1]]

def raw9960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -4, 4], ![-2, 2, 0], ![2, -1, -1]]

def raw9960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw9961 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, -1, 5], ![2, 2, -1, -3]]

def raw9961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![-2, 5, -3]]

def raw9961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw9962 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 0, 4], ![2, 2, -2, -2]]

def raw9962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 4, -2]]

def raw9962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw9963 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 1, 3], ![2, 2, -3, -1]]

def raw9963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 1, -3], ![-2, 3, -1]]

def raw9963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]

def raw9964 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 2, 2], ![2, 2, -4, 0]]

def raw9964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 2, -4], ![-2, 2, 0]]

def raw9964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-2, -2, 4], ![2, -2, 0]]

def raw9964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw9965 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, -2, 3, 1], ![2, 2, -5, 1]]

def raw9965step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 3, -5], ![-2, 1, 1]]

def raw9965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-2, -3, 5], ![2, -1, -1]]

def raw9965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def raw9966 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 2, -1, 1], ![2, -2, -1, 1]]

def raw9966step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![-2, 1, 1]]

def raw9966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw9967 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 2, 1, -1], ![2, -2, -3, 3]]

def raw9967step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![2, 1, -3], ![-2, -1, 3]]

def raw9967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw9968 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, -2, 1], ![2, -3, 0, 1]]

def raw9968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, -2, 0], ![-2, 1, 1]]

def raw9968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![-2, 2, 0], ![2, -1, -1]]

def raw9968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9969 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, -1, 0], ![2, -3, -1, 2]]

def raw9969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, -1, -1], ![-2, 0, 2]]

def raw9969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9970 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 3, 0, -1], ![2, -3, -2, 3]]

def raw9970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![2, 0, -2], ![-2, -1, 3]]

def raw9970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw9971 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 4, -3, 1], ![2, -4, 1, 1]]

def raw9971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![2, -3, 1], ![-2, 1, 1]]

def raw9971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -4, 4], ![-2, 3, -1], ![2, -1, -1]]

def raw9971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw9972 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-2, 4, -2, 0], ![2, -4, 0, 2]]

def raw9972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 4, -4], ![2, -2, 0], ![-2, 0, 2]]

def raw9972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def raw9973 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, -1, 4], ![1, 2, -1, -2]]

def raw9973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![-2, 4, -2]]

def raw9973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw9974 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 0, 3], ![1, 2, -2, -1]]

def raw9974step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![-2, 3, -1]]

def raw9974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw9975 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 1, 2], ![1, 2, -3, 0]]

def raw9975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 1, -3], ![-2, 2, 0]]

def raw9975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -1, 3], ![2, -2, 0]]

def raw9975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw9976 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 2, 1], ![1, 2, -4, 1]]

def raw9976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 2, -4], ![-2, 1, 1]]

def raw9976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -2, 4], ![2, -1, -1]]

def raw9976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw9977 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, -2, 3, 0], ![1, 2, -5, 2]]

def raw9977step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![2, 3, -5], ![-2, 0, 2]]

def raw9977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 2, -2], ![-2, -3, 5], ![2, 0, -2]]

def raw9977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw9978 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 2, 0, -1], ![1, -2, -2, 3]]

def raw9978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![2, 0, -2], ![-2, -1, 3]]

def raw9978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw9979 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -2, -3, 4]]

def raw9979step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![2, 1, -3], ![-2, -2, 4]]

def raw9979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw9980 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, -2, 0], ![1, -3, 0, 2]]

def raw9980step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, -2, 0], ![-2, 0, 2]]

def raw9980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw9981 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, -1, -1], ![1, -3, -1, 3]]

def raw9981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, -1, -1], ![-2, -1, 3]]

def raw9981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw9982 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 3, 0, -2], ![1, -3, -2, 4]]

def raw9982step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![2, 0, -2], ![-2, -2, 4]]

def raw9982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw9983 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![-1, 4, -3, 0], ![1, -4, 1, 2]]

def raw9983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 4, -4], ![2, -3, 1], ![-2, 0, 2]]

def raw9983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -4, 4], ![-2, 3, -1], ![2, 0, -2]]

def raw9983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9984 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -2, -2, 4]]

def raw9984step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, -2, 4]]

def raw9984step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw9985 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -3, 1, 1], ![-1, 3, -3, 1]]

def raw9985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -3, 3], ![2, 1, -3], ![-2, 1, 1]]

def raw9985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 3, -3], ![-2, -1, 3], ![2, -1, -1]]

def raw9985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw9986 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -2, 0, 1], ![-1, 2, -2, 1]]

def raw9986step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![-2, 1, 1]]

def raw9986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, 0, 2], ![2, -1, -1]]

def raw9986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw9987 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![1, -2, 1, 0], ![-1, 2, -3, 2]]

def raw9987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, -2, 2], ![2, 1, -3], ![-2, 0, 2]]

def raw9987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 2, -2], ![-2, -1, 3], ![2, 0, -2]]

def raw9987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw9988 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -3, 0, 1], ![-2, 3, -2, 1]]

def raw9988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![2, 0, -2], ![-2, 1, 1]]

def raw9988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-2, 0, 2], ![2, -1, -1]]

def raw9988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw9989 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -3, 1, 0], ![-2, 3, -3, 2]]

def raw9989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -3, 3], ![2, 1, -3], ![-2, 0, 2]]

def raw9989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![-2, -1, 3], ![2, 0, -2]]

def raw9989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw9990 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -2, 0, 0], ![-2, 2, -2, 2]]

def raw9990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![2, 0, -2], ![-2, 0, 2]]

def raw9990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw9991 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![2, -2, 1, -1], ![-2, 2, -3, 3]]

def raw9991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![2, 1, -3], ![-2, -1, 3]]

def raw9991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw9992 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![3, -3, 0, 0], ![-3, 3, -2, 2]]

def raw9992step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -3, 3], ![2, 0, -2], ![-2, 0, 2]]

def raw9992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw9993 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 2, -2], ![3, -2, 0, -1], ![-3, 2, -2, 3]]

def raw9993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -2, 2], ![2, 0, -2], ![-2, -1, 3]]

def raw9993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw9994 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![-1, 1, 1, -1], ![1, -2, 2, -1]]

def raw9994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-3, 1, 2], ![2, -1, -1]]

def raw9994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![3, -1, -2], ![-2, 1, 1]]

def raw9994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw9995 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 1, 1, -2], ![0, -2, 2, 0]]

def raw9995step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, -1, -1, 2], ![0, 2, -2, 0]]

def raw9995step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]

def raw9995step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw9996 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw9996step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9997 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw9997step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw9998 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw9998step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw9999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw9999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

def coordinateChunk1 : Array (Fin 909) := #[65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 125, 126, 127, 128, 129, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 177]

def coordinateChunk2 : Array (Fin 909) := #[190, 191, 196, 197, 199, 201, 203, 204, 205, 207, 208, 209, 216, 217, 226, 228, 230, 231, 236, 237, 238, 239, 253, 256, 257, 259, 260, 262, 266, 267, 268, 271, 273, 275, 276, 277, 278, 279, 280, 281, 282, 284, 286, 287, 288, 289, 290, 291, 293, 299, 300, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318]

def coordinateChunk3 : Array (Fin 909) := #[319, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 352, 378, 379, 383, 392, 398, 399, 400, 425, 426, 428, 453, 460, 472, 489, 490, 492, 493, 494, 495, 498, 499, 500, 501, 502, 503, 505, 506, 507, 508, 517, 538, 539, 540, 541, 543, 545, 546, 640, 643, 702, 709, 721, 723, 726, 727, 728, 735, 736, 737, 738, 739, 745]

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraPermutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraPermutation0 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation1 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation2 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation3 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation4 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation5 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation11 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation12 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation13 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation14 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation15 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation16 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation17 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation18 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation19 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation20 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation21 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation22 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation23 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation24 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation25 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation26 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation27 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation28 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation29 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation30 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation31 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation32 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation33 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation34 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation35 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 4, 3]
  invFun := ![1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation36 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation37 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation38 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 0, 2]
  invFun := ![3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation39 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation40 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation41 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 1, 3]
  invFun := ![2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation42 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation43 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation44 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 1, 0]
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation45 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation46 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 0, 2]
  invFun := ![3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation47 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 2, 0]
  invFun := ![4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation48 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation49 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation50 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 1, 3]
  invFun := ![2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
end


