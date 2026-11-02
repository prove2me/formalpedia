-- Prove2me | Definitions.Def_OAIQ106D001
-- name    : OAIQ106D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:54:59.556191+00:00
-- url     : https://prove2.me/theorems/0c212481-0ae7-4a61-9b93-0c8c44c28f36
-- title:
--   Definitions bundle OAIQ106D001 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1477 declarations of OpenAI's Lean: 1476 definitions and 1 inductive type or structure. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block1.weights`, `OAI.MUB6.Certificate.GramAssembly.Block2.weights`, `OAI.MUB6.Certificate.GramAssembly.Block3.weights`, `OAI.MUB6.Certificate.GramAssembly.Block4.weights`, `OAI.MUB6.Certificate.GramAssembly.Block5.weights`, `OAI.MUB6.Certificate.GramAssembly.key`, `OAI.MUB6.Certificate.GramAssembly.keyBlock0`, `OAI.MUB6.Certificate.GramAssembly.keyBlock1`, `OAI.MUB6.Certificate.GramAssembly.keyBlock10`, `OAI.MUB6.Certificate.GramAssembly.keyBlock11`, `OAI.MUB6.Certificate.GramAssembly.keyBlock12`, `OAI.MUB6.Certificate.GramAssembly.keyBlock13`, `OAI.MUB6.Certificate.GramAssembly.keyBlock14`, `OAI.MUB6.Certificate.GramAssembly.keyBlock15`, `OAI.MUB6.Certificate.GramAssembly.keyBlock16`, `OAI.MUB6.Certificate.GramAssembly.keyBlock17`, `OAI.MUB6.Certificate.GramAssembly.keyBlock18`, `OAI.MUB6.Certificate.GramAssembly.keyBlock19`, `OAI.MUB6.Certificate.GramAssembly.keyBlock2`, `OAI.MUB6.Certificate.GramAssembly.keyBlock20`, `OAI.MUB6.Certificate.GramAssembly.keyBlock21`, `OAI.MUB6.Certificate.GramAssembly.keyBlock22`, `OAI.MUB6.Certificate.GramAssembly.keyBlock23`, `OAI.MUB6.Certificate.GramAssembly.keyBlock24`, `OAI.MUB6.Certificate.GramAssembly.keyBlock25`, `OAI.MUB6.Certificate.GramAssembly.keyBlock26`, `OAI.MUB6.Certificate.GramAssembly.keyBlock27`, `OAI.MUB6.Certificate.GramAssembly.keyBlock28`, `OAI.MUB6.Certificate.GramAssembly.keyBlock29`, `OAI.MUB6.Certificate.GramAssembly.keyBlock3`, `OAI.MUB6.Certificate.GramAssembly.keyBlock30`, `OAI.MUB6.Certificate.GramAssembly.keyBlock31`, `OAI.MUB6.Certificate.GramAssembly.keyBlock32`, `OAI.MUB6.Certificate.GramAssembly.keyBlock33`, `OAI.MUB6.Certificate.GramAssembly.keyBlock34`, `OAI.MUB6.Certificate.GramAssembly.keyBlock35`, `OAI.MUB6.Certificate.GramAssembly.keyBlock36`, `OAI.MUB6.Certificate.GramAssembly.keyBlock37`, `OAI.MUB6.Certificate.GramAssembly.keyBlock38`, `OAI.MUB6.Certificate.GramAssembly.keyBlock39` and 1437 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramAssembly_Block1Data`, `MutuallyUnbiased_GramAssembly_Block2Data`, `MutuallyUnbiased_GramAssembly_Block3Data`, `MutuallyUnbiased_GramAssembly_Block4Data`, `MutuallyUnbiased_GramAssembly_Block5Data`, `MutuallyUnbiased_GramAssembly_Coordinates`, `MutuallyUnbiased_GramData_Block0`, `MutuallyUnbiased_GramData_Block1`, `MutuallyUnbiased_GramData_Block2`, `MutuallyUnbiased_GramData_Block3Data`, `MutuallyUnbiased_GramData_Block4Data`, `MutuallyUnbiased_GramData_Block5`, `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block16`, `MutuallyUnbiased_GramKeys_Block17`, `MutuallyUnbiased_GramKeys_Block18`, `MutuallyUnbiased_GramKeys_Block19`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block20`, `MutuallyUnbiased_GramKeys_Block21`, `MutuallyUnbiased_GramKeys_Block22`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block24`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block6`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_Moments_GramNormalization`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D073`, `OAIQ106D076`, `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D082`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092`, `OAIQ106D093`, `OAIQ106D094`, `OAIQ106D095`, `OAIQ106D096`, `OAIQ106D097`, `OAIQ106D098`, `OAIQ106D099`, `OAIQ106D100`, `OAIQ106D101`, `OAIQ106D102`, `OAIQ106D103`, `OAIQ106D104`, `OAIQ106D105`, `OAIQ106D106`, `OAIQ106D107`, `OAIQ106D108` and `OAIQ106D140`; the statements `OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_0_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_10_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_11_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_12_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_13_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_14_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_1_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_20_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_21_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_2_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_3_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_26`, `OAI.MUB6.Certificate.GramData.Block3.entry_5_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_6_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_0`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_1`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_10`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_11`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_12`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_13`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_14`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_15`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_16`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_17`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_18`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_19`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_2`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_20`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_3`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_4`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_5`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_6`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_7`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_8`, `OAI.MUB6.Certificate.GramData.Block3.entry_8_9`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_21`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_22`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_23`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_24`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_25`, `OAI.MUB6.Certificate.GramData.Block3.entry_9_26`, `OAI.MUB6.Certificate.GramData.Block3.gram` and `OAI.MUB6.Certificate.GramData.Block4.positiveDefinite`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

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

structure Key where
  leftTag : Fin 2
  rightTag : Fin 2
  rows : List (ℤ × ℤ)
  deriving DecidableEq, Repr

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly

open GramNormalization

def keyBlock0 : Array Key := #[
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, -3), (0, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -3), (0, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, -2), (0, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, -1), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
]

def keyBlock1 : Array Key := #[
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, -1), (0, 0), (0, 2), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
]

def keyBlock2 : Array Key := #[
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 0), (0, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-3, 1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 2), (0, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, 2), (0, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-3, 2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-3, 2), (0, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-3, 2), (0, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
]

def keyBlock3 : Array Key := #[
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, -3), (0, 0), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -3), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -2), (0, -1), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
]

def keyBlock4 : Array Key := #[
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 3), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -2), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -2), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, -1), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
]

def keyBlock5 : Array Key := #[
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 0), (1, -2), (1, 3)]⟩,
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 1), (0, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 3), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 1)]⟩
]

def keyBlock6 : Array Key := #[
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -3), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
]

def keyBlock7 : Array Key := #[
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 3), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -2), (0, 1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 3), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 0), (1, -2), (1, 3)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 1), (0, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 3), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, -1), (0, 1), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 0), (0, 3), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 0), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (0, 2), (2, -3)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (1, -3), (1, 2)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -1), (1, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -2), (1, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1)]⟩,
  ⟨0, 0, [(-2, 0), (0, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
]

def keyBlock8 : Array Key := #[
  ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -3), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, -1), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 2), (1, -1), (1, -1)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 0), (0, 2), (2, -3)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 0), (1, -3), (1, 2)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -1), (1, -1)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 2), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-2, 1), (0, 0), (0, 1), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
]

def keyBlock9 : Array Key := #[
  ⟨0, 0, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 2), (0, -3), (0, 0), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -3), (0, 0), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -3), (0, 0), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -1), (0, -1), (0, -1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, -1), (0, -1), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 0), (0, 1), (2, -2)]⟩,
  ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 0), (0, 1), (2, -3)]⟩,
  ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 0), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -2), (1, -1)]⟩,
  ⟨0, 0, [(-2, 3), (0, -3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-2, 3), (0, -2), (0, -1), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-2, 3), (0, -2), (0, 0), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-2, 3), (0, -1), (0, -1), (0, -1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-2, 3), (0, -1), (0, -1), (0, 0), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-2, 3), (0, -1), (0, 0), (0, 0), (1, -1), (1, -1)]⟩,
  ⟨0, 0, [(-2, 3), (0, 0), (0, 0), (0, 0), (0, 0), (2, -3)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 2), (0, 0), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -3), (-1, 3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -2), (-1, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 2)]⟩
]

def keyBlock10 : Array Key := #[
  ⟨0, 0, [(-1, -2), (-1, 0), (0, -1), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 3), (0, -1), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, -2), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, -1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (0, -1), (3, 3)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 3)]⟩
]

def keyBlock11 : Array Key := #[
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 0), (0, 1), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -1), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, -1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 3), (0, -2), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, -1), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 1), (2, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 2), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (1, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 3), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (1, -1), (1, 3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 0), (0, 2), (2, -1)]⟩
]

def keyBlock12 : Array Key := #[
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, 0), (0, 1), (0, 1), (2, -2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (2, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 2), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, -1), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, 2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -3), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, 1), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, -1), (1, -1), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -3)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 0), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 3), (0, -3), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 3), (0, -2), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 3), (0, -2), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-1, 0), (-1, 3), (0, -1), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -1), (0, -1), (1, 0), (1, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
]

def keyBlock13 : Array Key := #[
  ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -3)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (1, -3), (1, 1)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (1, -1), (1, -1)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 0, [(-1, 1), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -3)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -3), (0, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -2), (0, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
]

def keyBlock14 : Array Key := #[
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-3, -1), (0, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, -1), (0, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
]

def keyBlock15 : Array Key := #[
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
]

def keyBlock16 : Array Key := #[
  ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 0), (0, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩
]

def keyBlock17 : Array Key := #[
  ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-3, 2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -3), (0, 0), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -3), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
]

def keyBlock18 : Array Key := #[
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (-1, 2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 0), (1, 3)]⟩
]

def keyBlock19 : Array Key := #[
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, -1), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 3), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 1), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -2), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
]

def keyBlock20 : Array Key := #[
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (-1, 2), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -2), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 2), (1, 0), (1, 1)]⟩
]

def keyBlock21 : Array Key := #[
  ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, -1), (0, 1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 0), (0, 3), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 0), (1, -2), (1, 3)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 1), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 3), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 3), (1, -1), (1, -1)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 1), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-2, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, -1), (0, 1), (0, 1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
]

def keyBlock22 : Array Key := #[
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
]

def keyBlock23 : Array Key := #[
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (0, -1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (0, -1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -3), (0, 1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
]

def keyBlock24 : Array Key := #[
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 3), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 3), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 1), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 1), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -2), (0, 1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 0), (2, 3)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 3), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 0), (0, 3), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 0), (1, -2), (1, 3)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 1), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 3), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 3), (1, -1), (1, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 2), (1, -1), (1, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 0), (0, 3), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 1), (0, 2), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 1), (1, -3), (1, 2)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-2, 0), (0, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-2, 0), (0, 1), (0, 1), (0, 1), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
]

def keyBlock25 : Array Key := #[
  ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 2), (1, 0), (1, 0)]⟩
]

def keyBlock26 : Array Key := #[
  ⟨0, 1, [(-2, 1), (0, -3), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -2), (0, 1), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, -1), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, -1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 2), (1, -1), (1, -1)]⟩,
  ⟨0, 1, [(-2, 1), (0, -1), (0, 1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 0), (0, 2), (2, -3)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 0), (1, -3), (1, 2)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 1), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 2), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 2), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 1), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-2, 1), (0, 0), (0, 1), (0, 1), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 2), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
]

def keyBlock27 : Array Key := #[
  ⟨0, 1, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, -1), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, -1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 0), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 1), (1, -1), (1, -1)]⟩,
  ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 0), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 0), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-2, 3), (0, -3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -2), (0, -1), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -2), (0, 0), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-2, 3), (0, -2), (0, 0), (0, 0), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, -1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, 0), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, 0), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, 0), (0, 0), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-2, 3), (0, -1), (0, 0), (0, 0), (1, -1), (1, -1)]⟩,
  ⟨0, 1, [(-2, 3), (0, 0), (0, 0), (0, 0), (0, 0), (2, -3)]⟩,
  ⟨0, 1, [(-2, 3), (0, 0), (0, 0), (0, 0), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
]

def keyBlock28 : Array Key := #[
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 2), (0, 0), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -3), (-1, 3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 2), (0, 0), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, -1), (0, 1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 2), (0, -1), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (0, 1), (2, 1)]⟩
]

def keyBlock29 : Array Key := #[
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 0), (0, 1), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (-1, 1), (0, -1), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (-1, 1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 1), (0, 1), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 3), (0, -1), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, -2), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 1), (0, -1), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (-1, 1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 0), (3, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (0, -1), (3, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -2)]⟩
]

def keyBlock30 : Array Key := #[
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, -1), (3, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -2), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 0), (0, 1), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 2), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, -1), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, -1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 1), (0, 1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, -1), (0, -1), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, -1), (0, -1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 2), (0, 0), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 3), (0, -2), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 3), (0, -1), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 3), (0, -1), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-1, -1), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (0, 1), (3, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (0, 2), (3, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (0, -1), (3, 3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, -1)]⟩
]

def keyBlock31 : Array Key := #[
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (0, 0), (3, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (0, 1), (3, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -2), (0, -1), (3, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 2), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (0, 1), (2, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (0, 2), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (0, 3), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (1, 0), (1, 3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 2), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 3), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, -1), (1, -1), (1, 3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 1), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 2), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (0, 0), (3, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (1, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (2, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 1), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 2), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (1, 1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 1), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 1), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 2), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, -1), (0, -1), (2, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, -1), (0, 2), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, -1), (1, -1), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 2), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, 2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 1), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 1), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 2), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -3)]⟩
]

def keyBlock32 : Array Key := #[
  ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 2), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 1), (0, 1), (0, 1), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -3), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, -1), (2, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 3), (0, -3), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 3), (0, -2), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 3), (0, -2), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 3), (0, -1), (0, -1), (0, -1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 3), (0, -1), (0, -1), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-1, 0), (-1, 3), (0, -1), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, -1), (0, 1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, -1), (1, 0), (1, 1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, 0), (0, 1), (2, -1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, 0), (1, -1), (1, 1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, 1), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -1), (0, 0), (0, 1), (2, -2)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -1), (0, 0), (1, -2), (1, 1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, -1), (0, 1), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -3)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 0), (1, -3), (1, 1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 1), (1, -2), (1, -1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, -1), (1, 0), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, -1), (0, -1), (2, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, -1), (0, 0), (2, -1)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, 0), (0, 0), (2, -2)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 0)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -3)]⟩,
  ⟨0, 1, [(-1, 1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, -1)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
]

def keyBlock33 : Array Key := #[
  ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -3), (0, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -3), (0, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -2), (0, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
]

def keyBlock34 : Array Key := #[
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, -1), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, 0), (0, 2), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-3, -1), (0, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
]

def keyBlock35 : Array Key := #[
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, -1), (0, 2), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, -3), (2, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 0), (0, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
]

def keyBlock36 : Array Key := #[
  ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 2), (0, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 2), (0, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -1), (0, -1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-3, 2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, -1), (0, 0), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-3, 2), (0, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-3, 2), (0, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -3), (-1, 2), (0, 0), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
]

def keyBlock37 : Array Key := #[
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -2), (-1, 2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
]

def keyBlock38 : Array Key := #[
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, -1), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 0), (0, 2), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
]

def keyBlock39 : Array Key := #[
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, -2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, -1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, -1), (-1, 2), (0, 0), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
]

def keyBlock40 : Array Key := #[
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, -1), (0, 2), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (1, 0), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (1, 0), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (1, 1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (1, -1), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
]

def keyBlock41 : Array Key := #[
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -3), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, 0), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 0), (-1, 2), (0, 0), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
]

def keyBlock42 : Array Key := #[
  ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (1, 0), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (1, 0), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (1, -1), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -3), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, 0), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 1), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩
]

def keyBlock43 : Array Key := #[
  ⟨1, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, -1), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, -1), (0, 0), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -3), (1, 0), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (1, -1), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩,
  ⟨1, 1, [(-2, 2), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩
]

def keyBlock44 : Array Key := #[
  ⟨1, 1, [(-1, -2), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 1), (-1, 1), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -2), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 1), (0, -1), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 1), (0, 0), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -1), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, 0)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (0, -1), (3, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 0), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (1, -1), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, -2), (2, 2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 1), (-1, 1), (0, -2), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, -1), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (0, 0), (3, 3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 0), (2, 3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 1), (2, 2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 2), (2, 1)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (0, -1), (3, 3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (1, -1), (2, 3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, -1)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -1), (1, -2), (2, 3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 0), (1, -3), (2, 3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 0), (2, 2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 1), (2, 1)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 2), (2, 0)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, -1)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, -2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, -3), (2, 2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, -1)]⟩
]

def keyBlock45 : Array Key := #[
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -3)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (1, 1), (2, 0)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -2), (1, 1), (2, -1)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -1), (1, 1), (2, -2)]⟩,
  ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -3)]⟩
]

def keyBlocks : Array (Array Key) := #[keyBlock0, keyBlock1, keyBlock2, keyBlock3, keyBlock4, keyBlock5, keyBlock6, keyBlock7, keyBlock8, keyBlock9, keyBlock10, keyBlock11, keyBlock12, keyBlock13, keyBlock14, keyBlock15, keyBlock16, keyBlock17, keyBlock18, keyBlock19, keyBlock20, keyBlock21, keyBlock22, keyBlock23, keyBlock24, keyBlock25, keyBlock26, keyBlock27, keyBlock28, keyBlock29, keyBlock30, keyBlock31, keyBlock32, keyBlock33, keyBlock34, keyBlock35, keyBlock36, keyBlock37, keyBlock38, keyBlock39, keyBlock40, keyBlock41, keyBlock42, keyBlock43, keyBlock44, keyBlock45]

def key (i : Fin 2886) : Key :=
  ((keyBlocks.getD (i.val / 64) #[]).getD (i.val % 64) ⟨0, 0, []⟩)

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (1, 1, 3), m = 21, exponent = 13.
-/

namespace MUB6.Certificate.GramData.Block1

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 21) (Fin 21) ℚ := ![
  ![8281974, 317457, -4538959, 591578, -3564906, -1637779, 2692899, -164059, 144765, -6253927, -1632149, -1203380, 208493, 1265023, -3980129, 4968645, -5318840, -2763722, 2313302, 1101122, -8259767],
  ![317457, 670055, -459927, -52372, 303397, -104535, -981918, -162011, -485696, -1175469, 154981, 419927, 3385699, -52654, -72835, -1358640, -1304244, -320066, -1529579, -252593, -1803981],
  ![-4538959, -459927, 7528052, 113157, 3208427, 1798169, -1474042, -1709009, 445414, -425014, 581829, 158367, -2343572, -1105957, 1559599, -2556995, 940149, 2067282, -1719750, -678125, 2527166],
  ![591578, -52372, 113157, 274017, -181761, 94961, 300328, -195608, 174240, -1057177, -69659, -55345, -724852, 26271, -167456, 610565, -578406, 64222, 300878, 153302, -720802],
  ![-3564906, 303397, 3208427, -181761, 3093541, 792287, -2353153, -496914, -366545, 263008, 835313, 637100, 3794703, -673257, 1902740, -4006041, -316085, 1025294, -4308765, -921008, 1327786],
  ![-1637779, -104535, 1798169, 94961, 792287, 4872019, -2061591, 173690, -125916, -3017686, 991536, 1695692, 1212441, -2053220, 2143288, -3714554, -137926, 5235805, 250358, -1888253, 3409136],
  ![2692899, -981918, -1474042, 300328, -2353153, -2061591, 3943670, -132639, 1112745, 1793037, -1169740, -1576236, -8279149, 1211833, -2161046, 6223125, 1708504, -2418137, 5095570, 1712829, -299969],
  ![-164059, -162011, -1709009, -195608, -496914, 173690, -132639, 1557465, -199316, 1053902, -85533, -178234, 1114705, -133074, 339938, -371680, 979706, 808468, 201825, -403513, 1677944],
  ![144765, -485696, 445414, 174240, -366545, -125916, 1112745, -199316, 574590, 419757, -184323, -374293, -3151845, 175194, -218282, 1575701, 691622, -213776, 1306896, 427205, 660976],
  ![-6253927, -1175469, -425014, -1057177, 263008, -3017686, 1793037, 1053902, 419757, 16546248, 681453, -488773, -9664796, 1241050, 2081231, 2667867, 11353138, -1846105, 4400021, 1567125, 10741408],
  ![-1632149, 154981, 581829, -69659, 835313, 991536, -1169740, -85533, -184323, 681453, 1080797, 996503, 1912285, -343789, 1767463, -2335848, 174111, 1098524, -1981023, -498704, 1464376],
  ![-1203380, 419927, 158367, -55345, 637100, 1695692, -1576236, -178234, -374293, -488773, 996503, 1840985, 3483873, -606873, 1777812, -3265860, -757413, 1395572, -2418328, -838818, 905478],
  ![208493, 3385699, -2343572, -724852, 3794703, 1212441, -8279149, 1114705, -3151845, -9664796, 1912285, 3483873, 33924189, -474182, 3152718, -16306805, -13773212, -390763, -23030655, -3874823, -9593464],
  ![1265023, -52654, -1105957, 26271, -673257, -2053220, 1211833, -133074, 175194, 1241050, -343789, -606873, -474182, 1191495, -785273, 1774465, -563678, -2506791, -760335, 897209, -1728565],
  ![-3980129, -72835, 1559599, -167456, 1902740, 2143288, -2161046, 339938, -218282, 2081231, 1767463, 1777812, 3152718, -785273, 4167901, -4625257, 1019431, 2549610, -4161086, -1143525, 4379858],
  ![4968645, -1358640, -2556995, 610565, -4006041, -3714554, 6223125, -371680, 1575701, 2667867, -2335848, -3265860, -16306805, 1774465, -4625257, 12672461, 3981236, -3562699, 12375243, 3263582, -1351879],
  ![-5318840, -1304244, 940149, -578406, -316085, -137926, 1708504, 979706, 691622, 11353138, 174111, -757413, -13773212, -563678, 1019431, 3981236, 12230833, 1826615, 10606059, 842121, 10905753],
  ![-2763722, -320066, 2067282, 64222, 1025294, 5235805, -2418137, 808468, -213776, -1846105, 1098524, 1395572, -390763, -2506791, 2549610, -3562699, 1826615, 6914992, 1990541, -2100658, 5534083],
  ![2313302, -1529579, -1719750, 300878, -4308765, 250358, 5095570, 201825, 1306896, 4400021, -1981023, -2418328, -23030655, -760335, -4161086, 12375243, 10606059, 1990541, 22638314, 2123881, 5457071],
  ![1101122, -252593, -678125, 153302, -921008, -1888253, 1712829, -403513, 427205, 1567125, -498704, -838818, -3874823, 897209, -1143525, 3263582, 842121, -2100658, 2123881, 1293251, -963816],
  ![-8259767, -1803981, 2527166, -720802, 1327786, 3409136, -299969, 1677944, 660976, 10741408, 1464376, 905478, -9593464, -1728565, 4379858, -1351879, 10905753, 5534083, 5457071, -963816, 15446253]
]

def entries : Matrix (Fin 21) (Fin 21) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-9203208993782996869087665786488300222716345548164113562824081952810745206437146077643843264222965069155279994802431 / 21382635319649418476782483793524736028643088123814558960635838949965674596189964146649888317276782583403426089371020), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-141003724600356129531687875172758610418527887995710123912844943589935709257205095312073748827144356408192500478 / 517348911307745860195885683588210317099110627874293252653917319745221355836651312983829898751731737655171246897), (-46149117760782678522089604803950767165719380628300161662041314960617064712756843798879031563116056529805537707 / 517348911307745860195885683588210317099110627874293252653917319745221355836651312983829898751731737655171246897), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-567187384006743284913779031230980738530880259138774997677263866125686568940531407216936322999546860419712 / 1457100541808693579706706937703300365542596691556066726458670109059805192627619894105572128802526253660971), (405176010258025078639061720534934445564612218827437580349379459841965073682624948623822421760813556554575 / 1457100541808693579706706937703300365542596691556066726458670109059805192627619894105572128802526253660971), (-461008157896238928672597051205801502764362770222865796258647351730282466506176423489794770700811418274180 / 1457100541808693579706706937703300365542596691556066726458670109059805192627619894105572128802526253660971), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-364360165690699232311861731846438918325783040649929491456915061947099266880060009708183848829338436 / 1820988069863750958997115813279373630798139864971050769144736473152934834816775792406424298571834131), (109312638100828391480927903029032831379168203260666243861949858265415984868461944705114280740201759 / 1820988069863750958997115813279373630798139864971050769144736473152934834816775792406424298571834131), (345562730896505139514269973712974602390675388213643225262456561914117877571185760516167200604203766 / 1820988069863750958997115813279373630798139864971050769144736473152934834816775792406424298571834131), (282473051609634573048996520545755442106313270274308790921875945445377061147911235619341753097958046 / 1820988069863750958997115813279373630798139864971050769144736473152934834816775792406424298571834131), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(573461683530272058986663108248052548468602334971944288240250245583328382214510409028967288323 / 1017822719868897060740498276664813752997665830751412576001943802934840762154518047721328165343), (48229196581324957023003291842659099320282405791449694152742665129702884700128793790959682665 / 1017822719868897060740498276664813752997665830751412576001943802934840762154518047721328165343), (-733273502819662382403322763040782809159438196747525860691423563795552856337154025140998285 / 6401400753892434344279863375250400962249470633656682867936753477577614856317723570574390977), (-23649758452449571497248660571381762677082587933891891794448052719480650079910673476054992464 / 339274239956299020246832758888271250999221943583804192000647934311613587384839349240442721781), (-621902720486357813431967632127911356783680664568481957810599948378568480880349283612362761083 / 1017822719868897060740498276664813752997665830751412576001943802934840762154518047721328165343), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(152473336103864538967217934685520052278357302133384785360929363937448769217855007910309653 / 153642790468549951336570070517215212123055709648878912650270975725793674297346497775057055), (-29676501180237353235681986249203092389630643999082231526725173486557802567551277895808299 / 307285580937099902673140141034430424246111419297757825300541951451587348594692995550114110), (-127412952097595284845028544284106470706435892646140685859010475835522890459270687788967473 / 153642790468549951336570070517215212123055709648878912650270975725793674297346497775057055), (-12371721486776048378365091560178835105324371527021535900460828813070256764572414124932791 / 307285580937099902673140141034430424246111419297757825300541951451587348594692995550114110), (-17791643457094613456933234762060939102198789417258152063703461911186283741357212725714419 / 21948970066935707333795724359602173160436529949839844664324425103684810613906642539293865), (-1475384312760302536349387917496426651584958107187744988977247596309054406212922756535 / 4389794013387141466759144871920434632087305989967968932864885020736962122781328507858773), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(448072374131710162876420846015295722068236566754450916527600764563654973142729042117 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (-169766780820926999279911989356767901214837685718586321062856448816316143194367091598 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (-846223107870322697510019758284089953115369242145402402823775663448894468906570140814 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (115815757454211897656334091725203961859429652265102418055922342476889762410024634341 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (-698354053725476456115813779524351869808277202612976281929307011053809664638904688038 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (-241675612193935446369090011076495679176696962557334805541599349548204616017470958800 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (373315194492319722255371151680919028065837262246654927860793271957936886010780750591 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(2275451935208445324310156641379822349339603598988560456067281852562721841798968 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (-1485639956263106539436803988414600290498786356921678674029988184621753375182810 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (-308275363629241355581215821556660203950829559262347477346913812219222505185628 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (593515795094187953644622667045887290802252855513548572880961369086779066356087 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (-1863072873344641246050437807562620519734416772910383950541847889675223936564020 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (1901655797342032674695038922281368884592545654285374566349822288273767018967963 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (4125979376089908165978795161486047084674784483494108135317878597128914696724782 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (-263873006275144790314567279569435942499631892882826565302878239360901009057719 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-10931664129692524211773676271881010273146603590938218192838685920872192373 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (4575884847508225451330405181888524860888496691350105679672886255057538901 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (3439402720963535569975389207873865581050977402189898114435644915729481475 / 6740547712473010364789394664344656691561244136338591691683961307786744731), (-6768951963418935595546685749019664218418102134983328312813489119188692610 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (23854913562199292724433774451555839140335238328488629844778079762006340883 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (-5224449400150910096016899000823252432871108448827047719038475520637470155 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (-15114229258457805286493085737642024349324013953489144699544259344421461937 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (-15512728235800302898684309112809143338845949407411734157601838064826593134 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (-11873478382288411049360019207196704924799022874926164856091230499188416747 / 47183833987311072553525762650412596840928708954370141841787729154507213117), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-2497387787379266238719578978822728180506490965483511155319833394666 / 16937925268881711750357100981152574584053560923254929737336700682057), (1779391653391128228675270268851826868442413696339627339312837747547 / 16937925268881711750357100981152574584053560923254929737336700682057), (819201467454414316253293324089778372155981558507273667557421080357 / 16937925268881711750357100981152574584053560923254929737336700682057), (-1047447613337858902553096829164075049733672171957953314172928237548 / 16937925268881711750357100981152574584053560923254929737336700682057), (4577073741039010418524129059956597472066360058969699703974220053178 / 16937925268881711750357100981152574584053560923254929737336700682057), (2055870814122100175527093802503419427392921893228862619485879717384 / 16937925268881711750357100981152574584053560923254929737336700682057), (-801997998403638548150542910906050466284209219458743898672573354037 / 16937925268881711750357100981152574584053560923254929737336700682057), (-7585547312904570422278801479897491860189930262389555641489380061628 / 16937925268881711750357100981152574584053560923254929737336700682057), (910401962487716312363737914099086555977021613562799183830046297566 / 16937925268881711750357100981152574584053560923254929737336700682057), (1374564324764891005546078991650654680933561805608886193923462198983 / 16937925268881711750357100981152574584053560923254929737336700682057), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(4485656113319704668807235195082969229408558667091233457903293 / 19085949157072465915971402684060152239988570168664944045319046), (13029342511663159291039601241604444275874135600974209977007645 / 76343796628289863663885610736240608959954280674659776181276184), (-43544392889551945176814263095348466361083443138670152148090969 / 76343796628289863663885610736240608959954280674659776181276184), (556868162222778248200508526365769609765199486294842066902828 / 9542974578536232957985701342030076119994285084332472022659523), (-4231112817497634932877097827577513780735513276886542821030034 / 9542974578536232957985701342030076119994285084332472022659523), (14337562789921228062536815470696327228191307561874503104777113 / 38171898314144931831942805368120304479977140337329888090638092), (8086627699685944977981782678792024277343768971722918644217889 / 76343796628289863663885610736240608959954280674659776181276184), (-2765373722002761294741541617314899079678276022761478591333782 / 9542974578536232957985701342030076119994285084332472022659523), (24563082093809779475422691472020196155134559783396659236653 / 9542974578536232957985701342030076119994285084332472022659523), (15392333614217373453571546179120077399196753781228777602368657 / 76343796628289863663885610736240608959954280674659776181276184), (13579351169291147278414063649314386035692669897945948547984209 / 76343796628289863663885610736240608959954280674659776181276184), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(121542279251838030136331726169886415960848227566541067721 / 495280339844214943426099438623407143348133760331072579556), (13371374588495183500685725375807293746013576763391527760 / 123820084961053735856524859655851785837033440082768144889), (-274336363638291056577740874268281018034558070658649468539 / 247640169922107471713049719311703571674066880165536289778), (-17774605172577681195332923261693788136877797508451501805 / 247640169922107471713049719311703571674066880165536289778), (-117105529816950949248906603608219791787425614099686535383 / 495280339844214943426099438623407143348133760331072579556), (-70264592617565244825977667047080686769646472311582758879 / 495280339844214943426099438623407143348133760331072579556), (-36798348973403588492232412743827821225246642739747440121 / 247640169922107471713049719311703571674066880165536289778), (107804439451073541921520360540878119741200880327221744537 / 247640169922107471713049719311703571674066880165536289778), (-83551675971166226344476642403814290459297278590850856689 / 495280339844214943426099438623407143348133760331072579556), (29898584769817111666468537812858287689865833980778071713 / 123820084961053735856524859655851785837033440082768144889), (-2803771830987438778215091653749619757344088048941670503 / 495280339844214943426099438623407143348133760331072579556), (1082545835112494009005626992088614799719058034549514265 / 123820084961053735856524859655851785837033440082768144889), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(263042164685208819977230364967974870227189397552185 / 170173405510616022519433571105966097343494500530421), (11406343252304737308622467834974507408019601792108 / 170173405510616022519433571105966097343494500530421), (-431422284477221856999271569740073806972867766022798 / 170173405510616022519433571105966097343494500530421), (-21001835139319344294405190733537929316079671889937 / 170173405510616022519433571105966097343494500530421), (-248122234115803131628930762852118893942925493050070 / 170173405510616022519433571105966097343494500530421), (-79912649357345535375238003832117046047901028087397 / 170173405510616022519433571105966097343494500530421), (37400747954359685058518766112871507272424390998494 / 170173405510616022519433571105966097343494500530421), (134885943684789132087761231433609053900605434104482 / 170173405510616022519433571105966097343494500530421), (-58762726967315819556090993047508992976943481107978 / 170173405510616022519433571105966097343494500530421), (315767072311892966172955786546179245748300176457281 / 170173405510616022519433571105966097343494500530421), (50576788343572096744645219681970025042785384502931 / 170173405510616022519433571105966097343494500530421), (24152817264498389100954835107601950985652396186032 / 170173405510616022519433571105966097343494500530421), (148071646976362749053127394984541807849506127208075 / 170173405510616022519433571105966097343494500530421), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(24504208413378184737276616067494784849965973 / 519475562008723717758247955240282825438961217), (38071356944344238403241013775584389808832269 / 519475562008723717758247955240282825438961217), (-173128186481598196793378224387960417027382779 / 519475562008723717758247955240282825438961217), (40810846534062924131616500154956643548819366 / 519475562008723717758247955240282825438961217), (1765442434568833464537105654612500958571744 / 519475562008723717758247955240282825438961217), (109816173759153616231835957218887286219593499 / 519475562008723717758247955240282825438961217), (-20933914307973216587988467976304576039521929 / 519475562008723717758247955240282825438961217), (-56362950532508770066281031964260570474197358 / 519475562008723717758247955240282825438961217), (-8894503504744979651712676143214904436896381 / 519475562008723717758247955240282825438961217), (35105210428638932419002304922032901312368611 / 519475562008723717758247955240282825438961217), (207818449129355402536495077629558006494213509 / 519475562008723717758247955240282825438961217), (245735329511569271749233791126674259801910571 / 519475562008723717758247955240282825438961217), (52644847652615940265561981338337929023083988 / 519475562008723717758247955240282825438961217), (18769026735055734450452382661319682078118809 / 519475562008723717758247955240282825438961217), 0, 0, 0, 0, 0, 0, 0],
  ![(156108053164750597316966643821023353241 / 352350426833979009721084999699067408390), (-43548695519008773284300224689677606596 / 176175213416989504860542499849533704195), (-17950239783926407808044161343376721859 / 176175213416989504860542499849533704195), (22426077231914920545154465393706251687 / 352350426833979009721084999699067408390), (-30324157883637972946045533462042007936 / 176175213416989504860542499849533704195), (-64059113186027341148721042110418471547 / 352350426833979009721084999699067408390), (95808956602562514077846102773133049471 / 176175213416989504860542499849533704195), (53980882414400514745173003808521201627 / 176175213416989504860542499849533704195), (2804431021445854012962272509901756409 / 16015928492453591350958409077230336745), (-36876894533089879197862105464451487743 / 352350426833979009721084999699067408390), (-91095953507094616737641915758429310967 / 352350426833979009721084999699067408390), (-83145642541597101904742467034721778309 / 176175213416989504860542499849533704195), (-233446499455359185285736328747331046639 / 352350426833979009721084999699067408390), (62897409397172007746726879876487847393 / 352350426833979009721084999699067408390), (-32912786919560339194716688855177183808 / 176175213416989504860542499849533704195), 0, 0, 0, 0, 0, 0],
  ![(-547226431705663476104987172586969 / 708676201887685590802476775269669), (190589781674281112102216844073583 / 708676201887685590802476775269669), (256398658160961808845947480313185 / 708676201887685590802476775269669), (-49490493380369431590149252509654 / 708676201887685590802476775269669), (263378622903558192884505352563073 / 708676201887685590802476775269669), (-266724170180229749048431943148905 / 708676201887685590802476775269669), (-363487222949892852566835999948170 / 708676201887685590802476775269669), (-2414016228442569083244809464138 / 708676201887685590802476775269669), (-148370328731597950407354969208691 / 708676201887685590802476775269669), (191669949800620704767339204798826 / 236225400629228530267492258423223), (34233969999180173929278621260387 / 236225400629228530267492258423223), (-26524042929623181312041269625222 / 708676201887685590802476775269669), (305509536277199287653707546052038 / 708676201887685590802476775269669), (-13669371771971090332585926413163 / 236225400629228530267492258423223), (109671212286891229715485799778745 / 708676201887685590802476775269669), (-85818642378379767900370211636932 / 236225400629228530267492258423223), 0, 0, 0, 0, 0],
  ![(17709006437486600077555514 / 246250676023066963197233087), (-23612316181265617641492212 / 246250676023066963197233087), (116355166965587825849331841 / 246250676023066963197233087), (60216975806386578970666474 / 246250676023066963197233087), (7962425238664974386368905 / 246250676023066963197233087), (164120759426969932880505694 / 246250676023066963197233087), (-46106665746803351521413054 / 246250676023066963197233087), (-39740545289760465124598394 / 246250676023066963197233087), (27879725093796019165333399 / 246250676023066963197233087), (-246801465684681197761124267 / 246250676023066963197233087), (55941859161601816514926881 / 246250676023066963197233087), (1750398425216179871461922 / 12960561895950892799854373), (-138214786202724789749179657 / 246250676023066963197233087), (-56542363633286442734704337 / 246250676023066963197233087), (95104980290941126150193241 / 246250676023066963197233087), (-1745770209615789716011900 / 246250676023066963197233087), (-112159859200181183273601773 / 246250676023066963197233087), 0, 0, 0, 0],
  ![(77346604587705260195 / 300660470993474738902), (-3094540684089000639 / 300660470993474738902), (-29951043437137062647 / 300660470993474738902), (3228867581325688871 / 150330235496737369451), (-59098741205114599885 / 300660470993474738902), (45607952898135458851 / 300660470993474738902), (17293082884477839661 / 150330235496737369451), (1963728976322544602 / 150330235496737369451), (2612764221485822975 / 300660470993474738902), (-36820319052382566287 / 150330235496737369451), (-32081207778786893857 / 300660470993474738902), (-11187727206712709910 / 150330235496737369451), (-101911667069761426915 / 150330235496737369451), (-32897333576144986901 / 300660470993474738902), (-10800417777691507229 / 42951495856210676986), (61894150654806250493 / 150330235496737369451), (70666862745155469963 / 300660470993474738902), (33746045016438726499 / 150330235496737369451), 0, 0, 0],
  ![(3015771134998 / 6348980285549), (-1880107045175 / 6348980285549), (-243599008793 / 577180025959), (557740325658 / 6348980285549), (-4315460397216 / 6348980285549), (-8626884581011 / 6348980285549), (8722558386011 / 6348980285549), (-1538511537495 / 6348980285549), (2411925252427 / 6348980285549), (11519650041851 / 6348980285549), (-2097239712432 / 6348980285549), (-4027960288302 / 6348980285549), (-23032610162281 / 6348980285549), (4064166201279 / 6348980285549), (-407327249809 / 577180025959), (16369050215994 / 6348980285549), (7839584418687 / 6348980285549), (-821619914962 / 577180025959), (12688538536943 / 6348980285549), 0, 0],
  ![(-8259767 / 15446253), (-601327 / 5148751), (2527166 / 15446253), (-720802 / 15446253), (1327786 / 15446253), (3409136 / 15446253), (-299969 / 15446253), (1677944 / 15446253), (660976 / 15446253), (10741408 / 15446253), (1464376 / 15446253), (301826 / 5148751), (-9593464 / 15446253), (-1728565 / 15446253), (4379858 / 15446253), (-1351879 / 15446253), (3635251 / 5148751), (5534083 / 15446253), (5457071 / 15446253), (-321272 / 5148751), 0]
]

def D : Fin 21 → ℚ := ![(5560751706652352768357597341549993262439216053766671451568471920826360244408618922373174197970350025602245343143739404907 / 21382635319649418476782483793524736028643088123814558960635838949965674596189964146649888317276782583403426089371020), (21382635319649418476782483793524736028643088123814558960635838949965674596189964146649888317276782583403426089371020 / 517348911307745860195885683588210317099110627874293252653917319745221355836651312983829898751731737655171246897), (1034697822615491720391771367176420634198221255748586505307834639490442711673302625967659797503463475310342493794 / 1457100541808693579706706937703300365542596691556066726458670109059805192627619894105572128802526253660971), (1457100541808693579706706937703300365542596691556066726458670109059805192627619894105572128802526253660971 / 25493832978092513425959621385911230831173958109594710768026310624141087687434861093689940180005677834), (1820988069863750958997115813279373630798139864971050769144736473152934834816775792406424298571834131 / 5089113599344485303702491383324068764988329153757062880009719014674203810772590238606640826715), (1017822719868897060740498276664813752997665830751412576001943802934840762154518047721328165343 / 4389794013387141466759144871920434632087305989967968932864885020736962122781328507858773), (307285580937099902673140141034430424246111419297757825300541951451587348594692995550114110 / 1186125211529247547201432909264050918833925204120462838858926684897853732357162380071), (1186125211529247547201432909264050918833925204120462838858926684897853732357162380071 / 4244692605376647162130298823317217187278873105856797795183239758402563366020417), (4244692605376647162130298823317217187278873105856797795183239758402563366020417 / 47183833987311072553525762650412596840928708954370141841787729154507213117), (47183833987311072553525762650412596840928708954370141841787729154507213117 / 67751701075526847001428403924610298336214243693019718949346802728228), (16937925268881711750357100981152574584053560923254929737336700682057 / 76343796628289863663885610736240608959954280674659776181276184), (76343796628289863663885610736240608959954280674659776181276184 / 123820084961053735856524859655851785837033440082768144889), (495280339844214943426099438623407143348133760331072579556 / 170173405510616022519433571105966097343494500530421), (170173405510616022519433571105966097343494500530421 / 1038951124017447435516495910480565650877922434), (519475562008723717758247955240282825438961217 / 528525640250968514581627499548601112585), (352350426833979009721084999699067408390 / 236225400629228530267492258423223), (708676201887685590802476775269669 / 492501352046133926394466174), (246250676023066963197233087 / 150330235496737369451), (300660470993474738902 / 19046940856647), (6348980285549 / 5148751), 15446253]

end MUB6.Certificate.GramData.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

def weights : Matrix (Fin 21) (Fin 21) ℤ := ![
  ![8281974, 317457, -4538959, 591578, -3564906, -1637779, 2692899, -164059, 144765, -6253927, -1632149, -1203380, 208493, 1265023, -3980129, 4968645, -5318840, -2763722, 2313302, 1101122, -8259767],
  ![317457, 670055, -459927, -52372, 303397, -104535, -981918, -162011, -485696, -1175469, 154981, 419927, 3385699, -52654, -72835, -1358640, -1304244, -320066, -1529579, -252593, -1803981],
  ![-4538959, -459927, 7528052, 113157, 3208427, 1798169, -1474042, -1709009, 445414, -425014, 581829, 158367, -2343572, -1105957, 1559599, -2556995, 940149, 2067282, -1719750, -678125, 2527166],
  ![591578, -52372, 113157, 274017, -181761, 94961, 300328, -195608, 174240, -1057177, -69659, -55345, -724852, 26271, -167456, 610565, -578406, 64222, 300878, 153302, -720802],
  ![-3564906, 303397, 3208427, -181761, 3093541, 792287, -2353153, -496914, -366545, 263008, 835313, 637100, 3794703, -673257, 1902740, -4006041, -316085, 1025294, -4308765, -921008, 1327786],
  ![-1637779, -104535, 1798169, 94961, 792287, 4872019, -2061591, 173690, -125916, -3017686, 991536, 1695692, 1212441, -2053220, 2143288, -3714554, -137926, 5235805, 250358, -1888253, 3409136],
  ![2692899, -981918, -1474042, 300328, -2353153, -2061591, 3943670, -132639, 1112745, 1793037, -1169740, -1576236, -8279149, 1211833, -2161046, 6223125, 1708504, -2418137, 5095570, 1712829, -299969],
  ![-164059, -162011, -1709009, -195608, -496914, 173690, -132639, 1557465, -199316, 1053902, -85533, -178234, 1114705, -133074, 339938, -371680, 979706, 808468, 201825, -403513, 1677944],
  ![144765, -485696, 445414, 174240, -366545, -125916, 1112745, -199316, 574590, 419757, -184323, -374293, -3151845, 175194, -218282, 1575701, 691622, -213776, 1306896, 427205, 660976],
  ![-6253927, -1175469, -425014, -1057177, 263008, -3017686, 1793037, 1053902, 419757, 16546248, 681453, -488773, -9664796, 1241050, 2081231, 2667867, 11353138, -1846105, 4400021, 1567125, 10741408],
  ![-1632149, 154981, 581829, -69659, 835313, 991536, -1169740, -85533, -184323, 681453, 1080797, 996503, 1912285, -343789, 1767463, -2335848, 174111, 1098524, -1981023, -498704, 1464376],
  ![-1203380, 419927, 158367, -55345, 637100, 1695692, -1576236, -178234, -374293, -488773, 996503, 1840985, 3483873, -606873, 1777812, -3265860, -757413, 1395572, -2418328, -838818, 905478],
  ![208493, 3385699, -2343572, -724852, 3794703, 1212441, -8279149, 1114705, -3151845, -9664796, 1912285, 3483873, 33924189, -474182, 3152718, -16306805, -13773212, -390763, -23030655, -3874823, -9593464],
  ![1265023, -52654, -1105957, 26271, -673257, -2053220, 1211833, -133074, 175194, 1241050, -343789, -606873, -474182, 1191495, -785273, 1774465, -563678, -2506791, -760335, 897209, -1728565],
  ![-3980129, -72835, 1559599, -167456, 1902740, 2143288, -2161046, 339938, -218282, 2081231, 1767463, 1777812, 3152718, -785273, 4167901, -4625257, 1019431, 2549610, -4161086, -1143525, 4379858],
  ![4968645, -1358640, -2556995, 610565, -4006041, -3714554, 6223125, -371680, 1575701, 2667867, -2335848, -3265860, -16306805, 1774465, -4625257, 12672461, 3981236, -3562699, 12375243, 3263582, -1351879],
  ![-5318840, -1304244, 940149, -578406, -316085, -137926, 1708504, 979706, 691622, 11353138, 174111, -757413, -13773212, -563678, 1019431, 3981236, 12230833, 1826615, 10606059, 842121, 10905753],
  ![-2763722, -320066, 2067282, 64222, 1025294, 5235805, -2418137, 808468, -213776, -1846105, 1098524, 1395572, -390763, -2506791, 2549610, -3562699, 1826615, 6914992, 1990541, -2100658, 5534083],
  ![2313302, -1529579, -1719750, 300878, -4308765, 250358, 5095570, 201825, 1306896, 4400021, -1981023, -2418328, -23030655, -760335, -4161086, 12375243, 10606059, 1990541, 22638314, 2123881, 5457071],
  ![1101122, -252593, -678125, 153302, -921008, -1888253, 1712829, -403513, 427205, 1567125, -498704, -838818, -3874823, 897209, -1143525, 3263582, 842121, -2100658, 2123881, 1293251, -963816],
  ![-8259767, -1803981, 2527166, -720802, 1327786, 3409136, -299969, 1677944, 660976, 10741408, 1464376, 905478, -9593464, -1728565, 4379858, -1351879, 10905753, 5534083, 5457071, -963816, 15446253]
]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (1, 2, 2), m = 11, exponent = 13.
-/

namespace MUB6.Certificate.GramData.Block2

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 11) (Fin 11) ℚ := ![
  ![4921588, 1243280, -7309127, -624690, 1603998, -2795071, 3367935, -1583320, 2340968, -248222, 702355],
  ![1243280, 1259868, -2872973, -210702, 1253342, -2034588, 1682712, -885538, 2724267, -409660, 794],
  ![-7309127, -2872973, 13379731, 1150717, -3887583, 6470784, -6302383, 2324542, -6055529, 725259, -836950],
  ![-624690, -210702, 1150717, 690108, 8436, 557254, -693384, -181298, 1653368, -526328, -588904],
  ![1603998, 1253342, -3887583, 8436, 1940509, -2484968, 1935441, -879724, 3975384, -709322, -233345],
  ![-2795071, -2034588, 6470784, 557254, -2484968, 4332981, -3363650, 1243475, -4427358, 537643, -211242],
  ![3367935, 1682712, -6302383, -693384, 1935441, -3363650, 3298003, -1116848, 2778884, -234978, 508720],
  ![-1583320, -885538, 2324542, -181298, -879724, 1243475, -1116848, 1720010, -3611042, 821982, 282809],
  ![2340968, 2724267, -6055529, 1653368, 3975384, -4427358, 2778884, -3611042, 15022074, -3403183, -2223239],
  ![-248222, -409660, 725259, -526328, -709322, 537643, -234978, 821982, -3403183, 873834, 642996],
  ![702355, 794, -836950, -588904, -233345, -211242, 508720, 282809, -2223239, 642996, 680229]
]

def entries : Matrix (Fin 11) (Fin 11) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-14827153955215089202732638206951917239133001841574472989 / 27507193756326595116897163357783180615127072140170648614), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-11393478122050259797789923181655993722042228591674 / 17479418652284552137434755866464075063379980195961), (5658031728703927773343020507526599668741930181320 / 17479418652284552137434755866464075063379980195961), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(189756908932443978670324120470906799618796531 / 189915925886052455618184221018667842370673476), (-21066435804720785928533956539802970850506971 / 47478981471513113904546055254666960592668369), (-6082608645798733789422806265046988388465867 / 18087231036766900535065163906539794511492712), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(6957201992055347941835705121579867822 / 3520003250857510716841109304189444968363), (177157843568628361209030820238058237489 / 3520003250857510716841109304189444968363), (-579960192052915214128865646888981082024 / 3520003250857510716841109304189444968363), (302228261280040133466533430515126081286 / 3520003250857510716841109304189444968363), 0, 0, 0, 0, 0, 0, 0],
  ![(4650820566461172754344495271033409 / 7653737263479163532482722018743552), (-2865428485893563144517681673963401 / 15307474526958327064965444037487104), (406219908150596939503835320206381 / 1913434315869790883120680504685888), (2007139815275909459453615706409973 / 7653737263479163532482722018743552), (-4981736393472402681607486085932019 / 15307474526958327064965444037487104), 0, 0, 0, 0, 0, 0],
  ![(29429149021131038751634709825 / 34425022755281971937245195013), (11809836990062242357994329922 / 34425022755281971937245195013), (-57726063333875233258409906259 / 34425022755281971937245195013), (-9949645983959050352458621412 / 34425022755281971937245195013), (18635080458244273734881588183 / 34425022755281971937245195013), (-15820869753746313878842815228 / 34425022755281971937245195013), 0, 0, 0, 0, 0],
  ![(5771252348976692509063 / 111830209413948198594007), (-11101839075590262135160 / 111830209413948198594007), (-116038567147699746951479 / 111830209413948198594007), (672989850357148607094 / 111830209413948198594007), (55289105352156247953139 / 111830209413948198594007), (-44299552785540597149338 / 111830209413948198594007), (36600909915959275872914 / 111830209413948198594007), 0, 0, 0, 0],
  ![(952401039090908 / 7606625109860333), (43360189344211154 / 83672876208463663), (-82737834488103571 / 83672876208463663), (-7415417341907512 / 83672876208463663), (4504310994446048 / 7606625109860333), (-91099031377911129 / 83672876208463663), (56646018017229742 / 83672876208463663), (1632534949772216 / 83672876208463663), 0, 0, 0],
  ![(-11489986267 / 3351173555), (-5169873166 / 3351173555), (2438528857 / 427809390), (1146630404 / 10053520665), (-6156694317 / 3351173555), (55727569031 / 20107041330), (-27052431949 / 10053520665), (20960607673 / 10053520665), (-98378887207 / 20107041330), 0, 0],
  ![(702355 / 680229), (794 / 680229), (-836950 / 680229), (-588904 / 680229), (-233345 / 680229), (-70414 / 226743), (508720 / 680229), (282809 / 680229), (-2223239 / 680229), (71444 / 75581), 0]
]

def D : Fin 11 → ℚ := ![(3213472828238838540323513005837750309890513122790494441732261 / 27507193756326595116897163357783180615127072140170648614), (27507193756326595116897163357783180615127072140170648614 / 367067791697975594886129873195745576330979584115181), (17479418652284552137434755866464075063379980195961 / 18087231036766900535065163906539794511492712), (379831851772104911236368442037335684741346952 / 3520003250857510716841109304189444968363), (3520003250857510716841109304189444968363 / 15307474526958327064965444037487104), (15307474526958327064965444037487104 / 34425022755281971937245195013), (34425022755281971937245195013 / 111830209413948198594007), (111830209413948198594007 / 251018628625390989), (83672876208463663 / 60321123990), (20107041330 / 75581), 680229]

end MUB6.Certificate.GramData.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

open scoped BigOperators

def weights : Matrix (Fin 11) (Fin 11) ℤ := ![
  ![4921588, 1243280, -7309127, -624690, 1603998, -2795071, 3367935, -1583320, 2340968, -248222, 702355],
  ![1243280, 1259868, -2872973, -210702, 1253342, -2034588, 1682712, -885538, 2724267, -409660, 794],
  ![-7309127, -2872973, 13379731, 1150717, -3887583, 6470784, -6302383, 2324542, -6055529, 725259, -836950],
  ![-624690, -210702, 1150717, 690108, 8436, 557254, -693384, -181298, 1653368, -526328, -588904],
  ![1603998, 1253342, -3887583, 8436, 1940509, -2484968, 1935441, -879724, 3975384, -709322, -233345],
  ![-2795071, -2034588, 6470784, 557254, -2484968, 4332981, -3363650, 1243475, -4427358, 537643, -211242],
  ![3367935, 1682712, -6302383, -693384, 1935441, -3363650, 3298003, -1116848, 2778884, -234978, 508720],
  ![-1583320, -885538, 2324542, -181298, -879724, 1243475, -1116848, 1720010, -3611042, 821982, 282809],
  ![2340968, 2724267, -6055529, 1653368, 3975384, -4427358, 2778884, -3611042, 15022074, -3403183, -2223239],
  ![-248222, -409660, 725259, -526328, -709322, 537643, -234978, 821982, -3403183, 873834, 642996],
  ![702355, 794, -836950, -588904, -233345, -211242, 508720, 282809, -2223239, 642996, 680229]
]

end MUB6.Certificate.GramAssembly.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (1, 4), m = 27, exponent = 14.
-/

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 27) (Fin 27) ℚ := ![
  ![21638825, 1103969, -366698, 4472903, 4675758, -348911, -1653142, -6679308, 8323724, 7441570, 4676581, 5623964, 8331635, -2350116, 1781770, 196990, -196597, 6566227, -8510275, 4751159, 70965, 14265487, 26849611, -9014352, 2605212, -9952367, -3848880],
  ![1103969, 944580, 262232, -1282119, 95477, 1215062, -564931, -35356, -831071, 337531, -143710, 302472, 204411, -65538, 56758, -848390, -1894747, 1697129, 37861, -2357894, -256571, -1198268, 1132197, -1361624, 449476, 312826, 206227],
  ![-366698, 262232, 4372564, 3731369, -407706, 2092458, -1007026, 873692, -2456751, -216243, -1563203, 1156547, 42736, 737006, 2315448, -2604186, 830681, 2358685, 4672623, -140249, 456406, -1590279, -234365, -483957, -124524, 5876220, -1320981],
  ![4472903, -1282119, 3731369, 19481819, -144329, -427246, -3175977, -1883385, -68139, -3526786, 3743961, 6685420, 1352597, 2280274, 2706754, -11269051, 4787889, -3225514, 3611637, 21924365, 2276614, 2837114, 17953246, -685263, 1227195, 2993143, -2602804],
  ![4675758, 95477, -407706, -144329, 6492797, -1491868, 817068, -4627001, 7215886, 5805250, -1305636, 2952474, 3939166, -1359246, 1532955, 5894401, -29611, 6202189, -2291217, -481138, 684539, 6508035, 2071984, 3406557, 1483542, -1112872, -1483981],
  ![-348911, 1215062, 2092458, -427246, -1491868, 6691737, -614723, 2447831, -2470731, -3927318, 469732, -959011, -1289212, 420869, 995398, -3671401, -3970214, 728173, 1583616, -2751073, -341589, -2391480, 1842073, -3406562, 619147, 869639, -393268],
  ![-1653142, -564931, -1007026, -3175977, 817068, -614723, 3480564, -1569264, 3004866, 1839889, -1954425, -3083192, -381717, -777936, 548165, 7957870, 1340972, 1639448, -1148157, -5852439, -380245, 3554996, -10414524, 2933849, -467475, -1973233, -1032694],
  ![-6679308, -35356, 873692, -1883385, -4627001, 2447831, -1569264, 7383368, -7671834, -6735967, 118611, -3301327, -3540810, 1566438, -1531264, -6992208, -99872, -5499711, 4157406, 380152, -257758, -8817786, -4896596, -1431032, -1723883, 4284472, 2854925],
  ![8323724, -831071, -2456751, -68139, 7215886, -2470731, 3004866, -7671834, 20205267, 10681732, 909816, 2492242, 4317945, -3579665, 2295640, 13833571, 730101, 6141615, -9345834, -1057876, -83947, 11010772, 7616015, 5283323, 2916394, -10448615, -3097019],
  ![7441570, 337531, -216243, -3526786, 5805250, -3927318, 1839889, -6735967, 10681732, 16547778, -2924799, 3946206, 5011875, -2276717, 1384567, 12642667, 479639, 12059339, -4897979, -9757133, -304344, 4755447, -1246459, 4687144, 2310344, -1413894, -2054950],
  ![4676581, -143710, -1563203, 3743961, -1305636, 469732, -1954425, 118611, 909816, -2924799, 7987018, 2298496, 670012, 1060859, -1536421, -6516193, -3482292, -6804900, -6889389, 9482366, -31994, 1772760, 18979737, -5584492, 2189272, -9602945, -1745575],
  ![5623964, 302472, 1156547, 6685420, 2952474, -959011, -3083192, -3301327, 2492242, 3946206, 2298496, 11293001, 3855450, 207606, 919586, -1479887, -1937263, 3041223, -1958480, 5974596, 1576779, 4701210, 16943621, -736999, 2493931, 458016, -1738479],
  ![8331635, 204411, 42736, 1352597, 3939166, -1289212, -381717, -3540810, 4317945, 5011875, 670012, 3855450, 5397378, -1102075, 962591, 2637949, 188406, 4768294, -3725397, 446791, 474966, 7981741, 9023959, -1518183, 1177088, -3205049, -1956856],
  ![-2350116, -65538, 737006, 2280274, -1359246, 420869, -777936, 1566438, -3579665, -2276717, 1060859, 207606, -1102075, 2217189, -487516, -4116005, -24349, -2063816, 1117744, 3592223, 593484, -3987844, -147587, 115748, 503866, 1956747, 242711],
  ![1781770, 56758, 2315448, 2706754, 1532955, 995398, 548165, -1531264, 2295640, 1384567, -1536421, 919586, 962591, -487516, 3205882, 2761862, 1941024, 3868069, 2452580, -1000408, 392906, 3595017, -827728, 802693, -106086, 2607707, -1763362],
  ![196990, -848390, -2604186, -11269051, 5894401, -3671401, 7957870, -6992208, 13833571, 12642667, -6516193, -1479887, 2637949, -4116005, 2761862, 32801715, 4724490, 10794029, -6316274, -25027763, -614355, 16030892, -22856504, 8622411, -639546, -4918260, -4211536],
  ![-196597, -1894747, 830681, 4787889, -29611, -3970214, 1340972, -99872, 730101, 479639, -3482292, -1937263, 188406, -24349, 1941024, 4724490, 12353120, 774544, 4523372, 3167390, 1143666, 3762949, -9242889, 3957804, -3010232, 6368365, 344604],
  ![6566227, 1697129, 2358685, -3225514, 6202189, 728173, 1639448, -5499711, 6141615, 12059339, -6804900, 3041223, 4768294, -2063816, 3868069, 10794029, 774544, 17833685, 2066116, -13574800, 196572, 4428060, -8076457, 3932306, 1121311, 6669123, -1006711],
  ![-8510275, 37861, 4672623, 3611637, -2291217, 1583616, -1148157, 4157406, -9345834, -4897979, -6889389, -1958480, -3725397, 1117744, 2452580, -6316274, 4523372, 2066116, 15960711, 902133, 788329, -8554511, -16299324, 3279438, -3450350, 17682257, 3152538],
  ![4751159, -2357894, -140249, 21924365, -481138, -2751073, -5852439, 380152, -1057876, -9757133, 9482366, 5974596, 446791, 3592223, -1000408, -25027763, 3167390, -13574800, 902133, 41963642, 2913559, -1690663, 32194445, -2228810, 1782706, -1930609, 618762],
  ![70965, -256571, 456406, 2276614, 684539, -341589, -380245, -257758, -83947, -304344, -31994, 1576779, 474966, 593484, 392906, -614355, 1143666, 196572, 788329, 2913559, 935757, 954088, 1261245, 918772, 233548, 1646149, -428236],
  ![14265487, -1198268, -1590279, 2837114, 6508035, -2391480, 3554996, -8817786, 11010772, 4755447, 1772760, 4701210, 7981741, -3987844, 3595017, 16030892, 3762949, 4428060, -8554511, -1690663, 954088, 32392892, 11308744, -3684421, -299084, -12045329, -8338454],
  ![26849611, 1132197, -234365, 17953246, 2071984, 1842073, -10414524, -4896596, 7616015, -1246459, 18979737, 16943621, 9023959, -147587, -827728, -22856504, -9242889, -8076457, -16299324, 32194445, 1261245, 11308744, 76533185, -18865439, 7037228, -20572372, -5290054],
  ![-9014352, -1361624, -483957, -685263, 3406557, -3406562, 2933849, -1431032, 5283323, 4687144, -5584492, -736999, -1518183, 115748, 802693, 8622411, 3957804, 3932306, 3279438, -2228810, 918772, -3684421, -18865439, 14224969, 472, 6264265, 1201176],
  ![2605212, 449476, -124524, 1227195, 1483542, 619147, -467475, -1723883, 2916394, 2310344, 2189272, 2493931, 1177088, 503866, -106086, -639546, -3010232, 1121311, -3450350, 1782706, 233548, -299084, 7037228, 472, 2520573, -3319037, -1287392],
  ![-9952367, 312826, 5876220, 2993143, -1112872, 869639, -1973233, 4284472, -10448615, -1413894, -9602945, 458016, -3205049, 1956747, 2607707, -4918260, 6368365, 6669123, 17682257, -1930609, 1646149, -12045329, -20572372, 6264265, -3319037, 24934572, 4540900],
  ![-3848880, 206227, -1320981, -2602804, -1483981, -393268, -1032694, 2854925, -3097019, -2054950, -1745575, -1738479, -1956856, 242711, -1763362, -4211536, 344604, -1006711, 3152538, 618762, -428236, -8338454, -5290054, 1201176, -1287392, 4540900, 5497571]
]

def entries : Matrix (Fin 27) (Fin 27) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(12738296020772436347236218044151925931606567979986843175884737679668961208426686634194913825455149645755661746383368432304521824814966178081139737866832444854413119 / 13237772903188533738097767927467660066708853716647424271536033470019920597583588851098617682007757610687242401106197725136700576753531434189387503671847639853473675), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-1071933408483581197357177447611970781774563026489814263038096121362808653083100244652846810651992495041996938828756412281242820504921596916637469856889521637 / 387370202298328952841734074741226159998708757595685237855957437098716608003406950622039400549558673764862670663466066327834240530485731994767105499801050305573), (-76233176408977812302493405243513375257672536355762688858783649342161703701207867366790014035264328193590608541539488955405999034011969654482406703098826118308 / 387370202298328952841734074741226159998708757595685237855957437098716608003406950622039400549558673764862670663466066327834240530485731994767105499801050305573), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(6070327571533309116779183325537529350654433807055201213690879714724573654145101362547318863125929499896531392310343978757758172521019569869691708328911 / 330084211868767720878081295179951138219239079243577623389488432133070250587068306553070903610669259556876897160510627745473771182881500876745943686735178), (-859087479434591210034597085359293050363612933245633663972241167836484657160428017909951056566522413195543727713249597873539219975559624649820677055441 / 165042105934383860439040647589975569109619539621788811694744216066535125293534153276535451805334629778438448580255313872736885591440750438372971843367589), (64794518583328319782695055315635798702711950718322859503256881269718340612069906841579198402462284536860103272942772878216663876198109509742945935632301 / 330084211868767720878081295179951138219239079243577623389488432133070250587068306553070903610669259556876897160510627745473771182881500876745943686735178), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(51380746858520958282049057906589452775748975233944633199426606793151558953848408632232958799736100406067556291821360103225282945153434048100894289 / 280070256488662344563643167884306726719429041722243580851231973223636144890503132822491336810949975404681836605020868849081036017534656603067797823), (15983969364564907664300983550968116527361252609501220276863021917949136289739312719714402937222270793736286287382550542201423531762623353615763809 / 280070256488662344563643167884306726719429041722243580851231973223636144890503132822491336810949975404681836605020868849081036017534656603067797823), (-2782815401295647748908257481054668167522839327999181729085062809359847117783731794322666139818991827086001905762712563835978518356390091471478399 / 31118917387629149395960351987145191857714337969138175650136885913737349432278125869165704090105552822742426289446763205453448446392739622563088647), (-184101526565495970176921997884580793601997068848273336005937730777767181006164250357284848809774502780165121734162299432081489706963645493615577336 / 280070256488662344563643167884306726719429041722243580851231973223636144890503132822491336810949975404681836605020868849081036017534656603067797823), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(17505045441419582933481913893810983269594578922569624903956862063086062972823320947467227436929574906857016943000645329442621933610349411591 / 171158369917236823816452691371521513275517428429529524251217537078491593252152156283916465080458005125433106101716710768791008634418021405597), (-4626868601953776821096178976311334836352682426027667034421774040099552734893586597325196972288092392641893670129261194793612159026724078607 / 171158369917236823816452691371521513275517428429529524251217537078491593252152156283916465080458005125433106101716710768791008634418021405597), (12811053842018969630101621625572206533439193776755286191156582381758991862519288156626747243718699065746484692655917336683379406277909703643 / 171158369917236823816452691371521513275517428429529524251217537078491593252152156283916465080458005125433106101716710768791008634418021405597), (64214354589436436972388150513268408379300621927545605998796529657852331345521636824366532757013921725908093277099982894611242122010071379076 / 171158369917236823816452691371521513275517428429529524251217537078491593252152156283916465080458005125433106101716710768791008634418021405597), (-9805107580922187028797147224107132008845874594188620759825344431876746012317669300384364660116610898882697999486855218620147362846954067942 / 171158369917236823816452691371521513275517428429529524251217537078491593252152156283916465080458005125433106101716710768791008634418021405597), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-98876760387344829045431422108769223462254492930615861681287703251913993656299369194605839370580030576541773545992244657215431441294083 / 324937418655710586987216894341596286741290989843153121155933927604727951800082030373337598613161493339435416229557312178859181366011426), (-451376377325835139577404067917076474458614555638709211264538965925538211796553714072651866148358778507792569956642624952985482188729187 / 974812255967131760961650683024788860223872969529459363467801782814183855400246091120012795839484480018306248688671936536577544098034278), (353448230798741344229213823777451655210594335702845251869846544358207522917039427427156695760295476676880098033172632574232124127947077 / 974812255967131760961650683024788860223872969529459363467801782814183855400246091120012795839484480018306248688671936536577544098034278), (171974103989506509973090473482436481406796187472577267581161406362400928580071207241342297638343261976177188802199095834250262386667270 / 487406127983565880480825341512394430111936484764729681733900891407091927700123045560006397919742240009153124344335968268288772049017139), (-180144222575088230024421497234668263653497181517791535085529104962166085152326631215054467256355257153141779646894236322552202651275595 / 324937418655710586987216894341596286741290989843153121155933927604727951800082030373337598613161493339435416229557312178859181366011426), (108198459804726138612736162251671031130135847680800525631101130775415198834067012001121491410630941753702326830068213967712803635676868 / 162468709327855293493608447170798143370645494921576560577966963802363975900041015186668799306580746669717708114778656089429590683005713), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(73856294057517524353023922614991198358598791464117757349365817208606669064499210566326597330479386774100955655207932198185991271 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (-188430556116206099744589809767118009737237057454744641564512030248263112398884166116021468233189122294244310769701415535131070768 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (458501065781127497026215704014188500687606911160468677489661700006380358764012646158299695319462441195207517814612424054249621829 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (-806222516901310903959297203586439678503362430447222033724707667049872151677880545914287810202235702454997723215677807825701897961 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (-672556926472863628836901919684479828490883762687461948264885928509581333142795758231672103146366681143410823447739017817410066486 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (1890801907468793724109415647107610975112596411894327818616479251078350717972762380139830517981783503221069143471820594902601458977 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (-215805902348575046332042810402250687777639194485499175209771523204787938653712434812882651857604787844406500340095680421119520368 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-247319995899377692506353488122832091518701744461518749929969407495338831715624269043965434604070261865331091274336651433904 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (-9243514897574468890028874369742924183461182171388198037203097710511651546522301888273005614166210925566869249499513176252 / 109743485487350624374917058244372321642389153431817106677096656194439285425717220517537395702698702997181769193228032306245), (292680401408573633126798634516025456631967525943256823276624458811547856324240889984764703646929751579812257645504381447099 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (353543575978071272986961033793134848003964341382672872446933738498474420641663430206129783216835746960217262611472911686189 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (107855476988019737667269322170159369265961789166568202460103259726235577395581029564098427467676241176155344341569890510289 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (388089738385981562759376398805179371473446679796434572419718165201202398935897582989630437050673535200272107357433360617447 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (-27210189365809454816951854060143213942080471405176737089472399164391999109879578182144312589829723700298670154298331657288 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (355157737998174538293503545267548671178492789444095381779761164527458385563793734372401234797937448245605269156164743919987 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(58246143158624419337660083256597173840636851797748895615709183028116820335670271237279452066535298271585498653064447 / 285032396151687426143202541499727122529598895194525678882431231301811836098393338294403332898400862724818852186776807), (-21695580761268794140158281108733150100332086475090520449980885944468790506044219280227869568259420459071305125806595 / 285032396151687426143202541499727122529598895194525678882431231301811836098393338294403332898400862724818852186776807), (18473991165157421354834569797599600746686001584481434294534634025802540056305645636440607520681892212840867362304139 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), (-218583135616703369536586996654139360582590745573847738242800939168927997802584406010965828543827901545338444223012171 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), (-97398144629559954647731655910655887019292012274197596664044302476880156260828021036787341536999179877282830364342411 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), (-528633131637803300738297973477226037077551700471304598269766831012919082855696536810346903628513678486776291827200005 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), (11748805500818391176916847225064010024820119377779044203451497898455025394097465157786159292472956619484275333603660 / 285032396151687426143202541499727122529598895194525678882431231301811836098393338294403332898400862724818852186776807), (-136763739327385650246498785532321369665356748406426366629365986323218408782517761097616376407535064668519474898012157 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), (284026448321122718641922481395288288751557665714929820645052093038559634324340070604419148466193136195581312085528775 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(14380051121713024889160106584493736187565988628344364587039167268514621004772386926761800504340772497314253033 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (-38396607772412736134403092592819238349129263384144474813639076370617456818872415646274045999894997199145134775 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (-136910401971523724068555019062590137621753311422454840929783397325169339651299386187958812538477080113021602905 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (-155466683680568367394688277982790006834148087892688146517983042373347963402695008052808402046983864966090859142 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (16936923838182951719509694763316459706579565209431862072914754043128294474488411710162985416488620130202639556 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (-61244009501086035037930916521373135928144089583721191446251731572692976445567797547654485107095037210599477052 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (-48113005300754873692190948443548591086401308271292504703853460292809001645810554989311010849713315776176551206 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (193508206439603734211007332072378517444805873840331489475476548863360260075662438947145896831299601192350022922 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (8904266540531920294702589394842825798004235261135049873302334937695576071172301186811526811777667526623912858 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (44011381145348666484161627410139158468242073715312853123125321455750441588818883456775704270386463112838835407 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-77076919527770469230148574116694803811312247011423397719971325694728968317245462169620676969650110368930 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-22644993046536493751250913232509963157877715847819072233080491901842591062268118665946506057002704233100 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-15510517441759338250159873315969717317909591748287120785278133132904274815580203586405569863022895217181 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (353910631307126614408011042822333945048911934079299386840778632540789862752723237558669290593454882271532 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-215615165711686262101690555334515590663496815040247489173039246485983929101075406346981241586127455420743 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-190116634321534763419256826353344171217430393369652028768844676815953493875430099886620963048355546228650 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-26277936354203546721044507139049389199221588946398563260913368174350870396413472694271820033066465600897 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-71621188774839074247546110727735443780045441786064532955946974609461107159486854041802635167099294202094 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (-182953477459448052110496901205551311671610696399331802802476061807962194790634272136441951450646771651209 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (132050869053008730742974060984506067332648221101477514175638668054393376521093615627358261087325522803460 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (34939263220631867191028021638455640601351201883461604101722599563236581583691637319739071093368746728751 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(18603421133680823295929879366424788087938672172066417677225731557818715314592180296358438612813499 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (-6683070260867483243062770472250117575726717814710973859503212252434671799876918481743609226398256 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (17192245367892896921493417167555367682491224627746955533564574402972403339521675920195144765743493 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (-6403474962480157944430635925385624904882702499332102394568517976171240923853809003068751442655744 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (39215626707324683353998122954145629833978091741006300246293177512418698617200369501489265745273479 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (-37313406691006768384746074580083224963717247162593963620972717566364861135167422476802766995647934 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (-10972811139119271778979416799400155103295017597367320083776652952912468861288099188098275189967269 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (5357526150416644502863959215681034309594295656867791963541456626144613174355012534975558184520654 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (-1413793826302135130331123069036652414713032908265192041335300461236659782066937733428987136936271 / 9361680754795174323660749216499588066417513996899119676437127135391732949674045650163257328619523), (35049132268204653723437323022129990427306697278450247970270012496272106478611501249398472065865292 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (-9654421073921894972090780846289496119935391314223781569224078379532439557749071126620414816406294 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), (19459268382325907870276669468636082950651889522711494164762198552999986621351618011486329785735401 / 65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-6990006226811787176953591531950415351740322383857322031051527898858368554930370185849630587 / 17919474447541109040318460569320490429144301668661592751645001409967287842949514713142588667), (379126568419588149635478383169204937023027887790048289568055359015178947046377967635418036 / 17919474447541109040318460569320490429144301668661592751645001409967287842949514713142588667), (6538785456279755188998513653753209170682246668120287200659597844633863643120084178207026199 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (58711887656853690205989501919877001196621234388736856095279379150732144878887651992126515382 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (-43233642256449742656237218034184064193562612691235498016372263723012767978130318744678902438 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (-3909606793999714939655461077954282543278597093191905431822484305904082372905151972074545698 / 17919474447541109040318460569320490429144301668661592751645001409967287842949514713142588667), (-11666546001165572613938216230798553190860341498310336098569194550841610477518655415495644987 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (15989189738729494538687963458050633462985128464166014566733670933431642494493797018860512731 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (-130763123087256363424560487185443432977002725151455678716110661843443974263132268358956342419 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (-5261680930584408723405124919517398586716581496865898759439651835479596634170495409351282780 / 17919474447541109040318460569320490429144301668661592751645001409967287842949514713142588667), (45618390575207462436164937208042609329459438744569878753248812080901153896613521890373841776 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (51747145770938798756001916195203363812358994195504387703455064017899222138451736237643763642 / 89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335), (1510333732655729091068302097027989491916357990602212344628981222129602306851586111845873672 / 17919474447541109040318460569320490429144301668661592751645001409967287842949514713142588667), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-8755339021432622845264635328530936913904828366959705168996047188553728493882744379305 / 26784327725709865474303511468155266163410724721866675022586161564412692703671828451832), (255922577740312460751155365089879236886461491060440110285362622425110673102611695101 / 6696081931427466368575877867038816540852681180466668755646540391103173175917957112958), (14390105272260972630583767351574504141515035431295618788567778492110092468997494199729 / 26784327725709865474303511468155266163410724721866675022586161564412692703671828451832), (3748263208347077256490467297334515296553996782145149012293174600968690297807331524457 / 13392163862854932737151755734077633081705362360933337511293080782206346351835914225916), (479328790336490173553222917078339870875521000892342428374510597156062012800318253047 / 13392163862854932737151755734077633081705362360933337511293080782206346351835914225916), (12456359818070675458437499288837059104255272433659881430297544866934412642669070527173 / 13392163862854932737151755734077633081705362360933337511293080782206346351835914225916), (4905379160459532060099078023781750490106337176388533937649978591860259131065647499147 / 26784327725709865474303511468155266163410724721866675022586161564412692703671828451832), (8415177758579489549276031252012261352152191529810148341848065660590964442188537713349 / 26784327725709865474303511468155266163410724721866675022586161564412692703671828451832), (18388583398611780574823734781328974891852286654269949539964257487110613840064216595819 / 26784327725709865474303511468155266163410724721866675022586161564412692703671828451832), (-5864099768217308672257348229587411393178967585410403676414144610322208912545695639183 / 6696081931427466368575877867038816540852681180466668755646540391103173175917957112958), (650570051277793212725862972918042118038436201460594063290375722041951282028353767834 / 3348040965713733184287938933519408270426340590233334377823270195551586587958978556479), (-6069329363397014372973228033548668378415632059084783079158131091335337288018795506553 / 13392163862854932737151755734077633081705362360933337511293080782206346351835914225916), (-664866408952808836994303535435106400148822970629878671372634069940513022680951738083 / 3348040965713733184287938933519408270426340590233334377823270195551586587958978556479), (3311271717374271534652892786291996707714867617379028892068125878354216436373265003713 / 26784327725709865474303511468155266163410724721866675022586161564412692703671828451832), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-1183390278971122651057312476612786021973715769583872589276479479612192782918050 / 19219771037964104886810676434038272361695654535647438263894086495277899490257867), (-3259695753635063394718796238453619679488227528018716715438201263685230243525399 / 48788649557908881635750178640250999071996661513566574054500373411090052552193047), (-63204807298650171727192967149566477693709400862742499778473277491515091649299404 / 634252444252815461264752322323262987935956599676365462708504854344170683178509611), (-6640957635569550564643605425287249150479987154957882584647900990331174388608559 / 90607492036116494466393188903323283990850942810909351815500693477738669025501373), (6999980995772763799851704846197932670941005489850563434885403314179557970406001 / 57659313113892314660432029302114817085086963606942314791682259485833698470773601), (-16219070481600688837039176859675369308103388289319579953050348373375593872313969 / 90607492036116494466393188903323283990850942810909351815500693477738669025501373), (21934796530407963660656864562824318430281639922921325069792264206337599093090194 / 211417481417605153754917440774420995978652199892121820902834951448056894392836537), (-65920253919192480532997691539425704975931823729164921780296439036740834186442639 / 211417481417605153754917440774420995978652199892121820902834951448056894392836537), (405550077056460674901392107786950955051052195999470600995306810415507439069096630 / 634252444252815461264752322323262987935956599676365462708504854344170683178509611), (191375737444739743764695075028586277730458463429620794141353988505236073743904837 / 634252444252815461264752322323262987935956599676365462708504854344170683178509611), (-2562680672631997976962073255875532823544565474766731252010345517715722763734973 / 57659313113892314660432029302114817085086963606942314791682259485833698470773601), (24193656684275427733088326107044459495442851876727506890634817296047738961218939 / 90607492036116494466393188903323283990850942810909351815500693477738669025501373), (-118347944452066065973471629618890756108534253421314956774315124203894657589561812 / 634252444252815461264752322323262987935956599676365462708504854344170683178509611), (-2318631035869750399063088135256980605624987779297102188358464895996599862664333 / 19219771037964104886810676434038272361695654535647438263894086495277899490257867), (4979855051456233706911354921671017679569102757964273723860320671606433426598254 / 30202497345372164822131062967774427996950314270303117271833564492579556341833791), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(25250011362415979921512817178122576927952836482933696387524464040655200046 / 59597467165445891976298201257606235271411725679732828066049546727576220269), (-9376992274092657587402777519661957656035780413141672026624400653615616233 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (198105701268050197162659074263532523731838534788830149412203654694126865 / 2591194224584603998969487011200271098757031551292731655045632466416357403), (59695100587477232447240154463661929101473925025525450439675908764257882359 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (-17521248740450851306396373309996630276473357270357769283931509306181561629 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (-21484544482281675236567155951833220620987199755587784767715534246330330477 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (3093713975828284975804686697616588557617449145600832574259278292570853647 / 59597467165445891976298201257606235271411725679732828066049546727576220269), (-5151704957806604009371028749092824909359928115092841591310391924368916289 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (23468611204423949756276409170411309790077109444561005082606257237596140850 / 59597467165445891976298201257606235271411725679732828066049546727576220269), (27666850970431468245320462620707904386938840871469248459235157979987755255 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (6210867065359606828827708085649974428559475337344256831075750578516850131 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (-10917751019727653130347006838182056657366276672402060044819788284031945175 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (-151509020786892283351091490822840712078007644530276171896182704229557903 / 59597467165445891976298201257606235271411725679732828066049546727576220269), (3291188386622884859640902552478305463167603647280025565630505296929621277 / 119194934330891783952596402515212470542823451359465656132099093455152440538), (10421567012583592504826460714776635504757752701294378900074290686085304123 / 59597467165445891976298201257606235271411725679732828066049546727576220269), (62149167968450059177746353352804916195647971926099213508482347867297881539 / 119194934330891783952596402515212470542823451359465656132099093455152440538), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(7083812953418461815143216235358447491347175136660796307302166164831 / 7182904753257242596599680468641735483398517637402608284429379166551), (3632389648288561941138004738235946231622948507855386547593656326543 / 57463238026057940772797443749133883867188141099220866275435033332408), (343856114570380425671067198327270526748729583651994177381231361225 / 28731619013028970386398721874566941933594070549610433137717516666204), (188176181379780177484566399922627085824580541025107024973692771219 / 57463238026057940772797443749133883867188141099220866275435033332408), (15002020732400701483417105832182288466519834488255213547016602042903 / 57463238026057940772797443749133883867188141099220866275435033332408), (-6588043162421600515048975145258172797280963318036296920679742589933 / 57463238026057940772797443749133883867188141099220866275435033332408), (3054868758221058888427450057841924479506797456385924573609198937175 / 28731619013028970386398721874566941933594070549610433137717516666204), (-17894222513341603909490705243363932537164169475894460882409503187349 / 57463238026057940772797443749133883867188141099220866275435033332408), (3462839385283399419151147825945914623333258280422387448498500889698 / 7182904753257242596599680468641735483398517637402608284429379166551), (37887575998112951978449442974033395632215350233530896120900116773519 / 57463238026057940772797443749133883867188141099220866275435033332408), (-15470603554993473845715442444905262971881884221347321092940354054293 / 57463238026057940772797443749133883867188141099220866275435033332408), (-18052528939858059320551570042975473708282232801695090797582966852211 / 57463238026057940772797443749133883867188141099220866275435033332408), (11698570154584079700078426629341557723275988577049400733799390546947 / 28731619013028970386398721874566941933594070549610433137717516666204), (-7000313431198878243630519630678457723835628926061318019891443832659 / 57463238026057940772797443749133883867188141099220866275435033332408), (5515270908425103536128096796483901679807269025853682235550234998835 / 28731619013028970386398721874566941933594070549610433137717516666204), (3317893712521795823807929202304385575948346839190777259188508668527 / 57463238026057940772797443749133883867188141099220866275435033332408), (11832076709424496004061290459973778844461908046802895116059434362999 / 28731619013028970386398721874566941933594070549610433137717516666204), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-3766150041077688012906386275715589452929993301459749394433896 / 14457133534575895981631322572858826899406824367863187516660681), (1744091411271218450926146712880458623600071006278587125707702 / 14457133534575895981631322572858826899406824367863187516660681), (2304723704515610302906948285093941189254171707193624423393689 / 14457133534575895981631322572858826899406824367863187516660681), (909928558266460223118060063298731472853370868573571935099164 / 4819044511525298660543774190952942299802274789287729172220227), (-146203058010922533789655172681010934279613512768151285376862 / 14457133534575895981631322572858826899406824367863187516660681), (8078209888438245584811584257505783572533683608690480323161519 / 14457133534575895981631322572858826899406824367863187516660681), (-168557103923147918727688038019599726432619514742523274078582 / 14457133534575895981631322572858826899406824367863187516660681), (1531116040433524835281020911955644304584818323263805137661550 / 14457133534575895981631322572858826899406824367863187516660681), (670283455103867706895583594637295804744117049271350484737188 / 14457133534575895981631322572858826899406824367863187516660681), (-10760239410602027466147369315362295243449740407127715621184986 / 14457133534575895981631322572858826899406824367863187516660681), (-2333810620337620504007167417257853653625552460156813875425280 / 14457133534575895981631322572858826899406824367863187516660681), (-90051570411450108815511798715436883719663330316863473685220 / 4819044511525298660543774190952942299802274789287729172220227), (-2816089400142654435411588610439562106827784519983684421795171 / 14457133534575895981631322572858826899406824367863187516660681), (-945586209143179646838274648535939380125903922328505712413775 / 4819044511525298660543774190952942299802274789287729172220227), (4640105007292288379580622664562957715634945268676211089774105 / 14457133534575895981631322572858826899406824367863187516660681), (-1773709978490061398910338698160853017145564831546655199774723 / 4819044511525298660543774190952942299802274789287729172220227), (-8648928698603990837564103789963918251754960228174787420147025 / 14457133534575895981631322572858826899406824367863187516660681), (-376970241864434703094160085637680770414408964003104862478705 / 14457133534575895981631322572858826899406824367863187516660681), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(71022987819521185074216981363629043153684167645127029 / 7602779807890812582079933600291583262810748160100125755), (-552437662999319551409449461811266587035446601919750578 / 7602779807890812582079933600291583262810748160100125755), (70918722566483770547278204583569026932098665429965404 / 7602779807890812582079933600291583262810748160100125755), (4254485627113046915010627776199062885628380943528980212 / 7602779807890812582079933600291583262810748160100125755), (-147963417243250907695984624111633470250207838303272072 / 7602779807890812582079933600291583262810748160100125755), (-283901788439276520714653772358786392412148586422112656 / 7602779807890812582079933600291583262810748160100125755), (294863261006887694385667081289674194582904639872613713 / 7602779807890812582079933600291583262810748160100125755), (-88886276091663944228666467958653579020366374444995130 / 1520555961578162516415986720058316652562149632020025151), (-777711669515427660829164310009759722944158301110107252 / 7602779807890812582079933600291583262810748160100125755), (-2097529691702123060888504092740495337356578598860922476 / 7602779807890812582079933600291583262810748160100125755), (177286644712623042724605435949769420245531507296954133 / 1520555961578162516415986720058316652562149632020025151), (-256211131545182266312935578005147515855306965217627754 / 1520555961578162516415986720058316652562149632020025151), (-653345441761751095342951159050181624041868259108755086 / 7602779807890812582079933600291583262810748160100125755), (150606020488835045023049238758848098531381042742071547 / 1520555961578162516415986720058316652562149632020025151), (42420685532187747296730764685720214694394683225304487 / 1520555961578162516415986720058316652562149632020025151), (-4359153144938513393789344791899699228642979104226032149 / 7602779807890812582079933600291583262810748160100125755), (159466859199676594630047097750930519384523166636298180 / 1520555961578162516415986720058316652562149632020025151), (-423268160739794020473255110688267549223888578586677369 / 1520555961578162516415986720058316652562149632020025151), (1632571271589160695763109276584469296029316371437439436 / 7602779807890812582079933600291583262810748160100125755), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-607177789211137308186317755973460118166954917087 / 525480683981912276687499434611558048779917623804), (-116934271478729342929409400854729225784415218823 / 262740341990956138343749717305779024389958811902), (-72132811014078286663128469346468300813182122713 / 131370170995478069171874858652889512194979405951), (150025784046182712393940880883114761462040091722 / 131370170995478069171874858652889512194979405951), (-72309724900325325413108657744760089415849447248 / 131370170995478069171874858652889512194979405951), (-49446783625007545273952451032202874391914177016 / 131370170995478069171874858652889512194979405951), (-26574035315146370543221669283603114128940831011 / 525480683981912276687499434611558048779917623804), (19133719110128838457080682748060247039192288605 / 20210795537765856795673055177367617260766062454), (-208068241043783473166009649741345291503107406331 / 131370170995478069171874858652889512194979405951), (-335328324633101496409878897970031285137515639649 / 131370170995478069171874858652889512194979405951), (447430028137976446773924703427470548882196564257 / 525480683981912276687499434611558048779917623804), (-243291805896117137436372153572813476247834489 / 20210795537765856795673055177367617260766062454), (-89222175588479112477075417795725487703508295581 / 262740341990956138343749717305779024389958811902), (626018627579270741118930393511395956399833028955 / 525480683981912276687499434611558048779917623804), (-346580524159015970864077711397949780235459578577 / 525480683981912276687499434611558048779917623804), (-718329918186469928028496695992411675307662005593 / 525480683981912276687499434611558048779917623804), (144042097356093577567947854357256211524675699577 / 131370170995478069171874858652889512194979405951), (-1328412101248162696765503006368429869387629166297 / 525480683981912276687499434611558048779917623804), (-1189560553539811110492082800536746260292227323 / 10105397768882928397836527588683808630383031227), (1831709879527314923288714443047198246314014059547 / 525480683981912276687499434611558048779917623804), 0, 0, 0, 0, 0, 0, 0],
  ![(634684782910775642842165155425608798952782 / 1188953655075915851853003755487819451123245), (24565451527795220414493323225209269870446 / 1188953655075915851853003755487819451123245), (-130679951628648589542436402605661109023573 / 1188953655075915851853003755487819451123245), (-25258238645407650559099841241076744444026 / 396317885025305283951001251829273150374415), (3704488751358286464755074866993200246771 / 9361839803747368912228376027463145284435), (-75765906125986297242924560396612084247136 / 1188953655075915851853003755487819451123245), (128012016295907040495442048949412126524686 / 1188953655075915851853003755487819451123245), (-85296181877613466607166906825953060479499 / 237790731015183170370600751097563890224649), (147754119064377760122186196293266130000743 / 396317885025305283951001251829273150374415), (390808362574373162833153163687964854327371 / 1188953655075915851853003755487819451123245), (-67415622145690608964870972632701717920099 / 396317885025305283951001251829273150374415), (357527692090321821612880340468378839569799 / 1188953655075915851853003755487819451123245), (423541934103812791169876064443545791436252 / 1188953655075915851853003755487819451123245), (-11337499871669833918837685270423952949173 / 79263577005061056790200250365854630074883), (140648389113660570855284361498012266864032 / 1188953655075915851853003755487819451123245), (245627772142542308060375980118652638168896 / 396317885025305283951001251829273150374415), (133410000993925616563665557190753511201172 / 1188953655075915851853003755487819451123245), (704378476449456120131814605228524178189962 / 1188953655075915851853003755487819451123245), (-139649646018095113112455334826829999501564 / 1188953655075915851853003755487819451123245), (-305112106413021247163753813047067354655592 / 1188953655075915851853003755487819451123245), (76744115500604883336401098692308542300031 / 1188953655075915851853003755487819451123245), 0, 0, 0, 0, 0, 0],
  ![(20628914259350482385225651192708137 / 88775005697376683078106916798058681), (-4811486288484456173433098278665692 / 88775005697376683078106916798058681), (1715998847783746429498882651392739 / 88775005697376683078106916798058681), (41385774548467287652346900715918209 / 88775005697376683078106916798058681), (6789923718153760504230588208416773 / 88775005697376683078106916798058681), (-10921516390184366852007724509944486 / 88775005697376683078106916798058681), (-16445120449261533456227677041043285 / 88775005697376683078106916798058681), (-4672847693371214765343892044878765 / 88775005697376683078106916798058681), (14260375924110239760703921158959840 / 88775005697376683078106916798058681), (-4179212708299017725026432143721864 / 88775005697376683078106916798058681), (13362426363214455020447555336556671 / 88775005697376683078106916798058681), (3944504500479597971751644164561194 / 12682143671053811868300988114008383), (10279713044632122352521592094611766 / 88775005697376683078106916798058681), (-396019490551377862376667386749521 / 12682143671053811868300988114008383), (2914857951123296020436502382784294 / 88775005697376683078106916798058681), (-4444348131223926371558494912568179 / 12682143671053811868300988114008383), (13107667703055066417148902002236317 / 88775005697376683078106916798058681), (-13621307365401214276463213878263638 / 88775005697376683078106916798058681), (-909640955689009473469575053374449 / 88775005697376683078106916798058681), (69107694084044836578642660966865699 / 88775005697376683078106916798058681), (6023836906925185846319089955982837 / 88775005697376683078106916798058681), (16643704284639824589793734702706930 / 88775005697376683078106916798058681), 0, 0, 0, 0, 0],
  ![(-1591673936980059314472507643 / 2832677216948119172647607770), (-191364195393013492390697891 / 1416338608474059586323803885), (-474883480145514918422197161 / 2832677216948119172647607770), (-436274440729973136722237501 / 2832677216948119172647607770), (740610702465925334278125303 / 2832677216948119172647607770), (-449018969141805039639154868 / 1416338608474059586323803885), (174752103052165319288256729 / 566535443389623834529521554), (-100112931039179902109920563 / 566535443389623834529521554), (169348360128632555953138409 / 283267721694811917264760777), (492433272197630907887483673 / 1416338608474059586323803885), (-820533561527860866393645009 / 2832677216948119172647607770), (-207826585221097848656505596 / 1416338608474059586323803885), (-107099800028261214509562272 / 1416338608474059586323803885), (-159698266950556853302437227 / 2832677216948119172647607770), (24573028205790066606540417 / 1416338608474059586323803885), (2456483409438397969047476117 / 2832677216948119172647607770), (769883810991093594531512857 / 2832677216948119172647607770), (180679087484089996806322316 / 1416338608474059586323803885), (-159137202755155749897888159 / 2832677216948119172647607770), (-568515494845160677628700201 / 2832677216948119172647607770), (84607021421404939643598237 / 2832677216948119172647607770), (14162240424424729556931287 / 283267721694811917264760777), (-3552029890821940337873350919 / 2832677216948119172647607770), 0, 0, 0, 0],
  ![(114442770449396066615 / 230463790325663091369), (59737028125471121162 / 230463790325663091369), (11957382908173116936 / 76821263441887697123), (135712482318090150205 / 230463790325663091369), (44567219137357391372 / 76821263441887697123), (76192871640949346285 / 230463790325663091369), (-32165823056412449049 / 76821263441887697123), (-33005191482122727784 / 76821263441887697123), (157332688353992778467 / 230463790325663091369), (72178283219232695130 / 76821263441887697123), (35384355762490349383 / 76821263441887697123), (266517627287618894408 / 230463790325663091369), (64014914849676037889 / 230463790325663091369), (87078377994133855225 / 230463790325663091369), (-3348621446030698977 / 76821263441887697123), (-207190277421973608436 / 230463790325663091369), (-265730391941743542533 / 230463790325663091369), (196146175209413274589 / 230463790325663091369), (-42956422397857037683 / 76821263441887697123), (64736547350901872339 / 76821263441887697123), (13439965544547935345 / 76821263441887697123), (-326198868359342031487 / 230463790325663091369), (474356783144755819996 / 230463790325663091369), (98191395878236040143 / 230463790325663091369), 0, 0, 0],
  ![(-37236465008557 / 116459807114612), (391663480673 / 58229903557306), (9575844821130 / 29114951778653), (28274088839253 / 116459807114612), (155129122247 / 29114951778653), (345615410951 / 6129463532348), (-6158628332443 / 116459807114612), (2647565021253 / 29114951778653), (-43378749237065 / 116459807114612), (779169901763 / 58229903557306), (-44866390429095 / 116459807114612), (200235284043 / 2239611675281), (-8734097025579 / 116459807114612), (742709937049 / 8958446701124), (22343304885497 / 116459807114612), (-1978579931015 / 29114951778653), (33445726437815 / 116459807114612), (41235351180133 / 116459807114612), (82894103493547 / 116459807114612), (-13423396416539 / 116459807114612), (10994397856479 / 116459807114612), (-28355965627259 / 116459807114612), (-22269117374953 / 29114951778653), (28983821501915 / 116459807114612), (-12400723226327 / 116459807114612), 0, 0],
  ![(-3848880 / 5497571), (206227 / 5497571), (-1320981 / 5497571), (-2602804 / 5497571), (-1483981 / 5497571), (-393268 / 5497571), (-1032694 / 5497571), (2854925 / 5497571), (-3097019 / 5497571), (-2054950 / 5497571), (-1745575 / 5497571), (-1738479 / 5497571), (-52888 / 148583), (242711 / 5497571), (-1763362 / 5497571), (-135856 / 177341), (344604 / 5497571), (-1006711 / 5497571), (3152538 / 5497571), (618762 / 5497571), (-428236 / 5497571), (-8338454 / 5497571), (-5290054 / 5497571), (1201176 / 5497571), (-1287392 / 5497571), (4540900 / 5497571), 0]
]

def D : Fin 27 → ℚ := ![(4275996723645910471498112093881010384403504495182398091637789620943636539892427305409591442648376639371673936279548597839081096789035975505379653166632269569988590228318 / 4412590967729511246032589309155886688902951238882474757178677823339973532527862950366205894002585870229080800368732575045566858917843811396462501223949213284491225), (39713318709565601214293303782402980200126561149942272814608100410059761792750766553295853046023272832061727203318593175410101730260594302568162511015542919560421025 / 387370202298328952841734074741226159998708757595685237855957437098716608003406950622039400549558673764862670663466066327834240530485731994767105499801050305573), (387370202298328952841734074741226159998708757595685237855957437098716608003406950622039400549558673764862670663466066327834240530485731994767105499801050305573 / 990252635606303162634243885539853414657717237730732870168465296399210751761204919659212710832007778670630691481531883236421313548644502630237831060205534), (330084211868767720878081295179951138219239079243577623389488432133070250587068306553070903610669259556876897160510627745473771182881500876745943686735178 / 280070256488662344563643167884306726719429041722243580851231973223636144890503132822491336810949975404681836605020868849081036017534656603067797823), (280070256488662344563643167884306726719429041722243580851231973223636144890503132822491336810949975404681836605020868849081036017534656603067797823 / 342316739834473647632905382743043026551034856859059048502435074156983186504304312567832930160916010250866212203433421537582017268836042811194), (171158369917236823816452691371521513275517428429529524251217537078491593252152156283916465080458005125433106101716710768791008634418021405597 / 162468709327855293493608447170798143370645494921576560577966963802363975900041015186668799306580746669717708114778656089429590683005713), (974812255967131760961650683024788860223872969529459363467801782814183855400246091120012795839484480018306248688671936536577544098034278 / 3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047), (3513618207763405232261537218945117549057180867735899799813291897892188499253186575753741183425900513223682878394544946632000497047 / 2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655), (2085126224259661863123424106643074111205393915204525026864836467694346423088627189833210518351275356946453614671332613818655 / 1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228), (1140129584606749704572810165998908490118395580778102715529724925207247344393573353177613331593603450899275408747107228 / 432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221), (432187524458851371849273623492666225897401859359823958113905324889666259521036464061843608223531467546760364221 / 636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477), (636521120043387572881195077008148831760923511823266255889688775473081875979669926858766620343754923467477 / 327658826417831101328126222577485582324612989891469188675299449738710653238591597755714006501683305), (65531765283566220265625244515497116464922597978293837735059889947742130647718319551142801300336661 / 53758423342623327120955381707961471287432905005984778254935004229901863528848544139427766001), (89597372237705545201592302846602452145721508343307963758225007049836439214747573565712943335 / 187490294079969058320124580277086863143875073053066725158103130950888848925702799162824), (26784327725709865474303511468155266163410724721866675022586161564412692703671828451832 / 30202497345372164822131062967774427996950314270303117271833564492579556341833791), (634252444252815461264752322323262987935956599676365462708504854344170683178509611 / 238389868661783567905192805030424941085646902718931312264198186910304881076), (59597467165445891976298201257606235271411725679732828066049546727576220269 / 14365809506514485193199360937283470966797035274805216568858758333102), (57463238026057940772797443749133883867188141099220866275435033332408 / 14457133534575895981631322572858826899406824367863187516660681), (14457133534575895981631322572858826899406824367863187516660681 / 7602779807890812582079933600291583262810748160100125755), (7602779807890812582079933600291583262810748160100125755 / 525480683981912276687499434611558048779917623804), (525480683981912276687499434611558048779917623804 / 1188953655075915851853003755487819451123245), (1188953655075915851853003755487819451123245 / 88775005697376683078106916798058681), (88775005697376683078106916798058681 / 2832677216948119172647607770), (2832677216948119172647607770 / 230463790325663091369), (230463790325663091369 / 116459807114612), (116459807114612 / 5497571), 5497571]

end MUB6.Certificate.GramData.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

def weights : Matrix (Fin 27) (Fin 27) ℤ := ![
  ![21638825, 1103969, -366698, 4472903, 4675758, -348911, -1653142, -6679308, 8323724, 7441570, 4676581, 5623964, 8331635, -2350116, 1781770, 196990, -196597, 6566227, -8510275, 4751159, 70965, 14265487, 26849611, -9014352, 2605212, -9952367, -3848880],
  ![1103969, 944580, 262232, -1282119, 95477, 1215062, -564931, -35356, -831071, 337531, -143710, 302472, 204411, -65538, 56758, -848390, -1894747, 1697129, 37861, -2357894, -256571, -1198268, 1132197, -1361624, 449476, 312826, 206227],
  ![-366698, 262232, 4372564, 3731369, -407706, 2092458, -1007026, 873692, -2456751, -216243, -1563203, 1156547, 42736, 737006, 2315448, -2604186, 830681, 2358685, 4672623, -140249, 456406, -1590279, -234365, -483957, -124524, 5876220, -1320981],
  ![4472903, -1282119, 3731369, 19481819, -144329, -427246, -3175977, -1883385, -68139, -3526786, 3743961, 6685420, 1352597, 2280274, 2706754, -11269051, 4787889, -3225514, 3611637, 21924365, 2276614, 2837114, 17953246, -685263, 1227195, 2993143, -2602804],
  ![4675758, 95477, -407706, -144329, 6492797, -1491868, 817068, -4627001, 7215886, 5805250, -1305636, 2952474, 3939166, -1359246, 1532955, 5894401, -29611, 6202189, -2291217, -481138, 684539, 6508035, 2071984, 3406557, 1483542, -1112872, -1483981],
  ![-348911, 1215062, 2092458, -427246, -1491868, 6691737, -614723, 2447831, -2470731, -3927318, 469732, -959011, -1289212, 420869, 995398, -3671401, -3970214, 728173, 1583616, -2751073, -341589, -2391480, 1842073, -3406562, 619147, 869639, -393268],
  ![-1653142, -564931, -1007026, -3175977, 817068, -614723, 3480564, -1569264, 3004866, 1839889, -1954425, -3083192, -381717, -777936, 548165, 7957870, 1340972, 1639448, -1148157, -5852439, -380245, 3554996, -10414524, 2933849, -467475, -1973233, -1032694],
  ![-6679308, -35356, 873692, -1883385, -4627001, 2447831, -1569264, 7383368, -7671834, -6735967, 118611, -3301327, -3540810, 1566438, -1531264, -6992208, -99872, -5499711, 4157406, 380152, -257758, -8817786, -4896596, -1431032, -1723883, 4284472, 2854925],
  ![8323724, -831071, -2456751, -68139, 7215886, -2470731, 3004866, -7671834, 20205267, 10681732, 909816, 2492242, 4317945, -3579665, 2295640, 13833571, 730101, 6141615, -9345834, -1057876, -83947, 11010772, 7616015, 5283323, 2916394, -10448615, -3097019],
  ![7441570, 337531, -216243, -3526786, 5805250, -3927318, 1839889, -6735967, 10681732, 16547778, -2924799, 3946206, 5011875, -2276717, 1384567, 12642667, 479639, 12059339, -4897979, -9757133, -304344, 4755447, -1246459, 4687144, 2310344, -1413894, -2054950],
  ![4676581, -143710, -1563203, 3743961, -1305636, 469732, -1954425, 118611, 909816, -2924799, 7987018, 2298496, 670012, 1060859, -1536421, -6516193, -3482292, -6804900, -6889389, 9482366, -31994, 1772760, 18979737, -5584492, 2189272, -9602945, -1745575],
  ![5623964, 302472, 1156547, 6685420, 2952474, -959011, -3083192, -3301327, 2492242, 3946206, 2298496, 11293001, 3855450, 207606, 919586, -1479887, -1937263, 3041223, -1958480, 5974596, 1576779, 4701210, 16943621, -736999, 2493931, 458016, -1738479],
  ![8331635, 204411, 42736, 1352597, 3939166, -1289212, -381717, -3540810, 4317945, 5011875, 670012, 3855450, 5397378, -1102075, 962591, 2637949, 188406, 4768294, -3725397, 446791, 474966, 7981741, 9023959, -1518183, 1177088, -3205049, -1956856],
  ![-2350116, -65538, 737006, 2280274, -1359246, 420869, -777936, 1566438, -3579665, -2276717, 1060859, 207606, -1102075, 2217189, -487516, -4116005, -24349, -2063816, 1117744, 3592223, 593484, -3987844, -147587, 115748, 503866, 1956747, 242711],
  ![1781770, 56758, 2315448, 2706754, 1532955, 995398, 548165, -1531264, 2295640, 1384567, -1536421, 919586, 962591, -487516, 3205882, 2761862, 1941024, 3868069, 2452580, -1000408, 392906, 3595017, -827728, 802693, -106086, 2607707, -1763362],
  ![196990, -848390, -2604186, -11269051, 5894401, -3671401, 7957870, -6992208, 13833571, 12642667, -6516193, -1479887, 2637949, -4116005, 2761862, 32801715, 4724490, 10794029, -6316274, -25027763, -614355, 16030892, -22856504, 8622411, -639546, -4918260, -4211536],
  ![-196597, -1894747, 830681, 4787889, -29611, -3970214, 1340972, -99872, 730101, 479639, -3482292, -1937263, 188406, -24349, 1941024, 4724490, 12353120, 774544, 4523372, 3167390, 1143666, 3762949, -9242889, 3957804, -3010232, 6368365, 344604],
  ![6566227, 1697129, 2358685, -3225514, 6202189, 728173, 1639448, -5499711, 6141615, 12059339, -6804900, 3041223, 4768294, -2063816, 3868069, 10794029, 774544, 17833685, 2066116, -13574800, 196572, 4428060, -8076457, 3932306, 1121311, 6669123, -1006711],
  ![-8510275, 37861, 4672623, 3611637, -2291217, 1583616, -1148157, 4157406, -9345834, -4897979, -6889389, -1958480, -3725397, 1117744, 2452580, -6316274, 4523372, 2066116, 15960711, 902133, 788329, -8554511, -16299324, 3279438, -3450350, 17682257, 3152538],
  ![4751159, -2357894, -140249, 21924365, -481138, -2751073, -5852439, 380152, -1057876, -9757133, 9482366, 5974596, 446791, 3592223, -1000408, -25027763, 3167390, -13574800, 902133, 41963642, 2913559, -1690663, 32194445, -2228810, 1782706, -1930609, 618762],
  ![70965, -256571, 456406, 2276614, 684539, -341589, -380245, -257758, -83947, -304344, -31994, 1576779, 474966, 593484, 392906, -614355, 1143666, 196572, 788329, 2913559, 935757, 954088, 1261245, 918772, 233548, 1646149, -428236],
  ![14265487, -1198268, -1590279, 2837114, 6508035, -2391480, 3554996, -8817786, 11010772, 4755447, 1772760, 4701210, 7981741, -3987844, 3595017, 16030892, 3762949, 4428060, -8554511, -1690663, 954088, 32392892, 11308744, -3684421, -299084, -12045329, -8338454],
  ![26849611, 1132197, -234365, 17953246, 2071984, 1842073, -10414524, -4896596, 7616015, -1246459, 18979737, 16943621, 9023959, -147587, -827728, -22856504, -9242889, -8076457, -16299324, 32194445, 1261245, 11308744, 76533185, -18865439, 7037228, -20572372, -5290054],
  ![-9014352, -1361624, -483957, -685263, 3406557, -3406562, 2933849, -1431032, 5283323, 4687144, -5584492, -736999, -1518183, 115748, 802693, 8622411, 3957804, 3932306, 3279438, -2228810, 918772, -3684421, -18865439, 14224969, 472, 6264265, 1201176],
  ![2605212, 449476, -124524, 1227195, 1483542, 619147, -467475, -1723883, 2916394, 2310344, 2189272, 2493931, 1177088, 503866, -106086, -639546, -3010232, 1121311, -3450350, 1782706, 233548, -299084, 7037228, 472, 2520573, -3319037, -1287392],
  ![-9952367, 312826, 5876220, 2993143, -1112872, 869639, -1973233, 4284472, -10448615, -1413894, -9602945, 458016, -3205049, 1956747, 2607707, -4918260, 6368365, 6669123, 17682257, -1930609, 1646149, -12045329, -20572372, 6264265, -3319037, 24934572, 4540900],
  ![-3848880, 206227, -1320981, -2602804, -1483981, -393268, -1032694, 2854925, -3097019, -2054950, -1745575, -1738479, -1956856, 242711, -1763362, -4211536, 344604, -1006711, 3152538, 618762, -428236, -8338454, -5290054, 1201176, -1287392, 4540900, 5497571]
]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (2, 3), m = 22, exponent = 14.
-/

namespace MUB6.Certificate.GramData.Block4

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 22) (Fin 22) ℚ := ![
  ![17001745, 2527050, 5536296, -6681691, 1894258, -1068497, 2181374, 2283451, 5870760, 5122348, 11944156, 4278803, -12939117, -653324, 12048267, -1896215, 4000099, -814376, -2263423, -227986, -7748966, -15099711],
  ![2527050, 4519314, 4041704, -1483567, 3743702, -2156927, 6647397, -394829, 5057136, -292814, 8387639, 3154912, -8313712, 3042363, 10815796, 10377904, -11676267, 1579557, 804909, -14681, 236179, 6258575],
  ![5536296, 4041704, 9649493, -6443349, 4926450, -2350703, 8255371, 1999663, 9422497, 1200964, 9488222, 3809106, -16699012, 533958, 15992020, 16606019, -11528195, 1552071, 1207709, 97824, -2753502, 220430],
  ![-6681691, -1483567, -6443349, 10582467, -4013447, 507536, -4628999, -2274383, -3889906, -2349413, -3559336, 112700, 12695356, 3371581, -7453387, -14511117, -146963, 189281, -767850, 318017, 4576468, 7350062],
  ![1894258, 3743702, 4926450, -4013447, 8001862, -2149155, 3463174, 2764593, 3803854, -683505, 5967631, 3481743, -11947838, 2934355, 4800575, 22116163, -8882925, 1039608, 3446947, -11230, -4019963, 3505349],
  ![-1068497, -2156927, -2350703, 507536, -2149155, 2095556, -4702242, 354131, -3195150, 90661, -5369286, -2205269, 5002923, -1757350, -6415795, -6460067, 6777335, -1444903, -396942, 65585, -74307, -3345646],
  ![2181374, 6647397, 8255371, -4628999, 3463174, -4702242, 48094530, -7277099, 8611573, -158959, 32218355, 4328739, -12463162, -826686, 42159577, 30525040, -26700880, 5748703, 677023, -524585, 9575677, 17455872],
  ![2283451, -394829, 1999663, -2274383, 2764593, 354131, -7277099, 6526673, -281, 1533901, -160327, 1671992, -4900936, 1492337, -4093860, 4067062, 6927530, -917759, 331917, -100234, -6691783, -8777026],
  ![5870760, 5057136, 9422497, -3889906, 3803854, -3195150, 8611573, -281, 15645334, 1309529, 13559036, 5861827, -17607260, 2684271, 21938238, 11639620, -17209683, 2061355, 52682, 294656, -2279851, 2493568],
  ![5122348, -292814, 1200964, -2349413, -683505, 90661, -158959, 1533901, 1309529, 3394404, 3491225, 854563, -1013940, -1050249, 2839721, -5240018, 8303639, -457001, -2183598, -290864, -4392796, -11111890],
  ![11944156, 8387639, 9488222, -3559336, 5967631, -5369286, 32218355, -160327, 13559036, 3491225, 44787203, 11712236, -18233209, 11108282, 40989979, 22667693, -18516868, 5024836, -2050110, -579570, -2671294, 2653116],
  ![4278803, 3154912, 3809106, 112700, 3481743, -2205269, 4328739, 1671992, 5861827, 854563, 11712236, 7193374, -8643946, 4853940, 9853406, 7247397, -7480837, 1622012, 505346, 410918, -3651298, 787079],
  ![-12939117, -8313712, -16699012, 12695356, -11947838, 5002923, -12463162, -4900936, -17607260, -1013940, -18233209, -8643946, 39243904, -2209331, -28830365, -39888927, 26441031, -2442740, -4212976, -270161, 6351203, -3952727],
  ![-653324, 3042363, 533958, 3371581, 2934355, -1757350, -826686, 1492337, 2684271, -1050249, 11108282, 4853940, -2209331, 12676281, 3479938, 4913859, -8763480, 2169781, -175103, 28798, -575196, 7485003],
  ![12048267, 10815796, 15992020, -7453387, 4800575, -6415795, 42159577, -4093860, 21938238, 2839721, 40989979, 9853406, -28830365, 3479938, 58430304, 28297024, -34667430, 6272171, -1826502, -293742, 4188233, 11611437],
  ![-1896215, 10377904, 16606019, -14511117, 22116163, -6460067, 30525040, 4067062, 11639620, -5240018, 22667693, 7247397, -39888927, 4913859, 28297024, 88538092, -40418461, 5471920, 12508886, -287708, -1840193, 25550802],
  ![4000099, -11676267, -11528195, -146963, -8882925, 6777335, -26700880, 6927530, -17209683, 8303639, -18516868, -7480837, 26441031, -8763480, -34667430, -40418461, 62053757, -6575663, -6508672, -977591, -15271475, -47014529],
  ![-814376, 1579557, 1552071, 189281, 1039608, -1444903, 5748703, -917759, 2061355, -457001, 5024836, 1622012, -2442740, 2169781, 6272171, 5471920, -6575663, 1995295, 135130, -105331, 1847776, 5047208],
  ![-2263423, 804909, 1207709, -767850, 3446947, -396942, 677023, 331917, 52682, -2183598, -2050110, 505346, -4212976, -175103, -1826502, 12508886, -6508672, 135130, 4058466, 292521, 298837, 6360316],
  ![-227986, -14681, 97824, 318017, -11230, 65585, -524585, -100234, 294656, -290864, -579570, 410918, -270161, 28798, -293742, -287708, -977591, -105331, 292521, 332991, 64677, 847534],
  ![-7748966, 236179, -2753502, 4576468, -4019963, -74307, 9575677, -6691783, -2279851, -4392796, -2671294, -3651298, 6351203, -575196, 4188233, -1840193, -15271475, 1847776, 298837, 64677, 13948174, 20619430],
  ![-15099711, 6258575, 220430, 7350062, 3505349, -3345646, 17455872, -8777026, 2493568, -11111890, 2653116, 787079, -3952727, 7485003, 11611437, 25550802, -47014529, 5047208, 6360316, 847534, 20619430, 50740836]
]

def entries : Matrix (Fin 22) (Fin 22) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-1945379163503408547541836004904897310738537189946045042084115705090752875213872000497755375041273283574225635880170478088295815870891 / 182703471616822988787622912516117073889048296478542601419727344290040412767850070571752373697364801733285418676306327771289513028266245), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(9951488830568497738361739071828637020883145849465304353504262730589128102724313111488274662677882032914220553764487423081466840 / 92942684449542433497009720849893866513592191529601952866778122132969029237003355401896783577609803083603354682804692984511895439), (19492354523210029739644776159595076304754055814129206838713879174849191153206023038853308576467564257043769361906523355700249866 / 92942684449542433497009720849893866513592191529601952866778122132969029237003355401896783577609803083603354682804692984511895439), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-2049172040878919700345330756008142892003240285468529872727501069384141173476939748248596841505372575975249163370881815083 / 11799281986960865913534248112935733160730092230457414066428655189600991826979717270697224521507587294142100088299701688126), (-3240584281968376024905745599153424002847325020463177172553680665891271366957336710877652517980745239366391898201554251283 / 47197127947843463654136992451742932642920368921829656265714620758403967307918869082788898086030349176568400353198806752504), (-26633000943340877034222047525205600167425337784984300431778190266670312395026322703131976913721144272551205729943428261809 / 94394255895686927308273984903485865285840737843659312531429241516807934615837738165577796172060698353136800706397613505008), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(44015272961890626295588878132508586427078997480846268600670995172192760890501604146880931474332728976555778563155269 / 53885008986812393707157569303517564474757409360866126879094150489141611493138069977037410988560813834174863534265793), (33272046634197295733100334108087939135285528162449032382724074802078976141103139832125623632798247822594201785069026 / 53885008986812393707157569303517564474757409360866126879094150489141611493138069977037410988560813834174863534265793), (14038336622009136480651306932023964863694750832042558619039745739190696141884027266073971174341322651194148716507750 / 53885008986812393707157569303517564474757409360866126879094150489141611493138069977037410988560813834174863534265793), (-17169878340744529199381750379921834031327557276113112136387934439330725707747003185224939386745015294714064533907751 / 53885008986812393707157569303517564474757409360866126879094150489141611493138069977037410988560813834174863534265793), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(16974798919155232363679513906071677991593696846059547416103978570586049246288805055222720151159164610321317843 / 151396915504099357316130439969424068581754492121689135431186398929195763729697913304374092270669610036465347556), (-34973766339336322736243347926296958865215020995461812354212472833634207767665453066407038926117831201563135983 / 151396915504099357316130439969424068581754492121689135431186398929195763729697913304374092270669610036465347556), (1937797327675012568365122398676284243153171458312601269260317920602077486382991791940858260920905170172095865 / 37849228876024839329032609992356017145438623030422283857796599732298940932424478326093523067667402509116336889), (-50867508878630698355326026971189263508165558783488404437188850665292495944400017303004714984234155009687607323 / 75698457752049678658065219984712034290877246060844567715593199464597881864848956652187046135334805018232673778), (-22118429972641843831608095003636181373494209021004106318525873639456683856878664845083111404185090068286675243 / 75698457752049678658065219984712034290877246060844567715593199464597881864848956652187046135334805018232673778), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-34293794970085688865914153251155285883901070647175420091510252604415607193229178724250897230004231249074 / 301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695), (-15027687425686364929568199506344172721497160297584945230884999724464823681604309706223735337328885311166 / 301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695), (9432561071031984270225467201750485295157072023202971471987352939538276854634302898339074713311174768495 / 60325635636799591141689543536767045340602024390801576908064952283763376985339967301392896997519951129339), (-26931498842119348060141716656272503544335147932215957838577863280865032698896558923263322944356746620487 / 301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695), (28039488341165563450193603145181671799138743149766027687379402513493691463438174949803602665632483728638 / 301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695), (-20814421945483644988507031360249485271232799655817091791679812367324307338499897652773644467139224323748 / 301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-33426596691575013991513174659151874195570677540527824650328294216442824577716187221749451014149879 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), (-5291275421185112103238409899041942871611352217330434296261023107755730163675321716428074856272763 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), (16384323748322892738289977466294018068053301948245698802853069388120733496202171012399701220680543 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), (9894570201260579845060696530439203980880795894263096747726047406712596936628866634273826419260117 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), (920205131379362979962647152183535968966334772215963555896529964449486338859304917461147973660324 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), (5199697329273322816766547096060965583984301948398004924311611890456265906225140485447054961586429 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), (-7950105938469215104571066910119633357929760612829223771058732646986697639108816504746225260359398 / 56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-3035014390664034013226878512426642291590336362765752009417829592181740715079889520348377577 / 6938541582276010958881373155087642789508864220280921232861257080293192927232865032733064960), (-1592113928199811062358906086060150149244809466209112835722336307963999883585436489997609189 / 6938541582276010958881373155087642789508864220280921232861257080293192927232865032733064960), (592173662306299253892531306410162730099901489407049029555114080805286883271616849634467969 / 6938541582276010958881373155087642789508864220280921232861257080293192927232865032733064960), (20740853830037078809817599518446726990544647252377123132617432136141175996423726602616641 / 630776507479637359898306650462512980864442201843720112078296098208472084293896821157551360), (-24912597853796557709796600636766808555671326221936786577671256339173387678038870162827387 / 157694126869909339974576662615628245216110550460930028019574024552118021073474205289387840), (178822576246506097862769982397099124515063491519599253527609086432507507779534059393649827 / 6938541582276010958881373155087642789508864220280921232861257080293192927232865032733064960), (-537426629965903910867878503610775872906619876632064230413166155894764079270474860758009837 / 3469270791138005479440686577543821394754432110140460616430628540146596463616432516366532480), (-657399250491610578146482281894521736362954216605340904455407014237129025206450705687194671 / 6938541582276010958881373155087642789508864220280921232861257080293192927232865032733064960), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(970353734704498607631441847887091882894800475995611562019054389967444606989972605451 / 851854903580760027068538244200760374751193470402544503615019885289393686544758961713), (735660685004039952814661972922649957785463243893657912212935617228401352513422696795 / 1703709807161520054137076488401520749502386940805089007230039770578787373089517923426), (9438520422969013613521633846130468307591372193762174451187642449771678273618932315 / 65527300275443079005272172630827721134707190030964961816539991176107206657289150901), (-990975751441663585105874473015033960436693282312358265679295102931058391501526937269 / 851854903580760027068538244200760374751193470402544503615019885289393686544758961713), (500942580467321545548279528450621078988670430036397298174298159104986567737265250353 / 1703709807161520054137076488401520749502386940805089007230039770578787373089517923426), (-54694832539694592413089255995099551858238688605387955174427265117388486020398317993 / 851854903580760027068538244200760374751193470402544503615019885289393686544758961713), (60419030745402252149401535315755571332142782013815953065758737684051579964922004224 / 65527300275443079005272172630827721134707190030964961816539991176107206657289150901), (-144084666504156289288139859854027401820262294517741111123107417995020523311304628033 / 851854903580760027068538244200760374751193470402544503615019885289393686544758961713), (-839684701605361416202084617796898570856627136649106869572418578201293130902387810293 / 1703709807161520054137076488401520749502386940805089007230039770578787373089517923426), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(18589306018110761773053552479539939711530261967050763818458314072191259608386251 / 42362174515676335863846963457707519882629626417569701269948911938632923880462856), (571794431425551495328296754691410770703991331276512685283509256213889750904309 / 42362174515676335863846963457707519882629626417569701269948911938632923880462856), (-6994591055311620682255941121264927716139520934052552836449319100385144702588247 / 42362174515676335863846963457707519882629626417569701269948911938632923880462856), (-4264545226667519328538831300576654497126876836582073705833293999275393209125317 / 42362174515676335863846963457707519882629626417569701269948911938632923880462856), (1006775565937936576324175513171134194586410048979159485523882842258223159337685 / 21181087257838167931923481728853759941314813208784850634974455969316461940231428), (-4267029263608825792434433453678349730125185881083733136563903352209864033163281 / 42362174515676335863846963457707519882629626417569701269948911938632923880462856), (14790743182821643619380603234935481362875777484781938960915842374321545903119961 / 21181087257838167931923481728853759941314813208784850634974455969316461940231428), (-150481778785386658851139745209316942721740290380598273589726318271660249586147 / 1033223768675032582045047889212378533722673815062675640730461266795924972694216), (-5122336030004779896231159815615333129651249321599595228831018198065216430877359 / 21181087257838167931923481728853759941314813208784850634974455969316461940231428), (-32468379246049308940497217094091497868577294631289665017956329405679718776169 / 5295271814459541982980870432213439985328703302196212658743613992329115485057857), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(5245944132208565453680610300775270644438371141087375492985852117426896550 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (-1088064389731799103903142657561029989474034240361184111285150971227997628 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (-6360069560045438937264169475724423802054015286578794146252498931676929677 / 20253855266707999236540880497756407445225741895943392109211695173417466534), (11088147329142544601844953437818758081370810843203759665968730509357398769 / 20253855266707999236540880497756407445225741895943392109211695173417466534), (-515704213244288671289576835329589502005854836270718838234882703739081954 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (-289707443295857408220602125441726545124622118152301789284291575324061826 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (12332059414640607204710693843757206740664295301091946570282383872767801297 / 20253855266707999236540880497756407445225741895943392109211695173417466534), (2105069161376348825502559407395363615452748676852638726160900410010965751 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (-5119828368935778203339716295989013522656780975914841678371256069432204830 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (16347604135296172035656643884415137116280160318513649912896322024175763 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (9632181333858419898533386951892516805378916628777563695494541411090096654 / 10126927633353999618270440248878203722612870947971696054605847586708733267), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-7059431799620206723228151603802700866954369859221516222879898902220 / 14332325888336902272738053527103543129003162276503560050437412119721), (-379561463121517769433875062309179341669706247606143229532014652023 / 28664651776673804545476107054207086258006324553007120100874824239442), (-2784792008048670242719072874246364148106255107152888520047014897521 / 14332325888336902272738053527103543129003162276503560050437412119721), (8329131959066711226872644250346453317551665866791755002652909524599 / 28664651776673804545476107054207086258006324553007120100874824239442), (-6778613117195369898933452299680812271736829411847463380827752655 / 28664651776673804545476107054207086258006324553007120100874824239442), (150897299019799607682339070101666582676666582765377861688842689436 / 14332325888336902272738053527103543129003162276503560050437412119721), (8751101983766263897038709175480370735086306821836249673778141473444 / 14332325888336902272738053527103543129003162276503560050437412119721), (-4313377706097043223401209740246198291947012773361609066648820294402 / 14332325888336902272738053527103543129003162276503560050437412119721), (192296031007923352014426292356330137503870661329479791726891956832 / 14332325888336902272738053527103543129003162276503560050437412119721), (-241162022018448265072354283121238684528294304002075883171727295154 / 14332325888336902272738053527103543129003162276503560050437412119721), (5190611402354328939607767169256093823590605889020347639855331479621 / 14332325888336902272738053527103543129003162276503560050437412119721), (18372060192425745201406764914460450011132003622994163337624243309 / 14332325888336902272738053527103543129003162276503560050437412119721), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(606542399733432170972903587784155904699631214140053924717017 / 5229692131529864070562520443758176258538202101212861113151961), (-127400709129387856312110098158315939538009917339805317386646 / 5229692131529864070562520443758176258538202101212861113151961), (-251389446980141096954663047664718655771866802732608495125417 / 5229692131529864070562520443758176258538202101212861113151961), (837446017583560136399480831688170612344587668629408422750928 / 5229692131529864070562520443758176258538202101212861113151961), (-30580138027925696177144710500502888216823681290273059247331 / 5229692131529864070562520443758176258538202101212861113151961), (143876757690017848710141346936368299657269436416006183574902 / 1743230710509954690187506814586058752846067367070953704383987), (-1017589587977819712275460602316385733505522155257867285317325 / 5229692131529864070562520443758176258538202101212861113151961), (953882107441451517497436260442666084464214199180913050691387 / 5229692131529864070562520443758176258538202101212861113151961), (-426935983587004407509614033995671850391476326350621685876384 / 5229692131529864070562520443758176258538202101212861113151961), (-118024849467063060238755231230264084838164800205700423216856 / 5229692131529864070562520443758176258538202101212861113151961), (1527025979390154687150733450316120832610888805074997326989697 / 1743230710509954690187506814586058752846067367070953704383987), (195783444310184635595276345005746213004389376706702104200855 / 1743230710509954690187506814586058752846067367070953704383987), (413272275709146071776249532183731158420030072310897427007040 / 5229692131529864070562520443758176258538202101212861113151961), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(223658023913054610874631658097922124726149878145837036 / 1006944206317306260051545962073463397083476967395215595), (132340099821272705682484718029027930636376564736799497 / 1006944206317306260051545962073463397083476967395215595), (30538941336619662342503913535773058459316310097671919 / 1006944206317306260051545962073463397083476967395215595), (77910504105965968090535690827127018065385250778527419 / 1006944206317306260051545962073463397083476967395215595), (-48798514429659961862017958971635502067233043769578353 / 1006944206317306260051545962073463397083476967395215595), (1329663987378848182730942428439947236997425219714158 / 1006944206317306260051545962073463397083476967395215595), (178981888280148445963378980376903709983202784060727276 / 201388841263461252010309192414692679416695393479043119), (-114862306160056418442971921443935452840741746874834284 / 1006944206317306260051545962073463397083476967395215595), (151426066445801635294385934986953663455541240389557483 / 1006944206317306260051545962073463397083476967395215595), (97593608356908924696684838573618591442465532869434057 / 1006944206317306260051545962073463397083476967395215595), (869301018942623987115640034337478441174223478041641578 / 1006944206317306260051545962073463397083476967395215595), (33141213537123033536130246218248783364033123413523441 / 201388841263461252010309192414692679416695393479043119), (-1527099152731529297658486229931239522443964964106710 / 201388841263461252010309192414692679416695393479043119), (-37374709419062777241826543942274266437936060167698067 / 1006944206317306260051545962073463397083476967395215595), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-2985618686083771062732391519453968217082453432 / 81209051428341235521112351043879940997685563761), (88277777150194873293530495483015570700975809 / 27069683809447078507037450347959980332561854587), (10132282220163820906661186873081208964226965940 / 81209051428341235521112351043879940997685563761), (-24485769751815041650563249868726144876086358166 / 81209051428341235521112351043879940997685563761), (11073011376025772283031936702122197480772584155 / 81209051428341235521112351043879940997685563761), (1434799246896789512078860750953027958119523501 / 81209051428341235521112351043879940997685563761), (43568640247391609039304440135010093771234552874 / 81209051428341235521112351043879940997685563761), (5078759810062251235376366237025851844613641655 / 81209051428341235521112351043879940997685563761), (-4665334066474339665484330467381521591945876954 / 81209051428341235521112351043879940997685563761), (224967908663878173897975411195916391296849469 / 81209051428341235521112351043879940997685563761), (6575802984878064184421611983872023061514686684 / 27069683809447078507037450347959980332561854587), (-7106388288582756255103076939518092616817454085 / 81209051428341235521112351043879940997685563761), (-23109817839826257467628762602194200898982785709 / 81209051428341235521112351043879940997685563761), (-9555790801894123403175725343058541971196444725 / 81209051428341235521112351043879940997685563761), (27742858590465903620055613660726087221055660393 / 81209051428341235521112351043879940997685563761), 0, 0, 0, 0, 0, 0, 0],
  ![(-979741546445512490112728287561514656029 / 1654953194604372719469627481313208737651), (-401231763891496834927654766296033494467 / 1654953194604372719469627481313208737651), (-932742285264119145171361448634220213528 / 1654953194604372719469627481313208737651), (651553517563682708640827021892505892206 / 1654953194604372719469627481313208737651), (-203082606582985058105404646320887853337 / 1654953194604372719469627481313208737651), (11153870389801576981239726232279237606 / 97350187917904277615860440077247572803), (-933693365421239930327355992611059929614 / 1654953194604372719469627481313208737651), (77703982298264848350935956904970804352 / 1654953194604372719469627481313208737651), (-1252083670440445481263394078420853157032 / 1654953194604372719469627481313208737651), (-153095875052266722842047006796380380174 / 1654953194604372719469627481313208737651), (-965557205472574429695761499232302090672 / 1654953194604372719469627481313208737651), (-238282823059233774474363585092454512269 / 1654953194604372719469627481313208737651), (1873988160935011429507889933631224506097 / 1654953194604372719469627481313208737651), (289631272289357321464223796425747138565 / 1654953194604372719469627481313208737651), (-2099643196667621179062544284844104972571 / 1654953194604372719469627481313208737651), (-843041700568193894515060667677950717722 / 1654953194604372719469627481313208737651), 0, 0, 0, 0, 0, 0],
  ![(1260676462534596296690153837269 / 4366686530900113813884868128521), (3666562436590476864009797439951 / 8733373061800227627769736257042), (4966338981190207284419439492715 / 4366686530900113813884868128521), (-1980854154325596854165700046907 / 4366686530900113813884868128521), (471043091952642889100225587845 / 1247624723114318232538533751006), (-5859374380063884099051073297745 / 8733373061800227627769736257042), (12673649310082941320652870196207 / 4366686530900113813884868128521), (-1352531878533678077547656534671 / 8733373061800227627769736257042), (4868586958960688184000553441028 / 4366686530900113813884868128521), (2991717591748788348537995148821 / 8733373061800227627769736257042), (11447671771397498338174068305223 / 4366686530900113813884868128521), (1251337687457678730681818481879 / 1247624723114318232538533751006), (-12386606060324197132774112189435 / 8733373061800227627769736257042), (48322107529475602853546169077 / 113420429374028930230775795546), (2565457901012813017786664584937 / 793943005618202511615430568822), (19002298246557683018454385695959 / 8733373061800227627769736257042), (-5452273928390833357388495596161 / 4366686530900113813884868128521), 0, 0, 0, 0, 0],
  ![(-43897847822731967504987249 / 99314840383272835917041810), (-37525004691181630172226793 / 99314840383272835917041810), (105824503586048133257759 / 9931484038327283591704181), (-23711096525782492876861334 / 49657420191636417958520905), (1050037687772382349254693 / 2837566868093509597629766), (2180416580666378037427182 / 9931484038327283591704181), (-7108020224660447748782781 / 49657420191636417958520905), (290479407486984973270823 / 3819801553202801381424685), (-35140954779602778624706614 / 49657420191636417958520905), (-15440864148385410455496739 / 49657420191636417958520905), (-80337086755371039958040944 / 49657420191636417958520905), (-7811224605390317726478957 / 14187834340467547988148830), (-4283004449270156198663955 / 19862968076654567183408362), (-15580719405732450114687461 / 14187834340467547988148830), (-11193169896048664395354617 / 7639603106405602762849370), (7620045238267934570878253 / 3819801553202801381424685), (41254469251064887400452711 / 99314840383272835917041810), (-1642827918144033767068929 / 7093917170233773994074415), 0, 0, 0, 0],
  ![(-8023806624703668503 / 43063047102502138108), (-33217942951229865271 / 43063047102502138108), (-3437895899701745285 / 21531523551251069054), (9717058396680180360 / 10765761775625534527), (-48498135748827899019 / 43063047102502138108), (6570917523590431585 / 10765761775625534527), (-48849469276491115269 / 21531523551251069054), (-7813438595824643351 / 21531523551251069054), (3093977987783210716 / 10765761775625534527), (-7000665006602561941 / 21531523551251069054), (-28689671242573973186 / 10765761775625534527), (28018326654780916487 / 43063047102502138108), (27630980280931339851 / 43063047102502138108), (-39264416832248778677 / 43063047102502138108), (-72669363280120115363 / 43063047102502138108), (-93848968107908508447 / 21531523551251069054), (37692423035846125 / 43063047102502138108), (-14118064390321327371 / 21531523551251069054), (5048976308808307131 / 21531523551251069054), 0, 0, 0],
  ![(-40920789495423 / 141290557954282), (-58532164603303 / 141290557954282), (-36065033590643 / 70645278977141), (20164930835647 / 70645278977141), (-138127290820069 / 141290557954282), (16303728550282 / 70645278977141), (31486931363253 / 70645278977141), (-39642347633852 / 70645278977141), (-41774374130419 / 70645278977141), (1556674151311 / 70645278977141), (-47562357601416 / 70645278977141), (-9159046970459 / 12844596177662), (18353105795969 / 12844596177662), (-91761210656073 / 141290557954282), (-13453384319061 / 141290557954282), (-155053976126052 / 70645278977141), (97262690622685 / 141290557954282), (-2578213267676 / 70645278977141), (-28995712833037 / 70645278977141), (-3548475733912 / 70645278977141), 0, 0],
  ![(-5033237 / 16913612), (6258575 / 50740836), (110215 / 25370418), (3675031 / 25370418), (3505349 / 50740836), (-1672823 / 25370418), (1454656 / 4228403), (-4388513 / 25370418), (623392 / 12685209), (-5555945 / 25370418), (221093 / 4228403), (787079 / 50740836), (-3952727 / 50740836), (2495001 / 16913612), (3870479 / 16913612), (4258467 / 8456806), (-47014529 / 50740836), (1261802 / 12685209), (1590079 / 12685209), (423767 / 25370418), (10309715 / 25370418), 0]
]

def D : Fin 22 → ℚ := ![(256817215465023738208373455098554192233574228074141337689258707980766856962426274525122760330375068130088327922624356668858242604061683888064 / 182703471616822988787622912516117073889048296478542601419727344290040412767850070571752373697364801733285418676306327771289513028266245), (182703471616822988787622912516117073889048296478542601419727344290040412767850070571752373697364801733285418676306327771289513028266245 / 371770737798169733988038883399575466054368766118407811467112488531876116948013421607587134310439212334413418731218771938047581756), (92942684449542433497009720849893866513592191529601952866778122132969029237003355401896783577609803083603354682804692984511895439 / 94394255895686927308273984903485865285840737843659312531429241516807934615837738165577796172060698353136800706397613505008), (94394255895686927308273984903485865285840737843659312531429241516807934615837738165577796172060698353136800706397613505008 / 53885008986812393707157569303517564474757409360866126879094150489141611493138069977037410988560813834174863534265793), (53885008986812393707157569303517564474757409360866126879094150489141611493138069977037410988560813834174863534265793 / 75698457752049678658065219984712034290877246060844567715593199464597881864848956652187046135334805018232673778), (151396915504099357316130439969424068581754492121689135431186398929195763729697913304374092270669610036465347556 / 301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695), (301628178183997955708447717683835226703010121954007884540324761418816884926699836506964484987599755646695 / 113135045716461578446803931743698461835969186794665475718844546641431306829644984183175394563711006), (56567522858230789223401965871849230917984593397332737859422273320715653414822492091587697281855503 / 27754166329104043835525492620350571158035456881123684931445028321172771708931460130932259840), (1734635395569002739720343288771910697377216055070230308215314270073298231808216258183266240 / 851854903580760027068538244200760374751193470402544503615019885289393686544758961713), (1703709807161520054137076488401520749502386940805089007230039770578787373089517923426 / 5295271814459541982980870432213439985328703302196212658743613992329115485057857), (42362174515676335863846963457707519882629626417569701269948911938632923880462856 / 10126927633353999618270440248878203722612870947971696054605847586708733267), (20253855266707999236540880497756407445225741895943392109211695173417466534 / 14332325888336902272738053527103543129003162276503560050437412119721), (28664651776673804545476107054207086258006324553007120100874824239442 / 5229692131529864070562520443758176258538202101212861113151961), (5229692131529864070562520443758176258538202101212861113151961 / 1006944206317306260051545962073463397083476967395215595), (1006944206317306260051545962073463397083476967395215595 / 81209051428341235521112351043879940997685563761), (81209051428341235521112351043879940997685563761 / 3309906389208745438939254962626417475302), (1654953194604372719469627481313208737651 / 122267222865203186788776307598588), (1247624723114318232538533751006 / 1013416738604824856296345), (49657420191636417958520905 / 21531523551251069054), (21531523551251069054 / 70645278977141), (70645278977141 / 12685209), 50740836]

end MUB6.Certificate.GramData.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

def weights : Matrix (Fin 22) (Fin 22) ℤ := ![
  ![17001745, 2527050, 5536296, -6681691, 1894258, -1068497, 2181374, 2283451, 5870760, 5122348, 11944156, 4278803, -12939117, -653324, 12048267, -1896215, 4000099, -814376, -2263423, -227986, -7748966, -15099711],
  ![2527050, 4519314, 4041704, -1483567, 3743702, -2156927, 6647397, -394829, 5057136, -292814, 8387639, 3154912, -8313712, 3042363, 10815796, 10377904, -11676267, 1579557, 804909, -14681, 236179, 6258575],
  ![5536296, 4041704, 9649493, -6443349, 4926450, -2350703, 8255371, 1999663, 9422497, 1200964, 9488222, 3809106, -16699012, 533958, 15992020, 16606019, -11528195, 1552071, 1207709, 97824, -2753502, 220430],
  ![-6681691, -1483567, -6443349, 10582467, -4013447, 507536, -4628999, -2274383, -3889906, -2349413, -3559336, 112700, 12695356, 3371581, -7453387, -14511117, -146963, 189281, -767850, 318017, 4576468, 7350062],
  ![1894258, 3743702, 4926450, -4013447, 8001862, -2149155, 3463174, 2764593, 3803854, -683505, 5967631, 3481743, -11947838, 2934355, 4800575, 22116163, -8882925, 1039608, 3446947, -11230, -4019963, 3505349],
  ![-1068497, -2156927, -2350703, 507536, -2149155, 2095556, -4702242, 354131, -3195150, 90661, -5369286, -2205269, 5002923, -1757350, -6415795, -6460067, 6777335, -1444903, -396942, 65585, -74307, -3345646],
  ![2181374, 6647397, 8255371, -4628999, 3463174, -4702242, 48094530, -7277099, 8611573, -158959, 32218355, 4328739, -12463162, -826686, 42159577, 30525040, -26700880, 5748703, 677023, -524585, 9575677, 17455872],
  ![2283451, -394829, 1999663, -2274383, 2764593, 354131, -7277099, 6526673, -281, 1533901, -160327, 1671992, -4900936, 1492337, -4093860, 4067062, 6927530, -917759, 331917, -100234, -6691783, -8777026],
  ![5870760, 5057136, 9422497, -3889906, 3803854, -3195150, 8611573, -281, 15645334, 1309529, 13559036, 5861827, -17607260, 2684271, 21938238, 11639620, -17209683, 2061355, 52682, 294656, -2279851, 2493568],
  ![5122348, -292814, 1200964, -2349413, -683505, 90661, -158959, 1533901, 1309529, 3394404, 3491225, 854563, -1013940, -1050249, 2839721, -5240018, 8303639, -457001, -2183598, -290864, -4392796, -11111890],
  ![11944156, 8387639, 9488222, -3559336, 5967631, -5369286, 32218355, -160327, 13559036, 3491225, 44787203, 11712236, -18233209, 11108282, 40989979, 22667693, -18516868, 5024836, -2050110, -579570, -2671294, 2653116],
  ![4278803, 3154912, 3809106, 112700, 3481743, -2205269, 4328739, 1671992, 5861827, 854563, 11712236, 7193374, -8643946, 4853940, 9853406, 7247397, -7480837, 1622012, 505346, 410918, -3651298, 787079],
  ![-12939117, -8313712, -16699012, 12695356, -11947838, 5002923, -12463162, -4900936, -17607260, -1013940, -18233209, -8643946, 39243904, -2209331, -28830365, -39888927, 26441031, -2442740, -4212976, -270161, 6351203, -3952727],
  ![-653324, 3042363, 533958, 3371581, 2934355, -1757350, -826686, 1492337, 2684271, -1050249, 11108282, 4853940, -2209331, 12676281, 3479938, 4913859, -8763480, 2169781, -175103, 28798, -575196, 7485003],
  ![12048267, 10815796, 15992020, -7453387, 4800575, -6415795, 42159577, -4093860, 21938238, 2839721, 40989979, 9853406, -28830365, 3479938, 58430304, 28297024, -34667430, 6272171, -1826502, -293742, 4188233, 11611437],
  ![-1896215, 10377904, 16606019, -14511117, 22116163, -6460067, 30525040, 4067062, 11639620, -5240018, 22667693, 7247397, -39888927, 4913859, 28297024, 88538092, -40418461, 5471920, 12508886, -287708, -1840193, 25550802],
  ![4000099, -11676267, -11528195, -146963, -8882925, 6777335, -26700880, 6927530, -17209683, 8303639, -18516868, -7480837, 26441031, -8763480, -34667430, -40418461, 62053757, -6575663, -6508672, -977591, -15271475, -47014529],
  ![-814376, 1579557, 1552071, 189281, 1039608, -1444903, 5748703, -917759, 2061355, -457001, 5024836, 1622012, -2442740, 2169781, 6272171, 5471920, -6575663, 1995295, 135130, -105331, 1847776, 5047208],
  ![-2263423, 804909, 1207709, -767850, 3446947, -396942, 677023, 331917, 52682, -2183598, -2050110, 505346, -4212976, -175103, -1826502, 12508886, -6508672, 135130, 4058466, 292521, 298837, 6360316],
  ![-227986, -14681, 97824, 318017, -11230, 65585, -524585, -100234, 294656, -290864, -579570, 410918, -270161, 28798, -293742, -287708, -977591, -105331, 292521, 332991, 64677, 847534],
  ![-7748966, 236179, -2753502, 4576468, -4019963, -74307, 9575677, -6691783, -2279851, -4392796, -2671294, -3651298, 6351203, -575196, 4188233, -1840193, -15271475, 1847776, 298837, 64677, 13948174, 20619430],
  ![-15099711, 6258575, 220430, 7350062, 3505349, -3345646, 17455872, -8777026, 2493568, -11111890, 2653116, 787079, -3952727, 7485003, 11611437, 25550802, -47014529, 5047208, 6360316, 847534, 20619430, 50740836]
]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (5,), m = 12, exponent = 15.
-/

namespace MUB6.Certificate.GramData.Block5

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 12) (Fin 12) ℚ := ![
  ![3616397, -219419, 1005407, 842091, 186248, 5630326, 3598595, -2799721, -212971, 17130, 919824, -418081],
  ![-219419, 858064, -20456, -237640, 8632, -668374, -719533, 1972640, 472837, -55599, -551864, -740155],
  ![1005407, -20456, 3980209, -871566, 1228704, 3015305, -741592, -4624965, -846239, -3742225, 946245, -2217477],
  ![842091, -237640, -871566, 1225103, -1032886, 1787740, 2550956, 1845322, 193740, 3000641, -537616, 2123549],
  ![186248, 8632, 1228704, -1032886, 2523431, 415506, -2373762, -4715938, -791330, -4758384, 1140990, -3681887],
  ![5630326, -668374, 3015305, 1787740, 415506, 14075688, 6490324, -6536077, -885101, 729531, 1366079, -804],
  ![3598595, -719533, -741592, 2550956, -2373762, 6490324, 11111814, 2309105, -369038, 7029198, -149445, 5321306],
  ![-2799721, 1972640, -4624965, 1845322, -4715938, -6536077, 2309105, 20933543, 2515724, 11792046, -5705771, 8194820],
  ![-212971, 472837, -846239, 193740, -791330, -885101, -369038, 2515724, 1454109, 1090081, -502420, -325129],
  ![17130, -55599, -3742225, 3000641, -4758384, 729531, 7029198, 11792046, 1090081, 14915142, -4206760, 10354295],
  ![919824, -551864, 946245, -537616, 1140990, 1366079, -149445, -5705771, -502420, -4206760, 3573400, -4063238],
  ![-418081, -740155, -2217477, 2123549, -3681887, -804, 5321306, 8194820, -325129, 10354295, -4063238, 10569070]
]

def entries : Matrix (Fin 12) (Fin 12) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(5596981437199023986587802591479864234103266874844442185081518081781 / 9431564276476137316302249406652340045066312658581041790680679499333), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(9024752121723864958855005808155216977010956324479945196573351 / 478995735357191027742975870517403818338762162597491826585334002), (-57603086073094515054582359527188582754702843364010638232418582 / 718493603035786541614463805776105727508143243896237739878001003), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(78143250083496273767036324975030346167235577000085768052 / 349379465359371639006642318106477150532122357473160614923), (-348693052313068535489210812175476395363963376171784539124 / 1048138396078114917019926954319431451596367072419481844769), (-387069283994005020319227948137243595319885390203365789112 / 349379465359371639006642318106477150532122357473160614923), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(119941803843766847785804406867237308267447484602212 / 990173937759478857566700889865251524679699764453343), (-962400671796460546757282745047917382337015835933958 / 2970521813278436572700102669595754574039099293360029), (-875665181236660139839521834514974753462905371754868 / 990173937759478857566700889865251524679699764453343), (76513347913309985461521495872043763142663901266383 / 990173937759478857566700889865251524679699764453343), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(195314986230313698334220333529271142314421519 / 679071827041941018173889076181579750285283604), (419123235125777758926279550702916040095508641 / 12223292886754938327130003371268435505135104872), (516620017490490207657894348485648592583229135 / 2037215481125823054521667228544739250855850812), (939245091506853894916515484801477633295493323 / 8148861924503292218086668914178957003423403248), (-143021512431600477192683756622905146359608117 / 8148861924503292218086668914178957003423403248), 0, 0, 0, 0, 0, 0, 0],
  ![(1811877281114823618349420095351540074354 / 3821540804474953610122690404992415618041), (197474390150077484280366644739903970099 / 3821540804474953610122690404992415618041), (509412198793257852386185192206395025475 / 3821540804474953610122690404992415618041), (543925650112671520180129531897177948436 / 3821540804474953610122690404992415618041), (34235715976631395165850965028603113864 / 3821540804474953610122690404992415618041), (2868035580068340510730897121269167289915 / 3821540804474953610122690404992415618041), 0, 0, 0, 0, 0, 0],
  ![(-152438554035250133801136889400924 / 673208220558333996413931095649023), (90672337087880422326261812076056 / 673208220558333996413931095649023), (-99980872472861022611553034139925 / 673208220558333996413931095649023), (-20430331459781462651255084932038 / 673208220558333996413931095649023), (-52463499548145177681310232782060 / 673208220558333996413931095649023), (-407988702464931557146032404570221 / 673208220558333996413931095649023), (-59994820743749938791278562642311 / 673208220558333996413931095649023), 0, 0, 0, 0, 0],
  ![(-1121563155940342130796688 / 7323623296747635808619611), (226110096320200742209041 / 7323623296747635808619611), (-7492059782719963807100963 / 14647246593495271617239222), (653499326372212378582465 / 7323623296747635808619611), (-424824783996151542791981 / 563355638211356600663047), (-11909155694107014855434297 / 14647246593495271617239222), (-3126155550699434803461339 / 14647246593495271617239222), (16654681570337646967878523 / 14647246593495271617239222), 0, 0, 0, 0],
  ![(13339287316993735 / 123633918401546947), (59968730129378299 / 494535673606187788), (-324964627294316905 / 989071347212375576), (99158623864243919 / 494535673606187788), (-123187159486268491 / 494535673606187788), (184200407072220213 / 989071347212375576), (422899695849938159 / 989071347212375576), (724532550227200193 / 989071347212375576), (139432751472697929 / 494535673606187788), 0, 0, 0],
  ![(235968283453 / 625223873334), (-260003387305 / 625223873334), (4856827606 / 104203978889), (431136063 / 3110566534), (-85328823259 / 625223873334), (424556403917 / 625223873334), (589477590667 / 625223873334), (-794329090465 / 625223873334), (-65011653501 / 208407957778), (-23427215745 / 208407957778), 0, 0],
  ![(-24593 / 621710), (-148031 / 2113814), (-2217477 / 10569070), (2123549 / 10569070), (-3681887 / 10569070), (-402 / 5284535), (156509 / 310855), (819482 / 1056907), (-325129 / 10569070), (2070859 / 2113814), (-119507 / 310855), 0]
]

def D : Fin 12 → ℚ := ![(18238248911296124259390454311074204811055825914347849551847187862294562799 / 18863128552952274632604498813304680090132625317162083581361358998666), (301810056847236394121671981012874881442122005074593337301781743978656 / 2155480809107359624843391417328317182524429731688713219634003009), (478995735357191027742975870517403818338762162597491826585334002 / 349379465359371639006642318106477150532122357473160614923), (349379465359371639006642318106477150532122357473160614923 / 990173937759478857566700889865251524679699764453343), (990173937759478857566700889865251524679699764453343 / 2716287308167764072695556304726319001141134416), (24446585773509876654260006742536871010270209744 / 3821540804474953610122690404992415618041), (3821540804474953610122690404992415618041 / 673208220558333996413931095649023), (673208220558333996413931095649023 / 87883479560971629703435332), (7323623296747635808619611 / 8407106451305192396), (494535673606187788 / 104203978889), (625223873334 / 310855), 10569070]

end MUB6.Certificate.GramData.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

open scoped BigOperators

def weights : Matrix (Fin 12) (Fin 12) ℤ := ![
  ![3616397, -219419, 1005407, 842091, 186248, 5630326, 3598595, -2799721, -212971, 17130, 919824, -418081],
  ![-219419, 858064, -20456, -237640, 8632, -668374, -719533, 1972640, 472837, -55599, -551864, -740155],
  ![1005407, -20456, 3980209, -871566, 1228704, 3015305, -741592, -4624965, -846239, -3742225, 946245, -2217477],
  ![842091, -237640, -871566, 1225103, -1032886, 1787740, 2550956, 1845322, 193740, 3000641, -537616, 2123549],
  ![186248, 8632, 1228704, -1032886, 2523431, 415506, -2373762, -4715938, -791330, -4758384, 1140990, -3681887],
  ![5630326, -668374, 3015305, 1787740, 415506, 14075688, 6490324, -6536077, -885101, 729531, 1366079, -804],
  ![3598595, -719533, -741592, 2550956, -2373762, 6490324, 11111814, 2309105, -369038, 7029198, -149445, 5321306],
  ![-2799721, 1972640, -4624965, 1845322, -4715938, -6536077, 2309105, 20933543, 2515724, 11792046, -5705771, 8194820],
  ![-212971, 472837, -846239, 193740, -791330, -885101, -369038, 2515724, 1454109, 1090081, -502420, -325129],
  ![17130, -55599, -3742225, 3000641, -4758384, 729531, 7029198, 11792046, 1090081, 14915142, -4206760, 10354295],
  ![919824, -551864, 946245, -537616, 1140990, 1366079, -149445, -5705771, -502420, -4206760, 3573400, -4063238],
  ![-418081, -740155, -2217477, 2123549, -3681887, -804, 5321306, 8194820, -325129, 10354295, -4063238, 10569070]
]

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (1, 1, 1, 2), m = 5, exponent = 14.
-/

namespace MUB6.Certificate.GramData.Block0

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 5) (Fin 5) ℚ := ![
  ![7856995, -2793048, 8971673, 4076125, -23581960],
  ![-2793048, 5486181, -1693736, -2967341, 9048932],
  ![8971673, -1693736, 37455549, -242661, -37895129],
  ![4076125, -2967341, -242661, 7655001, -9254062],
  ![-23581960, 9048932, -37895129, -9254062, 86753990]
]

def entries : Matrix (Fin 5) (Fin 5) ℚ := ![
  ![0, 0, 0, 0, 0],
  ![(1603752121147568130199833465 / 40829555837800662670634310286), 0, 0, 0, 0],
  ![(-62916225621601789934 / 3499499328906931120789), (562467881435179530688 / 10498497986720793362367), 0, 0, 0],
  ![(67695593783615 / 289232108352073), (-86844646839403 / 289232108352073), (-185867841615694 / 289232108352073), 0, 0],
  ![(-2358196 / 8675399), (4524466 / 43376995), (-37895129 / 86753990), (-4627031 / 43376995), 0]
]

def D : Fin 5 → ℚ := ![(43674396936336248004625370017787053 / 40829555837800662670634310286), (40829555837800662670634310286 / 10498497986720793362367), (10498497986720793362367 / 578464216704146), (289232108352073 / 43376995), 86753990]

end MUB6.Certificate.GramData.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key7 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key18 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key20 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key21 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key23 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key29 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key31 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key32 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key33 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key35 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key43 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key44 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key45 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key46 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key47 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key48 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key70 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key84 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key100 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key101 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key109 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key111 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key112 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key114 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key115 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key133 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key134 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key137 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key149 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key151 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
def key171 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key172 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key174 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key175 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key176 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key179 : Key := ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key185 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key193 : Key := ⟨0, 0, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key195 : Key := ⟨0, 0, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key196 : Key := ⟨0, 0, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key200 : Key := ⟨0, 0, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key202 : Key := ⟨0, 0, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key206 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key209 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key212 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key214 : Key := ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key218 : Key := ⟨0, 0, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key223 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key226 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key228 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key234 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key236 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key237 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key239 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key240 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key242 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key243 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key244 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key245 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key246 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key248 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key249 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key254 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key255 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (1, 1), (1, 1), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1280 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key1281 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key1284 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key1287 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key1288 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1289 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1291 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1292 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1294 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1295 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key1296 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1297 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1298 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1299 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1300 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key1301 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key1302 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key1303 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1304 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key1305 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key1306 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key1307 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key1308 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 1), (3, 2)]⟩
def key1309 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 2), (3, 1)]⟩
def key1311 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key1312 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key1314 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (0, 1), (3, 1)]⟩
def key1316 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 1), (2, 1)]⟩
def key1317 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key1320 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key1321 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key1324 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key1325 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key1326 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, -1), (2, 1)]⟩
def key1327 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key1329 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (0, 1), (1, -1), (2, 1)]⟩
def key1330 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key1331 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key1332 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key1333 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key1334 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (0, 0), (3, 2)]⟩
def key1336 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key1338 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key1339 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 1), (1, 0), (2, 1)]⟩
def key1340 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key1341 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key1342 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key1343 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key1344 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key1345 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 1), (1, -1), (2, 1)]⟩
def key1346 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key1347 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key1348 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key1351 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 0), (2, 1)]⟩
def key1352 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key1353 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key1354 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, -1), (2, 1)]⟩
def key1355 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key1356 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key1361 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 0), (1, 3)]⟩
def key1362 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key1365 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key1366 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key1367 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key1370 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key1373 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key1375 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key1376 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key1379 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 1), (0, 1), (1, -1), (1, 1)]⟩
def key1382 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key1383 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1384 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1386 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1387 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1389 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1390 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key1391 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1392 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1393 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1394 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1395 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key1396 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key1397 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key1398 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1399 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key1400 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key1401 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key1406 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1409 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 2), (1, 0), (2, 1)]⟩
def key1415 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 0), (3, 3)]⟩
def key1416 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (3, 2)]⟩
def key1417 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 2), (3, 1)]⟩
def key1419 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 2)]⟩
def key1420 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 1)]⟩
def key1422 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (0, 1), (3, 1)]⟩
def key1424 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, 1)]⟩
def key1425 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 2), (2, 0)]⟩
def key1427 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 1), (2, 0)]⟩
def key1428 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 1), (1, 2)]⟩
def key1429 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (1, 1), (1, 1), (1, 1)]⟩
def key1434 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, 1)]⟩
def key1438 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 2), (1, -1), (2, 1)]⟩
def key1442 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key1443 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key1444 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, -2), (2, 1)]⟩
def key1445 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key1447 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (0, 1), (1, -2), (2, 1)]⟩
def key1448 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key1449 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key1450 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key1451 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key1452 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (0, 0), (3, 2)]⟩
def key1453 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (0, 1), (3, 1)]⟩
def key1454 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩
def key1456 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key1457 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 1), (1, 0), (2, 1)]⟩
def key1458 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩
def key1459 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩
def key1460 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩
def key1464 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key1465 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key1466 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 1), (1, -2), (2, 1)]⟩
def key1467 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key1468 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key1469 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key1471 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (0, 0), (3, 1)]⟩
def key1472 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 0), (2, 1)]⟩
def key1473 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key1474 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -2), (1, 0), (1, 0), (1, 1)]⟩
def key1476 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (1, 0), (2, 1)]⟩
def key1478 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, 0), (1, -1), (2, 1)]⟩
def key1480 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, -2), (2, 1)]⟩
def key1481 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key1482 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key1487 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 0), (1, 3)]⟩
def key1488 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key1491 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key1492 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key1493 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key1496 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key1502 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (1, 1), (1, 2)]⟩
def key1504 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 2), (1, 0), (1, 1)]⟩
def key1512 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 0), (1, -2), (1, 3)]⟩
def key1514 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩
def key1515 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩
def key1519 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 1), (0, 1), (1, -2), (1, 1)]⟩
def key1524 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1525 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1526 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1527 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1529 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1530 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key1531 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1532 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1533 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1534 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1535 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 0), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1536 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1537 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key1538 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 1), (3, 2)]⟩
def key1539 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 2), (3, 1)]⟩
def key1540 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key1541 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key1542 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key1544 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (0, 1), (3, 1)]⟩
def key1545 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key1546 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩
def key1547 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key1548 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 0), (2, 1)]⟩
def key1549 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key1550 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key1551 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key1552 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key1554 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key1555 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key1556 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, -1), (2, 1)]⟩
def key1557 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key1559 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (0, 1), (1, -1), (2, 1)]⟩
def key1560 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key1561 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key1562 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key1563 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key1564 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 3)]⟩
def key1565 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 1), (3, 2)]⟩
def key1566 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 2), (3, 1)]⟩
def key1567 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 3)]⟩
def key1568 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 2)]⟩
def key1569 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 1)]⟩
def key1571 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (0, 1), (3, 1)]⟩
def key1572 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
def key1573 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 1)]⟩
def key1574 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 2), (2, 0)]⟩
def key1575 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 0), (2, 1)]⟩
def key1576 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 1), (2, 0)]⟩
def key1577 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 2)]⟩
def key1578 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (1, 1), (1, 1), (1, 1)]⟩
def key1589 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key1591 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key1592 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key1593 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, -2), (2, 1)]⟩
def key1594 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key1596 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (0, 1), (1, -2), (2, 1)]⟩
def key1597 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key1598 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key1599 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key1600 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key1604 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 2)]⟩
def key1605 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 1)]⟩
def key1609 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 1)]⟩
def key1617 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 2)]⟩
def key1618 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 1)]⟩
def key1620 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 3)]⟩
def key1622 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 2)]⟩
def key1623 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 2), (2, -1)]⟩
def key1624 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, -1), (2, 1)]⟩
def key1625 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, 1), (2, -1)]⟩
def key1629 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 3)]⟩
def key1631 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 2)]⟩
def key1632 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -2)]⟩
def key1633 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, -2), (2, 1)]⟩
def key1634 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -2)]⟩
def key1637 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩
def key1638 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩
def key1639 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, -3), (2, 1)]⟩
def key1640 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
def key1641 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, -3), (2, 1)]⟩
def key1642 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩
def key1645 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (0, 0), (3, 2)]⟩
def key1646 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (0, 1), (3, 1)]⟩
def key1647 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
def key1648 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 1)]⟩
def key1649 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 2), (2, 0)]⟩
def key1650 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 0), (2, 1)]⟩
def key1651 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 1), (2, 0)]⟩
def key1652 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (3, 2)]⟩
def key1653 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (0, 1), (3, 1)]⟩
def key1654 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 2)]⟩
def key1656 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 2), (2, 0)]⟩
def key1657 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 2)]⟩
def key1658 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 2), (2, -1)]⟩
def key1659 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 1), (1, -1), (2, 1)]⟩
def key1660 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, 1), (1, 1), (2, -1)]⟩
def key1661 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 2)]⟩
def key1662 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 1), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1665 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 2)]⟩
def key1666 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -2)]⟩
def key1667 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 1), (1, -2), (2, 1)]⟩
def key1668 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, 1), (1, 1), (2, -2)]⟩
def key1669 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 2)]⟩
def key1670 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 1), (1, 1)]⟩
def key1671 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key1672 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key1673 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (2, 1)]⟩
def key1674 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key1677 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (0, 0), (3, 1)]⟩
def key1678 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 0), (2, 1)]⟩
def key1679 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key1680 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (0, 0), (3, 1)]⟩
def key1681 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 0), (2, 1)]⟩
def key1682 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key1683 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, -1), (2, 1)]⟩
def key1684 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key1685 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key1689 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, -2), (2, 1)]⟩
def key1690 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key1691 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key1692 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, -3), (2, 1)]⟩
def key1693 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key1699 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key1703 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key1714 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (1, 1), (1, 2)]⟩
def key1718 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (1, 1), (1, 1)]⟩
def key1722 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key1724 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key1725 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key1728 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 1), (0, 1), (1, -1), (1, 1)]⟩
def key1734 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (1, 1), (1, 2)]⟩
def key1737 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 2), (1, -1), (1, 1)]⟩
def key1740 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 0), (1, -2), (1, 3)]⟩
def key1742 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 1), (1, -2), (1, 2)]⟩
def key1743 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 2), (1, -2), (1, 1)]⟩
def key1747 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 1), (1, -2), (1, 1)]⟩
def key1752 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 1), (1, -3), (1, 2)]⟩
def key1753 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -3), (1, 1)]⟩
def key1757 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩
def key1762 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 2)]⟩
def key1763 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (0, 1), (3, 1)]⟩
def key1765 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key1766 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key1767 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 1)]⟩
def key1768 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key1769 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 2)]⟩
def key1771 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key1772 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key1773 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key1774 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 1)]⟩
def key1775 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key1776 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key1777 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key1778 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key1779 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key1780 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 1)]⟩
def key1781 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key1782 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key1783 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key1785 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 2)]⟩
def key1786 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (0, 1), (3, 1)]⟩
def key1787 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩
def key1788 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩
def key1789 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key1790 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 1)]⟩
def key1791 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1792 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩
def key1793 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩
def key1796 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key1797 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key1798 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 1)]⟩
def key1799 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key1800 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key1801 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key1803 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 2)]⟩
def key1804 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (0, 1), (3, 1)]⟩
def key1806 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 1)]⟩
def key1807 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 0)]⟩
def key1809 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 0)]⟩
def key1810 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 2)]⟩
def key1811 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (0, 1), (3, 1)]⟩
def key1813 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 1)]⟩
def key1814 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 0)]⟩
def key1815 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 2)]⟩
def key1816 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, -1)]⟩
def key1817 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 1)]⟩
def key1818 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, -1)]⟩
def key1819 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 2)]⟩
def key1820 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 1)]⟩
def key1823 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 2)]⟩
def key1824 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 2), (2, -2)]⟩
def key1825 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 1)]⟩
def key1826 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, 1), (1, 1), (2, -2)]⟩
def key1827 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 2)]⟩
def key1828 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 1)]⟩
def key1831 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 1)]⟩
def key1832 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key1836 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 1)]⟩
def key1837 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key1839 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 1)]⟩
def key1840 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key1841 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 1)]⟩
def key1842 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key1844 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 1)]⟩
def key1847 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 1)]⟩
def key1848 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key1853 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 0), (1, 2)]⟩
def key1856 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key1862 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (1, 0), (1, 2)]⟩
def key1865 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 1), (1, 0), (1, 1)]⟩
def key1868 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 0), (1, -1), (1, 2)]⟩
def key1870 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 1), (1, -1), (1, 1)]⟩
def key1878 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩
def key1880 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 1), (1, -2), (1, 1)]⟩
def key1885 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 0), (1, -3), (1, 2)]⟩
def key1887 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -3), (1, 1)]⟩
def key1892 : Key := ⟨0, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 1)]⟩
def key1894 : Key := ⟨0, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key1896 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 1)]⟩
def key1897 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key1898 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key1899 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 1)]⟩
def key1900 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key1901 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key1902 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 1)]⟩
def key1903 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 1)]⟩
def key1904 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key1905 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 1)]⟩
def key1911 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 1)]⟩
def key1912 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key1913 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key1914 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 1)]⟩
def key1916 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key1917 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 1)]⟩
def key1919 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1920 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 1)]⟩
def key1921 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key1922 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key1926 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 1)]⟩
def key1927 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key1928 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key1934 : Key := ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 0), (1, 0), (1, 1)]⟩
def key1938 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩
def key1941 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩
def key1945 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, -1), (1, 0), (1, 1)]⟩
def key1947 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, 0), (1, -1), (1, 1)]⟩
def key1954 : Key := ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 0), (1, -3), (1, 1)]⟩
def key1998 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key1999 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key2000 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key2003 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key2006 : Key := ⟨0, 1, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 0), (2, 1)]⟩
def key2007 : Key := ⟨0, 1, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2078 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 1), (2, 1)]⟩
def key2079 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 2), (2, 0)]⟩
def key2082 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 1), (0, 1), (2, 0)]⟩
def key2085 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key2087 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -1)]⟩
def key2091 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 0), (0, 0), (2, 1)]⟩
def key2092 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩
def key2095 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩
def key2098 : Key := ⟨0, 1, [(-1, -2), (-1, 3), (0, -1), (0, 0), (0, 0), (2, 0)]⟩
def key2099 : Key := ⟨0, 1, [(-1, -2), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -1)]⟩
def key2174 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 2)]⟩
def key2175 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 1), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2176 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 2), (2, 0)]⟩
def key2179 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 1), (0, 1), (2, 0)]⟩
def key2182 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, -1), (0, 0), (2, 2)]⟩
def key2183 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, -1), (0, 2), (2, 0)]⟩
def key2187 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩
def key2189 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -2)]⟩
def key2193 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, 1)]⟩
def key2194 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 1), (2, 0)]⟩
def key2200 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -2)]⟩
def key2203 : Key := ⟨0, 1, [(-1, -1), (-1, 3), (0, -2), (0, 0), (0, 0), (2, 0)]⟩
def key2206 : Key := ⟨0, 1, [(-1, -1), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key2267 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 2)]⟩
def key2268 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 1)]⟩
def key2274 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (2, 2)]⟩
def key2275 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 1), (2, 1)]⟩
def key2279 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 2), (2, -1)]⟩
def key2281 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 1), (0, 1), (2, -1)]⟩
def key2284 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, -1), (0, -1), (2, 2)]⟩
def key2285 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, -1), (0, 2), (2, -1)]⟩
def key2287 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 2), (2, -2)]⟩
def key2289 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 1), (0, 1), (2, -2)]⟩
def key2292 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -3)]⟩
def key2294 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -3)]⟩
def key2299 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 1)]⟩
def key2302 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2305 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, 0), (0, 1), (2, -1)]⟩
def key2310 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (2, -2)]⟩
def key2313 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -3)]⟩
def key2318 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, -2), (0, 0), (0, 0), (2, -1)]⟩
def key2321 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, -1), (0, 0), (0, 0), (2, -2)]⟩
def key2324 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 0)]⟩
def key2328 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, -1), (0, 1), (2, 0)]⟩
def key2330 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, 0), (0, 1), (2, -1)]⟩
def key2333 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -1), (0, 0), (0, 1), (2, -2)]⟩
def key2336 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -3)]⟩
def key2340 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 0)]⟩
def key2341 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 0)]⟩
def key2343 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, -1)]⟩
def key2345 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, -1), (0, -1), (2, 0)]⟩
def key2346 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, -1), (0, 0), (2, -1)]⟩
def key2347 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, 0), (0, 0), (2, -2)]⟩
def key2349 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -3)]⟩
def key2353 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2354 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2356 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2358 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2359 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2361 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2362 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2363 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2364 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2366 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2367 : Key := ⟨1, 1, [(-3, -3), (0, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key2369 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2370 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2371 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2372 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2373 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2374 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2375 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2376 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2377 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2378 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2379 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2380 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2381 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2382 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2383 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2384 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key2385 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2386 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key2387 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key2388 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key2389 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key2390 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key2391 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key2392 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key2393 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key2394 : Key := ⟨1, 1, [(-3, -2), (0, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key2395 : Key := ⟨1, 1, [(-3, -2), (0, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key2397 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2398 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2399 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2400 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2401 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2402 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2403 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2404 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2405 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2406 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2407 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2408 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2409 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2410 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2411 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2414 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key2419 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key2426 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key2428 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key2430 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key2431 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2432 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key2433 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key2434 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key2435 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key2436 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key2437 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key2439 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key2440 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key2441 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key2443 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key2444 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 2), (1, -1), (1, -1), (1, 1)]⟩
def key2445 : Key := ⟨1, 1, [(-3, -1), (0, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key2448 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2449 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2452 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2456 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2457 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2460 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2464 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key2465 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key2468 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩
def key2472 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key2473 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key2474 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key2475 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2476 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key2477 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key2478 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key2479 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key2480 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key2481 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key2482 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key2483 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key2484 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key2487 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩
def key2494 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key2496 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩
def key2497 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key2498 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key2499 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key2500 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key2501 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key2502 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key2503 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key2505 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key2506 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key2507 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key2509 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key2510 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 2), (1, -1), (1, -1), (1, 1)]⟩
def key2513 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩
def key2514 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩
def key2515 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
def key2517 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩
def key2519 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩
def key2520 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩
def key2521 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩
def key2522 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩
def key2523 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩
def key2524 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩
def key2525 : Key := ⟨1, 1, [(-3, 0), (0, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key2526 : Key := ⟨1, 1, [(-3, 0), (0, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key2527 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key2528 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key2529 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key2530 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key2531 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩
def key2532 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩
def key2533 : Key := ⟨1, 1, [(-3, 1), (0, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key2534 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key2535 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key2536 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key2537 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key2538 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key2539 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key2540 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key2541 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key2542 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key2543 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key2544 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key2545 : Key := ⟨1, 1, [(-3, 1), (0, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key2551 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key2552 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key2553 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key2554 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key2555 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key2557 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key2558 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key2559 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key257 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key260 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key261 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key262 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key265 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key266 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key267 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key268 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key269 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key270 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key271 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key272 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key273 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key274 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key275 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key281 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 0), (1, 3)]⟩
def key282 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key285 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key290 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key291 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key294 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key295 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key300 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key302 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key303 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key305 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key306 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key308 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key309 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key310 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key311 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key314 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 0), (3, 3)]⟩
def key316 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 2)]⟩
def key317 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 1)]⟩
def key319 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
def key320 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 2), (2, 0)]⟩
def key322 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 1), (1, 2)]⟩
def key323 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (1, 1), (1, 1), (1, 1)]⟩
def key328 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key330 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key333 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key334 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key335 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩
def key336 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key337 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩
def key338 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩
def key340 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key342 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key343 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key344 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key350 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 0), (1, 3)]⟩
def key351 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key353 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key354 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key367 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 0), (1, -2), (1, 3)]⟩
def key371 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩
def key375 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key378 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key383 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2560 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key2561 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩
def key2562 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩
def key2563 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key2564 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key2565 : Key := ⟨1, 1, [(-3, 1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key2566 : Key := ⟨1, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key2567 : Key := ⟨1, 1, [(-3, 2), (0, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩
def key2568 : Key := ⟨1, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key2569 : Key := ⟨1, 1, [(-3, 2), (0, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key2570 : Key := ⟨1, 1, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key2571 : Key := ⟨1, 1, [(-3, 2), (0, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key2572 : Key := ⟨1, 1, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key2573 : Key := ⟨1, 1, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩
def key2574 : Key := ⟨1, 1, [(-3, 2), (0, -1), (0, -1), (1, -1), (1, 0), (1, 1)]⟩
def key2575 : Key := ⟨1, 1, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key2576 : Key := ⟨1, 1, [(-3, 2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key2577 : Key := ⟨1, 1, [(-3, 2), (0, -1), (0, 0), (1, -1), (1, -1), (1, 1)]⟩
def key2578 : Key := ⟨1, 1, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key2579 : Key := ⟨1, 1, [(-3, 2), (0, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩
def key2580 : Key := ⟨1, 1, [(-3, 2), (0, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key2583 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2586 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2587 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2588 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2589 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2591 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2592 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2593 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2594 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2595 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2596 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2597 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key2598 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key2599 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key2600 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key2601 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (1, 0), (1, 0), (1, 2)]⟩
def key2602 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 0), (1, 0), (1, 1), (1, 1)]⟩
def key2603 : Key := ⟨1, 1, [(-2, -3), (-1, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key2604 : Key := ⟨1, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key2605 : Key := ⟨1, 1, [(-2, -3), (-1, 2), (0, 0), (1, 0), (1, 0), (1, 1)]⟩
def key2606 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2607 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2608 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2609 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2610 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2611 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2612 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2613 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2614 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2615 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2616 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2617 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2618 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2619 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2620 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2621 : Key := ⟨1, 1, [(-2, -2), (-1, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2622 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key2623 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key2624 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key2625 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key2626 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key2627 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key2628 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 1), (2, 1)]⟩
def key2629 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key2630 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key2631 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key2632 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key2633 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key2634 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key2636 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key2637 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key2638 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key2640 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key2641 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key2642 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key2643 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key2644 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key2645 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key2646 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key2647 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key2648 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key2649 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key2650 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key2651 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key2652 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key2653 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key2654 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key2655 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key2657 : Key := ⟨1, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key2658 : Key := ⟨1, 1, [(-2, -2), (-1, 2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key2659 : Key := ⟨1, 1, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key2660 : Key := ⟨1, 1, [(-2, -2), (-1, 2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key2661 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2662 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2663 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2664 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2665 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2666 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2667 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2668 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2669 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2670 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2671 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2672 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2673 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2674 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2675 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2676 : Key := ⟨1, 1, [(-2, -1), (-1, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2679 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key2684 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2691 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key2693 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key2696 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (0, 0), (3, 3)]⟩
def key2697 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 0), (2, 3)]⟩
def key2698 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 2)]⟩
def key2699 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 1)]⟩
def key2700 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 3), (2, 0)]⟩
def key2701 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
def key2702 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, 1)]⟩
def key2703 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 2), (2, 0)]⟩
def key2704 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 1), (2, 0)]⟩
def key2705 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 0), (1, 3)]⟩
def key2706 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (1, 0), (1, 1), (1, 2)]⟩
def key2707 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -2), (1, 1), (1, 1), (1, 1)]⟩
def key2710 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 2)]⟩
def key2717 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key2719 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (1, -1), (1, 1), (1, 2)]⟩
def key2720 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key2722 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key2723 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key2724 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key2726 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key2728 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key2729 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key2730 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key2732 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key2733 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 2), (1, -1), (1, -1), (1, 1)]⟩
def key2734 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩
def key2735 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩
def key2736 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key2737 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩
def key2738 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩
def key2739 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩
def key2745 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key2746 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key2747 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key2748 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key2749 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key2752 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key2753 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, -2), (1, 0), (1, 0), (1, 1)]⟩
def key2754 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key2755 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -1)]⟩
def key2756 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, -1), (1, -1), (1, 0), (1, 1)]⟩
def key2757 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key2758 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key2759 : Key := ⟨1, 1, [(-2, -1), (-1, 2), (0, 0), (1, -1), (1, -1), (1, 1)]⟩
def key2762 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2763 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2765 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2766 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2767 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2768 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2770 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key2771 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key2772 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2773 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2774 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key2775 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2776 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key2777 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key2778 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key2779 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key2780 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key2781 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key2782 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩
def key2783 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key2784 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key2785 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key2786 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key2787 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key2788 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key2789 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2790 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key2791 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key2792 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key2793 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key2794 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key2795 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key2796 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key2797 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key2798 : Key := ⟨1, 1, [(-2, 0), (-1, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key2799 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 3)]⟩
def key2800 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 3)]⟩
def key2801 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 2)]⟩
def key2802 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 1)]⟩
def key2803 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 3), (2, 0)]⟩
def key2804 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
def key2805 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 1)]⟩
def key2806 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 2), (2, 0)]⟩
def key2807 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 1), (2, 0)]⟩
def key2808 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 3)]⟩
def key2809 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 2)]⟩
def key2810 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -2), (1, 1), (1, 1), (1, 1)]⟩
def key2813 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2820 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key2822 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩
def key2823 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key2824 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key2825 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key2826 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key2827 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key2828 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key2829 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key2831 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key2832 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key2833 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key2835 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key2836 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 2), (1, -1), (1, -1), (1, 1)]⟩
def key2839 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 2)]⟩
def key2840 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 1)]⟩
def key2843 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 1)]⟩
def key2847 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (1, 0), (1, 1), (1, 2)]⟩
def key2848 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (1, 1), (1, 1), (1, 1)]⟩
def key2851 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 2)]⟩
def key2852 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 1)]⟩
def key2854 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 3)]⟩
def key2855 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 3), (2, -1)]⟩
def key2856 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 2)]⟩
def key2857 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 2), (2, -1)]⟩
def key2858 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, 1), (2, -1)]⟩
def key2859 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 3)]⟩
def key2860 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 2)]⟩
def key2864 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 3)]⟩
def key2865 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -2)]⟩
def key2866 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 2)]⟩
def key2867 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -2)]⟩
def key2868 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -2)]⟩
def key2869 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 3)]⟩
def key2870 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 2)]⟩
def key2874 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩
def key2875 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩
def key2876 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
def key2878 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩
def key2880 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩
def key2881 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩
def key2882 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩
def key2883 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩
def key2884 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩
def key2885 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩
def key2886 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
def key2887 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 1)]⟩
def key2888 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 2), (2, 0)]⟩
def key2889 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 1), (2, 0)]⟩
def key2890 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (1, 0), (1, 0), (1, 2)]⟩
def key2891 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -3), (1, 0), (1, 1), (1, 1)]⟩
def key2892 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 2)]⟩
def key2893 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 1)]⟩
def key2894 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 2), (2, 0)]⟩
def key2895 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 2)]⟩
def key2896 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 2), (2, -1)]⟩
def key2897 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (0, 1), (1, 1), (2, -1)]⟩
def key2898 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 2)]⟩
def key2899 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 1), (1, 1)]⟩
def key2902 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 2)]⟩
def key2903 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -2)]⟩
def key2904 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, 1), (1, 1), (2, -2)]⟩
def key2905 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 2)]⟩
def key2906 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 1), (1, 1)]⟩
def key2908 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key2909 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key2910 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key2911 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (1, -3), (1, 0), (1, 2)]⟩
def key2912 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (1, -3), (1, 1), (1, 1)]⟩
def key2913 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key2914 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key2916 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key2917 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -3), (1, 0), (1, 0), (1, 1)]⟩
def key2918 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key2919 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key2920 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key2922 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key2923 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key2924 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (1, -1), (1, -1), (1, 1)]⟩
def key2925 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key2926 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, 0), (1, -3), (1, 0), (1, 1)]⟩
def key2927 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key2928 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key2929 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key2930 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key2931 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key2932 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩
def key2933 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩
def key2934 : Key := ⟨1, 1, [(-2, 1), (-1, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key2935 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key2936 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key2937 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key2938 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key2939 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key2940 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key2941 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key2942 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key2943 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2944 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key2945 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key2947 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩
def key2948 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩
def key2949 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key2950 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (0, 1), (1, 1), (2, 0)]⟩
def key2951 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩
def key2952 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩
def key2958 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key2959 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key2960 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key2961 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key2962 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key2964 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key2965 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
def key2966 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 1)]⟩
def key2967 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 0)]⟩
def key2968 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 0)]⟩
def key2969 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (1, 0), (1, 0), (1, 2)]⟩
def key2970 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -3), (1, 0), (1, 1), (1, 1)]⟩
def key2971 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 2)]⟩
def key2972 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 1)]⟩
def key2973 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 0)]⟩
def key2974 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 2)]⟩
def key2975 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, -1)]⟩
def key2976 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (0, 1), (1, 1), (2, -1)]⟩
def key2977 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 2)]⟩
def key2978 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 1)]⟩
def key2981 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 2)]⟩
def key2982 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 2), (2, -2)]⟩
def key2983 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, 1), (1, 1), (2, -2)]⟩
def key2984 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 2)]⟩
def key2985 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 1)]⟩
def key2987 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key2989 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key2990 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩
def key2991 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩
def key2992 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key2993 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key2994 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key2995 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key2996 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -3), (1, 0), (1, 0), (1, 1)]⟩
def key2997 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key2998 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key3000 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key3001 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key3002 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key3003 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, 0), (1, -3), (1, 0), (1, 1)]⟩
def key3004 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key3005 : Key := ⟨1, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key3006 : Key := ⟨1, 1, [(-2, 2), (-1, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩
def key3007 : Key := ⟨1, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key3008 : Key := ⟨1, 1, [(-2, 2), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key3009 : Key := ⟨1, 1, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key3010 : Key := ⟨1, 1, [(-2, 2), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key3011 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key3012 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 1)]⟩
def key3014 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩
def key3015 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, -1), (1, -1), (1, 0), (1, 1)]⟩
def key3016 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key3017 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key3018 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, 0), (1, -1), (1, -1), (1, 1)]⟩
def key3019 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key3020 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -3), (1, 0), (1, 0), (1, 1)]⟩
def key3021 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key3022 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key3023 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key3025 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key3026 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key3027 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (1, -1), (1, -1), (1, 1)]⟩
def key3028 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key3029 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩
def key3030 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key3034 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩
def key3037 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩
def key3038 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩
def key3040 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩
def key3042 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩
def key3043 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩
def key3044 : Key := ⟨1, 1, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩
def key3047 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩
def key3048 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩
def key3052 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩
def key3053 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩
def key3055 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩
def key3058 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩
def key3061 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩
def key3062 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 2), (2, 1)]⟩
def key3067 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -1)]⟩
def key3068 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩
def key3070 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, 1)]⟩
def key3071 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key3073 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -1)]⟩
def key3074 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -1)]⟩
def key3075 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩
def key3076 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩
def key3096 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 1), (2, 2)]⟩
def key3097 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 2), (2, 1)]⟩
def key3104 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -2)]⟩
def key3107 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 1), (2, 1)]⟩
def key3108 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, 0)]⟩
def key3111 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -2)]⟩
def key3112 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -2)]⟩
def key3113 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, 0)]⟩
def key3115 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -2)]⟩
def key3117 : Key := ⟨1, 1, [(-1, -1), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -2)]⟩
def key3120 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 1), (2, 2)]⟩
def key3121 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 2), (2, 1)]⟩
def key3129 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -3)]⟩
def key3130 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -3)]⟩
def key3132 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 1), (2, 1)]⟩
def key3133 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 2), (2, 0)]⟩
def key3135 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, -1)]⟩
def key3137 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, -2)]⟩
def key3139 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -3)]⟩
def key3140 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -3)]⟩
def key3141 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (1, 1), (2, 0)]⟩
def key3144 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -3)]⟩
def key3145 : Key := ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (1, 1), (2, 0)]⟩
def key3146 : Key := ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -2), (1, 1), (2, -1)]⟩
def key3147 : Key := ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -1), (1, 1), (2, -2)]⟩
def key3148 : Key := ⟨1, 1, [(-1, 0), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key384 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key385 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key386 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key387 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key388 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key391 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key392 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key393 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key394 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key396 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key397 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key398 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key399 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key402 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key403 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key404 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (0, 0), (3, 3)]⟩
def key405 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 3)]⟩
def key406 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 2)]⟩
def key407 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 1)]⟩
def key408 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 3), (2, 0)]⟩
def key409 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
def key410 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 1), (1, 2), (2, 0)]⟩
def key412 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 2)]⟩
def key413 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (1, 1), (1, 1), (1, 1)]⟩
def key416 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key417 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key418 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key420 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key423 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key424 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key426 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 2)]⟩
def key435 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 2)]⟩
def key436 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 1)]⟩
def key438 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 3)]⟩
def key439 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 1)]⟩
def key441 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 3), (2, -1)]⟩
def key442 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (2, 2)]⟩
def key444 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 2), (2, -1)]⟩
def key448 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 3)]⟩
def key449 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -2)]⟩
def key450 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (2, 2)]⟩
def key457 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩
def key458 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key463 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
def key467 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (2, 2)]⟩
def key468 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 2), (2, 0)]⟩
def key469 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (2, 2)]⟩
def key470 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key471 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (0, 0), (1, 2), (2, -1)]⟩
def key472 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 2)]⟩
def key473 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -2), (1, -1), (1, 1), (1, 1)]⟩
def key475 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (2, 2)]⟩
def key477 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -2)]⟩
def key478 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 2)]⟩
def key479 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (1, -2), (1, 1), (1, 1)]⟩
def key480 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key481 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key495 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key508 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (1, 1), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key516 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key518 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key521 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key523 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key538 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 0), (1, -2), (1, 3)]⟩
def key543 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 2), (1, -2), (1, 1)]⟩
def key552 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (1, -3), (1, 2)]⟩
def key553 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (1, -2), (1, 1)]⟩
def key554 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -3), (1, 1)]⟩
def key568 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key569 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key570 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key571 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key572 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key573 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key574 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key575 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key576 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key578 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 0), (2, 2)]⟩
def key579 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key580 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 0), (1, 2)]⟩
def key581 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, -2), (1, 0), (1, 1), (1, 1)]⟩
def key583 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key585 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key586 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key587 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key589 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
def key593 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 2)]⟩
def key594 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 2), (2, 0)]⟩
def key595 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, -1), (2, 2)]⟩
def key596 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key597 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (0, 0), (1, 2), (2, -1)]⟩
def key598 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 0), (1, 2)]⟩
def key599 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 1)]⟩
def key601 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, -2), (2, 2)]⟩
def key603 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 2), (2, -2)]⟩
def key604 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 0), (1, 2)]⟩
def key605 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 1)]⟩
def key606 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key607 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key620 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 0), (1, 2)]⟩
def key628 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, -1), (0, 0), (1, 0), (1, 2)]⟩
def key630 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 0), (1, -1), (1, 2)]⟩
def key631 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 0), (1, 0), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key646 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 0), (1, -3), (1, 2)]⟩
def key647 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 0), (1, -2), (1, 1)]⟩
def key665 : Key := ⟨0, 0, [(-2, 2), (0, -3), (0, 0), (0, 0), (1, 0), (1, 1)]⟩
def key668 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩
def key672 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩
def key678 : Key := ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 0), (1, -2), (1, 1)]⟩
def key682 : Key := ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 0), (1, -3), (1, 1)]⟩
def key713 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key715 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key721 : Key := ⟨0, 0, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 0), (2, 1)]⟩
def key722 : Key := ⟨0, 0, [(-1, -3), (-1, 2), (0, 0), (0, 0), (0, 1), (2, 0)]⟩
def key738 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 2), (2, 0)]⟩
def key741 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 0), (2, 1)]⟩
def key742 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 1), (2, 0)]⟩
def key743 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key754 : Key := ⟨0, 0, [(-1, -2), (-1, 3), (0, -1), (0, 0), (0, 0), (2, 0)]⟩
def key755 : Key := ⟨0, 0, [(-1, -2), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key776 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key778 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key801 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 0), (2, 2)]⟩
def key811 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key817 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 2)]⟩
def key818 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 0), (0, 2), (2, 0)]⟩
def key825 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩
def key830 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, 1)]⟩
def key831 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 0), (0, 1), (2, 0)]⟩
def key836 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, 0), (0, 0), (2, 0)]⟩
def key839 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -1)]⟩
def key843 : Key := ⟨0, 0, [(-1, -1), (-1, 3), (0, -2), (0, 0), (0, 0), (2, 0)]⟩
def key844 : Key := ⟨0, 0, [(-1, -1), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key890 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key897 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (2, 2)]⟩
def key900 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 1)]⟩
def key902 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 2), (2, -1)]⟩
def key908 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 2), (2, -2)]⟩
def key913 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -2)]⟩
def key914 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 0), (0, 2), (2, -3)]⟩
def key921 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 1)]⟩
def key924 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 1)]⟩
def key928 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 0), (0, 1), (2, -1)]⟩
def key939 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -3)]⟩
def key944 : Key := ⟨0, 0, [(-1, 0), (-1, 3), (0, -2), (0, 0), (0, 0), (2, -1)]⟩
def key945 : Key := ⟨0, 0, [(-1, 0), (-1, 3), (0, -1), (0, 0), (0, 0), (2, -2)]⟩
def key951 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -2), (0, 0), (0, 0), (2, 0)]⟩
def key954 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key959 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -3), (0, 0), (0, 0), (2, 0)]⟩
def key960 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (2, 0)]⟩
def key962 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -2), (0, 0), (0, 0), (2, -1)]⟩
def key966 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -3)]⟩
def key971 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key972 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key975 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key976 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key977 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key978 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key979 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key983 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key984 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key993 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key994 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key995 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key997 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key999 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1001 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1005 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key1006 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1011 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key1012 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key1013 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key1015 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key1018 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (0, 1), (1, -1), (2, 1)]⟩
def key1019 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (0, 1), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1028 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1029 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1030 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key1032 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key1033 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1034 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1035 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1036 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1040 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key1041 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1067 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key1068 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key1069 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key1071 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key1075 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (0, 1), (1, -2), (2, 1)]⟩
def key1076 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key1085 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1086 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1090 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1106 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key1107 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key1111 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 1), (2, 1)]⟩
def key1119 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key1120 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key1121 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key1122 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, -1), (2, 1)]⟩
def key1123 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key1126 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (0, 1), (1, -1), (2, 1)]⟩
def key1127 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (0, 1), (1, 1), (2, -1)]⟩
def key1146 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key1147 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key1148 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key1150 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1154 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (0, 1), (1, -2), (2, 1)]⟩
def key1155 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (0, 1), (1, 1), (2, -2)]⟩
def key1161 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩
def key1162 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩
def key1163 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, -3), (2, 1)]⟩
def key1164 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
def key1168 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, -3), (2, 1)]⟩
def key1169 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩
def key1179 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key1181 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key1182 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 0), (2, 1)]⟩
def key1183 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key1189 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 0), (2, 2)]⟩
def key1191 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 2), (2, 0)]⟩
def key1193 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key1196 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, -1), (2, 2)]⟩
def key1197 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 0), (1, 2), (2, -1)]⟩
def key1199 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key1209 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, -2), (2, 2)]⟩
def key1210 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key1217 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key1218 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key1219 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, -3), (2, 1)]⟩
def key1220 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key1227 : Key := ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 0), (2, 1)]⟩
def key1228 : Key := ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key1231 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 0), (2, 1)]⟩
def key1232 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key1234 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, -1), (2, 1)]⟩
def key1235 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key1244 : Key := ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, -3), (2, 1)]⟩
def key1245 : Key := ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key1249 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1250 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1254 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1256 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1257 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1259 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1261 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1262 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (0, 0), (3, 2)]⟩
def key1263 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (0, 1), (3, 1)]⟩
def key1265 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key1266 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key1268 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key1269 : Key := ⟨0, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (0, 0), (3, 1)]⟩
def key1271 : Key := ⟨0, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key1276 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key1279 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end


