-- Prove2me | Definitions.Def_OAIQ106D199
-- name    : OAIQ106D199
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:30:50.451304+00:00
-- url     : https://prove2.me/theorems/2e9f8a8b-6a50-43be-a070-7cb271f5fa15
-- title:
--   Definitions bundle OAIQ106D199 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 688 declarations of OpenAI's Lean: 688 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entries`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_11`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_12`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows12_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_11`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_12`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_13`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows13_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_11`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_12`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_13`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_14`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows14_6` and 648 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Interpretation`, `MutuallyUnbiased_GramEntries_Block3Data`, `MutuallyUnbiased_GramEntries_Block3Row1`, `MutuallyUnbiased_GramEntries_Block3Row12`, `MutuallyUnbiased_GramEntries_Block3Row13`, `MutuallyUnbiased_GramEntries_Block3Row14`, `MutuallyUnbiased_GramEntries_Block3Row15`, `MutuallyUnbiased_GramEntries_Block3Row16`, `MutuallyUnbiased_GramEntries_Block3Row17`, `MutuallyUnbiased_GramEntries_Block3Row18`, `MutuallyUnbiased_GramEntries_Block3Row19`, `MutuallyUnbiased_GramEntries_Block3Row2`, `MutuallyUnbiased_GramEntries_Block3Row20`, `MutuallyUnbiased_GramEntries_Block3Row21`, `MutuallyUnbiased_GramEntries_Block3Row22`, `MutuallyUnbiased_GramEntries_Block3Row23`, `MutuallyUnbiased_GramEntries_Block3Row24`, `MutuallyUnbiased_GramEntries_Block3Row25`, `MutuallyUnbiased_GramEntries_Block3Row26`, `MutuallyUnbiased_GramEntries_Block3Row3`, `MutuallyUnbiased_GramEntries_Block3Row4`, `MutuallyUnbiased_GramEntries_Block3Row5`, `MutuallyUnbiased_GramEntries_Block3Row6`, `MutuallyUnbiased_GramEntries_Block3Row7`, `MutuallyUnbiased_GramEntries_Block3Row8`, `MutuallyUnbiased_GramEntries_Block3Row9`, `MutuallyUnbiased_GramEntries_Block4Data`, `MutuallyUnbiased_GramEntries_Block4Row0`, `MutuallyUnbiased_GramEntries_Block4Row1`, `MutuallyUnbiased_GramEntries_Block4Row10`, `MutuallyUnbiased_GramEntries_Block4Row11`, `MutuallyUnbiased_GramEntries_Block4Row12`, `MutuallyUnbiased_GramEntries_Block4Row13`, `MutuallyUnbiased_GramEntries_Block4Row14`, `MutuallyUnbiased_GramEntries_Block4Row15`, `MutuallyUnbiased_GramEntries_Block4Row16`, `MutuallyUnbiased_GramEntries_Block4Row17`, `MutuallyUnbiased_GramEntries_Block4Row18`, `MutuallyUnbiased_GramEntries_Block4Row19`, `MutuallyUnbiased_GramEntries_Block4Row2`, `MutuallyUnbiased_GramEntries_Block4Row20`, `MutuallyUnbiased_GramEntries_Block4Row21`, `MutuallyUnbiased_GramEntries_Block4Row3`, `MutuallyUnbiased_GramEntries_Block4Row4`, `MutuallyUnbiased_GramEntries_Block4Row5`, `MutuallyUnbiased_GramEntries_Block4Row6`, `MutuallyUnbiased_GramEntries_Block4Row7`, `MutuallyUnbiased_GramEntries_Block4Row8`, `MutuallyUnbiased_GramEntries_Block4Row9`, `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramEntries_Block5Row0`, `MutuallyUnbiased_GramEntries_Block5Row1`, `MutuallyUnbiased_GramEntries_Block5Row10`, `MutuallyUnbiased_GramEntries_Block5Row11`, `MutuallyUnbiased_GramFunctions_Block3`, `MutuallyUnbiased_GramFunctions_Block4`, `MutuallyUnbiased_GramFunctions_Block5`, `MutuallyUnbiased_TaoCertificate_TargetMerge0`.
--
--   **Imports.** It imports the bundles `OAIQ106D142`, `OAIQ106D144`, `OAIQ106D146`, `OAIQ106D147`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D182`, `OAIQ106D183`, `OAIQ106D194` and `OAIQ106D195` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D201`; the statements `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_0`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_1`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_11`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_12`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_13`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_15`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_3`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_5`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_6`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_7`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_24`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_25`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval2_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_18`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_20`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_21`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_11`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_5` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_24`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_25`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval2_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_18`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_20`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_21`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_11`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_5`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6` and `OAI.MUB6.complete_family_not_equivalent_tao`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D142
import Definitions.Def_OAIQ106D144
import Definitions.Def_OAIQ106D146
import Definitions.Def_OAIQ106D147
import Definitions.Def_OAIQ106D148
import Definitions.Def_OAIQ106D149
import Definitions.Def_OAIQ106D150
import Definitions.Def_OAIQ106D151
import Definitions.Def_OAIQ106D152
import Definitions.Def_OAIQ106D153
import Definitions.Def_OAIQ106D154
import Definitions.Def_OAIQ106D182
import Definitions.Def_OAIQ106D183
import Definitions.Def_OAIQ106D194
import Definitions.Def_OAIQ106D195

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

end Integer.Sparse
end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization

def entries : Fin 27 → Fin 27 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0, entry5_0, entry6_0, entry7_0, entry8_0, entry9_0, entry10_0, entry11_0, entry12_0, entry13_0, entry14_0, entry15_0, entry16_0, entry17_0, entry18_0, entry19_0, entry20_0, entry21_0, entry22_0, entry23_0, entry24_0, entry25_0, entry26_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1, entry5_1, entry6_1, entry7_1, entry8_1, entry9_1, entry10_1, entry11_1, entry12_1, entry13_1, entry14_1, entry15_1, entry16_1, entry17_1, entry18_1, entry19_1, entry20_1, entry21_1, entry22_1, entry23_1, entry24_1, entry25_1, entry26_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2, entry5_2, entry6_2, entry7_2, entry8_2, entry9_2, entry10_2, entry11_2, entry12_2, entry13_2, entry14_2, entry15_2, entry16_2, entry17_2, entry18_2, entry19_2, entry20_2, entry21_2, entry22_2, entry23_2, entry24_2, entry25_2, entry26_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3, entry5_3, entry6_3, entry7_3, entry8_3, entry9_3, entry10_3, entry11_3, entry12_3, entry13_3, entry14_3, entry15_3, entry16_3, entry17_3, entry18_3, entry19_3, entry20_3, entry21_3, entry22_3, entry23_3, entry24_3, entry25_3, entry26_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4, entry5_4, entry6_4, entry7_4, entry8_4, entry9_4, entry10_4, entry11_4, entry12_4, entry13_4, entry14_4, entry15_4, entry16_4, entry17_4, entry18_4, entry19_4, entry20_4, entry21_4, entry22_4, entry23_4, entry24_4, entry25_4, entry26_4],
  ![entry5_0, entry5_1, entry5_2, entry5_3, entry5_4, entry5_5, entry6_5, entry7_5, entry8_5, entry9_5, entry10_5, entry11_5, entry12_5, entry13_5, entry14_5, entry15_5, entry16_5, entry17_5, entry18_5, entry19_5, entry20_5, entry21_5, entry22_5, entry23_5, entry24_5, entry25_5, entry26_5],
  ![entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry7_6, entry8_6, entry9_6, entry10_6, entry11_6, entry12_6, entry13_6, entry14_6, entry15_6, entry16_6, entry17_6, entry18_6, entry19_6, entry20_6, entry21_6, entry22_6, entry23_6, entry24_6, entry25_6, entry26_6],
  ![entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry8_7, entry9_7, entry10_7, entry11_7, entry12_7, entry13_7, entry14_7, entry15_7, entry16_7, entry17_7, entry18_7, entry19_7, entry20_7, entry21_7, entry22_7, entry23_7, entry24_7, entry25_7, entry26_7],
  ![entry8_0, entry8_1, entry8_2, entry8_3, entry8_4, entry8_5, entry8_6, entry8_7, entry8_8, entry9_8, entry10_8, entry11_8, entry12_8, entry13_8, entry14_8, entry15_8, entry16_8, entry17_8, entry18_8, entry19_8, entry20_8, entry21_8, entry22_8, entry23_8, entry24_8, entry25_8, entry26_8],
  ![entry9_0, entry9_1, entry9_2, entry9_3, entry9_4, entry9_5, entry9_6, entry9_7, entry9_8, entry9_9, entry10_9, entry11_9, entry12_9, entry13_9, entry14_9, entry15_9, entry16_9, entry17_9, entry18_9, entry19_9, entry20_9, entry21_9, entry22_9, entry23_9, entry24_9, entry25_9, entry26_9],
  ![entry10_0, entry10_1, entry10_2, entry10_3, entry10_4, entry10_5, entry10_6, entry10_7, entry10_8, entry10_9, entry10_10, entry11_10, entry12_10, entry13_10, entry14_10, entry15_10, entry16_10, entry17_10, entry18_10, entry19_10, entry20_10, entry21_10, entry22_10, entry23_10, entry24_10, entry25_10, entry26_10],
  ![entry11_0, entry11_1, entry11_2, entry11_3, entry11_4, entry11_5, entry11_6, entry11_7, entry11_8, entry11_9, entry11_10, entry11_11, entry12_11, entry13_11, entry14_11, entry15_11, entry16_11, entry17_11, entry18_11, entry19_11, entry20_11, entry21_11, entry22_11, entry23_11, entry24_11, entry25_11, entry26_11],
  ![entry12_0, entry12_1, entry12_2, entry12_3, entry12_4, entry12_5, entry12_6, entry12_7, entry12_8, entry12_9, entry12_10, entry12_11, entry12_12, entry13_12, entry14_12, entry15_12, entry16_12, entry17_12, entry18_12, entry19_12, entry20_12, entry21_12, entry22_12, entry23_12, entry24_12, entry25_12, entry26_12],
  ![entry13_0, entry13_1, entry13_2, entry13_3, entry13_4, entry13_5, entry13_6, entry13_7, entry13_8, entry13_9, entry13_10, entry13_11, entry13_12, entry13_13, entry14_13, entry15_13, entry16_13, entry17_13, entry18_13, entry19_13, entry20_13, entry21_13, entry22_13, entry23_13, entry24_13, entry25_13, entry26_13],
  ![entry14_0, entry14_1, entry14_2, entry14_3, entry14_4, entry14_5, entry14_6, entry14_7, entry14_8, entry14_9, entry14_10, entry14_11, entry14_12, entry14_13, entry14_14, entry15_14, entry16_14, entry17_14, entry18_14, entry19_14, entry20_14, entry21_14, entry22_14, entry23_14, entry24_14, entry25_14, entry26_14],
  ![entry15_0, entry15_1, entry15_2, entry15_3, entry15_4, entry15_5, entry15_6, entry15_7, entry15_8, entry15_9, entry15_10, entry15_11, entry15_12, entry15_13, entry15_14, entry15_15, entry16_15, entry17_15, entry18_15, entry19_15, entry20_15, entry21_15, entry22_15, entry23_15, entry24_15, entry25_15, entry26_15],
  ![entry16_0, entry16_1, entry16_2, entry16_3, entry16_4, entry16_5, entry16_6, entry16_7, entry16_8, entry16_9, entry16_10, entry16_11, entry16_12, entry16_13, entry16_14, entry16_15, entry16_16, entry17_16, entry18_16, entry19_16, entry20_16, entry21_16, entry22_16, entry23_16, entry24_16, entry25_16, entry26_16],
  ![entry17_0, entry17_1, entry17_2, entry17_3, entry17_4, entry17_5, entry17_6, entry17_7, entry17_8, entry17_9, entry17_10, entry17_11, entry17_12, entry17_13, entry17_14, entry17_15, entry17_16, entry17_17, entry18_17, entry19_17, entry20_17, entry21_17, entry22_17, entry23_17, entry24_17, entry25_17, entry26_17],
  ![entry18_0, entry18_1, entry18_2, entry18_3, entry18_4, entry18_5, entry18_6, entry18_7, entry18_8, entry18_9, entry18_10, entry18_11, entry18_12, entry18_13, entry18_14, entry18_15, entry18_16, entry18_17, entry18_18, entry19_18, entry20_18, entry21_18, entry22_18, entry23_18, entry24_18, entry25_18, entry26_18],
  ![entry19_0, entry19_1, entry19_2, entry19_3, entry19_4, entry19_5, entry19_6, entry19_7, entry19_8, entry19_9, entry19_10, entry19_11, entry19_12, entry19_13, entry19_14, entry19_15, entry19_16, entry19_17, entry19_18, entry19_19, entry20_19, entry21_19, entry22_19, entry23_19, entry24_19, entry25_19, entry26_19],
  ![entry20_0, entry20_1, entry20_2, entry20_3, entry20_4, entry20_5, entry20_6, entry20_7, entry20_8, entry20_9, entry20_10, entry20_11, entry20_12, entry20_13, entry20_14, entry20_15, entry20_16, entry20_17, entry20_18, entry20_19, entry20_20, entry21_20, entry22_20, entry23_20, entry24_20, entry25_20, entry26_20],
  ![entry21_0, entry21_1, entry21_2, entry21_3, entry21_4, entry21_5, entry21_6, entry21_7, entry21_8, entry21_9, entry21_10, entry21_11, entry21_12, entry21_13, entry21_14, entry21_15, entry21_16, entry21_17, entry21_18, entry21_19, entry21_20, entry21_21, entry22_21, entry23_21, entry24_21, entry25_21, entry26_21],
  ![entry22_0, entry22_1, entry22_2, entry22_3, entry22_4, entry22_5, entry22_6, entry22_7, entry22_8, entry22_9, entry22_10, entry22_11, entry22_12, entry22_13, entry22_14, entry22_15, entry22_16, entry22_17, entry22_18, entry22_19, entry22_20, entry22_21, entry22_22, entry23_22, entry24_22, entry25_22, entry26_22],
  ![entry23_0, entry23_1, entry23_2, entry23_3, entry23_4, entry23_5, entry23_6, entry23_7, entry23_8, entry23_9, entry23_10, entry23_11, entry23_12, entry23_13, entry23_14, entry23_15, entry23_16, entry23_17, entry23_18, entry23_19, entry23_20, entry23_21, entry23_22, entry23_23, entry24_23, entry25_23, entry26_23],
  ![entry24_0, entry24_1, entry24_2, entry24_3, entry24_4, entry24_5, entry24_6, entry24_7, entry24_8, entry24_9, entry24_10, entry24_11, entry24_12, entry24_13, entry24_14, entry24_15, entry24_16, entry24_17, entry24_18, entry24_19, entry24_20, entry24_21, entry24_22, entry24_23, entry24_24, entry25_24, entry26_24],
  ![entry25_0, entry25_1, entry25_2, entry25_3, entry25_4, entry25_5, entry25_6, entry25_7, entry25_8, entry25_9, entry25_10, entry25_11, entry25_12, entry25_13, entry25_14, entry25_15, entry25_16, entry25_17, entry25_18, entry25_19, entry25_20, entry25_21, entry25_22, entry25_23, entry25_24, entry25_25, entry26_25],
  ![entry26_0, entry26_1, entry26_2, entry26_3, entry26_4, entry26_5, entry26_6, entry26_7, entry26_8, entry26_9, entry26_10, entry26_11, entry26_12, entry26_13, entry26_14, entry26_15, entry26_16, entry26_17, entry26_18, entry26_19, entry26_20, entry26_21, entry26_22, entry26_23, entry26_24, entry26_25, entry26_26]
]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block3

def form1 : LinearForm := ⟨5, fun k => terms1[k.val]!⟩

def form2 : LinearForm := ⟨16, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨16, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨16, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨36, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨5, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨24, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨36, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨36, fun k => terms9[k.val]!⟩

def form12 : LinearForm := ⟨8, fun k => terms12[k.val]!⟩

def form13 : LinearForm := ⟨16, fun k => terms13[k.val]!⟩

def form14 : LinearForm := ⟨8, fun k => terms14[k.val]!⟩

def form15 : LinearForm := ⟨16, fun k => terms15[k.val]!⟩

def form16 : LinearForm := ⟨8, fun k => terms16[k.val]!⟩

def form17 : LinearForm := ⟨24, fun k => terms17[k.val]!⟩

def form18 : LinearForm := ⟨24, fun k => terms18[k.val]!⟩

def form19 : LinearForm := ⟨10, fun k => terms19[k.val]!⟩

def form20 : LinearForm := ⟨5, fun k => terms20[k.val]!⟩

def form21 : LinearForm := ⟨36, fun k => terms21[k.val]!⟩

def form22 : LinearForm := ⟨36, fun k => terms22[k.val]!⟩

def form23 : LinearForm := ⟨18, fun k => terms23[k.val]!⟩

def form24 : LinearForm := ⟨5, fun k => terms24[k.val]!⟩

def form25 : LinearForm := ⟨8, fun k => terms25[k.val]!⟩

def form26 : LinearForm := ⟨24, fun k => terms26[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block3.form1.size → Integer.Sparse Key := ![row7372, row7373, row7374, row7375, row7376]

def rows1_1 : Fin GramFunctions.Block3.form1.size → Integer.Sparse Key := ![row7377, row7378, row7379, row7380, row7381]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7494, row7495, row7496, row7497, row8757, row8758, row8759, row8760]

def rows12_1 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7510, row7511, row7512, row7513, row8761, row8762, row8763, row8764]

def rows12_2 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7526, row7527, row7528, row7529, row8765, row8766, row8767, row8768]

def rows12_3 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7542, row7543, row7544, row7545, row8769, row8770, row8771, row8772]

def rows12_4 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7558, row7559, row7560, row7561, row8773, row8774, row8775, row8776]

def rows12_5 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8777, row8778, row8779, row8780, row8781, row8782, row8783, row8784]

def rows12_6 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8785, row8786, row8787, row8788, row8789, row8790, row8791, row8792]

def rows12_7 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8793, row8794, row8795, row8796, row8797, row8798, row8799, row8800]

def rows12_8 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8801, row8802, row8803, row8804, row8805, row8806, row8807, row8808]

def rows12_9 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8809, row8810, row8811, row8812, row8813, row8814, row8815, row8816]

def rows12_10 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8817, row8818, row8819, row8820, row8821, row8822, row8823, row8824]

def rows12_11 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8825, row8826, row8827, row8828, row8829, row8830, row8831, row8832]

def rows12_12 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8833, row8834, row8835, row8836, row8837, row8838, row8839, row8840]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8841, row8842, row8843, row8844, row8845, row8846, row8847, row8848, row8849, row8850, row8851, row8852, row8853, row8854, row8855, row8856]

def rows13_1 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8857, row8858, row8859, row8860, row8861, row8862, row8863, row8864, row8865, row8866, row8867, row8868, row8869, row8870, row8871, row8872]

def rows13_2 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8873, row8874, row8875, row8876, row8877, row8878, row8879, row8880, row8881, row8882, row8883, row8884, row8885, row8886, row8887, row8888]

def rows13_3 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8889, row8890, row8891, row8892, row8893, row8894, row8895, row8896, row8897, row8898, row8899, row8900, row8901, row8902, row8903, row8904]

def rows13_4 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8905, row8906, row8907, row8908, row8909, row8910, row8911, row8912, row8913, row8914, row8915, row8916, row8917, row8918, row8919, row8920]

def rows13_5 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8921, row8922, row8923, row8924, row8925, row8926, row8927, row8928, row8929, row8930, row8931, row8932, row8933, row8934, row8935, row8936]

def rows13_6 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8937, row8938, row8939, row8940, row8941, row8942, row8943, row8944, row8945, row8946, row8947, row8948, row8949, row8950, row8951, row8952]

def rows13_7 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8953, row8954, row8955, row8956, row8957, row8958, row8959, row8960, row8961, row8962, row8963, row8964, row8965, row8966, row8967, row8968]

def rows13_8 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8969, row8970, row8971, row8972, row8973, row8974, row8975, row8976, row8977, row8978, row8979, row8980, row8981, row8982, row8983, row8984]

def rows13_9 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8985, row8986, row8987, row8988, row8989, row8990, row8991, row8992, row8993, row8994, row8995, row8996, row8997, row8998, row8999, row9000]

def rows13_10 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9001, row9002, row9003, row9004, row9005, row9006, row9007, row9008, row9009, row9010, row9011, row9012, row9013, row9014, row9015, row9016]

def rows13_11 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9017, row9018, row9019, row9020, row9021, row9022, row9023, row9024, row9025, row9026, row9027, row9028, row9029, row9030, row9031, row9032]

def rows13_12 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9033, row9034, row9035, row9036, row9037, row9038, row9039, row9040, row9041, row9042, row9043, row9044, row9045, row9046, row9047, row9048]

def rows13_13 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9049, row9050, row9051, row9052, row9053, row9054, row9055, row9056, row9057, row9058, row9059, row9060, row9061, row9062, row9063, row9064]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7382, row7383, row7384, row7385, row9065, row9066, row9067, row9068]

def rows14_1 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7398, row7399, row7400, row7401, row9069, row9070, row9071, row9072]

def rows14_2 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7414, row7415, row7416, row7417, row9073, row9074, row9075, row9076]

def rows14_3 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9077, row9078, row9079, row9080, row9081, row9082, row9083, row9084]

def rows14_4 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9085, row9086, row9087, row9088, row9089, row9090, row9091, row9092]

def rows14_5 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9093, row9094, row9095, row9096, row9097, row9098, row9099, row9100]

def rows14_6 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9101, row9102, row9103, row9104, row9105, row9106, row9107, row9108]

def rows14_7 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9109, row9110, row9111, row9112, row9113, row9114, row9115, row9116]

def rows14_8 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9117, row9118, row9119, row9120, row9121, row9122, row9123, row9124]

def rows14_9 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9125, row9126, row9127, row9128, row9129, row9130, row9131, row9132]

def rows14_10 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9133, row9134, row9135, row9136, row9137, row9138, row9139, row9140]

def rows14_11 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9141, row9142, row9143, row9144, row9145, row9146, row9147, row9148]

def rows14_12 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9149, row9150, row9151, row9152, row9153, row9154, row9155, row9156]

def rows14_13 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9157, row9158, row9159, row9160, row9161, row9162, row9163, row9164]

def rows14_14 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9165, row9166, row9167, row9168, row9169, row9170, row9171, row9172]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8661, row8662, row8663, row8664, row9173, row9174, row9175, row9176, row9177, row9178, row9179, row9180, row9181, row9182, row9183, row9184]

def rows15_1 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8669, row8670, row8671, row8672, row9185, row9186, row9187, row9188, row9189, row9190, row9191, row9192, row9193, row9194, row9195, row9196]

def rows15_2 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8677, row8678, row8679, row8680, row9197, row9198, row9199, row9200, row9201, row9202, row9203, row9204, row9205, row9206, row9207, row9208]

def rows15_3 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8685, row8686, row8687, row8688, row9209, row9210, row9211, row9212, row9213, row9214, row9215, row9216, row9217, row9218, row9219, row9220]

def rows15_4 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8693, row8694, row8695, row8696, row9221, row9222, row9223, row9224, row9225, row9226, row9227, row9228, row9229, row9230, row9231, row9232]

def rows15_5 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8701, row8702, row8703, row8704, row9233, row9234, row9235, row9236, row9237, row9238, row9239, row9240, row9241, row9242, row9243, row9244]

def rows15_6 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8709, row8710, row8711, row8712, row9245, row9246, row9247, row9248, row9249, row9250, row9251, row9252, row9253, row9254, row9255, row9256]

def rows15_7 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8717, row8718, row8719, row8720, row9257, row9258, row9259, row9260, row9261, row9262, row9263, row9264, row9265, row9266, row9267, row9268]

def rows15_8 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8725, row8726, row8727, row8728, row9269, row9270, row9271, row9272, row9273, row9274, row9275, row9276, row9277, row9278, row9279, row9280]

def rows15_9 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8733, row8734, row8735, row8736, row9281, row9282, row9283, row9284, row9285, row9286, row9287, row9288, row9289, row9290, row9291, row9292]

def rows15_10 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8741, row8742, row8743, row8744, row9293, row9294, row9295, row9296, row9297, row9298, row9299, row9300, row9301, row9302, row9303, row9304]

def rows15_11 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8749, row8750, row8751, row8752, row9305, row9306, row9307, row9308, row9309, row9310, row9311, row9312, row9313, row9314, row9315, row9316]

def rows15_12 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9317, row9318, row9319, row9320, row9321, row9322, row9323, row9324, row9325, row9326, row9327, row9328, row9329, row9330, row9331, row9332]

def rows15_13 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9333, row9334, row9335, row9336, row9337, row9338, row9339, row9340, row9341, row9342, row9343, row9344, row9345, row9346, row9347, row9348]

def rows15_14 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9349, row9350, row9351, row9352, row9353, row9354, row9355, row9356, row9357, row9358, row9359, row9360, row9361, row9362, row9363, row9364]

def rows15_15 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9365, row9366, row9367, row9368, row9369, row9370, row9371, row9372, row9373, row9374, row9375, row9376, row9377, row9378, row9379, row9380]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9381, row9382, row9383, row9384, row7430, row7431, row7432, row7433]

def rows16_1 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9385, row9386, row9387, row9388, row7446, row7447, row7448, row7449]

def rows16_2 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9389, row9390, row9391, row9392, row7462, row7463, row7464, row7465]

def rows16_3 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9393, row9394, row9395, row9396, row7478, row7479, row7480, row7481]

def rows16_4 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9397, row9398, row9399, row9400, row9401, row9402, row9403, row9404]

def rows16_5 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9405, row9406, row9407, row9408, row9409, row9410, row9411, row9412]

def rows16_6 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9413, row9414, row9415, row9416, row9417, row9418, row9419, row9420]

def rows16_7 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9421, row9422, row9423, row9424, row9425, row9426, row9427, row9428]

def rows16_8 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9429, row9430, row9431, row9432, row9433, row9434, row9435, row9436]

def rows16_9 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9437, row9438, row9439, row9440, row9441, row9442, row9443, row9444]

def rows16_10 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9445, row9446, row9447, row9448, row9449, row9450, row9451, row9452]

def rows16_11 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9453, row9454, row9455, row9456, row9457, row9458, row9459, row9460]

def rows16_12 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9461, row9462, row9463, row9464, row9465, row9466, row9467, row9468]

def rows16_13 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9469, row9470, row9471, row9472, row9473, row9474, row9475, row9476]

def rows16_14 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9477, row9478, row9479, row9480, row9481, row9482, row9483, row9484]

def rows16_15 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9485, row9486, row9487, row9488, row9489, row9490, row9491, row9492]

def rows16_16 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9493, row9494, row9495, row9496, row9497, row9498, row9499, row9500]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9501, row9502, row9503, row9504, row9505, row9506, row9507, row9508, row9509, row9510, row9511, row9512, row9513, row9514, row9515, row9516, row9517, row9518, row9519, row9520, row9521, row9522, row9523, row9524]

def rows17_1 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9525, row9526, row9527, row9528, row9529, row9530, row9531, row9532, row9533, row9534, row9535, row9536, row9537, row9538, row9539, row9540, row9541, row9542, row9543, row9544, row9545, row9546, row9547, row9548]

def rows17_2 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9549, row9550, row9551, row9552, row9553, row9554, row9555, row9556, row9557, row9558, row9559, row9560, row9561, row9562, row9563, row9564, row9565, row9566, row9567, row9568, row9569, row9570, row9571, row9572]

def rows17_3 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9573, row9574, row9575, row9576, row9577, row9578, row9579, row9580, row9581, row9582, row9583, row9584, row9585, row9586, row9587, row9588, row9589, row9590, row9591, row9592, row9593, row9594, row9595, row9596]

def rows17_4 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9597, row9598, row9599, row9600, row9601, row9602, row9603, row9604, row9605, row9606, row9607, row9608, row9609, row9610, row9611, row9612, row9613, row9614, row9615, row9616, row9617, row9618, row9619, row9620]

def rows17_5 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9621, row9622, row9623, row9624, row9625, row9626, row9627, row9628, row9629, row9630, row9631, row9632, row9633, row9634, row9635, row9636, row9637, row9638, row9639, row9640, row9641, row9642, row9643, row9644]

def rows17_6 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9645, row9646, row9647, row9648, row9649, row9650, row9651, row9652, row9653, row9654, row9655, row9656, row9657, row9658, row9659, row9660, row9661, row9662, row9663, row9664, row9665, row9666, row9667, row9668]

def rows17_7 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9669, row9670, row9671, row9672, row9673, row9674, row9675, row9676, row9677, row9678, row9679, row9680, row9681, row9682, row9683, row9684, row9685, row9686, row9687, row9688, row9689, row9690, row9691, row9692]

def rows17_8 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9693, row9694, row9695, row9696, row9697, row9698, row9699, row9700, row9701, row9702, row9703, row9704, row9705, row9706, row9707, row9708, row9709, row9710, row9711, row9712, row9713, row9714, row9715, row9716]

def rows17_9 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9717, row9718, row9719, row9720, row9721, row9722, row9723, row9724, row9725, row9726, row9727, row9728, row9729, row9730, row9731, row9732, row9733, row9734, row9735, row9736, row9737, row9738, row9739, row9740]

def rows17_10 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9741, row9742, row9743, row9744, row9745, row9746, row9747, row9748, row9749, row9750, row9751, row9752, row9753, row9754, row9755, row9756, row9757, row9758, row9759, row9760, row9761, row9762, row9763, row9764]

def rows17_11 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9765, row9766, row9767, row9768, row9769, row9770, row9771, row9772, row9773, row9774, row9775, row9776, row9777, row9778, row9779, row9780, row9781, row9782, row9783, row9784, row9785, row9786, row9787, row9788]

def rows17_12 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9789, row9790, row9791, row9792, row9793, row9794, row9795, row9796, row9797, row9798, row9799, row9800, row9801, row9802, row9803, row9804, row9805, row9806, row9807, row9808, row9809, row9810, row9811, row9812]

def rows17_13 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9813, row9814, row9815, row9816, row9817, row9818, row9819, row9820, row9821, row9822, row9823, row9824, row9825, row9826, row9827, row9828, row9829, row9830, row9831, row9832, row9833, row9834, row9835, row9836]

def rows17_14 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9837, row9838, row9839, row9840, row9841, row9842, row9843, row9844, row9845, row9846, row9847, row9848, row9849, row9850, row9851, row9852, row9853, row9854, row9855, row9856, row9857, row9858, row9859, row9860]

def rows17_15 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9861, row9862, row9863, row9864, row9865, row9866, row9867, row9868, row9869, row9870, row9871, row9872, row9873, row9874, row9875, row9876, row9877, row9878, row9879, row9880, row9881, row9882, row9883, row9884]

def rows17_16 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9885, row9886, row9887, row9888, row9889, row9890, row9891, row9892, row9893, row9894, row9895, row9896, row9897, row9898, row9899, row9900, row9901, row9902, row9903, row9904, row9905, row9906, row9907, row9908]

def rows17_17 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9909, row9910, row9911, row9912, row9913, row9914, row9915, row9916, row9917, row9918, row9919, row9920, row9921, row9922, row9923, row9924, row9925, row9926, row9927, row9928, row9929, row9930, row9931, row9932]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9933, row9934, row9935, row9936, row9937, row9938, row9939, row9940, row9941, row9942, row9943, row9944, row9945, row9946, row9947, row9948, row9949, row9950, row9951, row9952, row9953, row9954, row9955, row9956]

def rows18_1 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9957, row9958, row9959, row9960, row9961, row9962, row9963, row9964, row9965, row9966, row9967, row9968, row9969, row9970, row9971, row9972, row9973, row9974, row9975, row9976, row9977, row9978, row9979, row9980]

def rows18_2 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9981, row9982, row9983, row9984, row9985, row9986, row9987, row9988, row9989, row9990, row9991, row9992, row9993, row9994, row9995, row9996, row9997, row9998, row9999, row10000, row10001, row10002, row10003, row10004]

def rows18_3 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10005, row10006, row10007, row10008, row10009, row10010, row10011, row10012, row10013, row10014, row10015, row10016, row10017, row10018, row10019, row10020, row10021, row10022, row10023, row10024, row10025, row10026, row10027, row10028]

def rows18_4 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10029, row10030, row10031, row10032, row10033, row10034, row10035, row10036, row10037, row10038, row10039, row10040, row10041, row10042, row10043, row10044, row10045, row10046, row10047, row10048, row10049, row10050, row10051, row10052]

def rows18_5 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10053, row10054, row10055, row10056, row10057, row10058, row10059, row10060, row10061, row10062, row10063, row10064, row10065, row10066, row10067, row10068, row10069, row10070, row10071, row10072, row10073, row10074, row10075, row10076]

def rows18_6 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10077, row10078, row10079, row10080, row10081, row10082, row10083, row10084, row10085, row10086, row10087, row10088, row10089, row10090, row10091, row10092, row10093, row10094, row10095, row10096, row10097, row10098, row10099, row10100]

def rows18_7 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10101, row10102, row10103, row10104, row10105, row10106, row10107, row10108, row10109, row10110, row10111, row10112, row10113, row10114, row10115, row10116, row10117, row10118, row10119, row10120, row10121, row10122, row10123, row10124]

def rows18_8 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10125, row10126, row10127, row10128, row10129, row10130, row10131, row10132, row10133, row10134, row10135, row10136, row10137, row10138, row10139, row10140, row10141, row10142, row10143, row10144, row10145, row10146, row10147, row10148]

def rows18_9 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10149, row10150, row10151, row10152, row10153, row10154, row10155, row10156, row10157, row10158, row10159, row10160, row10161, row10162, row10163, row10164, row10165, row10166, row10167, row10168, row10169, row10170, row10171, row10172]

def rows18_10 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10173, row10174, row10175, row10176, row10177, row10178, row10179, row10180, row10181, row10182, row10183, row10184, row10185, row10186, row10187, row10188, row10189, row10190, row10191, row10192, row10193, row10194, row10195, row10196]

def rows18_11 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10197, row10198, row10199, row10200, row10201, row10202, row10203, row10204, row10205, row10206, row10207, row10208, row10209, row10210, row10211, row10212, row10213, row10214, row10215, row10216, row10217, row10218, row10219, row10220]

def rows18_12 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10221, row10222, row10223, row10224, row10225, row10226, row10227, row10228, row10229, row10230, row10231, row10232, row10233, row10234, row10235, row10236, row10237, row10238, row10239, row10240, row10241, row10242, row10243, row10244]

def rows18_13 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10245, row10246, row10247, row10248, row10249, row10250, row10251, row10252, row10253, row10254, row10255, row10256, row10257, row10258, row10259, row10260, row10261, row10262, row10263, row10264, row10265, row10266, row10267, row10268]

def rows18_14 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10269, row10270, row10271, row10272, row10273, row10274, row10275, row10276, row10277, row10278, row10279, row10280, row10281, row10282, row10283, row10284, row10285, row10286, row10287, row10288, row10289, row10290, row10291, row10292]

def rows18_15 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10293, row10294, row10295, row10296, row10297, row10298, row10299, row10300, row10301, row10302, row10303, row10304, row10305, row10306, row10307, row10308, row10309, row10310, row10311, row10312, row10313, row10314, row10315, row10316]

def rows18_16 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10317, row10318, row10319, row10320, row10321, row10322, row10323, row10324, row10325, row10326, row10327, row10328, row10329, row10330, row10331, row10332, row10333, row10334, row10335, row10336, row10337, row10338, row10339, row10340]

def rows18_17 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10341, row10342, row10343, row10344, row10345, row10346, row10347, row10348, row10349, row10350, row10351, row10352, row10353, row10354, row10355, row10356, row10357, row10358, row10359, row10360, row10361, row10362, row10363, row10364]

def rows18_18 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10365, row10366, row10367, row10368, row10369, row10370, row10371, row10372, row10373, row10374, row10375, row10376, row10377, row10378, row10379, row10380, row10381, row10382, row10383, row10384, row10385, row10386, row10387, row10388]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10389, row10390, row10391, row10392, row10393, row10394, row10395, row10396, row10397, row10398]

def rows19_1 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10399, row10400, row10401, row10402, row10403, row10404, row10405, row10406, row10407, row10408]

def rows19_2 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10409, row10410, row10411, row10412, row10413, row10414, row10415, row10416, row10417, row10418]

def rows19_3 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10419, row10420, row10421, row10422, row10423, row10424, row10425, row10426, row10427, row10428]

def rows19_4 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10429, row10430, row10431, row10432, row10433, row10434, row10435, row10436, row10437, row10438]

def rows19_5 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10439, row10440, row10441, row10442, row10443, row10444, row10445, row10446, row10447, row10448]

def rows19_6 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10449, row10450, row10451, row10452, row10453, row10454, row10455, row10456, row10457, row10458]

def rows19_7 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10459, row10460, row10461, row10462, row10463, row10464, row10465, row10466, row10467, row10468]

def rows19_8 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10469, row10470, row10471, row10472, row10473, row10474, row10475, row10476, row10477, row10478]

def rows19_9 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10479, row10480, row10481, row10482, row10483, row10484, row10485, row10486, row10487, row10488]

def rows19_10 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10489, row10490, row10491, row10492, row10493, row10494, row10495, row10496, row10497, row10498]

def rows19_11 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10499, row10500, row10501, row10502, row10503, row10504, row10505, row10506, row10507, row10508]

def rows19_12 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10509, row10510, row10511, row10512, row10513, row10514, row10515, row10516, row10517, row10518]

def rows19_13 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10519, row10520, row10521, row10522, row10523, row10524, row10525, row10526, row10527, row10528]

def rows19_14 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10529, row10530, row10531, row10532, row10533, row10534, row10535, row10536, row10537, row10538]

def rows19_15 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10539, row10540, row10541, row10542, row10543, row10544, row10545, row10546, row10547, row10548]

def rows19_16 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10549, row10550, row10551, row10552, row10553, row10554, row10555, row10556, row10557, row10558]

def rows19_17 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10559, row10560, row10561, row10562, row10563, row10564, row10565, row10566, row10567, row10568]

def rows19_18 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10569, row10570, row10571, row10572, row10573, row10574, row10575, row10576, row10577, row10578]

def rows19_19 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10579, row10580, row10581, row10582, row10583, row10584, row10585, row10586, row10587, row10588]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7382, row7383, row7384, row7385, row7386, row7387, row7388, row7389, row7390, row7391, row7392, row7393, row7394, row7395, row7396, row7397]

def rows2_1 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7398, row7399, row7400, row7401, row7402, row7403, row7404, row7405, row7406, row7407, row7408, row7409, row7410, row7411, row7412, row7413]

def rows2_2 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7414, row7415, row7416, row7417, row7418, row7419, row7420, row7421, row7422, row7423, row7424, row7425, row7426, row7427, row7428, row7429]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10589, row10590, row10591, row10592, row10593]

def rows20_1 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10594, row10595, row10596, row10597, row10598]

def rows20_2 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10599, row10600, row10601, row10602, row10603]

def rows20_3 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10604, row10605, row10606, row10607, row10608]

def rows20_4 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10609, row10610, row10611, row10612, row10613]

def rows20_5 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10614, row10615, row10616, row10617, row10618]

def rows20_6 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10619, row10620, row10621, row10622, row10623]

def rows20_7 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10624, row10625, row10626, row10627, row10628]

def rows20_8 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10629, row10630, row10631, row10632, row10633]

def rows20_9 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10634, row10635, row10636, row10637, row10638]

def rows20_10 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10639, row10640, row10641, row10642, row10643]

def rows20_11 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10644, row10645, row10646, row10647, row10648]

def rows20_12 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10649, row10650, row10651, row10652, row10653]

def rows20_13 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10654, row10655, row10656, row10657, row10658]

def rows20_14 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10659, row10660, row10661, row10662, row10663]

def rows20_15 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10664, row10665, row10666, row10667, row10668]

def rows20_16 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10669, row10670, row10671, row10672, row10673]

def rows20_17 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10674, row10675, row10676, row10677, row10678]

def rows20_18 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10679, row10680, row10681, row10682, row10683]

def rows20_19 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10684, row10685, row10686, row10687, row10688]

def rows20_20 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10689, row10690, row10691, row10692, row10693]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows21_0 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10694, row10695, row10696, row10697, row10698, row10699, row10700, row10701, row10702, row10703, row10704, row10705, row10706, row10707, row10708, row10709, row10710, row10711, row10712, row10713, row10714, row10715, row10716, row10717, row10718, row10719, row10720, row10721, row10722, row10723, row10724, row10725, row10726, row10727, row10728, row10729]

def rows21_1 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10730, row10731, row10732, row10733, row10734, row10735, row10736, row10737, row10738, row10739, row10740, row10741, row10742, row10743, row10744, row10745, row10746, row10747, row10748, row10749, row10750, row10751, row10752, row10753, row10754, row10755, row10756, row10757, row10758, row10759, row10760, row10761, row10762, row10763, row10764, row10765]

def rows21_2 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10766, row10767, row10768, row10769, row10770, row10771, row10772, row10773, row10774, row10775, row10776, row10777, row10778, row10779, row10780, row10781, row10782, row10783, row10784, row10785, row10786, row10787, row10788, row10789, row10790, row10791, row10792, row10793, row10794, row10795, row10796, row10797, row10798, row10799, row10800, row10801]

def rows21_3 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10802, row10803, row10804, row10805, row10806, row10807, row10808, row10809, row10810, row10811, row10812, row10813, row10814, row10815, row10816, row10817, row10818, row10819, row10820, row10821, row10822, row10823, row10824, row10825, row10826, row10827, row10828, row10829, row10830, row10831, row10832, row10833, row10834, row10835, row10836, row10837]

def rows21_4 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10838, row10839, row10840, row10841, row10842, row10843, row10844, row10845, row10846, row10847, row10848, row10849, row10850, row10851, row10852, row10853, row10854, row10855, row10856, row10857, row10858, row10859, row10860, row10861, row10862, row10863, row10864, row10865, row10866, row10867, row10868, row10869, row10870, row10871, row10872, row10873]

def rows21_5 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10874, row10875, row10876, row10877, row10878, row10879, row10880, row10881, row10882, row10883, row10884, row10885, row10886, row10887, row10888, row10889, row10890, row10891, row10892, row10893, row10894, row10895, row10896, row10897, row10898, row10899, row10900, row10901, row10902, row10903, row10904, row10905, row10906, row10907, row10908, row10909]

def rows21_6 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10910, row10911, row10912, row10913, row10914, row10915, row10916, row10917, row10918, row10919, row10920, row10921, row10922, row10923, row10924, row10925, row10926, row10927, row10928, row10929, row10930, row10931, row10932, row10933, row10934, row10935, row10936, row10937, row10938, row10939, row10940, row10941, row10942, row10943, row10944, row10945]

def rows21_7 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10946, row10947, row10948, row10949, row10950, row10951, row10952, row10953, row10954, row10955, row10956, row10957, row10958, row10959, row10960, row10961, row10962, row10963, row10964, row10965, row10966, row10967, row10968, row10969, row10970, row10971, row10972, row10973, row10974, row10975, row10976, row10977, row10978, row10979, row10980, row10981]

def rows21_8 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10982, row10983, row10984, row10985, row10986, row10987, row10988, row10989, row10990, row10991, row10992, row10993, row10994, row10995, row10996, row10997, row10998, row10999, row11000, row11001, row11002, row11003, row11004, row11005, row11006, row11007, row11008, row11009, row11010, row11011, row11012, row11013, row11014, row11015, row11016, row11017]

def rows21_9 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11018, row11019, row11020, row11021, row11022, row11023, row11024, row11025, row11026, row11027, row11028, row11029, row11030, row11031, row11032, row11033, row11034, row11035, row11036, row11037, row11038, row11039, row11040, row11041, row11042, row11043, row11044, row11045, row11046, row11047, row11048, row11049, row11050, row11051, row11052, row11053]

def rows21_10 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11054, row11055, row11056, row11057, row11058, row11059, row11060, row11061, row11062, row11063, row11064, row11065, row11066, row11067, row11068, row11069, row11070, row11071, row11072, row11073, row11074, row11075, row11076, row11077, row11078, row11079, row11080, row11081, row11082, row11083, row11084, row11085, row11086, row11087, row11088, row11089]

def rows21_11 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11090, row11091, row11092, row11093, row11094, row11095, row11096, row11097, row11098, row11099, row11100, row11101, row11102, row11103, row11104, row11105, row11106, row11107, row11108, row11109, row11110, row11111, row11112, row11113, row11114, row11115, row11116, row11117, row11118, row11119, row11120, row11121, row11122, row11123, row11124, row11125]

def rows21_12 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11126, row11127, row11128, row11129, row11130, row11131, row11132, row11133, row11134, row11135, row11136, row11137, row11138, row11139, row11140, row11141, row11142, row11143, row11144, row11145, row11146, row11147, row11148, row11149, row11150, row11151, row11152, row11153, row11154, row11155, row11156, row11157, row11158, row11159, row11160, row11161]

def rows21_13 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11162, row11163, row11164, row11165, row11166, row11167, row11168, row11169, row11170, row11171, row11172, row11173, row11174, row11175, row11176, row11177, row11178, row11179, row11180, row11181, row11182, row11183, row11184, row11185, row11186, row11187, row11188, row11189, row11190, row11191, row11192, row11193, row11194, row11195, row11196, row11197]

def rows21_14 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11198, row11199, row11200, row11201, row11202, row11203, row11204, row11205, row11206, row11207, row11208, row11209, row11210, row11211, row11212, row11213, row11214, row11215, row11216, row11217, row11218, row11219, row11220, row11221, row11222, row11223, row11224, row11225, row11226, row11227, row11228, row11229, row11230, row11231, row11232, row11233]

def rows21_15 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11234, row11235, row11236, row11237, row11238, row11239, row11240, row11241, row11242, row11243, row11244, row11245, row11246, row11247, row11248, row11249, row11250, row11251, row11252, row11253, row11254, row11255, row11256, row11257, row11258, row11259, row11260, row11261, row11262, row11263, row11264, row11265, row11266, row11267, row11268, row11269]

def rows21_16 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11270, row11271, row11272, row11273, row11274, row11275, row11276, row11277, row11278, row11279, row11280, row11281, row11282, row11283, row11284, row11285, row11286, row11287, row11288, row11289, row11290, row11291, row11292, row11293, row11294, row11295, row11296, row11297, row11298, row11299, row11300, row11301, row11302, row11303, row11304, row11305]

def rows21_17 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11306, row11307, row11308, row11309, row11310, row11311, row11312, row11313, row11314, row11315, row11316, row11317, row11318, row11319, row11320, row11321, row11322, row11323, row11324, row11325, row11326, row11327, row11328, row11329, row11330, row11331, row11332, row11333, row11334, row11335, row11336, row11337, row11338, row11339, row11340, row11341]

def rows21_18 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11342, row11343, row11344, row11345, row11346, row11347, row11348, row11349, row11350, row11351, row11352, row11353, row11354, row11355, row11356, row11357, row11358, row11359, row11360, row11361, row11362, row11363, row11364, row11365, row11366, row11367, row11368, row11369, row11370, row11371, row11372, row11373, row11374, row11375, row11376, row11377]

def rows21_19 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11378, row11379, row11380, row11381, row11382, row11383, row11384, row11385, row11386, row11387, row11388, row11389, row11390, row11391, row11392, row11393, row11394, row11395, row11396, row11397, row11398, row11399, row11400, row11401, row11402, row11403, row11404, row11405, row11406, row11407, row11408, row11409, row11410, row11411, row11412, row11413]

def rows21_20 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11414, row11415, row11416, row11417, row11418, row11419, row11420, row11421, row11422, row11423, row11424, row11425, row11426, row11427, row11428, row11429, row11430, row11431, row11432, row11433, row11434, row11435, row11436, row11437, row11438, row11439, row11440, row11441, row11442, row11443, row11444, row11445, row11446, row11447, row11448, row11449]

def rows21_21 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11450, row11451, row11452, row11453, row11454, row11455, row11456, row11457, row11458, row11459, row11460, row11461, row11462, row11463, row11464, row11465, row11466, row11467, row11468, row11469, row11470, row11471, row11472, row11473, row11474, row11475, row11476, row11477, row11478, row11479, row11480, row11481, row11482, row11483, row11484, row11485]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows22_0 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11486, row11487, row11488, row11489, row11490, row11491, row11492, row11493, row11494, row11495, row11496, row11497, row10694, row10695, row10696, row10697, row10698, row10699, row10700, row10701, row10702, row10703, row10704, row10705, row10706, row10707, row10708, row10709, row10710, row10711, row10712, row10713, row10714, row10715, row10716, row10717]

def rows22_1 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11498, row11499, row11500, row11501, row11502, row11503, row11504, row11505, row11506, row11507, row11508, row11509, row10730, row10731, row10732, row10733, row10734, row10735, row10736, row10737, row10738, row10739, row10740, row10741, row10742, row10743, row10744, row10745, row10746, row10747, row10748, row10749, row10750, row10751, row10752, row10753]

def rows22_2 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11510, row11511, row11512, row11513, row11514, row11515, row11516, row11517, row11518, row11519, row11520, row11521, row10766, row10767, row10768, row10769, row10770, row10771, row10772, row10773, row10774, row10775, row10776, row10777, row10778, row10779, row10780, row10781, row10782, row10783, row10784, row10785, row10786, row10787, row10788, row10789]

def rows22_3 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11522, row11523, row11524, row11525, row11526, row11527, row11528, row11529, row11530, row11531, row11532, row11533, row10802, row10803, row10804, row10805, row10806, row10807, row10808, row10809, row10810, row10811, row10812, row10813, row10814, row10815, row10816, row10817, row10818, row10819, row10820, row10821, row10822, row10823, row10824, row10825]

def rows22_4 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11534, row11535, row11536, row11537, row11538, row11539, row11540, row11541, row11542, row11543, row11544, row11545, row10838, row10839, row10840, row10841, row10842, row10843, row10844, row10845, row10846, row10847, row10848, row10849, row10850, row10851, row10852, row10853, row10854, row10855, row10856, row10857, row10858, row10859, row10860, row10861]

def rows22_5 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11546, row11547, row11548, row11549, row11550, row11551, row11552, row11553, row11554, row11555, row11556, row11557, row10874, row10875, row10876, row10877, row10878, row10879, row10880, row10881, row10882, row10883, row10884, row10885, row10886, row10887, row10888, row10889, row10890, row10891, row10892, row10893, row10894, row10895, row10896, row10897]

def rows22_6 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11558, row11559, row11560, row11561, row11562, row11563, row11564, row11565, row11566, row11567, row11568, row11569, row10910, row10911, row10912, row10913, row10914, row10915, row10916, row10917, row10918, row10919, row10920, row10921, row10922, row10923, row10924, row10925, row10926, row10927, row10928, row10929, row10930, row10931, row10932, row10933]

def rows22_7 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11570, row11571, row11572, row11573, row11574, row11575, row11576, row11577, row11578, row11579, row11580, row11581, row10946, row10947, row10948, row10949, row10950, row10951, row10952, row10953, row10954, row10955, row10956, row10957, row10958, row10959, row10960, row10961, row10962, row10963, row10964, row10965, row10966, row10967, row10968, row10969]

def rows22_8 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11582, row11583, row11584, row11585, row11586, row11587, row11588, row11589, row11590, row11591, row11592, row11593, row10982, row10983, row10984, row10985, row10986, row10987, row10988, row10989, row10990, row10991, row10992, row10993, row10994, row10995, row10996, row10997, row10998, row10999, row11000, row11001, row11002, row11003, row11004, row11005]

def rows22_9 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11594, row11595, row11596, row11597, row11598, row11599, row11600, row11601, row11602, row11603, row11604, row11605, row11018, row11019, row11020, row11021, row11022, row11023, row11024, row11025, row11026, row11027, row11028, row11029, row11030, row11031, row11032, row11033, row11034, row11035, row11036, row11037, row11038, row11039, row11040, row11041]

def rows22_10 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11606, row11607, row11608, row11609, row11610, row11611, row11612, row11613, row11614, row11615, row11616, row11617, row11054, row11055, row11056, row11057, row11058, row11059, row11060, row11061, row11062, row11063, row11064, row11065, row11066, row11067, row11068, row11069, row11070, row11071, row11072, row11073, row11074, row11075, row11076, row11077]

def rows22_11 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11618, row11619, row11620, row11621, row11622, row11623, row11624, row11625, row11626, row11627, row11628, row11629, row11090, row11091, row11092, row11093, row11094, row11095, row11096, row11097, row11098, row11099, row11100, row11101, row11102, row11103, row11104, row11105, row11106, row11107, row11108, row11109, row11110, row11111, row11112, row11113]

def rows22_12 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11630, row11631, row11632, row11633, row11634, row11635, row11636, row11637, row11638, row11639, row11640, row11641, row11126, row11127, row11128, row11129, row11130, row11131, row11132, row11133, row11134, row11135, row11136, row11137, row11138, row11139, row11140, row11141, row11142, row11143, row11144, row11145, row11146, row11147, row11148, row11149]

def rows22_13 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11642, row11643, row11644, row11645, row11646, row11647, row11648, row11649, row11650, row11651, row11652, row11653, row11162, row11163, row11164, row11165, row11166, row11167, row11168, row11169, row11170, row11171, row11172, row11173, row11174, row11175, row11176, row11177, row11178, row11179, row11180, row11181, row11182, row11183, row11184, row11185]

def rows22_14 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11654, row11655, row11656, row11657, row11658, row11659, row11660, row11661, row11662, row11663, row11664, row11665, row11198, row11199, row11200, row11201, row11202, row11203, row11204, row11205, row11206, row11207, row11208, row11209, row11210, row11211, row11212, row11213, row11214, row11215, row11216, row11217, row11218, row11219, row11220, row11221]

def rows22_15 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11666, row11667, row11668, row11669, row11670, row11671, row11672, row11673, row11674, row11675, row11676, row11677, row11234, row11235, row11236, row11237, row11238, row11239, row11240, row11241, row11242, row11243, row11244, row11245, row11246, row11247, row11248, row11249, row11250, row11251, row11252, row11253, row11254, row11255, row11256, row11257]

def rows22_16 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11678, row11679, row11680, row11681, row11682, row11683, row11684, row11685, row11686, row11687, row11688, row11689, row11270, row11271, row11272, row11273, row11274, row11275, row11276, row11277, row11278, row11279, row11280, row11281, row11282, row11283, row11284, row11285, row11286, row11287, row11288, row11289, row11290, row11291, row11292, row11293]

def rows22_17 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11690, row11691, row11692, row11693, row11694, row11695, row11696, row11697, row11698, row11699, row11700, row11701, row11306, row11307, row11308, row11309, row11310, row11311, row11312, row11313, row11314, row11315, row11316, row11317, row11318, row11319, row11320, row11321, row11322, row11323, row11324, row11325, row11326, row11327, row11328, row11329]

def rows22_18 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11702, row11703, row11704, row11705, row11706, row11707, row11708, row11709, row11710, row11711, row11712, row11713, row11342, row11343, row11344, row11345, row11346, row11347, row11348, row11349, row11350, row11351, row11352, row11353, row11354, row11355, row11356, row11357, row11358, row11359, row11360, row11361, row11362, row11363, row11364, row11365]

def rows22_19 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11714, row11715, row11716, row11717, row11718, row11719, row11720, row11721, row11722, row11723, row11724, row11725, row11378, row11379, row11380, row11381, row11382, row11383, row11384, row11385, row11386, row11387, row11388, row11389, row11390, row11391, row11392, row11393, row11394, row11395, row11396, row11397, row11398, row11399, row11400, row11401]

def rows22_20 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11726, row11727, row11728, row11729, row11730, row11731, row11732, row11733, row11734, row11735, row11736, row11737, row11414, row11415, row11416, row11417, row11418, row11419, row11420, row11421, row11422, row11423, row11424, row11425, row11426, row11427, row11428, row11429, row11430, row11431, row11432, row11433, row11434, row11435, row11436, row11437]

def rows22_21 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11738, row11739, row11740, row11741, row11742, row11743, row11744, row11745, row11746, row11747, row11748, row11749, row11450, row11451, row11452, row11453, row11454, row11455, row11456, row11457, row11458, row11459, row11460, row11461, row11462, row11463, row11464, row11465, row11466, row11467, row11468, row11469, row11470, row11471, row11472, row11473]

def rows22_22 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11750, row11751, row11752, row11753, row11754, row11755, row11756, row11757, row11758, row11759, row11760, row11761, row11762, row11763, row11764, row11765, row11766, row11767, row11768, row11769, row11770, row11771, row11772, row11773, row11774, row11775, row11776, row11777, row11778, row11779, row11780, row11781, row11782, row11783, row11784, row11785]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows23_0 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11786, row11787, row11788, row11789, row11790, row11791, row7348, row7349, row7350, row7351, row7352, row7353, row7354, row7355, row7356, row7357, row7358, row7359]

def rows23_1 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11792, row11793, row11794, row11795, row11796, row11797, row11798, row11799, row11800, row11801, row11802, row11803, row11804, row11805, row11806, row11807, row11808, row11809]

def rows23_2 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11810, row11811, row11812, row11813, row11814, row11815, row11816, row11817, row11818, row11819, row11820, row11821, row11822, row11823, row11824, row11825, row11826, row11827]

def rows23_3 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11828, row11829, row11830, row11831, row11832, row11833, row11834, row11835, row11836, row11837, row11838, row11839, row11840, row11841, row11842, row11843, row11844, row11845]

def rows23_4 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11846, row11847, row11848, row11849, row11850, row11851, row11852, row11853, row11854, row11855, row11856, row11857, row11858, row11859, row11860, row11861, row11862, row11863]

def rows23_5 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11864, row11865, row11866, row11867, row11868, row11869, row11870, row11871, row11872, row11873, row11874, row11875, row11876, row11877, row11878, row11879, row11880, row11881]

def rows23_6 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11882, row11883, row11884, row11885, row11886, row11887, row11888, row11889, row11890, row11891, row11892, row11893, row11894, row11895, row11896, row11897, row11898, row11899]

def rows23_7 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11900, row11901, row11902, row11903, row11904, row11905, row11906, row11907, row11908, row11909, row11910, row11911, row11912, row11913, row11914, row11915, row11916, row11917]

def rows23_8 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11918, row11919, row11920, row11921, row11922, row11923, row11924, row11925, row11926, row11927, row11928, row11929, row11930, row11931, row11932, row11933, row11934, row11935]

def rows23_9 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11936, row11937, row11938, row11939, row11940, row11941, row11942, row11943, row11944, row11945, row11946, row11947, row11948, row11949, row11950, row11951, row11952, row11953]

def rows23_10 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11954, row11955, row11956, row11957, row11958, row11959, row11960, row11961, row11962, row11963, row11964, row11965, row11966, row11967, row11968, row11969, row11970, row11971]

def rows23_11 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11972, row11973, row11974, row11975, row11976, row11977, row11978, row11979, row11980, row11981, row11982, row11983, row11984, row11985, row11986, row11987, row11988, row11989]

def rows23_12 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11990, row11991, row11992, row11993, row11994, row11995, row11996, row11997, row11998, row11999, row12000, row12001, row12002, row12003, row12004, row12005, row12006, row12007]

def rows23_13 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12008, row12009, row12010, row12011, row12012, row12013, row12014, row12015, row12016, row12017, row12018, row12019, row12020, row12021, row12022, row12023, row12024, row12025]

def rows23_14 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12026, row12027, row12028, row12029, row12030, row12031, row12032, row12033, row12034, row12035, row12036, row12037, row12038, row12039, row12040, row12041, row12042, row12043]

def rows23_15 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12044, row12045, row12046, row12047, row12048, row12049, row12050, row12051, row12052, row12053, row12054, row12055, row12056, row12057, row12058, row12059, row12060, row12061]

def rows23_16 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12062, row12063, row12064, row12065, row12066, row12067, row12068, row12069, row12070, row12071, row12072, row12073, row12074, row12075, row12076, row12077, row12078, row12079]

def rows23_17 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12080, row12081, row12082, row12083, row12084, row12085, row12086, row12087, row12088, row12089, row12090, row12091, row12092, row12093, row12094, row12095, row12096, row12097]

def rows23_18 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12098, row12099, row12100, row12101, row12102, row12103, row12104, row12105, row12106, row12107, row12108, row12109, row12110, row12111, row12112, row12113, row12114, row12115]

def rows23_19 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12116, row12117, row12118, row12119, row12120, row12121, row12122, row12123, row12124, row12125, row12126, row12127, row12128, row12129, row12130, row12131, row12132, row12133]

def rows23_20 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12134, row12135, row12136, row12137, row12138, row12139, row12140, row12141, row12142, row12143, row12144, row12145, row12146, row12147, row12148, row12149, row12150, row12151]

def rows23_21 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12152, row12153, row12154, row12155, row12156, row12157, row12158, row12159, row12160, row12161, row12162, row12163, row12164, row12165, row12166, row12167, row12168, row12169]

def rows23_22 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12170, row12171, row12172, row12173, row12174, row12175, row12176, row12177, row12178, row12179, row12180, row12181, row12182, row12183, row12184, row12185, row12186, row12187]

def rows23_23 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12188, row12189, row12190, row12191, row12192, row12193, row12194, row12195, row12196, row12197, row12198, row12199, row12200, row12201, row12202, row12203, row12204, row12205]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows24_0 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12206, row12207, row12208, row12209, row12210]

def rows24_1 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12211, row12212, row12213, row12214, row12215]

def rows24_2 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12216, row12217, row12218, row12219, row12220]

def rows24_3 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12221, row12222, row12223, row12224, row12225]

def rows24_4 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12226, row12227, row12228, row12229, row12230]

def rows24_5 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12231, row12232, row12233, row12234, row12235]

def rows24_6 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12236, row12237, row12238, row12239, row12240]

def rows24_7 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12241, row12242, row12243, row12244, row12245]

def rows24_8 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12246, row12247, row12248, row12249, row12250]

def rows24_9 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12251, row12252, row12253, row12254, row12255]

def rows24_10 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12256, row12257, row12258, row12259, row12260]

def rows24_11 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12261, row12262, row12263, row12264, row12265]

def rows24_12 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12266, row12267, row12268, row12269, row12270]

def rows24_13 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12271, row12272, row12273, row12274, row12275]

def rows24_14 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12276, row12277, row12278, row12279, row12280]

def rows24_15 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12281, row12282, row12283, row12284, row12285]

def rows24_16 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12286, row12287, row12288, row12289, row12290]

def rows24_17 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12291, row12292, row12293, row12294, row12295]

def rows24_18 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12296, row12297, row12298, row12299, row12300]

def rows24_19 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12301, row12302, row12303, row12304, row12305]

def rows24_20 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12306, row12307, row12308, row12309, row12310]

def rows24_21 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12311, row12312, row12313, row12314, row12315]

def rows24_22 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12316, row12317, row12318, row12319, row12320]

def rows24_23 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12321, row12322, row12323, row12324, row12325]

def rows24_24 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12326, row12327, row12328, row12329, row12330]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows25_0 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12331, row12332, row12333, row12334, row12335, row12336, row12337, row12338]

def rows25_1 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12339, row12340, row12341, row12342, row12343, row12344, row12345, row12346]

def rows25_2 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12347, row12348, row12349, row12350, row12351, row12352, row12353, row12354]

def rows25_3 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12355, row12356, row12357, row12358, row12359, row12360, row12361, row12362]

def rows25_4 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12363, row12364, row12365, row12366, row12367, row12368, row12369, row12370]

def rows25_5 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12371, row12372, row12373, row12374, row12375, row12376, row12377, row12378]

def rows25_6 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12379, row12380, row12381, row12382, row12383, row12384, row12385, row12386]

def rows25_7 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12387, row12388, row12389, row12390, row12391, row12392, row12393, row12394]

def rows25_8 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12395, row12396, row12397, row12398, row12399, row12400, row12401, row12402]

def rows25_9 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12403, row12404, row12405, row12406, row12407, row12408, row12409, row12410]

def rows25_10 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12411, row12412, row12413, row12414, row12415, row12416, row12417, row12418]

def rows25_11 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12419, row12420, row12421, row12422, row12423, row12424, row12425, row12426]

def rows25_12 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12427, row12428, row12429, row12430, row12431, row12432, row12433, row12434]

def rows25_13 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12435, row12436, row12437, row12438, row12439, row12440, row12441, row12442]

def rows25_14 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12443, row12444, row12445, row12446, row12447, row12448, row12449, row12450]

def rows25_15 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12451, row12452, row12453, row12454, row12455, row12456, row12457, row12458]

def rows25_16 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12459, row12460, row12461, row12462, row12463, row12464, row12465, row12466]

def rows25_17 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12467, row12468, row12469, row12470, row12471, row12472, row12473, row12474]

def rows25_18 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12475, row12476, row12477, row12478, row12479, row12480, row12481, row12482]

def rows25_19 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12483, row12484, row12485, row12486, row12487, row12488, row12489, row12490]

def rows25_20 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12491, row12492, row12493, row12494, row12495, row12496, row12497, row12498]

def rows25_21 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12499, row12500, row12501, row12502, row12503, row12504, row12505, row12506]

def rows25_22 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12507, row12508, row12509, row12510, row12511, row12512, row12513, row12514]

def rows25_23 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12515, row12516, row12517, row12518, row12519, row12520, row12521, row12522]

def rows25_24 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12523, row12524, row12525, row12526, row12527, row12528, row12529, row12530]

def rows25_25 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12531, row12532, row12533, row12534, row12535, row12536, row12537, row12538]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block4

def form0 : LinearForm := ⟨18, fun k => terms0[k.val]!⟩

def form1 : LinearForm := ⟨20, fun k => terms1[k.val]!⟩

def form2 : LinearForm := ⟨20, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨20, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨20, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨18, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨36, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨10, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨20, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨10, fun k => terms9[k.val]!⟩

def form10 : LinearForm := ⟨36, fun k => terms10[k.val]!⟩

def form11 : LinearForm := ⟨20, fun k => terms11[k.val]!⟩

def form12 : LinearForm := ⟨27, fun k => terms12[k.val]!⟩

def form13 : LinearForm := ⟨36, fun k => terms13[k.val]!⟩

def form14 : LinearForm := ⟨36, fun k => terms14[k.val]!⟩

def form15 : LinearForm := ⟨36, fun k => terms15[k.val]!⟩

def form16 : LinearForm := ⟨36, fun k => terms16[k.val]!⟩

def form17 : LinearForm := ⟨18, fun k => terms17[k.val]!⟩

def form18 : LinearForm := ⟨20, fun k => terms18[k.val]!⟩

def form19 : LinearForm := ⟨10, fun k => terms19[k.val]!⟩

def form20 : LinearForm := ⟨18, fun k => terms20[k.val]!⟩

def form21 : LinearForm := ⟨20, fun k => terms21[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows26_0 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12539, row12540, row12541, row12542, row12543, row12544, row12545, row12546, row12547, row12548, row12549, row12550, row12551, row12552, row12553, row12554, row12555, row12556, row12557, row12558, row12559, row12560, row12561, row12562]

def rows26_1 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12563, row12564, row12565, row12566, row12567, row12568, row12569, row12570, row12571, row12572, row12573, row12574, row12575, row12576, row12577, row12578, row12579, row12580, row12581, row12582, row12583, row12584, row12585, row12586]

def rows26_2 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12587, row12588, row12589, row12590, row12591, row12592, row12593, row12594, row12595, row12596, row12597, row12598, row12599, row12600, row12601, row12602, row12603, row12604, row12605, row12606, row12607, row12608, row12609, row12610]

def rows26_3 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12611, row12612, row12613, row12614, row12615, row12616, row12617, row12618, row12619, row12620, row12621, row12622, row12623, row12624, row12625, row12626, row12627, row12628, row12629, row12630, row12631, row12632, row12633, row12634]

def rows26_4 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12635, row12636, row12637, row12638, row12639, row12640, row12641, row12642, row12643, row12644, row12645, row12646, row12647, row12648, row12649, row12650, row12651, row12652, row12653, row12654, row12655, row12656, row12657, row12658]

def rows26_5 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12659, row12660, row12661, row12662, row12663, row12664, row12665, row12666, row12667, row12668, row12669, row12670, row12671, row12672, row12673, row12674, row12675, row12676, row12677, row12678, row12679, row12680, row12681, row12682]

def rows26_6 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12683, row12684, row12685, row12686, row12687, row12688, row12689, row12690, row12691, row12692, row12693, row12694, row12695, row12696, row12697, row12698, row12699, row12700, row12701, row12702, row12703, row12704, row12705, row12706]

def rows26_7 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12707, row12708, row12709, row12710, row12711, row12712, row12713, row12714, row12715, row12716, row12717, row12718, row12719, row12720, row12721, row12722, row12723, row12724, row12725, row12726, row12727, row12728, row12729, row12730]

def rows26_8 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12731, row12732, row12733, row12734, row12735, row12736, row12737, row12738, row12739, row12740, row12741, row12742, row12743, row12744, row12745, row12746, row12747, row12748, row12749, row12750, row12751, row12752, row12753, row12754]

def rows26_9 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12755, row12756, row12757, row12758, row12759, row12760, row12761, row12762, row12763, row12764, row12765, row12766, row12767, row12768, row12769, row12770, row12771, row12772, row12773, row12774, row12775, row12776, row12777, row12778]

def rows26_10 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12779, row12780, row12781, row12782, row12783, row12784, row12785, row12786, row12787, row12788, row12789, row12790, row12791, row12792, row12793, row12794, row12795, row12796, row12797, row12798, row12799, row12800, row12801, row12802]

def rows26_11 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12803, row12804, row12805, row12806, row12807, row12808, row12809, row12810, row12811, row12812, row12813, row12814, row12815, row12816, row12817, row12818, row12819, row12820, row12821, row12822, row12823, row12824, row12825, row12826]

def rows26_12 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12827, row12828, row12829, row12830, row12831, row12832, row12833, row12834, row12835, row12836, row12837, row12838, row12839, row12840, row12841, row12842, row12843, row12844, row12845, row12846, row12847, row12848, row12849, row12850]

def rows26_13 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12851, row12852, row12853, row12854, row12855, row12856, row12857, row12858, row12859, row12860, row12861, row12862, row12863, row12864, row12865, row12866, row12867, row12868, row12869, row12870, row12871, row12872, row12873, row12874]

def rows26_14 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12875, row12876, row12877, row12878, row12879, row12880, row12881, row12882, row12883, row12884, row12885, row12886, row12887, row12888, row12889, row12890, row12891, row12892, row12893, row12894, row12895, row12896, row12897, row12898]

def rows26_15 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12899, row12900, row12901, row12902, row12903, row12904, row12905, row12906, row12907, row12908, row12909, row12910, row12911, row12912, row12913, row12914, row12915, row12916, row12917, row12918, row12919, row12920, row12921, row12922]

def rows26_16 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12923, row12924, row12925, row12926, row12927, row12928, row12929, row12930, row12931, row12932, row12933, row12934, row12935, row12936, row12937, row12938, row12939, row12940, row12941, row12942, row12943, row12944, row12945, row12946]

def rows26_17 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12947, row12948, row12949, row12950, row12951, row12952, row12953, row12954, row12955, row12956, row12957, row12958, row12959, row12960, row12961, row12962, row12963, row12964, row12965, row12966, row12967, row12968, row12969, row12970]

def rows26_18 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12971, row12972, row12973, row12974, row12975, row12976, row12977, row12978, row12979, row12980, row12981, row12982, row12983, row12984, row12985, row12986, row12987, row12988, row12989, row12990, row12991, row12992, row12993, row12994]

def rows26_19 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12995, row12996, row12997, row12998, row12999, row13000, row13001, row13002, row13003, row13004, row13005, row13006, row13007, row13008, row13009, row13010, row13011, row13012, row13013, row13014, row13015, row13016, row13017, row13018]

def rows26_20 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13019, row13020, row13021, row13022, row13023, row13024, row13025, row13026, row13027, row13028, row13029, row13030, row13031, row13032, row13033, row13034, row13035, row13036, row13037, row13038, row13039, row13040, row13041, row13042]

def rows26_21 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13043, row13044, row13045, row13046, row13047, row13048, row13049, row13050, row13051, row13052, row13053, row13054, row13055, row13056, row13057, row13058, row13059, row13060, row13061, row13062, row13063, row13064, row13065, row13066]

def rows26_22 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13067, row13068, row13069, row13070, row13071, row13072, row13073, row13074, row13075, row13076, row13077, row13078, row13079, row13080, row13081, row13082, row13083, row13084, row13085, row13086, row13087, row13088, row13089, row13090]

def rows26_23 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13091, row13092, row13093, row13094, row13095, row13096, row13097, row13098, row13099, row13100, row13101, row13102, row13103, row13104, row13105, row13106, row13107, row13108, row13109, row13110, row13111, row13112, row13113, row13114]

def rows26_24 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13115, row13116, row13117, row13118, row13119, row13120, row13121, row13122, row13123, row13124, row13125, row13126, row13127, row13128, row13129, row13130, row13131, row13132, row13133, row13134, row13135, row13136, row13137, row13138]

def rows26_25 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13139, row13140, row13141, row13142, row13143, row13144, row13145, row13146, row13147, row13148, row13149, row13150, row13151, row13152, row13153, row13154, row13155, row13156, row13157, row13158, row13159, row13160, row13161, row13162]

def rows26_26 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13163, row13164, row13165, row13166, row13167, row13168, row13169, row13170, row13171, row13172, row13173, row13174, row13175, row13176, row13177, row13178, row13179, row13180, row13181, row13182, row13183, row13184, row13185, row13186]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7430, row7431, row7432, row7433, row7434, row7435, row7436, row7437, row7438, row7439, row7440, row7441, row7442, row7443, row7444, row7445]

def rows3_1 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7446, row7447, row7448, row7449, row7450, row7451, row7452, row7453, row7454, row7455, row7456, row7457, row7458, row7459, row7460, row7461]

def rows3_2 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7462, row7463, row7464, row7465, row7466, row7467, row7468, row7469, row7470, row7471, row7472, row7473, row7474, row7475, row7476, row7477]

def rows3_3 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7478, row7479, row7480, row7481, row7482, row7483, row7484, row7485, row7486, row7487, row7488, row7489, row7490, row7491, row7492, row7493]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7494, row7495, row7496, row7497, row7498, row7499, row7500, row7501, row7502, row7503, row7504, row7505, row7506, row7507, row7508, row7509]

def rows4_1 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7510, row7511, row7512, row7513, row7514, row7515, row7516, row7517, row7518, row7519, row7520, row7521, row7522, row7523, row7524, row7525]

def rows4_2 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7526, row7527, row7528, row7529, row7530, row7531, row7532, row7533, row7534, row7535, row7536, row7537, row7538, row7539, row7540, row7541]

def rows4_3 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7542, row7543, row7544, row7545, row7546, row7547, row7548, row7549, row7550, row7551, row7552, row7553, row7554, row7555, row7556, row7557]

def rows4_4 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7558, row7559, row7560, row7561, row7562, row7563, row7564, row7565, row7566, row7567, row7568, row7569, row7570, row7571, row7572, row7573]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7574, row7575, row7576, row7577, row7578, row7579, row7580, row7581, row7582, row7583, row7584, row7585, row7586, row7587, row7588, row7589, row7590, row7591, row7592, row7593, row7594, row7595, row7596, row7597, row7598, row7599, row7600, row7601, row7602, row7603, row7604, row7605, row7606, row7607, row7608, row7609]

def rows5_1 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7610, row7611, row7612, row7613, row7614, row7615, row7616, row7617, row7618, row7619, row7620, row7621, row7622, row7623, row7624, row7625, row7626, row7627, row7628, row7629, row7630, row7631, row7632, row7633, row7634, row7635, row7636, row7637, row7638, row7639, row7640, row7641, row7642, row7643, row7644, row7645]

def rows5_2 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7646, row7647, row7648, row7649, row7650, row7651, row7652, row7653, row7654, row7655, row7656, row7657, row7658, row7659, row7660, row7661, row7662, row7663, row7664, row7665, row7666, row7667, row7668, row7669, row7670, row7671, row7672, row7673, row7674, row7675, row7676, row7677, row7678, row7679, row7680, row7681]

def rows5_3 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7682, row7683, row7684, row7685, row7686, row7687, row7688, row7689, row7690, row7691, row7692, row7693, row7694, row7695, row7696, row7697, row7698, row7699, row7700, row7701, row7702, row7703, row7704, row7705, row7706, row7707, row7708, row7709, row7710, row7711, row7712, row7713, row7714, row7715, row7716, row7717]

def rows5_4 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7718, row7719, row7720, row7721, row7722, row7723, row7724, row7725, row7726, row7727, row7728, row7729, row7730, row7731, row7732, row7733, row7734, row7735, row7736, row7737, row7738, row7739, row7740, row7741, row7742, row7743, row7744, row7745, row7746, row7747, row7748, row7749, row7750, row7751, row7752, row7753]

def rows5_5 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7754, row7755, row7756, row7757, row7758, row7759, row7760, row7761, row7762, row7763, row7764, row7765, row7766, row7767, row7768, row7769, row7770, row7771, row7772, row7773, row7774, row7775, row7776, row7777, row7778, row7779, row7780, row7781, row7782, row7783, row7784, row7785, row7786, row7787, row7788, row7789]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7790, row7791, row7792, row7793, row7794]

def rows6_1 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7795, row7796, row7797, row7798, row7799]

def rows6_2 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7800, row7801, row7802, row7803, row7804]

def rows6_3 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7805, row7806, row7807, row7808, row7809]

def rows6_4 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7810, row7811, row7812, row7813, row7814]

def rows6_5 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7815, row7816, row7817, row7818, row7819]

def rows6_6 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7820, row7821, row7822, row7823, row7824]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7825, row7826, row7827, row7828, row7829, row7830, row7831, row7832, row7833, row7834, row7835, row7836, row7574, row7575, row7576, row7577, row7578, row7579, row7580, row7581, row7582, row7583, row7584, row7585]

def rows7_1 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7837, row7838, row7839, row7840, row7841, row7842, row7843, row7844, row7845, row7846, row7847, row7848, row7610, row7611, row7612, row7613, row7614, row7615, row7616, row7617, row7618, row7619, row7620, row7621]

def rows7_2 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7849, row7850, row7851, row7852, row7853, row7854, row7855, row7856, row7857, row7858, row7859, row7860, row7646, row7647, row7648, row7649, row7650, row7651, row7652, row7653, row7654, row7655, row7656, row7657]

def rows7_3 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7861, row7862, row7863, row7864, row7865, row7866, row7867, row7868, row7869, row7870, row7871, row7872, row7682, row7683, row7684, row7685, row7686, row7687, row7688, row7689, row7690, row7691, row7692, row7693]

def rows7_4 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7873, row7874, row7875, row7876, row7877, row7878, row7879, row7880, row7881, row7882, row7883, row7884, row7718, row7719, row7720, row7721, row7722, row7723, row7724, row7725, row7726, row7727, row7728, row7729]

def rows7_5 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7885, row7886, row7887, row7888, row7889, row7890, row7891, row7892, row7893, row7894, row7895, row7896, row7754, row7755, row7756, row7757, row7758, row7759, row7760, row7761, row7762, row7763, row7764, row7765]

def rows7_6 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7897, row7898, row7899, row7900, row7901, row7902, row7903, row7904, row7905, row7906, row7907, row7908, row7909, row7910, row7911, row7912, row7913, row7914, row7915, row7916, row7917, row7918, row7919, row7920]

def rows7_7 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7921, row7922, row7923, row7924, row7925, row7926, row7927, row7928, row7929, row7930, row7931, row7932, row7933, row7934, row7935, row7936, row7937, row7938, row7939, row7940, row7941, row7942, row7943, row7944]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row7945, row7946, row7947, row7948, row7949, row7950, row7951, row7952, row7953, row7954, row7955, row7956, row7957, row7958, row7959, row7960, row7961, row7962, row7963, row7964, row7965, row7966, row7967, row7968, row7969, row7970, row7971, row7972, row7973, row7974, row7975, row7976, row7977, row7978, row7979, row7980]

def rows8_1 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row7981, row7982, row7983, row7984, row7985, row7986, row7987, row7988, row7989, row7990, row7991, row7992, row7993, row7994, row7995, row7996, row7997, row7998, row7999, row8000, row8001, row8002, row8003, row8004, row8005, row8006, row8007, row8008, row8009, row8010, row8011, row8012, row8013, row8014, row8015, row8016]

def rows8_2 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8017, row8018, row8019, row8020, row8021, row8022, row8023, row8024, row8025, row8026, row8027, row8028, row8029, row8030, row8031, row8032, row8033, row8034, row8035, row8036, row8037, row8038, row8039, row8040, row8041, row8042, row8043, row8044, row8045, row8046, row8047, row8048, row8049, row8050, row8051, row8052]

def rows8_3 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8053, row8054, row8055, row8056, row8057, row8058, row8059, row8060, row8061, row8062, row8063, row8064, row8065, row8066, row8067, row8068, row8069, row8070, row8071, row8072, row8073, row8074, row8075, row8076, row8077, row8078, row8079, row8080, row8081, row8082, row8083, row8084, row8085, row8086, row8087, row8088]

def rows8_4 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8089, row8090, row8091, row8092, row8093, row8094, row8095, row8096, row8097, row8098, row8099, row8100, row8101, row8102, row8103, row8104, row8105, row8106, row8107, row8108, row8109, row8110, row8111, row8112, row8113, row8114, row8115, row8116, row8117, row8118, row8119, row8120, row8121, row8122, row8123, row8124]

def rows8_5 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8125, row8126, row8127, row8128, row8129, row8130, row8131, row8132, row8133, row8134, row8135, row8136, row8137, row8138, row8139, row8140, row8141, row8142, row8143, row8144, row8145, row8146, row8147, row8148, row8149, row8150, row8151, row8152, row8153, row8154, row8155, row8156, row8157, row8158, row8159, row8160]

def rows8_6 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8161, row8162, row8163, row8164, row8165, row8166, row8167, row8168, row8169, row8170, row8171, row8172, row8173, row8174, row8175, row8176, row8177, row8178, row8179, row8180, row8181, row8182, row8183, row8184, row8185, row8186, row8187, row8188, row8189, row8190, row8191, row8192, row8193, row8194, row8195, row8196]

def rows8_7 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8197, row8198, row8199, row8200, row8201, row8202, row8203, row8204, row8205, row8206, row8207, row8208, row8209, row8210, row8211, row8212, row8213, row8214, row8215, row8216, row8217, row8218, row8219, row8220, row8221, row8222, row8223, row8224, row8225, row8226, row8227, row8228, row8229, row8230, row8231, row8232]

def rows8_8 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8233, row8234, row8235, row8236, row8237, row8238, row8239, row8240, row8241, row8242, row8243, row8244, row8245, row8246, row8247, row8248, row8249, row8250, row8251, row8252, row8253, row8254, row8255, row8256, row8257, row8258, row8259, row8260, row8261, row8262, row8263, row8264, row8265, row8266, row8267, row8268]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7586, row7587, row7588, row7589, row7590, row7591, row7592, row7593, row7594, row7595, row7596, row7597, row7598, row7599, row7600, row7601, row7602, row7603, row7604, row7605, row7606, row7607, row7608, row7609, row8269, row8270, row8271, row8272, row8273, row8274, row8275, row8276, row8277, row8278, row8279, row8280]

def rows9_1 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7622, row7623, row7624, row7625, row7626, row7627, row7628, row7629, row7630, row7631, row7632, row7633, row7634, row7635, row7636, row7637, row7638, row7639, row7640, row7641, row7642, row7643, row7644, row7645, row8281, row8282, row8283, row8284, row8285, row8286, row8287, row8288, row8289, row8290, row8291, row8292]

def rows9_2 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7658, row7659, row7660, row7661, row7662, row7663, row7664, row7665, row7666, row7667, row7668, row7669, row7670, row7671, row7672, row7673, row7674, row7675, row7676, row7677, row7678, row7679, row7680, row7681, row8293, row8294, row8295, row8296, row8297, row8298, row8299, row8300, row8301, row8302, row8303, row8304]

def rows9_3 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7694, row7695, row7696, row7697, row7698, row7699, row7700, row7701, row7702, row7703, row7704, row7705, row7706, row7707, row7708, row7709, row7710, row7711, row7712, row7713, row7714, row7715, row7716, row7717, row8305, row8306, row8307, row8308, row8309, row8310, row8311, row8312, row8313, row8314, row8315, row8316]

def rows9_4 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7730, row7731, row7732, row7733, row7734, row7735, row7736, row7737, row7738, row7739, row7740, row7741, row7742, row7743, row7744, row7745, row7746, row7747, row7748, row7749, row7750, row7751, row7752, row7753, row8317, row8318, row8319, row8320, row8321, row8322, row8323, row8324, row8325, row8326, row8327, row8328]

def rows9_5 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7766, row7767, row7768, row7769, row7770, row7771, row7772, row7773, row7774, row7775, row7776, row7777, row7778, row7779, row7780, row7781, row7782, row7783, row7784, row7785, row7786, row7787, row7788, row7789, row8329, row8330, row8331, row8332, row8333, row8334, row8335, row8336, row8337, row8338, row8339, row8340]

def rows9_6 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8341, row8342, row8343, row8344, row8345, row8346, row8347, row8348, row8349, row8350, row8351, row8352, row8353, row8354, row8355, row8356, row8357, row8358, row8359, row8360, row8361, row8362, row8363, row8364, row8365, row8366, row8367, row8368, row8369, row8370, row8371, row8372, row8373, row8374, row8375, row8376]

def rows9_7 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8377, row8378, row8379, row8380, row8381, row8382, row8383, row8384, row8385, row8386, row8387, row8388, row8389, row8390, row8391, row8392, row8393, row8394, row8395, row8396, row8397, row8398, row8399, row8400, row8401, row8402, row8403, row8404, row8405, row8406, row8407, row8408, row8409, row8410, row8411, row8412]

def rows9_8 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8413, row8414, row8415, row8416, row8417, row8418, row8419, row8420, row8421, row8422, row8423, row8424, row8425, row8426, row8427, row8428, row8429, row8430, row8431, row8432, row8433, row8434, row8435, row8436, row8437, row8438, row8439, row8440, row8441, row8442, row8443, row8444, row8445, row8446, row8447, row8448]

def rows9_9 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8449, row8450, row8451, row8452, row8453, row8454, row8455, row8456, row8457, row8458, row8459, row8460, row8461, row8462, row8463, row8464, row8465, row8466, row8467, row8468, row8469, row8470, row8471, row8472, row8473, row8474, row8475, row8476, row8477, row8478, row8479, row8480, row8481, row8482, row8483, row8484]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization

def entries : Fin 22 → Fin 22 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0, entry5_0, entry6_0, entry7_0, entry8_0, entry9_0, entry10_0, entry11_0, entry12_0, entry13_0, entry14_0, entry15_0, entry16_0, entry17_0, entry18_0, entry19_0, entry20_0, entry21_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1, entry5_1, entry6_1, entry7_1, entry8_1, entry9_1, entry10_1, entry11_1, entry12_1, entry13_1, entry14_1, entry15_1, entry16_1, entry17_1, entry18_1, entry19_1, entry20_1, entry21_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2, entry5_2, entry6_2, entry7_2, entry8_2, entry9_2, entry10_2, entry11_2, entry12_2, entry13_2, entry14_2, entry15_2, entry16_2, entry17_2, entry18_2, entry19_2, entry20_2, entry21_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3, entry5_3, entry6_3, entry7_3, entry8_3, entry9_3, entry10_3, entry11_3, entry12_3, entry13_3, entry14_3, entry15_3, entry16_3, entry17_3, entry18_3, entry19_3, entry20_3, entry21_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4, entry5_4, entry6_4, entry7_4, entry8_4, entry9_4, entry10_4, entry11_4, entry12_4, entry13_4, entry14_4, entry15_4, entry16_4, entry17_4, entry18_4, entry19_4, entry20_4, entry21_4],
  ![entry5_0, entry5_1, entry5_2, entry5_3, entry5_4, entry5_5, entry6_5, entry7_5, entry8_5, entry9_5, entry10_5, entry11_5, entry12_5, entry13_5, entry14_5, entry15_5, entry16_5, entry17_5, entry18_5, entry19_5, entry20_5, entry21_5],
  ![entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry7_6, entry8_6, entry9_6, entry10_6, entry11_6, entry12_6, entry13_6, entry14_6, entry15_6, entry16_6, entry17_6, entry18_6, entry19_6, entry20_6, entry21_6],
  ![entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry8_7, entry9_7, entry10_7, entry11_7, entry12_7, entry13_7, entry14_7, entry15_7, entry16_7, entry17_7, entry18_7, entry19_7, entry20_7, entry21_7],
  ![entry8_0, entry8_1, entry8_2, entry8_3, entry8_4, entry8_5, entry8_6, entry8_7, entry8_8, entry9_8, entry10_8, entry11_8, entry12_8, entry13_8, entry14_8, entry15_8, entry16_8, entry17_8, entry18_8, entry19_8, entry20_8, entry21_8],
  ![entry9_0, entry9_1, entry9_2, entry9_3, entry9_4, entry9_5, entry9_6, entry9_7, entry9_8, entry9_9, entry10_9, entry11_9, entry12_9, entry13_9, entry14_9, entry15_9, entry16_9, entry17_9, entry18_9, entry19_9, entry20_9, entry21_9],
  ![entry10_0, entry10_1, entry10_2, entry10_3, entry10_4, entry10_5, entry10_6, entry10_7, entry10_8, entry10_9, entry10_10, entry11_10, entry12_10, entry13_10, entry14_10, entry15_10, entry16_10, entry17_10, entry18_10, entry19_10, entry20_10, entry21_10],
  ![entry11_0, entry11_1, entry11_2, entry11_3, entry11_4, entry11_5, entry11_6, entry11_7, entry11_8, entry11_9, entry11_10, entry11_11, entry12_11, entry13_11, entry14_11, entry15_11, entry16_11, entry17_11, entry18_11, entry19_11, entry20_11, entry21_11],
  ![entry12_0, entry12_1, entry12_2, entry12_3, entry12_4, entry12_5, entry12_6, entry12_7, entry12_8, entry12_9, entry12_10, entry12_11, entry12_12, entry13_12, entry14_12, entry15_12, entry16_12, entry17_12, entry18_12, entry19_12, entry20_12, entry21_12],
  ![entry13_0, entry13_1, entry13_2, entry13_3, entry13_4, entry13_5, entry13_6, entry13_7, entry13_8, entry13_9, entry13_10, entry13_11, entry13_12, entry13_13, entry14_13, entry15_13, entry16_13, entry17_13, entry18_13, entry19_13, entry20_13, entry21_13],
  ![entry14_0, entry14_1, entry14_2, entry14_3, entry14_4, entry14_5, entry14_6, entry14_7, entry14_8, entry14_9, entry14_10, entry14_11, entry14_12, entry14_13, entry14_14, entry15_14, entry16_14, entry17_14, entry18_14, entry19_14, entry20_14, entry21_14],
  ![entry15_0, entry15_1, entry15_2, entry15_3, entry15_4, entry15_5, entry15_6, entry15_7, entry15_8, entry15_9, entry15_10, entry15_11, entry15_12, entry15_13, entry15_14, entry15_15, entry16_15, entry17_15, entry18_15, entry19_15, entry20_15, entry21_15],
  ![entry16_0, entry16_1, entry16_2, entry16_3, entry16_4, entry16_5, entry16_6, entry16_7, entry16_8, entry16_9, entry16_10, entry16_11, entry16_12, entry16_13, entry16_14, entry16_15, entry16_16, entry17_16, entry18_16, entry19_16, entry20_16, entry21_16],
  ![entry17_0, entry17_1, entry17_2, entry17_3, entry17_4, entry17_5, entry17_6, entry17_7, entry17_8, entry17_9, entry17_10, entry17_11, entry17_12, entry17_13, entry17_14, entry17_15, entry17_16, entry17_17, entry18_17, entry19_17, entry20_17, entry21_17],
  ![entry18_0, entry18_1, entry18_2, entry18_3, entry18_4, entry18_5, entry18_6, entry18_7, entry18_8, entry18_9, entry18_10, entry18_11, entry18_12, entry18_13, entry18_14, entry18_15, entry18_16, entry18_17, entry18_18, entry19_18, entry20_18, entry21_18],
  ![entry19_0, entry19_1, entry19_2, entry19_3, entry19_4, entry19_5, entry19_6, entry19_7, entry19_8, entry19_9, entry19_10, entry19_11, entry19_12, entry19_13, entry19_14, entry19_15, entry19_16, entry19_17, entry19_18, entry19_19, entry20_19, entry21_19],
  ![entry20_0, entry20_1, entry20_2, entry20_3, entry20_4, entry20_5, entry20_6, entry20_7, entry20_8, entry20_9, entry20_10, entry20_11, entry20_12, entry20_13, entry20_14, entry20_15, entry20_16, entry20_17, entry20_18, entry20_19, entry20_20, entry21_20],
  ![entry21_0, entry21_1, entry21_2, entry21_3, entry21_4, entry21_5, entry21_6, entry21_7, entry21_8, entry21_9, entry21_10, entry21_11, entry21_12, entry21_13, entry21_14, entry21_15, entry21_16, entry21_17, entry21_18, entry21_19, entry21_20, entry21_21]
]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block4.form0.size → Integer.Sparse Key := ![row13187, row13188, row13189, row13190, row13191, row13192, row13193, row13194, row13195, row13196, row13197, row13198, row13199, row13200, row13201, row13202, row13203, row13204]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block4.form1.size → Integer.Sparse Key := ![row13205, row13206, row13207, row13208, row13209, row13210, row13211, row13212, row13213, row13214, row13215, row13216, row13217, row13218, row13219, row13220, row13221, row13222, row13223, row13224]

def rows1_1 : Fin GramFunctions.Block4.form1.size → Integer.Sparse Key := ![row13225, row13226, row13227, row13228, row13229, row13230, row13231, row13232, row13233, row13234, row13235, row13236, row13237, row13238, row13239, row13240, row13241, row13242, row13243, row13244]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14205, row14206, row14207, row14208, row14209, row14210, row14211, row14212, row14213, row14214, row14215, row14216, row14217, row14218, row14219, row14220, row14221, row14222, row14223, row14224, row14225, row14226, row14227, row14228, row14229, row14230, row14231, row14232, row14233, row14234, row14235, row14236, row14237, row14238, row14239, row14240]

def rows10_1 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14241, row14242, row14243, row14244, row14245, row14246, row14247, row14248, row14249, row14250, row14251, row14252, row14253, row14254, row14255, row14256, row14257, row14258, row14259, row14260, row14261, row14262, row14263, row14264, row14265, row14266, row14267, row14268, row14269, row14270, row14271, row14272, row14273, row14274, row14275, row14276]

def rows10_2 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14277, row14278, row14279, row14280, row14281, row14282, row14283, row14284, row14285, row14286, row14287, row14288, row14289, row14290, row14291, row14292, row14293, row14294, row14295, row14296, row14297, row14298, row14299, row14300, row14301, row14302, row14303, row14304, row14305, row14306, row14307, row14308, row14309, row14310, row14311, row14312]

def rows10_3 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14313, row14314, row14315, row14316, row14317, row14318, row14319, row14320, row14321, row14322, row14323, row14324, row14325, row14326, row14327, row14328, row14329, row14330, row14331, row14332, row14333, row14334, row14335, row14336, row14337, row14338, row14339, row14340, row14341, row14342, row14343, row14344, row14345, row14346, row14347, row14348]

def rows10_4 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14349, row14350, row14351, row14352, row14353, row14354, row14355, row14356, row14357, row14358, row14359, row14360, row14361, row14362, row14363, row14364, row14365, row14366, row14367, row14368, row14369, row14370, row14371, row14372, row14373, row14374, row14375, row14376, row14377, row14378, row14379, row14380, row14381, row14382, row14383, row14384]

def rows10_5 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14385, row14386, row14387, row14388, row14389, row14390, row14391, row14392, row14393, row14394, row14395, row14396, row14397, row14398, row14399, row14400, row14401, row14402, row14403, row14404, row14405, row14406, row14407, row14408, row14409, row14410, row14411, row14412, row14413, row14414, row14415, row14416, row14417, row14418, row14419, row14420]

def rows10_6 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14421, row14422, row14423, row14424, row14425, row14426, row14427, row14428, row14429, row14430, row14431, row14432, row14433, row14434, row14435, row14436, row14437, row14438, row14439, row14440, row14441, row14442, row14443, row14444, row14445, row14446, row14447, row14448, row14449, row14450, row14451, row14452, row14453, row14454, row14455, row14456]

def rows10_7 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14457, row14458, row14459, row14460, row14461, row14462, row14463, row14464, row14465, row14466, row14467, row14468, row14469, row14470, row14471, row14472, row14473, row14474, row14475, row14476, row14477, row14478, row14479, row14480, row14481, row14482, row14483, row14484, row14485, row14486, row14487, row14488, row14489, row14490, row14491, row14492]

def rows10_8 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14493, row14494, row14495, row14496, row14497, row14498, row14499, row14500, row14501, row14502, row14503, row14504, row14505, row14506, row14507, row14508, row14509, row14510, row14511, row14512, row14513, row14514, row14515, row14516, row14517, row14518, row14519, row14520, row14521, row14522, row14523, row14524, row14525, row14526, row14527, row14528]

def rows10_9 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14529, row14530, row14531, row14532, row14533, row14534, row14535, row14536, row14537, row14538, row14539, row14540, row14541, row14542, row14543, row14544, row14545, row14546, row14547, row14548, row14549, row14550, row14551, row14552, row14553, row14554, row14555, row14556, row14557, row14558, row14559, row14560, row14561, row14562, row14563, row14564]

def rows10_10 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14565, row14566, row14567, row14568, row14569, row14570, row14571, row14572, row14573, row14574, row14575, row14576, row14577, row14578, row14579, row14580, row14581, row14582, row14583, row14584, row14585, row14586, row14587, row14588, row14589, row14590, row14591, row14592, row14593, row14594, row14595, row14596, row14597, row14598, row14599, row14600]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14601, row14602, row14603, row14604, row14605, row14606, row14607, row14608, row14609, row14610, row14611, row14612, row14613, row14614, row14615, row14616, row14617, row14618, row14619, row14620]

def rows11_1 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14621, row14622, row14623, row14624, row14625, row14626, row14627, row14628, row14629, row14630, row14631, row14632, row14633, row14634, row14635, row14636, row14637, row14638, row14639, row14640]

def rows11_2 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14641, row14642, row14643, row14644, row14645, row14646, row14647, row14648, row14649, row14650, row14651, row14652, row14653, row14654, row14655, row14656, row14657, row14658, row14659, row14660]

def rows11_3 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14661, row14662, row14663, row14664, row14665, row14666, row14667, row14668, row14669, row14670, row14671, row14672, row14673, row14674, row14675, row14676, row14677, row14678, row14679, row14680]

def rows11_4 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14681, row14682, row14683, row14684, row14685, row14686, row14687, row14688, row14689, row14690, row14691, row14692, row14693, row14694, row14695, row14696, row14697, row14698, row14699, row14700]

def rows11_5 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14701, row14702, row14703, row14704, row14705, row14706, row14707, row14708, row14709, row14710, row14711, row14712, row14713, row14714, row14715, row14716, row14717, row14718, row14719, row14720]

def rows11_6 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14721, row14722, row14723, row14724, row14725, row14726, row14727, row14728, row14729, row14730, row14731, row14732, row14733, row14734, row14735, row14736, row14737, row14738, row14739, row14740]

def rows11_7 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14741, row14742, row14743, row14744, row14745, row14746, row14747, row14748, row14749, row14750, row14751, row14752, row14753, row14754, row14755, row14756, row14757, row14758, row14759, row14760]

def rows11_8 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14761, row14762, row14763, row14764, row14765, row14766, row14767, row14768, row14769, row14770, row14771, row14772, row14773, row14774, row14775, row14776, row14777, row14778, row14779, row14780]

def rows11_9 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14781, row14782, row14783, row14784, row14785, row14786, row14787, row14788, row14789, row14790, row14791, row14792, row14793, row14794, row14795, row14796, row14797, row14798, row14799, row14800]

def rows11_10 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14801, row14802, row14803, row14804, row14805, row14806, row14807, row14808, row14809, row14810, row14811, row14812, row14813, row14814, row14815, row14816, row14817, row14818, row14819, row14820]

def rows11_11 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14821, row14822, row14823, row14824, row14825, row14826, row14827, row14828, row14829, row14830, row14831, row14832, row14833, row14834, row14835, row14836, row14837, row14838, row14839, row14840]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14841, row14842, row14843, row14844, row14845, row14846, row14847, row14848, row14849, row13190, row13191, row13192, row13193, row13194, row13195, row14850, row14851, row14852, row13196, row13197, row13198, row13199, row13200, row13201, row13202, row13203, row13204]

def rows12_1 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14853, row14854, row14855, row14856, row14857, row14858, row14859, row14860, row14861, row14862, row14863, row14864, row14865, row14866, row14867, row14868, row14869, row14870, row14871, row14872, row14873, row14874, row14875, row14876, row14877, row14878, row14879]

def rows12_2 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14880, row14881, row14882, row14883, row14884, row14885, row14886, row14887, row14888, row14889, row14890, row14891, row14892, row14893, row14894, row14895, row14896, row14897, row14898, row14899, row14900, row14901, row14902, row14903, row14904, row14905, row14906]

def rows12_3 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14907, row14908, row14909, row14910, row14911, row14912, row14913, row14914, row14915, row14916, row14917, row14918, row14919, row14920, row14921, row14922, row14923, row14924, row14925, row14926, row14927, row14928, row14929, row14930, row14931, row14932, row14933]

def rows12_4 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14934, row14935, row14936, row14937, row14938, row14939, row14940, row14941, row14942, row14943, row14944, row14945, row14946, row14947, row14948, row14949, row14950, row14951, row14952, row14953, row14954, row14955, row14956, row14957, row14958, row14959, row14960]

def rows12_5 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14961, row14962, row14963, row14964, row14965, row14966, row14967, row14968, row14969, row14970, row14971, row14972, row14973, row14974, row14975, row14976, row14977, row14978, row14979, row14980, row14981, row14982, row14983, row14984, row14985, row14986, row14987]

def rows12_6 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14988, row14989, row14990, row14991, row14992, row14993, row14994, row14995, row14996, row14997, row14998, row14999, row15000, row15001, row15002, row15003, row15004, row15005, row15006, row15007, row15008, row15009, row15010, row15011, row15012, row15013, row15014]

def rows12_7 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15015, row15016, row15017, row15018, row15019, row15020, row15021, row15022, row15023, row15024, row15025, row15026, row15027, row15028, row15029, row15030, row15031, row15032, row15033, row15034, row15035, row15036, row15037, row15038, row15039, row15040, row15041]

def rows12_8 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15042, row15043, row15044, row15045, row15046, row15047, row15048, row15049, row15050, row15051, row15052, row15053, row15054, row15055, row15056, row15057, row15058, row15059, row15060, row15061, row15062, row15063, row15064, row15065, row15066, row15067, row15068]

def rows12_9 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15069, row15070, row15071, row15072, row15073, row15074, row15075, row15076, row15077, row15078, row15079, row15080, row15081, row15082, row15083, row15084, row15085, row15086, row15087, row15088, row15089, row15090, row15091, row15092, row15093, row15094, row15095]

def rows12_10 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15096, row15097, row15098, row15099, row15100, row15101, row15102, row15103, row15104, row15105, row15106, row15107, row15108, row15109, row15110, row15111, row15112, row15113, row15114, row15115, row15116, row15117, row15118, row15119, row15120, row15121, row15122]

def rows12_11 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15123, row15124, row15125, row15126, row15127, row15128, row15129, row15130, row15131, row15132, row15133, row15134, row15135, row15136, row15137, row15138, row15139, row15140, row15141, row15142, row15143, row15144, row15145, row15146, row15147, row15148, row15149]

def rows12_12 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15150, row15151, row15152, row15153, row15154, row15155, row15156, row15157, row15158, row15159, row15160, row15161, row15162, row15163, row15164, row15165, row15166, row15167, row15168, row15169, row15170, row15171, row15172, row15173, row15174, row15175, row15176]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15177, row15178, row15179, row15180, row15181, row15182, row15183, row15184, row15185, row15186, row15187, row15188, row13593, row13594, row13595, row13596, row13597, row13598, row15189, row15190, row15191, row15192, row15193, row15194, row13602, row13603, row13604, row13605, row13606, row13607, row13608, row13609, row13610, row13611, row13612, row13613]

def rows13_1 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15195, row15196, row15197, row15198, row15199, row15200, row15201, row15202, row15203, row15204, row15205, row15206, row13629, row13630, row13631, row13632, row13633, row13634, row15207, row15208, row15209, row15210, row15211, row15212, row13638, row13639, row13640, row13641, row13642, row13643, row13644, row13645, row13646, row13647, row13648, row13649]

def rows13_2 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15213, row15214, row15215, row15216, row15217, row15218, row15219, row15220, row15221, row15222, row15223, row15224, row13665, row13666, row13667, row13668, row13669, row13670, row15225, row15226, row15227, row15228, row15229, row15230, row13674, row13675, row13676, row13677, row13678, row13679, row13680, row13681, row13682, row13683, row13684, row13685]

def rows13_3 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15231, row15232, row15233, row15234, row15235, row15236, row15237, row15238, row15239, row15240, row15241, row15242, row13701, row13702, row13703, row13704, row13705, row13706, row15243, row15244, row15245, row15246, row15247, row15248, row13710, row13711, row13712, row13713, row13714, row13715, row13716, row13717, row13718, row13719, row13720, row13721]

def rows13_4 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15249, row15250, row15251, row15252, row15253, row15254, row15255, row15256, row15257, row15258, row15259, row15260, row13737, row13738, row13739, row13740, row13741, row13742, row15261, row15262, row15263, row15264, row15265, row15266, row13746, row13747, row13748, row13749, row13750, row13751, row13752, row13753, row13754, row13755, row13756, row13757]

def rows13_5 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15267, row15268, row15269, row15270, row15271, row15272, row15273, row15274, row15275, row15276, row15277, row15278, row13773, row13774, row13775, row13776, row13777, row13778, row15279, row15280, row15281, row15282, row15283, row15284, row13782, row13783, row13784, row13785, row13786, row13787, row13788, row13789, row13790, row13791, row13792, row13793]

def rows13_6 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15285, row15286, row15287, row15288, row15289, row15290, row15291, row15292, row15293, row15294, row15295, row15296, row13809, row13810, row13811, row13812, row13813, row13814, row15297, row15298, row15299, row15300, row15301, row15302, row13818, row13819, row13820, row13821, row13822, row13823, row13824, row13825, row13826, row13827, row13828, row13829]

def rows13_7 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15303, row15304, row15305, row15306, row15307, row15308, row15309, row15310, row15311, row15312, row15313, row15314, row15315, row15316, row15317, row15318, row15319, row15320, row15321, row15322, row15323, row15324, row15325, row15326, row15327, row15328, row15329, row15330, row15331, row15332, row15333, row15334, row15335, row15336, row15337, row15338]

def rows13_8 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15339, row15340, row15341, row15342, row15343, row15344, row15345, row15346, row15347, row15348, row15349, row15350, row15351, row15352, row15353, row15354, row15355, row15356, row15357, row15358, row15359, row15360, row15361, row15362, row15363, row15364, row15365, row15366, row15367, row15368, row15369, row15370, row15371, row15372, row15373, row15374]

def rows13_9 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15375, row15376, row15377, row15378, row15379, row15380, row15381, row15382, row15383, row15384, row15385, row15386, row15387, row15388, row15389, row15390, row15391, row15392, row15393, row15394, row15395, row15396, row15397, row15398, row15399, row15400, row15401, row15402, row15403, row15404, row15405, row15406, row15407, row15408, row15409, row15410]

def rows13_10 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15411, row15412, row15413, row15414, row15415, row15416, row15417, row15418, row15419, row15420, row15421, row15422, row15423, row15424, row15425, row15426, row15427, row15428, row15429, row15430, row15431, row15432, row15433, row15434, row15435, row15436, row15437, row15438, row15439, row15440, row15441, row15442, row15443, row15444, row15445, row15446]

def rows13_11 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15447, row15448, row15449, row15450, row15451, row15452, row15453, row15454, row15455, row15456, row15457, row15458, row15459, row15460, row15461, row15462, row15463, row15464, row15465, row15466, row15467, row15468, row15469, row15470, row15471, row15472, row15473, row15474, row15475, row15476, row15477, row15478, row15479, row15480, row15481, row15482]

def rows13_12 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15483, row15484, row15485, row15486, row15487, row15488, row15489, row15490, row15491, row15492, row15493, row15494, row15495, row15496, row15497, row15498, row15499, row15500, row15501, row15502, row15503, row15504, row15505, row15506, row15507, row15508, row15509, row15510, row15511, row15512, row15513, row15514, row15515, row15516, row15517, row15518]

def rows13_13 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15519, row15520, row15521, row15522, row15523, row15524, row15525, row15526, row15527, row15528, row15529, row15530, row15531, row15532, row15533, row15534, row15535, row15536, row15537, row15538, row15539, row15540, row15541, row15542, row15543, row15544, row15545, row15546, row15547, row15548, row15549, row15550, row15551, row15552, row15553, row15554]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15180, row15181, row15182, row15183, row15184, row15185, row15555, row15556, row15557, row13593, row13594, row13595, row13596, row13597, row13598, row13599, row13600, row13601, row15189, row15190, row15191, row15192, row15193, row15194, row13602, row13603, row13604, row13605, row13606, row13607, row15558, row15559, row15560, row13620, row13621, row13622]

def rows14_1 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15198, row15199, row15200, row15201, row15202, row15203, row15561, row15562, row15563, row13629, row13630, row13631, row13632, row13633, row13634, row13635, row13636, row13637, row15207, row15208, row15209, row15210, row15211, row15212, row13638, row13639, row13640, row13641, row13642, row13643, row15564, row15565, row15566, row13656, row13657, row13658]

def rows14_2 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15216, row15217, row15218, row15219, row15220, row15221, row15567, row15568, row15569, row13665, row13666, row13667, row13668, row13669, row13670, row13671, row13672, row13673, row15225, row15226, row15227, row15228, row15229, row15230, row13674, row13675, row13676, row13677, row13678, row13679, row15570, row15571, row15572, row13692, row13693, row13694]

def rows14_3 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15234, row15235, row15236, row15237, row15238, row15239, row15573, row15574, row15575, row13701, row13702, row13703, row13704, row13705, row13706, row13707, row13708, row13709, row15243, row15244, row15245, row15246, row15247, row15248, row13710, row13711, row13712, row13713, row13714, row13715, row15576, row15577, row15578, row13728, row13729, row13730]

def rows14_4 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15252, row15253, row15254, row15255, row15256, row15257, row15579, row15580, row15581, row13737, row13738, row13739, row13740, row13741, row13742, row13743, row13744, row13745, row15261, row15262, row15263, row15264, row15265, row15266, row13746, row13747, row13748, row13749, row13750, row13751, row15582, row15583, row15584, row13764, row13765, row13766]

def rows14_5 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15270, row15271, row15272, row15273, row15274, row15275, row15585, row15586, row15587, row13773, row13774, row13775, row13776, row13777, row13778, row13779, row13780, row13781, row15279, row15280, row15281, row15282, row15283, row15284, row13782, row13783, row13784, row13785, row13786, row13787, row15588, row15589, row15590, row13800, row13801, row13802]

def rows14_6 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15288, row15289, row15290, row15291, row15292, row15293, row15591, row15592, row15593, row13809, row13810, row13811, row13812, row13813, row13814, row13815, row13816, row13817, row15297, row15298, row15299, row15300, row15301, row15302, row13818, row13819, row13820, row13821, row13822, row13823, row15594, row15595, row15596, row13836, row13837, row13838]

def rows14_7 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15306, row15307, row15308, row15309, row15310, row15311, row15597, row15598, row15599, row15315, row15316, row15317, row15318, row15319, row15320, row15600, row15601, row15602, row15321, row15322, row15323, row15324, row15325, row15326, row15327, row15328, row15329, row15330, row15331, row15332, row15603, row15604, row15605, row15606, row15607, row15608]

def rows14_8 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15342, row15343, row15344, row15345, row15346, row15347, row15609, row15610, row15611, row15351, row15352, row15353, row15354, row15355, row15356, row15612, row15613, row15614, row15357, row15358, row15359, row15360, row15361, row15362, row15363, row15364, row15365, row15366, row15367, row15368, row15615, row15616, row15617, row15618, row15619, row15620]

def rows14_9 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15378, row15379, row15380, row15381, row15382, row15383, row15621, row15622, row15623, row15387, row15388, row15389, row15390, row15391, row15392, row15624, row15625, row15626, row15393, row15394, row15395, row15396, row15397, row15398, row15399, row15400, row15401, row15402, row15403, row15404, row15627, row15628, row15629, row15630, row15631, row15632]

def rows14_10 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15414, row15415, row15416, row15417, row15418, row15419, row15633, row15634, row15635, row15423, row15424, row15425, row15426, row15427, row15428, row15636, row15637, row15638, row15429, row15430, row15431, row15432, row15433, row15434, row15435, row15436, row15437, row15438, row15439, row15440, row15639, row15640, row15641, row15642, row15643, row15644]

def rows14_11 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15450, row15451, row15452, row15453, row15454, row15455, row15645, row15646, row15647, row15459, row15460, row15461, row15462, row15463, row15464, row15648, row15649, row15650, row15465, row15466, row15467, row15468, row15469, row15470, row15471, row15472, row15473, row15474, row15475, row15476, row15651, row15652, row15653, row15654, row15655, row15656]

def rows14_12 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15486, row15487, row15488, row15489, row15490, row15491, row15657, row15658, row15659, row15495, row15496, row15497, row15498, row15499, row15500, row15660, row15661, row15662, row15501, row15502, row15503, row15504, row15505, row15506, row15507, row15508, row15509, row15510, row15511, row15512, row15663, row15664, row15665, row15666, row15667, row15668]

def rows14_13 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15522, row15523, row15524, row15525, row15526, row15527, row15669, row15670, row15671, row15531, row15532, row15533, row15534, row15535, row15536, row15672, row15673, row15674, row15537, row15538, row15539, row15540, row15541, row15542, row15543, row15544, row15545, row15546, row15547, row15548, row15675, row15676, row15677, row15678, row15679, row15680]

def rows14_14 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15681, row15682, row15683, row15684, row15685, row15686, row15687, row15688, row15689, row15690, row15691, row15692, row15693, row15694, row15695, row15696, row15697, row15698, row15699, row15700, row15701, row15702, row15703, row15704, row15705, row15706, row15707, row15708, row15709, row15710, row15711, row15712, row15713, row15714, row15715, row15716]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15717, row15718, row15719, row15720, row15721, row15722, row15723, row15724, row15725, row14205, row14206, row14207, row14208, row14209, row14210, row14211, row14212, row14213, row15726, row15727, row15728, row15729, row15730, row15731, row14214, row14215, row14216, row14217, row14218, row14219, row15732, row15733, row15734, row14232, row14233, row14234]

def rows15_1 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15735, row15736, row15737, row15738, row15739, row15740, row15741, row15742, row15743, row14241, row14242, row14243, row14244, row14245, row14246, row14247, row14248, row14249, row15744, row15745, row15746, row15747, row15748, row15749, row14250, row14251, row14252, row14253, row14254, row14255, row15750, row15751, row15752, row14268, row14269, row14270]

def rows15_2 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15753, row15754, row15755, row15756, row15757, row15758, row15759, row15760, row15761, row14277, row14278, row14279, row14280, row14281, row14282, row14283, row14284, row14285, row15762, row15763, row15764, row15765, row15766, row15767, row14286, row14287, row14288, row14289, row14290, row14291, row15768, row15769, row15770, row14304, row14305, row14306]

def rows15_3 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15771, row15772, row15773, row15774, row15775, row15776, row15777, row15778, row15779, row14313, row14314, row14315, row14316, row14317, row14318, row14319, row14320, row14321, row15780, row15781, row15782, row15783, row15784, row15785, row14322, row14323, row14324, row14325, row14326, row14327, row15786, row15787, row15788, row14340, row14341, row14342]

def rows15_4 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15789, row15790, row15791, row15792, row15793, row15794, row15795, row15796, row15797, row14349, row14350, row14351, row14352, row14353, row14354, row14355, row14356, row14357, row15798, row15799, row15800, row15801, row15802, row15803, row14358, row14359, row14360, row14361, row14362, row14363, row15804, row15805, row15806, row14376, row14377, row14378]

def rows15_5 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15807, row15808, row15809, row15810, row15811, row15812, row15813, row15814, row15815, row14385, row14386, row14387, row14388, row14389, row14390, row14391, row14392, row14393, row15816, row15817, row15818, row15819, row15820, row15821, row14394, row14395, row14396, row14397, row14398, row14399, row15822, row15823, row15824, row14412, row14413, row14414]

def rows15_6 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15825, row15826, row15827, row15828, row15829, row15830, row15831, row15832, row15833, row14421, row14422, row14423, row14424, row14425, row14426, row14427, row14428, row14429, row15834, row15835, row15836, row15837, row15838, row15839, row14430, row14431, row14432, row14433, row14434, row14435, row15840, row15841, row15842, row14448, row14449, row14450]

def rows15_7 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15843, row15844, row15845, row15846, row15847, row15848, row15849, row15850, row15851, row14457, row14458, row14459, row14460, row14461, row14462, row14463, row14464, row14465, row15852, row15853, row15854, row15855, row15856, row15857, row14466, row14467, row14468, row14469, row14470, row14471, row15858, row15859, row15860, row14484, row14485, row14486]

def rows15_8 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15861, row15862, row15863, row15864, row15865, row15866, row15867, row15868, row15869, row14493, row14494, row14495, row14496, row14497, row14498, row14499, row14500, row14501, row15870, row15871, row15872, row15873, row15874, row15875, row14502, row14503, row14504, row14505, row14506, row14507, row15876, row15877, row15878, row14520, row14521, row14522]

def rows15_9 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15879, row15880, row15881, row15882, row15883, row15884, row15885, row15886, row15887, row14529, row14530, row14531, row14532, row14533, row14534, row14535, row14536, row14537, row15888, row15889, row15890, row15891, row15892, row15893, row14538, row14539, row14540, row14541, row14542, row14543, row15894, row15895, row15896, row14556, row14557, row14558]

def rows15_10 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15897, row15898, row15899, row15900, row15901, row15902, row15903, row15904, row15905, row14565, row14566, row14567, row14568, row14569, row14570, row14571, row14572, row14573, row15906, row15907, row15908, row15909, row15910, row15911, row14574, row14575, row14576, row14577, row14578, row14579, row15912, row15913, row15914, row14592, row14593, row14594]

def rows15_11 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15915, row15916, row15917, row15918, row15919, row15920, row15921, row15922, row15923, row15924, row15925, row15926, row15927, row15928, row15929, row15930, row15931, row15932, row15933, row15934, row15935, row15936, row15937, row15938, row15939, row15940, row15941, row15942, row15943, row15944, row15945, row15946, row15947, row15948, row15949, row15950]

def rows15_12 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15951, row15952, row15953, row15954, row15955, row15956, row15957, row15958, row15959, row15960, row15961, row15962, row15963, row15964, row15965, row15966, row15967, row15968, row15969, row15970, row15971, row15972, row15973, row15974, row15975, row15976, row15977, row15978, row15979, row15980, row15981, row15982, row15983, row15984, row15985, row15986]

def rows15_13 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15987, row15988, row15989, row15990, row15991, row15992, row15993, row15994, row15995, row15996, row15997, row15998, row15999, row16000, row16001, row16002, row16003, row16004, row16005, row16006, row16007, row16008, row16009, row16010, row16011, row16012, row16013, row16014, row16015, row16016, row16017, row16018, row16019, row16020, row16021, row16022]

def rows15_14 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row16023, row16024, row16025, row16026, row16027, row16028, row16029, row16030, row16031, row16032, row16033, row16034, row16035, row16036, row16037, row16038, row16039, row16040, row16041, row16042, row16043, row16044, row16045, row16046, row16047, row16048, row16049, row16050, row16051, row16052, row16053, row16054, row16055, row16056, row16057, row16058]

def rows15_15 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row16059, row16060, row16061, row16062, row16063, row16064, row16065, row16066, row16067, row16068, row16069, row16070, row16071, row16072, row16073, row16074, row16075, row16076, row16077, row16078, row16079, row16080, row16081, row16082, row16083, row16084, row16085, row16086, row16087, row16088, row16089, row16090, row16091, row16092, row16093, row16094]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16095, row16096, row16097, row16098, row16099, row16100, row16101, row16102, row16103, row16104, row16105, row16106, row16107, row16108, row16109, row16110, row16111, row16112, row16113, row16114, row16115, row16116, row16117, row16118, row16119, row16120, row16121, row16122, row16123, row16124, row16125, row16126, row16127, row16128, row16129, row16130]

def rows16_1 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16131, row16132, row16133, row16134, row16135, row16136, row16137, row16138, row16139, row16140, row16141, row16142, row16143, row16144, row16145, row16146, row16147, row16148, row16149, row16150, row16151, row16152, row16153, row16154, row16155, row16156, row16157, row16158, row16159, row16160, row16161, row16162, row16163, row16164, row16165, row16166]

def rows16_2 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16167, row16168, row16169, row16170, row16171, row16172, row16173, row16174, row16175, row16176, row16177, row16178, row16179, row16180, row16181, row16182, row16183, row16184, row16185, row16186, row16187, row16188, row16189, row16190, row16191, row16192, row16193, row16194, row16195, row16196, row16197, row16198, row16199, row16200, row16201, row16202]

def rows16_3 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16203, row16204, row16205, row16206, row16207, row16208, row16209, row16210, row16211, row16212, row16213, row16214, row16215, row16216, row16217, row16218, row16219, row16220, row16221, row16222, row16223, row16224, row16225, row16226, row16227, row16228, row16229, row16230, row16231, row16232, row16233, row16234, row16235, row16236, row16237, row16238]

def rows16_4 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16239, row16240, row16241, row16242, row16243, row16244, row16245, row16246, row16247, row16248, row16249, row16250, row16251, row16252, row16253, row16254, row16255, row16256, row16257, row16258, row16259, row16260, row16261, row16262, row16263, row16264, row16265, row16266, row16267, row16268, row16269, row16270, row16271, row16272, row16273, row16274]

def rows16_5 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16275, row16276, row16277, row16278, row16279, row16280, row16281, row16282, row16283, row16284, row16285, row16286, row16287, row16288, row16289, row16290, row16291, row16292, row16293, row16294, row16295, row16296, row16297, row16298, row16299, row16300, row16301, row16302, row16303, row16304, row16305, row16306, row16307, row16308, row16309, row16310]

def rows16_6 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16311, row16312, row16313, row16314, row16315, row16316, row16317, row16318, row16319, row16320, row16321, row16322, row16323, row16324, row16325, row16326, row16327, row16328, row16329, row16330, row16331, row16332, row16333, row16334, row16335, row16336, row16337, row16338, row16339, row16340, row16341, row16342, row16343, row16344, row16345, row16346]

def rows16_7 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16347, row16348, row16349, row16350, row16351, row16352, row16353, row16354, row16355, row16356, row16357, row16358, row16359, row16360, row16361, row16362, row16363, row16364, row16365, row16366, row16367, row16368, row16369, row16370, row16371, row16372, row16373, row16374, row16375, row16376, row16377, row16378, row16379, row16380, row16381, row16382]

def rows16_8 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16383, row16384, row16385, row16386, row16387, row16388, row16389, row16390, row16391, row16392, row16393, row16394, row16395, row16396, row16397, row16398, row16399, row16400, row16401, row16402, row16403, row16404, row16405, row16406, row16407, row16408, row16409, row16410, row16411, row16412, row16413, row16414, row16415, row16416, row16417, row16418]

def rows16_9 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16419, row16420, row16421, row16422, row16423, row16424, row16425, row16426, row16427, row16428, row16429, row16430, row16431, row16432, row16433, row16434, row16435, row16436, row16437, row16438, row16439, row16440, row16441, row16442, row16443, row16444, row16445, row16446, row16447, row16448, row16449, row16450, row16451, row16452, row16453, row16454]

def rows16_10 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16455, row16456, row16457, row16458, row16459, row16460, row16461, row16462, row16463, row16464, row16465, row16466, row16467, row16468, row16469, row16470, row16471, row16472, row16473, row16474, row16475, row16476, row16477, row16478, row16479, row16480, row16481, row16482, row16483, row16484, row16485, row16486, row16487, row16488, row16489, row16490]

def rows16_11 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16491, row16492, row16493, row16494, row16495, row16496, row16497, row16498, row16499, row16500, row16501, row16502, row16503, row16504, row16505, row16506, row16507, row16508, row16509, row16510, row16511, row16512, row16513, row16514, row16515, row16516, row16517, row16518, row16519, row16520, row16521, row16522, row16523, row16524, row16525, row16526]

def rows16_12 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16527, row16528, row16529, row16530, row16531, row16532, row16533, row16534, row16535, row16536, row16537, row16538, row16539, row16540, row16541, row16542, row16543, row16544, row16545, row16546, row16547, row16548, row16549, row16550, row16551, row16552, row16553, row16554, row16555, row16556, row16557, row16558, row16559, row16560, row16561, row16562]

def rows16_13 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16563, row16564, row16565, row16566, row16567, row16568, row16569, row16570, row16571, row16572, row16573, row16574, row16575, row16576, row16577, row16578, row16579, row16580, row16581, row16582, row16583, row16584, row16585, row16586, row16587, row16588, row16589, row16590, row16591, row16592, row16593, row16594, row16595, row16596, row16597, row16598]

def rows16_14 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16599, row16600, row16601, row16602, row16603, row16604, row16605, row16606, row16607, row16608, row16609, row16610, row16611, row16612, row16613, row16614, row16615, row16616, row16617, row16618, row16619, row16620, row16621, row16622, row16623, row16624, row16625, row16626, row16627, row16628, row16629, row16630, row16631, row16632, row16633, row16634]

def rows16_15 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16635, row16636, row16637, row16638, row16639, row16640, row16641, row16642, row16643, row16644, row16645, row16646, row16647, row16648, row16649, row16650, row16651, row16652, row16653, row16654, row16655, row16656, row16657, row16658, row16659, row16660, row16661, row16662, row16663, row16664, row16665, row16666, row16667, row16668, row16669, row16670]

def rows16_16 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16671, row16672, row16673, row16674, row16675, row16676, row16677, row16678, row16679, row16680, row16681, row16682, row16683, row16684, row16685, row16686, row16687, row16688, row16689, row16690, row16691, row16692, row16693, row16694, row16695, row16696, row16697, row16698, row16699, row16700, row16701, row16702, row16703, row16704, row16705, row16706]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16707, row16708, row16709, row16710, row16711, row16712, row16713, row16714, row16715, row16716, row16717, row16718, row16719, row16720, row16721, row16722, row16723, row16724]

def rows17_1 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16725, row16726, row16727, row16728, row16729, row16730, row16731, row16732, row16733, row16734, row16735, row16736, row16737, row16738, row16739, row16740, row16741, row16742]

def rows17_2 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16743, row16744, row16745, row16746, row16747, row16748, row16749, row16750, row16751, row16752, row16753, row16754, row16755, row16756, row16757, row16758, row16759, row16760]

def rows17_3 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16761, row16762, row16763, row16764, row16765, row16766, row16767, row16768, row16769, row16770, row16771, row16772, row16773, row16774, row16775, row16776, row16777, row16778]

def rows17_4 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16779, row16780, row16781, row16782, row16783, row16784, row16785, row16786, row16787, row16788, row16789, row16790, row16791, row16792, row16793, row16794, row16795, row16796]

def rows17_5 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16797, row16798, row16799, row16800, row16801, row16802, row16803, row16804, row16805, row16806, row16807, row16808, row16809, row16810, row16811, row16812, row16813, row16814]

def rows17_6 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16815, row16816, row16817, row16818, row16819, row16820, row16821, row16822, row16823, row16824, row16825, row16826, row16827, row16828, row16829, row16830, row16831, row16832]

def rows17_7 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16833, row16834, row16835, row16836, row16837, row16838, row16839, row16840, row16841, row16842, row16843, row16844, row16845, row16846, row16847, row16848, row16849, row16850]

def rows17_8 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16851, row16852, row16853, row16854, row16855, row16856, row16857, row16858, row16859, row16860, row16861, row16862, row16863, row16864, row16865, row16866, row16867, row16868]

def rows17_9 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16869, row16870, row16871, row16872, row16873, row16874, row16875, row16876, row16877, row16878, row16879, row16880, row16881, row16882, row16883, row16884, row16885, row16886]

def rows17_10 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16887, row16888, row16889, row16890, row16891, row16892, row16893, row16894, row16895, row16896, row16897, row16898, row16899, row16900, row16901, row16902, row16903, row16904]

def rows17_11 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16905, row16906, row16907, row16908, row16909, row16910, row16911, row16912, row16913, row16914, row16915, row16916, row16917, row16918, row16919, row16920, row16921, row16922]

def rows17_12 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16923, row16924, row16925, row16926, row16927, row16928, row16929, row16930, row16931, row16932, row16933, row16934, row16935, row16936, row16937, row16938, row16939, row16940]

def rows17_13 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16941, row16942, row16943, row16944, row16945, row16946, row16947, row16948, row16949, row16950, row16951, row16952, row16953, row16954, row16955, row16956, row16957, row16958]

def rows17_14 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16959, row16960, row16961, row16962, row16963, row16964, row16965, row16966, row16967, row16968, row16969, row16970, row16971, row16972, row16973, row16974, row16975, row16976]

def rows17_15 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16977, row16978, row16979, row16980, row16981, row16982, row16983, row16984, row16985, row16986, row16987, row16988, row16989, row16990, row16991, row16992, row16993, row16994]

def rows17_16 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16995, row16996, row16997, row16998, row16999, row17000, row17001, row17002, row17003, row17004, row17005, row17006, row17007, row17008, row17009, row17010, row17011, row17012]

def rows17_17 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row17013, row17014, row17015, row17016, row17017, row17018, row17019, row17020, row17021, row17022, row17023, row17024, row17025, row17026, row17027, row17028, row17029, row17030]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17031, row17032, row17033, row17034, row17035, row17036, row17037, row17038, row17039, row17040, row17041, row17042, row17043, row17044, row17045, row17046, row17047, row17048, row17049, row17050]

def rows18_1 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17051, row17052, row17053, row17054, row17055, row17056, row17057, row17058, row17059, row17060, row17061, row17062, row17063, row17064, row17065, row17066, row17067, row17068, row17069, row17070]

def rows18_2 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17071, row17072, row17073, row17074, row17075, row17076, row17077, row17078, row17079, row17080, row17081, row17082, row17083, row17084, row17085, row17086, row17087, row17088, row17089, row17090]

def rows18_3 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17091, row17092, row17093, row17094, row17095, row17096, row17097, row17098, row17099, row17100, row17101, row17102, row17103, row17104, row17105, row17106, row17107, row17108, row17109, row17110]

def rows18_4 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17111, row17112, row17113, row17114, row17115, row17116, row17117, row17118, row17119, row17120, row17121, row17122, row17123, row17124, row17125, row17126, row17127, row17128, row17129, row17130]

def rows18_5 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17131, row17132, row17133, row17134, row17135, row17136, row17137, row17138, row17139, row17140, row17141, row17142, row17143, row17144, row17145, row17146, row17147, row17148, row17149, row17150]

def rows18_6 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17151, row17152, row17153, row17154, row17155, row17156, row17157, row17158, row17159, row17160, row17161, row17162, row17163, row17164, row17165, row17166, row17167, row17168, row17169, row17170]

def rows18_7 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17171, row17172, row17173, row17174, row17175, row17176, row17177, row17178, row17179, row17180, row17181, row17182, row17183, row17184, row17185, row17186, row17187, row17188, row17189, row17190]

def rows18_8 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17191, row17192, row17193, row17194, row17195, row17196, row17197, row17198, row17199, row17200, row17201, row17202, row17203, row17204, row17205, row17206, row17207, row17208, row17209, row17210]

def rows18_9 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17211, row17212, row17213, row17214, row17215, row17216, row17217, row17218, row17219, row17220, row17221, row17222, row17223, row17224, row17225, row17226, row17227, row17228, row17229, row17230]

def rows18_10 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17231, row17232, row17233, row17234, row17235, row17236, row17237, row17238, row17239, row17240, row17241, row17242, row17243, row17244, row17245, row17246, row17247, row17248, row17249, row17250]

def rows18_11 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17251, row17252, row17253, row17254, row17255, row17256, row17257, row17258, row17259, row17260, row17261, row17262, row17263, row17264, row17265, row17266, row17267, row17268, row17269, row17270]

def rows18_12 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17271, row17272, row17273, row17274, row17275, row17276, row17277, row17278, row17279, row17280, row17281, row17282, row17283, row17284, row17285, row17286, row17287, row17288, row17289, row17290]

def rows18_13 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17291, row17292, row17293, row17294, row17295, row17296, row17297, row17298, row17299, row17300, row17301, row17302, row17303, row17304, row17305, row17306, row17307, row17308, row17309, row17310]

def rows18_14 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17311, row17312, row17313, row17314, row17315, row17316, row17317, row17318, row17319, row17320, row17321, row17322, row17323, row17324, row17325, row17326, row17327, row17328, row17329, row17330]

def rows18_15 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17331, row17332, row17333, row17334, row17335, row17336, row17337, row17338, row17339, row17340, row17341, row17342, row17343, row17344, row17345, row17346, row17347, row17348, row17349, row17350]

def rows18_16 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17351, row17352, row17353, row17354, row17355, row17356, row17357, row17358, row17359, row17360, row17361, row17362, row17363, row17364, row17365, row17366, row17367, row17368, row17369, row17370]

def rows18_17 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17371, row17372, row17373, row17374, row17375, row17376, row17377, row17378, row17379, row17380, row17381, row17382, row17383, row17384, row17385, row17386, row17387, row17388, row17389, row17390]

def rows18_18 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17391, row17392, row17393, row17394, row17395, row17396, row17397, row17398, row17399, row17400, row17401, row17402, row17403, row17404, row17405, row17406, row17407, row17408, row17409, row17410]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17411, row17412, row17413, row17414, row17415, row17416, row17417, row17418, row17419, row17420]

def rows19_1 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17421, row17422, row17423, row17424, row17425, row17426, row17427, row17428, row17429, row17430]

def rows19_2 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17431, row17432, row17433, row17434, row17435, row17436, row17437, row17438, row17439, row17440]

def rows19_3 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17441, row17442, row17443, row17444, row17445, row17446, row17447, row17448, row17449, row17450]

def rows19_4 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17451, row17452, row17453, row17454, row17455, row17456, row17457, row17458, row17459, row17460]

def rows19_5 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17461, row17462, row17463, row17464, row17465, row17466, row17467, row17468, row17469, row17470]

def rows19_6 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17471, row17472, row17473, row17474, row17475, row17476, row17477, row17478, row17479, row17480]

def rows19_7 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17481, row17482, row17483, row17484, row17485, row17486, row17487, row17488, row17489, row17490]

def rows19_8 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17491, row17492, row17493, row17494, row17495, row17496, row17497, row17498, row17499, row17500]

def rows19_9 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17501, row17502, row17503, row17504, row17505, row17506, row17507, row17508, row17509, row17510]

def rows19_10 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17511, row17512, row17513, row17514, row17515, row17516, row17517, row17518, row17519, row17520]

def rows19_11 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17521, row17522, row17523, row17524, row17525, row17526, row17527, row17528, row17529, row17530]

def rows19_12 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17531, row17532, row17533, row17534, row17535, row17536, row17537, row17538, row17539, row17540]

def rows19_13 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17541, row17542, row17543, row17544, row17545, row17546, row17547, row17548, row17549, row17550]

def rows19_14 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17551, row17552, row17553, row17554, row17555, row17556, row17557, row17558, row17559, row17560]

def rows19_15 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17561, row17562, row17563, row17564, row17565, row17566, row17567, row17568, row17569, row17570]

def rows19_16 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17571, row17572, row17573, row17574, row17575, row17576, row17577, row17578, row17579, row17580]

def rows19_17 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17581, row17582, row17583, row17584, row17585, row17586, row17587, row17588, row17589, row17590]

def rows19_18 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17591, row17592, row17593, row17594, row17595, row17596, row17597, row17598, row17599, row17600]

def rows19_19 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17601, row17602, row17603, row17604, row17605, row17606, row17607, row17608, row17609, row17610]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13245, row13246, row13247, row13248, row13249, row13250, row13251, row13252, row13253, row13254, row13255, row13256, row13257, row13258, row13259, row13260, row13261, row13262, row13263, row13264]

def rows2_1 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13265, row13266, row13267, row13268, row13269, row13270, row13271, row13272, row13273, row13274, row13275, row13276, row13277, row13278, row13279, row13280, row13281, row13282, row13283, row13284]

def rows2_2 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13285, row13286, row13287, row13288, row13289, row13290, row13291, row13292, row13293, row13294, row13295, row13296, row13297, row13298, row13299, row13300, row13301, row13302, row13303, row13304]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17611, row17612, row17613, row17614, row17615, row17616, row17617, row17618, row17619, row17620, row17621, row17622, row17623, row17624, row17625, row17626, row17627, row17628]

def rows20_1 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17629, row17630, row17631, row17632, row17633, row17634, row17635, row17636, row17637, row17638, row17639, row17640, row17641, row17642, row17643, row17644, row17645, row17646]

def rows20_2 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17647, row17648, row17649, row17650, row17651, row17652, row17653, row17654, row17655, row17656, row17657, row17658, row17659, row17660, row17661, row17662, row17663, row17664]

def rows20_3 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17665, row17666, row17667, row17668, row17669, row17670, row17671, row17672, row17673, row17674, row17675, row17676, row17677, row17678, row17679, row17680, row17681, row17682]

def rows20_4 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17683, row17684, row17685, row17686, row17687, row17688, row17689, row17690, row17691, row17692, row17693, row17694, row17695, row17696, row17697, row17698, row17699, row17700]

def rows20_5 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17701, row17702, row17703, row17704, row17705, row17706, row17707, row17708, row17709, row17710, row17711, row17712, row17713, row17714, row17715, row17716, row17717, row17718]

def rows20_6 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17719, row17720, row17721, row17722, row17723, row17724, row17725, row17726, row17727, row17728, row17729, row17730, row17731, row17732, row17733, row17734, row17735, row17736]

def rows20_7 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17737, row17738, row17739, row17740, row17741, row17742, row17743, row17744, row17745, row17746, row17747, row17748, row17749, row17750, row17751, row17752, row17753, row17754]

def rows20_8 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17755, row17756, row17757, row17758, row17759, row17760, row17761, row17762, row17763, row17764, row17765, row17766, row17767, row17768, row17769, row17770, row17771, row17772]

def rows20_9 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17773, row17774, row17775, row17776, row17777, row17778, row17779, row17780, row17781, row17782, row17783, row17784, row17785, row17786, row17787, row17788, row17789, row17790]

def rows20_10 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17791, row17792, row17793, row17794, row17795, row17796, row17797, row17798, row17799, row17800, row17801, row17802, row17803, row17804, row17805, row17806, row17807, row17808]

def rows20_11 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17809, row17810, row17811, row17812, row17813, row17814, row17815, row17816, row17817, row17818, row17819, row17820, row17821, row17822, row17823, row17824, row17825, row17826]

def rows20_12 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17827, row17828, row17829, row17830, row17831, row17832, row17833, row17834, row17835, row17836, row17837, row17838, row17839, row17840, row17841, row17842, row17843, row17844]

def rows20_13 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17845, row17846, row17847, row17848, row17849, row17850, row17851, row17852, row17853, row17854, row17855, row17856, row17857, row17858, row17859, row17860, row17861, row17862]

def rows20_14 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17863, row17864, row17865, row17866, row17867, row17868, row17869, row17870, row17871, row17872, row17873, row17874, row17875, row17876, row17877, row17878, row17879, row17880]

def rows20_15 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17881, row17882, row17883, row17884, row17885, row17886, row17887, row17888, row17889, row17890, row17891, row17892, row17893, row17894, row17895, row17896, row17897, row17898]

def rows20_16 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17899, row17900, row17901, row17902, row17903, row17904, row17905, row17906, row17907, row17908, row17909, row17910, row17911, row17912, row17913, row17914, row17915, row17916]

def rows20_17 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17917, row17918, row17919, row17920, row17921, row17922, row17923, row17924, row17925, row17926, row17927, row17928, row17929, row17930, row17931, row17932, row17933, row17934]

def rows20_18 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17935, row17936, row17937, row17938, row17939, row17940, row17941, row17942, row17943, row17944, row17945, row17946, row17947, row17948, row17949, row17950, row17951, row17952]

def rows20_19 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17953, row17954, row17955, row17956, row17957, row17958, row17959, row17960, row17961, row17962, row17963, row17964, row17965, row17966, row17967, row17968, row17969, row17970]

def rows20_20 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17971, row17972, row17973, row17974, row17975, row17976, row17977, row17978, row17979, row17980, row17981, row17982, row17983, row17984, row17985, row17986, row17987, row17988]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block5

def form0 : LinearForm := ⟨20, fun k => terms0[k.val]!⟩

def form1 : LinearForm := ⟨5, fun k => terms1[k.val]!⟩

def form10 : LinearForm := ⟨20, fun k => terms10[k.val]!⟩

def form11 : LinearForm := ⟨60, fun k => terms11[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows21_0 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row17989, row17990, row17991, row17992, row17993, row17994, row17995, row17996, row17997, row17998, row17999, row18000, row18001, row18002, row18003, row18004, row18005, row18006, row18007, row18008]

def rows21_1 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18009, row18010, row18011, row18012, row18013, row18014, row18015, row18016, row18017, row18018, row18019, row18020, row18021, row18022, row18023, row18024, row18025, row18026, row18027, row18028]

def rows21_2 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18029, row18030, row18031, row18032, row18033, row18034, row18035, row18036, row18037, row18038, row18039, row18040, row18041, row18042, row18043, row18044, row18045, row18046, row18047, row18048]

def rows21_3 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18049, row18050, row18051, row18052, row18053, row18054, row18055, row18056, row18057, row18058, row18059, row18060, row18061, row18062, row18063, row18064, row18065, row18066, row18067, row18068]

def rows21_4 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18069, row18070, row18071, row18072, row18073, row18074, row18075, row18076, row18077, row18078, row18079, row18080, row18081, row18082, row18083, row18084, row18085, row18086, row18087, row18088]

def rows21_5 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18089, row18090, row18091, row18092, row18093, row18094, row18095, row18096, row18097, row18098, row18099, row18100, row18101, row18102, row18103, row18104, row18105, row18106, row18107, row18108]

def rows21_6 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18109, row18110, row18111, row18112, row18113, row18114, row18115, row18116, row18117, row18118, row18119, row18120, row18121, row18122, row18123, row18124, row18125, row18126, row18127, row18128]

def rows21_7 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18129, row18130, row18131, row18132, row18133, row18134, row18135, row18136, row18137, row18138, row18139, row18140, row18141, row18142, row18143, row18144, row18145, row18146, row18147, row18148]

def rows21_8 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18149, row18150, row18151, row18152, row18153, row18154, row18155, row18156, row18157, row18158, row18159, row18160, row18161, row18162, row18163, row18164, row18165, row18166, row18167, row18168]

def rows21_9 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18169, row18170, row18171, row18172, row18173, row18174, row18175, row18176, row18177, row18178, row18179, row18180, row18181, row18182, row18183, row18184, row18185, row18186, row18187, row18188]

def rows21_10 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18189, row18190, row18191, row18192, row18193, row18194, row18195, row18196, row18197, row18198, row18199, row18200, row18201, row18202, row18203, row18204, row18205, row18206, row18207, row18208]

def rows21_11 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18209, row18210, row18211, row18212, row18213, row18214, row18215, row18216, row18217, row18218, row18219, row18220, row18221, row18222, row18223, row18224, row18225, row18226, row18227, row18228]

def rows21_12 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18229, row18230, row18231, row18232, row18233, row18234, row18235, row18236, row18237, row18238, row18239, row18240, row18241, row18242, row18243, row18244, row18245, row18246, row18247, row18248]

def rows21_13 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18249, row18250, row18251, row18252, row18253, row18254, row18255, row18256, row18257, row18258, row18259, row18260, row18261, row18262, row18263, row18264, row18265, row18266, row18267, row18268]

def rows21_14 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18269, row18270, row18271, row18272, row18273, row18274, row18275, row18276, row18277, row18278, row18279, row18280, row18281, row18282, row18283, row18284, row18285, row18286, row18287, row18288]

def rows21_15 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18289, row18290, row18291, row18292, row18293, row18294, row18295, row18296, row18297, row18298, row18299, row18300, row18301, row18302, row18303, row18304, row18305, row18306, row18307, row18308]

def rows21_16 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18309, row18310, row18311, row18312, row18313, row18314, row18315, row18316, row18317, row18318, row18319, row18320, row18321, row18322, row18323, row18324, row18325, row18326, row18327, row18328]

def rows21_17 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18329, row18330, row18331, row18332, row18333, row18334, row18335, row18336, row18337, row18338, row18339, row18340, row18341, row18342, row18343, row18344, row18345, row18346, row18347, row18348]

def rows21_18 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18349, row18350, row18351, row18352, row18353, row18354, row18355, row18356, row18357, row18358, row18359, row18360, row18361, row18362, row18363, row18364, row18365, row18366, row18367, row18368]

def rows21_19 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18369, row18370, row18371, row18372, row18373, row18374, row18375, row18376, row18377, row18378, row18379, row18380, row18381, row18382, row18383, row18384, row18385, row18386, row18387, row18388]

def rows21_20 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18389, row18390, row18391, row18392, row18393, row18394, row18395, row18396, row18397, row18398, row18399, row18400, row18401, row18402, row18403, row18404, row18405, row18406, row18407, row18408]

def rows21_21 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18409, row18410, row18411, row18412, row18413, row18414, row18415, row18416, row18417, row18418, row18419, row18420, row18421, row18422, row18423, row18424, row18425, row18426, row18427, row18428]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13305, row13306, row13307, row13308, row13309, row13310, row13311, row13312, row13313, row13314, row13315, row13316, row13317, row13318, row13319, row13320, row13321, row13322, row13323, row13324]

def rows3_1 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13325, row13326, row13327, row13328, row13329, row13330, row13331, row13332, row13333, row13334, row13335, row13336, row13337, row13338, row13339, row13340, row13341, row13342, row13343, row13344]

def rows3_2 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13345, row13346, row13347, row13348, row13349, row13350, row13351, row13352, row13353, row13354, row13355, row13356, row13357, row13358, row13359, row13360, row13361, row13362, row13363, row13364]

def rows3_3 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13365, row13366, row13367, row13368, row13369, row13370, row13371, row13372, row13373, row13374, row13375, row13376, row13377, row13378, row13379, row13380, row13381, row13382, row13383, row13384]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13385, row13386, row13387, row13388, row13389, row13390, row13391, row13392, row13393, row13394, row13395, row13396, row13397, row13398, row13399, row13400, row13401, row13402, row13403, row13404]

def rows4_1 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13405, row13406, row13407, row13408, row13409, row13410, row13411, row13412, row13413, row13414, row13415, row13416, row13417, row13418, row13419, row13420, row13421, row13422, row13423, row13424]

def rows4_2 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13425, row13426, row13427, row13428, row13429, row13430, row13431, row13432, row13433, row13434, row13435, row13436, row13437, row13438, row13439, row13440, row13441, row13442, row13443, row13444]

def rows4_3 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13445, row13446, row13447, row13448, row13449, row13450, row13451, row13452, row13453, row13454, row13455, row13456, row13457, row13458, row13459, row13460, row13461, row13462, row13463, row13464]

def rows4_4 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13465, row13466, row13467, row13468, row13469, row13470, row13471, row13472, row13473, row13474, row13475, row13476, row13477, row13478, row13479, row13480, row13481, row13482, row13483, row13484]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13485, row13486, row13487, row13488, row13489, row13490, row13491, row13492, row13493, row13494, row13495, row13496, row13497, row13498, row13499, row13500, row13501, row13502]

def rows5_1 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13503, row13504, row13505, row13506, row13507, row13508, row13509, row13510, row13511, row13512, row13513, row13514, row13515, row13516, row13517, row13518, row13519, row13520]

def rows5_2 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13521, row13522, row13523, row13524, row13525, row13526, row13527, row13528, row13529, row13530, row13531, row13532, row13533, row13534, row13535, row13536, row13537, row13538]

def rows5_3 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13539, row13540, row13541, row13542, row13543, row13544, row13545, row13546, row13547, row13548, row13549, row13550, row13551, row13552, row13553, row13554, row13555, row13556]

def rows5_4 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13557, row13558, row13559, row13560, row13561, row13562, row13563, row13564, row13565, row13566, row13567, row13568, row13569, row13570, row13571, row13572, row13573, row13574]

def rows5_5 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13575, row13576, row13577, row13578, row13579, row13580, row13581, row13582, row13583, row13584, row13585, row13586, row13587, row13588, row13589, row13590, row13591, row13592]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13593, row13594, row13595, row13596, row13597, row13598, row13599, row13600, row13601, row13602, row13603, row13604, row13605, row13606, row13607, row13608, row13609, row13610, row13611, row13612, row13613, row13614, row13615, row13616, row13617, row13618, row13619, row13620, row13621, row13622, row13623, row13624, row13625, row13626, row13627, row13628]

def rows6_1 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13629, row13630, row13631, row13632, row13633, row13634, row13635, row13636, row13637, row13638, row13639, row13640, row13641, row13642, row13643, row13644, row13645, row13646, row13647, row13648, row13649, row13650, row13651, row13652, row13653, row13654, row13655, row13656, row13657, row13658, row13659, row13660, row13661, row13662, row13663, row13664]

def rows6_2 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13665, row13666, row13667, row13668, row13669, row13670, row13671, row13672, row13673, row13674, row13675, row13676, row13677, row13678, row13679, row13680, row13681, row13682, row13683, row13684, row13685, row13686, row13687, row13688, row13689, row13690, row13691, row13692, row13693, row13694, row13695, row13696, row13697, row13698, row13699, row13700]

def rows6_3 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13701, row13702, row13703, row13704, row13705, row13706, row13707, row13708, row13709, row13710, row13711, row13712, row13713, row13714, row13715, row13716, row13717, row13718, row13719, row13720, row13721, row13722, row13723, row13724, row13725, row13726, row13727, row13728, row13729, row13730, row13731, row13732, row13733, row13734, row13735, row13736]

def rows6_4 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13737, row13738, row13739, row13740, row13741, row13742, row13743, row13744, row13745, row13746, row13747, row13748, row13749, row13750, row13751, row13752, row13753, row13754, row13755, row13756, row13757, row13758, row13759, row13760, row13761, row13762, row13763, row13764, row13765, row13766, row13767, row13768, row13769, row13770, row13771, row13772]

def rows6_5 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13773, row13774, row13775, row13776, row13777, row13778, row13779, row13780, row13781, row13782, row13783, row13784, row13785, row13786, row13787, row13788, row13789, row13790, row13791, row13792, row13793, row13794, row13795, row13796, row13797, row13798, row13799, row13800, row13801, row13802, row13803, row13804, row13805, row13806, row13807, row13808]

def rows6_6 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13809, row13810, row13811, row13812, row13813, row13814, row13815, row13816, row13817, row13818, row13819, row13820, row13821, row13822, row13823, row13824, row13825, row13826, row13827, row13828, row13829, row13830, row13831, row13832, row13833, row13834, row13835, row13836, row13837, row13838, row13839, row13840, row13841, row13842, row13843, row13844]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13845, row13846, row13847, row13848, row13849, row13850, row13851, row13852, row13853, row13854]

def rows7_1 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13855, row13856, row13857, row13858, row13859, row13860, row13861, row13862, row13863, row13864]

def rows7_2 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13865, row13866, row13867, row13868, row13869, row13870, row13871, row13872, row13873, row13874]

def rows7_3 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13875, row13876, row13877, row13878, row13879, row13880, row13881, row13882, row13883, row13884]

def rows7_4 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13885, row13886, row13887, row13888, row13889, row13890, row13891, row13892, row13893, row13894]

def rows7_5 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13895, row13896, row13897, row13898, row13899, row13900, row13901, row13902, row13903, row13904]

def rows7_6 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13905, row13906, row13907, row13908, row13909, row13910, row13911, row13912, row13913, row13914]

def rows7_7 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13915, row13916, row13917, row13918, row13919, row13920, row13921, row13922, row13923, row13924]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13925, row13926, row13927, row13928, row13929, row13930, row13931, row13932, row13933, row13934, row13935, row13936, row13937, row13938, row13939, row13940, row13941, row13942, row13943, row13944]

def rows8_1 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13945, row13946, row13947, row13948, row13949, row13950, row13951, row13952, row13953, row13954, row13955, row13956, row13957, row13958, row13959, row13960, row13961, row13962, row13963, row13964]

def rows8_2 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13965, row13966, row13967, row13968, row13969, row13970, row13971, row13972, row13973, row13974, row13975, row13976, row13977, row13978, row13979, row13980, row13981, row13982, row13983, row13984]

def rows8_3 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13985, row13986, row13987, row13988, row13989, row13990, row13991, row13992, row13993, row13994, row13995, row13996, row13997, row13998, row13999, row14000, row14001, row14002, row14003, row14004]

def rows8_4 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14005, row14006, row14007, row14008, row14009, row14010, row14011, row14012, row14013, row14014, row14015, row14016, row14017, row14018, row14019, row14020, row14021, row14022, row14023, row14024]

def rows8_5 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14025, row14026, row14027, row14028, row14029, row14030, row14031, row14032, row14033, row14034, row14035, row14036, row14037, row14038, row14039, row14040, row14041, row14042, row14043, row14044]

def rows8_6 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14045, row14046, row14047, row14048, row14049, row14050, row14051, row14052, row14053, row14054, row14055, row14056, row14057, row14058, row14059, row14060, row14061, row14062, row14063, row14064]

def rows8_7 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14065, row14066, row14067, row14068, row14069, row14070, row14071, row14072, row14073, row14074, row14075, row14076, row14077, row14078, row14079, row14080, row14081, row14082, row14083, row14084]

def rows8_8 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14085, row14086, row14087, row14088, row14089, row14090, row14091, row14092, row14093, row14094, row14095, row14096, row14097, row14098, row14099, row14100, row14101, row14102, row14103, row14104]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14105, row14106, row14107, row14108, row14109, row14110, row14111, row14112, row14113, row14114]

def rows9_1 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14115, row14116, row14117, row14118, row14119, row14120, row14121, row14122, row14123, row14124]

def rows9_2 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14125, row14126, row14127, row14128, row14129, row14130, row14131, row14132, row14133, row14134]

def rows9_3 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14135, row14136, row14137, row14138, row14139, row14140, row14141, row14142, row14143, row14144]

def rows9_4 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14145, row14146, row14147, row14148, row14149, row14150, row14151, row14152, row14153, row14154]

def rows9_5 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14155, row14156, row14157, row14158, row14159, row14160, row14161, row14162, row14163, row14164]

def rows9_6 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14165, row14166, row14167, row14168, row14169, row14170, row14171, row14172, row14173, row14174]

def rows9_7 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14175, row14176, row14177, row14178, row14179, row14180, row14181, row14182, row14183, row14184]

def rows9_8 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14185, row14186, row14187, row14188, row14189, row14190, row14191, row14192, row14193, row14194]

def rows9_9 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14195, row14196, row14197, row14198, row14199, row14200, row14201, row14202, row14203, row14204]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization

def entries : Fin 12 → Fin 12 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0, entry5_0, entry6_0, entry7_0, entry8_0, entry9_0, entry10_0, entry11_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1, entry5_1, entry6_1, entry7_1, entry8_1, entry9_1, entry10_1, entry11_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2, entry5_2, entry6_2, entry7_2, entry8_2, entry9_2, entry10_2, entry11_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3, entry5_3, entry6_3, entry7_3, entry8_3, entry9_3, entry10_3, entry11_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4, entry5_4, entry6_4, entry7_4, entry8_4, entry9_4, entry10_4, entry11_4],
  ![entry5_0, entry5_1, entry5_2, entry5_3, entry5_4, entry5_5, entry6_5, entry7_5, entry8_5, entry9_5, entry10_5, entry11_5],
  ![entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry7_6, entry8_6, entry9_6, entry10_6, entry11_6],
  ![entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry8_7, entry9_7, entry10_7, entry11_7],
  ![entry8_0, entry8_1, entry8_2, entry8_3, entry8_4, entry8_5, entry8_6, entry8_7, entry8_8, entry9_8, entry10_8, entry11_8],
  ![entry9_0, entry9_1, entry9_2, entry9_3, entry9_4, entry9_5, entry9_6, entry9_7, entry9_8, entry9_9, entry10_9, entry11_9],
  ![entry10_0, entry10_1, entry10_2, entry10_3, entry10_4, entry10_5, entry10_6, entry10_7, entry10_8, entry10_9, entry10_10, entry11_10],
  ![entry11_0, entry11_1, entry11_2, entry11_3, entry11_4, entry11_5, entry11_6, entry11_7, entry11_8, entry11_9, entry11_10, entry11_11]
]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block5.form0.size → Integer.Sparse Key := ![row18429, row18430, row18431, row18432, row18433, row18434, row18435, row18436, row18437, row18438, row18439, row18440, row18441, row18442, row18443, row18444, row18445, row18446, row18447, row18448]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block5.form1.size → Integer.Sparse Key := ![row18449, row18450, row18451, row18452, row18453]

def rows1_1 : Fin GramFunctions.Block5.form1.size → Integer.Sparse Key := ![row18454, row18455, row18456, row18457, row18458]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19384, row19385, row19386, row19387, row19388, row19389, row19390, row19391, row19392, row19393, row19394, row19395, row19396, row19397, row19398, row19399, row19400, row19401, row19402, row19403]

def rows10_1 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19404, row19405, row19406, row19407, row19408, row19409, row19410, row19411, row19412, row19413, row19414, row19415, row19416, row19417, row19418, row19419, row19420, row19421, row19422, row19423]

def rows10_2 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19424, row19425, row19426, row19427, row19428, row19429, row19430, row19431, row19432, row19433, row19434, row19435, row19436, row19437, row19438, row19439, row19440, row19441, row19442, row19443]

def rows10_3 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19444, row19445, row19446, row19447, row19448, row19449, row19450, row19451, row19452, row19453, row19454, row19455, row19456, row19457, row19458, row19459, row19460, row19461, row19462, row19463]

def rows10_4 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19464, row19465, row19466, row19467, row19468, row19469, row19470, row19471, row19472, row19473, row19474, row19475, row19476, row19477, row19478, row19479, row19480, row19481, row19482, row19483]

def rows10_5 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19484, row19485, row19486, row19487, row19488, row19489, row19490, row19491, row19492, row19493, row19494, row19495, row19496, row19497, row19498, row19499, row19500, row19501, row19502, row19503]

def rows10_6 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19504, row19505, row19506, row19507, row19508, row19509, row19510, row19511, row19512, row19513, row19514, row19515, row19516, row19517, row19518, row19519, row19520, row19521, row19522, row19523]

def rows10_7 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19524, row19525, row19526, row19527, row19528, row19529, row19530, row19531, row19532, row19533, row19534, row19535, row19536, row19537, row19538, row19539, row19540, row19541, row19542, row19543]

def rows10_8 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19544, row19545, row19546, row19547, row19548, row19549, row19550, row19551, row19552, row19553, row19554, row19555, row19556, row19557, row19558, row19559, row19560, row19561, row19562, row19563]

def rows10_9 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19564, row19565, row19566, row19567, row19568, row19569, row19570, row19571, row19572, row19573, row19574, row19575, row19576, row19577, row19578, row19579, row19580, row19581, row19582, row19583]

def rows10_10 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19584, row19585, row19586, row19587, row19588, row19589, row19590, row19591, row19592, row19593, row19594, row19595, row19596, row19597, row19598, row19599, row19600, row19601, row19602, row19603]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19604, row19605, row19606, row19607, row19608, row19609, row19610, row19611, row19612, row19613, row19614, row19615, row19616, row19617, row19618, row19619, row19620, row19621, row19622, row19623, row19624, row19625, row19626, row19627, row19628, row19629, row19630, row19631, row19632, row19633, row19634, row19635, row19636, row19637, row19638, row19639, row19640, row19641, row19642, row19643, row19644, row19645, row19646, row19647, row19648, row19649, row19650, row19651, row19652, row19653, row19654, row19655, row19656, row19657, row19658, row19659, row19660, row19661, row19662, row19663]

def rows11_1 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19664, row19665, row19666, row19667, row19668, row19669, row19670, row19671, row19672, row19673, row19674, row19675, row19676, row19677, row19678, row19679, row19680, row19681, row19682, row19683, row19684, row19685, row19686, row19687, row19688, row19689, row19690, row19691, row19692, row19693, row19694, row19695, row19696, row19697, row19698, row19699, row19700, row19701, row19702, row19703, row19704, row19705, row19706, row19707, row19708, row19709, row19710, row19711, row19712, row19713, row19714, row19715, row19716, row19717, row19718, row19719, row19720, row19721, row19722, row19723]

def rows11_2 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19724, row19725, row19726, row19727, row19728, row19729, row19730, row19731, row19732, row19733, row19734, row19735, row19736, row19737, row19738, row19739, row19740, row19741, row19742, row19743, row19744, row19745, row19746, row19747, row19748, row19749, row19750, row19751, row19752, row19753, row19754, row19755, row19756, row19757, row19758, row19759, row19760, row19761, row19762, row19763, row19764, row19765, row19766, row19767, row19768, row19769, row19770, row19771, row19772, row19773, row19774, row19775, row19776, row19777, row19778, row19779, row19780, row19781, row19782, row19783]

def rows11_3 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19784, row19785, row19786, row19787, row19788, row19789, row19790, row19791, row19792, row19793, row19794, row19795, row19796, row19797, row19798, row19799, row19800, row19801, row19802, row19803, row19804, row19805, row19806, row19807, row19808, row19809, row19810, row19811, row19812, row19813, row19814, row19815, row19816, row19817, row19818, row19819, row19820, row19821, row19822, row19823, row19824, row19825, row19826, row19827, row19828, row19829, row19830, row19831, row19832, row19833, row19834, row19835, row19836, row19837, row19838, row19839, row19840, row19841, row19842, row19843]

def rows11_4 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19844, row19845, row19846, row19847, row19848, row19849, row19850, row19851, row19852, row19853, row19854, row19855, row19856, row19857, row19858, row19859, row19860, row19861, row19862, row19863, row19864, row19865, row19866, row19867, row19868, row19869, row19870, row19871, row19872, row19873, row19874, row19875, row19876, row19877, row19878, row19879, row19880, row19881, row19882, row19883, row19884, row19885, row19886, row19887, row19888, row19889, row19890, row19891, row19892, row19893, row19894, row19895, row19896, row19897, row19898, row19899, row19900, row19901, row19902, row19903]

def rows11_5 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19904, row19905, row19906, row19907, row19908, row19909, row19910, row19911, row19912, row19913, row19914, row19915, row19916, row19917, row19918, row19919, row19920, row19921, row19922, row19923, row19924, row19925, row19926, row19927, row19928, row19929, row19930, row19931, row19932, row19933, row19934, row19935, row19936, row19937, row19938, row19939, row19940, row19941, row19942, row19943, row19944, row19945, row19946, row19947, row19948, row19949, row19950, row19951, row19952, row19953, row19954, row19955, row19956, row19957, row19958, row19959, row19960, row19961, row19962, row19963]

def rows11_6 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19964, row19965, row19966, row19967, row19968, row19969, row19970, row19971, row19972, row19973, row19974, row19975, row19976, row19977, row19978, row19979, row19980, row19981, row19982, row19983, row19984, row19985, row19986, row19987, row19988, row19989, row19990, row19991, row19992, row19993, row19994, row19995, row19996, row19997, row19998, row19999, row20000, row20001, row20002, row20003, row20004, row20005, row20006, row20007, row20008, row20009, row20010, row20011, row20012, row20013, row20014, row20015, row20016, row20017, row20018, row20019, row20020, row20021, row20022, row20023]

def rows11_7 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20024, row20025, row20026, row20027, row20028, row20029, row20030, row20031, row20032, row20033, row20034, row20035, row20036, row20037, row20038, row20039, row20040, row20041, row20042, row20043, row20044, row20045, row20046, row20047, row20048, row20049, row20050, row20051, row20052, row20053, row20054, row20055, row20056, row20057, row20058, row20059, row20060, row20061, row20062, row20063, row20064, row20065, row20066, row20067, row20068, row20069, row20070, row20071, row20072, row20073, row20074, row20075, row20076, row20077, row20078, row20079, row20080, row20081, row20082, row20083]

def rows11_8 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20084, row20085, row20086, row20087, row20088, row20089, row20090, row20091, row20092, row20093, row20094, row20095, row20096, row20097, row20098, row20099, row20100, row20101, row20102, row20103, row20104, row20105, row20106, row20107, row20108, row20109, row20110, row20111, row20112, row20113, row20114, row20115, row20116, row20117, row20118, row20119, row20120, row20121, row20122, row20123, row20124, row20125, row20126, row20127, row20128, row20129, row20130, row20131, row20132, row20133, row20134, row20135, row20136, row20137, row20138, row20139, row20140, row20141, row20142, row20143]

def rows11_9 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20144, row20145, row20146, row20147, row20148, row20149, row20150, row20151, row20152, row20153, row20154, row20155, row20156, row20157, row20158, row20159, row20160, row20161, row20162, row20163, row20164, row20165, row20166, row20167, row20168, row20169, row20170, row20171, row20172, row20173, row20174, row20175, row20176, row20177, row20178, row20179, row20180, row20181, row20182, row20183, row20184, row20185, row20186, row20187, row20188, row20189, row20190, row20191, row20192, row20193, row20194, row20195, row20196, row20197, row20198, row20199, row20200, row20201, row20202, row20203]

def rows11_10 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20204, row20205, row20206, row20207, row20208, row20209, row20210, row20211, row20212, row20213, row20214, row20215, row20216, row20217, row20218, row20219, row20220, row20221, row20222, row20223, row20224, row20225, row20226, row20227, row20228, row20229, row20230, row20231, row20232, row20233, row20234, row20235, row20236, row20237, row20238, row20239, row20240, row20241, row20242, row20243, row20244, row20245, row20246, row20247, row20248, row20249, row20250, row20251, row20252, row20253, row20254, row20255, row20256, row20257, row20258, row20259, row20260, row20261, row20262, row20263]

def rows11_11 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20264, row20265, row20266, row20267, row20268, row20269, row20270, row20271, row20272, row20273, row20274, row20275, row20276, row20277, row20278, row20279, row20280, row20281, row20282, row20283, row20284, row20285, row20286, row20287, row20288, row20289, row20290, row20291, row20292, row20293, row20294, row20295, row20296, row20297, row20298, row20299, row20300, row20301, row20302, row20303, row20304, row20305, row20306, row20307, row20308, row20309, row20310, row20311, row20312, row20313, row20314, row20315, row20316, row20317, row20318, row20319, row20320, row20321, row20322, row20323]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined0 : Sparse := targetCombined0_part0 ++ targetCombined0_part1 ++ targetCombined0_part2

end MUB6.TaoCertificate

end OAI
end


