-- Prove2me | Definitions.Def_OAIQ106E018
-- name    : OAIQ106E018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:18:44.129859+00:00
-- url     : https://prove2.me/theorems/ec1f2217-afb2-4b2f-8f18-22d8a72fd5ed
-- title:
--   Definitions bundle OAIQ106E018 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 96 definitions. The definitions and types are `OAI.MUB6.Certificate.GramFunctions.Block0.forms`, `OAI.MUB6.Certificate.GramFunctions.Block1.form1`, `OAI.MUB6.Certificate.GramFunctions.Block1.form15`, `OAI.MUB6.Certificate.GramFunctions.Block1.form16`, `OAI.MUB6.Certificate.GramFunctions.Block1.form17`, `OAI.MUB6.Certificate.GramFunctions.Block1.form18`, `OAI.MUB6.Certificate.GramFunctions.Block1.form19`, `OAI.MUB6.Certificate.GramFunctions.Block1.form2`, `OAI.MUB6.Certificate.GramFunctions.Block1.form20`, `OAI.MUB6.Certificate.GramFunctions.Block1.form3`, `OAI.MUB6.Certificate.GramFunctions.Block1.form4`, `OAI.MUB6.Certificate.GramFunctions.Block1.form5`, `OAI.MUB6.Certificate.GramFunctions.Block1.form6`, `OAI.MUB6.Certificate.GramFunctions.Block1.form7`, `OAI.MUB6.Certificate.GramFunctions.Block1.form8`, `OAI.MUB6.Certificate.GramFunctions.Block1.form9`, `OAI.MUB6.Certificate.GramFunctions.Block1.forms`, `OAI.MUB6.Certificate.GramFunctions.Block2.form0`, `OAI.MUB6.Certificate.GramFunctions.Block2.form1`, `OAI.MUB6.Certificate.GramFunctions.Block2.form10`, `OAI.MUB6.Certificate.GramFunctions.Block2.form2`, `OAI.MUB6.Certificate.GramFunctions.Block2.form3`, `OAI.MUB6.Certificate.GramFunctions.Block2.form4`, `OAI.MUB6.Certificate.GramFunctions.Block2.form5`, `OAI.MUB6.Certificate.GramFunctions.Block2.form6`, `OAI.MUB6.Certificate.GramFunctions.Block2.form7`, `OAI.MUB6.Certificate.GramFunctions.Block2.form8`, `OAI.MUB6.Certificate.GramFunctions.Block2.form9`, `OAI.MUB6.Certificate.GramFunctions.Block2.forms`, `OAI.MUB6.Certificate.GramFunctions.Block3.form0`, `OAI.MUB6.Certificate.GramFunctions.Block3.form1`, `OAI.MUB6.Certificate.GramFunctions.Block3.form10`, `OAI.MUB6.Certificate.GramFunctions.Block3.form11`, `OAI.MUB6.Certificate.GramFunctions.Block3.form12`, `OAI.MUB6.Certificate.GramFunctions.Block3.form13`, `OAI.MUB6.Certificate.GramFunctions.Block3.form14`, `OAI.MUB6.Certificate.GramFunctions.Block3.form15`, `OAI.MUB6.Certificate.GramFunctions.Block3.form16`, `OAI.MUB6.Certificate.GramFunctions.Block3.form17`, `OAI.MUB6.Certificate.GramFunctions.Block3.form18` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Certificate_AuxiliaryInterpretation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Certificate/AuxiliaryInterpretation.lean), [`MutuallyUnbiased_GramFunctions_Basic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Basic.lean), [`MutuallyUnbiased_GramFunctions_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block0.lean), [`MutuallyUnbiased_GramFunctions_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block1.lean), [`MutuallyUnbiased_GramFunctions_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block2.lean), [`MutuallyUnbiased_GramFunctions_Block3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block3.lean), [`MutuallyUnbiased_GramFunctions_Block4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block4.lean), [`MutuallyUnbiased_GramFunctions_Block5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block5.lean).
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundle `OAIQ106E196` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E019`, `OAIQ106E020`, `OAIQ106E022`, `OAIQ106E023`, `OAIQ106E024`, `OAIQ106E026`, `OAIQ106E027`, `OAIQ106E030`, `OAIQ106E031`, `OAIQ106E033`, `OAIQ106E034`, `OAIQ106E036`, `OAIQ106E037`, `OAIQ106E040`, `OAIQ106E041` and `OAIQ106E042`; the statements `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval0_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval19_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval0_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval1_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval3_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval3_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_3_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval2_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval0_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_9_e` and `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow0_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E196

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions

open scoped BigOperators

noncomputable def LinearForm.eval (P : LinearForm) (F : Fin 2 → Charge → ℂ) : ℂ :=
  ∑ i, ((P.terms i).coefficient : ℂ) * F (P.terms i).tag (P.terms i).charge

end MUB6.Certificate.GramFunctions

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_AuxiliaryInterpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interpreting the certificate's expanded auxiliary functions

The integer tagged terms are ordinary finite linear combinations of the
manuscript's two auxiliary functions. Their real Gram products expand into
the exact mixed-moment expressions used by the certificate. Positive
semidefiniteness of a coefficient matrix proves nonnegativity independently
of how its entries or its finite lists of terms were obtained.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramFunctions

def LinearForm.auxiliaryEval (P : LinearForm) (B : Fin 7 → Basis) : AuxiliarySample → ℂ :=
  fun ω => P.eval (fun t a => auxiliaryF B t a ω)

/-- Explicit mixed-moment expansion of a pair of integer linear forms. -/
def LinearForm.mixedGram (P Q : LinearForm) (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, ((P.terms i).coefficient : ℝ) * ((Q.terms j).coefficient : ℝ) *
    auxiliaryMixedEntry B (P.terms i).tag (Q.terms j).tag
      (P.terms i).charge (Q.terms j).charge

end MUB6.Certificate.GramFunctions

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block0

def forms (i : Fin 5) : LinearForm :=
  (#[form0, form1, form2, form3, form4])[i.val]!

end MUB6.Certificate.GramFunctions.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block1

def form1 : LinearForm := ⟨14, fun k => terms1[k.val]!⟩

def form2 : LinearForm := ⟨30, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨14, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨14, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨30, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨14, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨30, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨14, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨30, fun k => terms9[k.val]!⟩

def form15 : LinearForm := ⟨30, fun k => terms15[k.val]!⟩

def form16 : LinearForm := ⟨18, fun k => terms16[k.val]!⟩

def form17 : LinearForm := ⟨30, fun k => terms17[k.val]!⟩

def form18 : LinearForm := ⟨30, fun k => terms18[k.val]!⟩

def form19 : LinearForm := ⟨14, fun k => terms19[k.val]!⟩

def form20 : LinearForm := ⟨18, fun k => terms20[k.val]!⟩

def forms (i : Fin 21) : LinearForm :=
  (#[form0, form1, form2, form3, form4, form5, form6, form7, form8, form9, form10, form11, form12, form13, form14, form15, form16, form17, form18, form19, form20])[i.val]!

end MUB6.Certificate.GramFunctions.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block2

def form0 : LinearForm := ⟨40, fun k => terms0[k.val]!⟩

def form1 : LinearForm := ⟨40, fun k => terms1[k.val]!⟩

def form2 : LinearForm := ⟨40, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨30, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨30, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨40, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨40, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨40, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨40, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨30, fun k => terms9[k.val]!⟩

def form10 : LinearForm := ⟨30, fun k => terms10[k.val]!⟩

def forms (i : Fin 11) : LinearForm :=
  (#[form0, form1, form2, form3, form4, form5, form6, form7, form8, form9, form10])[i.val]!

end MUB6.Certificate.GramFunctions.Block2

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

def form0 : LinearForm := ⟨24, fun k => terms0[k.val]!⟩

def form1 : LinearForm := ⟨5, fun k => terms1[k.val]!⟩

def form2 : LinearForm := ⟨16, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨16, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨16, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨36, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨5, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨24, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨36, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨36, fun k => terms9[k.val]!⟩

def form10 : LinearForm := ⟨16, fun k => terms10[k.val]!⟩

def form11 : LinearForm := ⟨8, fun k => terms11[k.val]!⟩

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

def forms (i : Fin 27) : LinearForm :=
  (#[form0, form1, form2, form3, form4, form5, form6, form7, form8, form9, form10, form11, form12, form13, form14, form15, form16, form17, form18, form19, form20, form21, form22, form23, form24, form25, form26])[i.val]!

end MUB6.Certificate.GramFunctions.Block3

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

def forms (i : Fin 22) : LinearForm :=
  (#[form0, form1, form2, form3, form4, form5, form6, form7, form8, form9, form10, form11, form12, form13, form14, form15, form16, form17, form18, form19, form20, form21])[i.val]!

end MUB6.Certificate.GramFunctions.Block4

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

def form2 : LinearForm := ⟨60, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨5, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨20, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨30, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨20, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨20, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨5, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨10, fun k => terms9[k.val]!⟩

def form10 : LinearForm := ⟨20, fun k => terms10[k.val]!⟩

def form11 : LinearForm := ⟨60, fun k => terms11[k.val]!⟩

def forms (i : Fin 12) : LinearForm :=
  (#[form0, form1, form2, form3, form4, form5, form6, form7, form8, form9, form10, form11])[i.val]!

end MUB6.Certificate.GramFunctions.Block5

end OAI
end


