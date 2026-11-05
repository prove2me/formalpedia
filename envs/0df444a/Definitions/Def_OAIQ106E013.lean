-- Prove2me | Definitions.Def_OAIQ106E013
-- name    : OAIQ106E013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:53:33.229976+00:00
-- url     : https://prove2.me/theorems/8c7963d8-2f00-4af4-b11b-334d69251cf2
-- title:
--   Definitions bundle OAIQ106E013 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2132 declarations of OpenAI's Lean: 2132 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block0.entries`, `OAI.MUB6.Certificate.GramEntries.Block0.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block0.entry1_0`, `OAI.MUB6.Certificate.GramEntries.Block0.entry1_1`, `OAI.MUB6.Certificate.GramEntries.Block0.entry2_0`, `OAI.MUB6.Certificate.GramEntries.Block0.entry2_1`, `OAI.MUB6.Certificate.GramEntries.Block0.entry2_2`, `OAI.MUB6.Certificate.GramEntries.Block0.entry3_0`, `OAI.MUB6.Certificate.GramEntries.Block0.entry3_1`, `OAI.MUB6.Certificate.GramEntries.Block0.entry3_2`, `OAI.MUB6.Certificate.GramEntries.Block0.entry3_3`, `OAI.MUB6.Certificate.GramEntries.Block0.entry4_0`, `OAI.MUB6.Certificate.GramEntries.Block0.entry4_1`, `OAI.MUB6.Certificate.GramEntries.Block0.entry4_2`, `OAI.MUB6.Certificate.GramEntries.Block0.entry4_3`, `OAI.MUB6.Certificate.GramEntries.Block0.entry4_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entries`, `OAI.MUB6.Certificate.GramEntries.Block1.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_8` and 2092 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block0Data`, `MutuallyUnbiased_GramEntries_Block1Data`, `MutuallyUnbiased_GramEntries_Block3Data`, `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block10`, `MutuallyUnbiased_GramRows_Block11`, `MutuallyUnbiased_GramRows_Block12`, `MutuallyUnbiased_GramRows_Block13`, `MutuallyUnbiased_GramRows_Block14`, `MutuallyUnbiased_GramRows_Block15`, `MutuallyUnbiased_GramRows_Block16`, `MutuallyUnbiased_GramRows_Block17`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block3`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block38`, `MutuallyUnbiased_GramRows_Block39`, `MutuallyUnbiased_GramRows_Block4`, `MutuallyUnbiased_GramRows_Block40`, `MutuallyUnbiased_GramRows_Block41`, `MutuallyUnbiased_GramRows_Block42`, `MutuallyUnbiased_GramRows_Block43`, `MutuallyUnbiased_GramRows_Block44`, `MutuallyUnbiased_GramRows_Block45`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block5`, `MutuallyUnbiased_GramRows_Block6`, `MutuallyUnbiased_GramRows_Block7`, `MutuallyUnbiased_GramRows_Block8`, `MutuallyUnbiased_GramRows_Block9`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E014`, `OAIQ106E016`, `OAIQ106E020`, `OAIQ106E024` and `OAIQ106E028`; the statements `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval0_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval19_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval19_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key236, 60), (key239, -60), (key248, -60), (key260, 88), (key267, 32), (key271, -60), (key302, -60), (key305, 60), (key316, 76), (key328, -92), (key335, -56), (key340, 80), (key385, 44), (key397, -64), (key406, -60), (key418, 88), (key469, 60), (key475, -60), (key568, -28), (key572, 40), (key578, 32), (key583, -60), (key595, -60), (key601, 60)]

def entry1_0 : Integer.Sparse Key := [(key1296, 60), (key1302, -60), (key1316, -60), (key1329, 60), (key1339, 60), (key1345, -60), (key1391, -60), (key1397, 60), (key1424, 60), (key1447, -60), (key1457, -60), (key1466, 60), (key1546, 60), (key1559, -60), (key1573, -60), (key1596, 60), (key1659, 60), (key1667, -60), (key1774, -60), (key1780, 60), (key1790, 60), (key1798, -60), (key1817, -60), (key1825, 60)]

def entry1_1 : Integer.Sparse Key := [(key2617, 60), (key2620, -60), (key2633, -60), (key2643, 76), (key2650, 44), (key2655, -60), (key2672, -60), (key2675, 60), (key2707, 80), (key2730, -88), (key2739, -60), (key2749, 76), (key2787, 40), (key2797, -60), (key2810, -60), (key2833, 76), (key2899, 60), (key2906, -60), (key2940, -32), (key2945, 44), (key2952, 44), (key2962, -60), (key2978, -60), (key2985, 60)]

def entry2_0 : Integer.Sparse Key := [(key1292, 60), (key1298, -60), (key1312, -60), (key1326, 60), (key1351, 60), (key1354, -60), (key1387, -60), (key1393, 60), (key1420, 60), (key1444, -60), (key1472, -60), (key1480, 60), (key1542, 60), (key1556, -60), (key1569, -60), (key1593, 60), (key1683, 60), (key1689, -60), (key1896, -60), (key1899, 60), (key1903, 60), (key1911, -60), (key1920, -60), (key1926, 60)]

def entry2_1 : Integer.Sparse Key := [(key2616, 60), (key2618, -24), (key2621, -36), (key2628, -16), (key2632, -44), (key2640, 6), (key2641, 38), (key2644, 44), (key2646, -6), (key2648, 16), (key2653, -24), (key2658, 22), (key2660, -36), (key2667, -18), (key2671, -42), (key2673, 28), (key2676, 32), (key2702, 28), (key2706, 48), (key2726, -2), (key2728, -44), (key2732, -48), (key2735, 2), (key2737, -28), (key2747, 38), (key2753, -32), (key2758, 44), (key2782, 12), (key2786, 32), (key2794, -2), (key2795, -28), (key2798, -32), (key2805, -16), (key2809, -44), (key2829, 6), (key2831, 38), (key2835, 44), (key2897, 28), (key2904, -28), (key2920, 32), (key2923, -32), (key2936, 2), (key2938, -12), (key2943, 16), (key2948, -6), (key2950, 16), (key2960, -24), (key2976, -28), (key2983, 28), (key3008, -16), (key3010, 22), (key3012, 22), (key3017, -36), (key3023, -32), (key3026, 32)]

def entry2_2 : Integer.Sparse Key := [(key2608, 60), (key2614, -60), (key2624, -60), (key2638, 88), (key2657, 32), (key2659, -60), (key2663, -60), (key2669, 60), (key2698, 76), (key2724, -92), (key2752, -56), (key2757, 80), (key2778, 44), (key2792, -64), (key2801, -60), (key2827, 88), (key2919, 60), (key2922, -60), (key3007, -28), (key3009, 40), (key3011, 32), (key3016, -60), (key3022, -60), (key3025, 60)]

def entry3_0 : Integer.Sparse Key := [(key242, 60), (key244, -60), (key254, -60), (key265, 60), (key269, 60), (key274, -60), (key308, -60), (key310, 60), (key322, 60), (key333, -60), (key337, -60), (key343, 60), (key391, 60), (key402, -60), (key412, -60), (key423, 60), (key472, 60), (key478, -60), (key570, -60), (key575, 60), (key580, 60), (key586, -60), (key598, -60), (key604, 60)]

def entry3_1 : Integer.Sparse Key := [(key1301, 60), (key1305, -60), (key1321, -60), (key1332, 60), (key1342, 60), (key1348, -60), (key1396, -60), (key1400, 60), (key1429, 60), (key1450, -60), (key1460, -60), (key1469, 60), (key1551, 60), (key1562, -60), (key1578, -60), (key1599, 60), (key1662, 60), (key1670, -60), (key1777, -60), (key1783, 60), (key1793, 60), (key1801, -60), (key1820, -60), (key1828, 60)]

def entry3_2 : Integer.Sparse Key := [(key1300, 60), (key1306, -60), (key1320, -60), (key1333, 60), (key1353, 60), (key1356, -60), (key1395, -60), (key1401, 60), (key1428, 60), (key1451, -60), (key1474, -60), (key1482, 60), (key1550, 60), (key1563, -60), (key1577, -60), (key1600, 60), (key1685, 60), (key1691, -60), (key1898, -60), (key1901, 60), (key1905, 60), (key1913, -60), (key1922, -60), (key1928, 60)]

def entry3_3 : Integer.Sparse Key := [(key243, 60), (key245, -60), (key255, -60), (key266, 76), (key270, 44), (key275, -60), (key309, -60), (key311, 60), (key323, 80), (key334, -88), (key338, -60), (key344, 76), (key392, 40), (key403, -60), (key413, -60), (key424, 76), (key473, 60), (key479, -60), (key571, -32), (key576, 44), (key581, 44), (key587, -60), (key599, -60), (key605, 60)]

def entry4_0 : Integer.Sparse Key := [(key1291, 60), (key1295, -60), (key1311, -60), (key1324, 60), (key1336, 60), (key1343, -60), (key1386, -60), (key1390, 60), (key1419, 60), (key1442, -60), (key1454, -60), (key1464, 60), (key1541, 60), (key1554, -60), (key1568, -60), (key1591, 60), (key1657, 60), (key1665, -60), (key1771, -60), (key1778, 60), (key1787, 60), (key1796, -60), (key1815, -60), (key1823, 60)]

def entry4_1 : Integer.Sparse Key := [(key2616, 60), (key2619, -60), (key2632, -60), (key2642, 60), (key2649, 60), (key2654, -60), (key2671, -60), (key2674, 60), (key2706, 60), (key2729, -60), (key2738, -60), (key2748, 60), (key2786, 60), (key2796, -60), (key2809, -60), (key2832, 60), (key2898, 60), (key2905, -60), (key2939, -60), (key2944, 60), (key2951, 60), (key2961, -60), (key2977, -60), (key2984, 60)]

def entry4_2 : Integer.Sparse Key := [(key2609, 60), (key2613, -60), (key2625, -60), (key2637, 60), (key2647, 60), (key2652, -60), (key2664, -60), (key2668, 60), (key2699, 60), (key2723, -60), (key2736, -60), (key2746, 60), (key2779, 60), (key2791, -60), (key2802, -60), (key2826, 60), (key2896, 60), (key2903, -60), (key2937, -60), (key2942, 60), (key2949, 60), (key2959, -60), (key2975, -60), (key2982, 60)]

def entry4_3 : Integer.Sparse Key := [(key1300, 60), (key1304, -60), (key1320, -60), (key1331, 60), (key1341, 60), (key1347, -60), (key1395, -60), (key1399, 60), (key1428, 60), (key1449, -60), (key1459, -60), (key1468, 60), (key1550, 60), (key1561, -60), (key1577, -60), (key1598, 60), (key1661, 60), (key1669, -60), (key1776, -60), (key1782, 60), (key1792, 60), (key1800, -60), (key1819, -60), (key1827, 60)]

def entry4_4 : Integer.Sparse Key := [(key2608, 60), (key2611, -60), (key2624, -60), (key2636, 88), (key2645, 32), (key2651, -60), (key2663, -60), (key2666, 60), (key2698, 76), (key2722, -92), (key2734, -56), (key2745, 80), (key2778, 44), (key2790, -64), (key2801, -60), (key2825, 88), (key2895, 60), (key2902, -60), (key2935, -28), (key2941, 40), (key2947, 32), (key2958, -60), (key2974, -60), (key2981, 60)]

def entries : Fin 5 → Fin 5 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4]
]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2617, 48), (key2620, -48), (key2633, -48), (key2643, 60), (key2650, 36), (key2655, -48), (key2672, 12), (key2675, -12), (key2707, -24), (key2730, 24), (key2739, 12), (key2749, -32), (key2797, 12), (key2810, 12), (key2833, -32), (key2899, -12), (key2906, 24), (key2945, 8), (key2952, 8), (key2962, 72), (key2964, -60), (key2985, -72), (key2994, 84), (key3001, 36), (key3004, -60)]

def entry1_0 : Integer.Sparse Key := [(key1422, 120), (key1453, -120), (key1571, -120), (key1653, 120), (key1786, 120), (key1811, -120)]

def entry1_1 : Integer.Sparse Key := [(key234, 120), (key246, -120), (key300, -120), (key314, 144), (key383, 96), (key404, -120)]

def entry2_0 : Integer.Sparse Key := [(key2616, 12), (key2618, -12), (key2632, -12), (key2640, 6), (key2641, 12), (key2644, 6), (key2646, -6), (key2648, 6), (key2653, -12), (key2667, -12), (key2673, 12), (key2702, 72), (key2706, 12), (key2726, -6), (key2728, 48), (key2732, -6), (key2735, -60), (key2737, -12), (key2747, -48), (key2795, -12), (key2805, -72), (key2829, 16), (key2831, -48), (key2860, 18), (key2870, -18), (key2893, 42), (key2897, 12), (key2904, 30), (key2936, 6), (key2938, -6), (key2943, 12), (key2948, 44), (key2950, 12), (key2960, 40), (key2972, -42), (key2976, -12), (key2983, -30), (key3017, 8), (key3023, 18), (key3026, -18)]

def entry2_1 : Integer.Sparse Key := [(key1289, 120), (key1309, -120), (key1384, -120), (key1417, 120), (key1539, 120), (key1566, -120)]

def entry2_2 : Integer.Sparse Key := [(key2608, 48), (key2614, 72), (key2624, -48), (key2630, -60), (key2638, -32), (key2657, 8), (key2659, 12), (key2663, -48), (key2669, -72), (key2698, 60), (key2704, 84), (key2724, 24), (key2757, -24), (key2778, 36), (key2784, 36), (key2792, 24), (key2801, -48), (key2807, -60), (key2827, -32), (key2919, -12), (key2922, 12), (key3011, 8), (key3016, 12), (key3022, 12), (key3025, -12)]

def entry3_0 : Integer.Sparse Key := [(key1033, 120), (key1041, -120), (key1111, -120), (key1127, 120), (key1193, 120), (key1199, -120)]

def entry3_1 : Integer.Sparse Key := [(key20, 120), (key31, -120), (key45, -120), (key70, 120), (key111, 120), (key133, -120)]

def entry3_2 : Integer.Sparse Key := [(key1001, 120), (key1015, -120), (key1036, -120), (key1071, 120), (key1123, 120), (key1150, -120)]

def entry3_3 : Integer.Sparse Key := [(key1, 120), (key7, -120), (key84, -120), (key151, 192), (key193, 48), (key202, -120)]

def entry4_0 : Integer.Sparse Key := [(key2785, 120), (key2793, -120), (key2808, -120), (key2828, 120), (key2859, 120), (key2869, -120)]

def entry4_1 : Integer.Sparse Key := [(key1287, 120), (key1307, -120), (key1382, -120), (key1415, 120), (key1537, 120), (key1564, -120)]

def entry4_2 : Integer.Sparse Key := [(key2610, 120), (key2626, -120), (key2665, -120), (key2700, 120), (key2780, 120), (key2803, -120)]

def entry4_3 : Integer.Sparse Key := [(key995, 120), (key1011, -120), (key1030, -120), (key1067, 120), (key1119, 120), (key1146, -120)]

def entry4_4 : Integer.Sparse Key := [(key2606, 120), (key2622, -120), (key2661, -120), (key2696, 144), (key2776, 96), (key2799, -120)]

def entry5_0 : Integer.Sparse Key := [(key1296, 48), (key1303, -48), (key1316, -48), (key1330, 48), (key1340, 48), (key1346, -48), (key1391, 12), (key1398, -12), (key1424, -12), (key1448, 12), (key1458, 12), (key1467, -12), (key1546, -12), (key1560, 12), (key1573, 12), (key1597, -12), (key1660, -12), (key1668, 12), (key1775, 12), (key1781, -12), (key1788, 60), (key1791, -72), (key1799, 12), (key1813, -60), (key1818, 72), (key1826, -12), (key1840, 60), (key1842, -60)]

def entry5_1 : Integer.Sparse Key := [(key387, 120), (key396, -120), (key408, -120), (key417, 120), (key441, 120), (key449, -120)]

def entry5_2 : Integer.Sparse Key := [(key1291, 12), (key1299, -12), (key1311, -12), (key1327, 12), (key1352, 12), (key1355, -12), (key1386, -12), (key1394, 12), (key1419, 12), (key1445, -12), (key1473, -12), (key1481, 12), (key1541, 12), (key1549, 60), (key1557, -72), (key1568, -12), (key1576, -60), (key1594, 72), (key1625, 60), (key1634, -60), (key1684, 12), (key1690, -12), (key1897, 48), (key1900, -48), (key1904, -48), (key1912, 48), (key1921, 48), (key1927, -48)]

def entry5_3 : Integer.Sparse Key := [(key18, 12), (key23, -12), (key35, 12), (key43, 108), (key48, -72), (key100, -76), (key115, 84), (key137, 12), (key195, 36), (key196, -60), (key200, -12), (key206, -12), (key212, 12), (key218, -12), (key375, 12), (key381, -48), (key426, -44), (key460, 84), (key486, 36), (key490, -60), (key659, -12), (key663, 12)]

def entry5_4 : Integer.Sparse Key := [(key1543, 120), (key1553, -120), (key1570, -120), (key1590, 120), (key1621, 120), (key1630, -120)]

def entry5_5 : Integer.Sparse Key := [(key236, 48), (key241, -48), (key248, -48), (key263, 72), (key277, 24), (key278, -48), (key302, 12), (key307, -12), (key316, -32), (key321, 12), (key331, 24), (key347, -24), (key385, 8), (key390, -12), (key400, 24), (key406, 72), (key411, -60), (key421, -32), (key435, -60), (key445, 72), (key453, 12), (key487, 48), (key488, -72), (key657, 8), (key658, 12), (key660, -12), (key661, 24), (key662, -12)]

def entry6_0 : Integer.Sparse Key := [(key2686, 12), (key2693, 128), (key2695, -72), (key2719, -96), (key2733, 96), (key2756, 48), (key2759, -84), (key2822, 12), (key2836, -12), (key3018, 8), (key3051, -12), (key3055, -8), (key3057, -48), (key3070, -24), (key3074, 72), (key3077, 24), (key3078, -36), (key3107, -12), (key3116, 12), (key3117, -8)]

def entry6_1 : Integer.Sparse Key := [(key1432, 120), (key1475, -120), (key1581, -120), (key1686, 120), (key1906, 120), (key1923, -120)]

def entry6_2 : Integer.Sparse Key := [(key2679, -12), (key2691, -8), (key2710, 12), (key2717, 132), (key2754, -12), (key2755, -132), (key2813, -12), (key2820, -132), (key2921, 96), (key3013, 12), (key3014, 116), (key3024, -96), (key3047, 12), (key3058, 8), (key3061, -12), (key3068, 12), (key3075, -12), (key3076, 12), (key3096, 12), (key3105, -12), (key3113, 12), (key3115, 4), (key3142, 24), (key3143, -24)]

def entry6_3 : Integer.Sparse Key := [(key1048, 120), (key1054, -120), (key1134, -120), (key1142, 120), (key1238, 120), (key1240, -120)]

def entry6_4 : Integer.Sparse Key := [(key3063, 120), (key3065, -120), (key3098, -120), (key3102, 120), (key3124, 120), (key3126, -120)]

def entry6_5 : Integer.Sparse Key := [(key1405, 120), (key1410, -120), (key1433, -120), (key1439, 120), (key1477, 120), (key1479, -120)]

def entry6_6 : Integer.Sparse Key := [(key3081, 120), (key3083, -120), (key3086, -120), (key3089, 144), (key3092, 96), (key3093, -120)]

def entry7_0 : Integer.Sparse Key := [(key1296, 12), (key1303, -12), (key1316, -12), (key1330, 12), (key1340, 12), (key1346, -12), (key1391, -12), (key1398, 12), (key1424, 72), (key1448, 48), (key1455, -60), (key1458, -12), (key1467, -48), (key1546, 12), (key1560, -12), (key1573, -72), (key1597, -48), (key1655, 60), (key1660, 12), (key1668, 48), (key1775, -12), (key1781, 12), (key1788, 60), (key1791, 12), (key1799, 48), (key1813, -60), (key1818, -12), (key1826, -48)]

def entry7_1 : Integer.Sparse Key := [(key238, 120), (key250, -120), (key304, -120), (key318, 120), (key387, 120), (key408, -120)]

def entry7_2 : Integer.Sparse Key := [(key1291, 48), (key1299, 72), (key1311, -48), (key1319, -60), (key1327, -12), (key1352, -12), (key1355, 12), (key1386, -48), (key1394, -72), (key1419, 48), (key1427, 60), (key1445, 12), (key1473, 12), (key1481, -12), (key1541, 48), (key1549, 60), (key1557, 12), (key1568, -48), (key1576, -60), (key1594, -12), (key1684, -12), (key1690, 12), (key1897, 12), (key1900, -12), (key1904, -12), (key1912, 12), (key1921, 12), (key1927, -12)]

def entry7_3 : Integer.Sparse Key := [(key18, -12), (key23, 36), (key35, -60), (key43, 12), (key48, -36), (key74, 60), (key115, 48), (key137, -48), (key206, 12), (key212, 84), (key218, -60), (key375, -12), (key381, -84), (key486, 72), (key654, 60), (key659, -72)]

def entry7_4 : Integer.Sparse Key := [(key1293, 120), (key1313, -120), (key1388, -120), (key1421, 120), (key1543, 120), (key1570, -120)]

def entry7_5 : Integer.Sparse Key := [(key236, 12), (key241, -12), (key248, -12), (key263, 24), (key278, -12), (key302, -12), (key307, 12), (key316, 18), (key321, 66), (key331, 36), (key346, -72), (key347, -48), (key385, 6), (key390, -6), (key400, -12), (key406, -12), (key411, -60), (key421, -44), (key445, 18), (key453, -18), (key487, 42), (key488, 12), (key489, 30), (key656, 12), (key657, 68), (key658, 48), (key660, -42), (key661, 6), (key662, -48)]

def entry7_6 : Integer.Sparse Key := [(key1439, 120), (key1479, -120), (key1588, -120), (key1688, 120), (key1910, 120), (key1925, -120)]

def entry7_7 : Integer.Sparse Key := [(key236, 48), (key241, 72), (key248, -48), (key253, -60), (key263, -32), (key277, 8), (key278, 12), (key302, -48), (key307, -72), (key316, 60), (key321, 84), (key331, 24), (key347, -24), (key385, 36), (key390, 36), (key400, 24), (key406, -48), (key411, -60), (key421, -32), (key488, -12), (key489, 12), (key657, 8), (key658, 12), (key661, 12), (key662, -12)]

def entry8_0 : Integer.Sparse Key := [(key1033, 120), (key1040, -120), (key1111, -120), (key1126, 120), (key1192, 120), (key1198, -120)]

def entry8_1 : Integer.Sparse Key := [(key17, 120), (key28, -120), (key42, -120), (key69, 120), (key108, 120), (key132, -120)]

def entry8_2 : Integer.Sparse Key := [(key1000, 120), (key1014, -120), (key1035, -120), (key1070, 120), (key1122, 120), (key1149, -120)]

def entry8_3 : Integer.Sparse Key := [(key2, 120), (key6, -120), (key85, -120), (key150, 120), (key166, 120), (key186, -120)]

def entry8_4 : Integer.Sparse Key := [(key992, 120), (key1010, -120), (key1027, -120), (key1066, 120), (key1118, 120), (key1145, -120)]

def entry8_5 : Integer.Sparse Key := [(key376, 120), (key380, -120), (key427, -120), (key459, 120), (key465, 120), (key482, -120)]

def entry8_6 : Integer.Sparse Key := [(key1049, 120), (key1053, -120), (key1135, -120), (key1141, 120), (key1237, 120), (key1239, -120)]

def entry8_7 : Integer.Sparse Key := [(key211, 120), (key216, -120), (key380, -120), (key465, 120), (key566, 120), (key591, -120)]

def entry8_8 : Integer.Sparse Key := [(key1, 120), (key4, -120), (key84, -120), (key148, 192), (key164, 48), (key184, -120)]

def entry9_0 : Integer.Sparse Key := [(key2617, 12), (key2620, -12), (key2633, -12), (key2643, 18), (key2650, 6), (key2655, -12), (key2672, 48), (key2675, -48), (key2707, -12), (key2730, 18), (key2739, 18), (key2749, 46), (key2751, -42), (key2787, -24), (key2797, 18), (key2810, -12), (key2833, 18), (key2899, 12), (key2906, -42), (key2915, 42), (key2940, 18), (key2945, -22), (key2946, -18), (key2952, 6), (key2962, -12), (key2978, -42), (key2985, 12), (key2994, 42), (key2999, 18), (key3001, 18), (key3004, -60)]

def entry9_1 : Integer.Sparse Key := [(key1314, 120), (key1335, -120), (key1544, -120), (key1653, 120), (key1770, 120), (key1811, -120)]

def entry9_2 : Integer.Sparse Key := [(key2616, -12), (key2618, 12), (key2628, 72), (key2640, -16), (key2641, 48), (key2646, -44), (key2648, -12), (key2653, -40), (key2660, -8), (key2667, -6), (key2671, 18), (key2673, -6), (key2676, -6), (key2706, -30), (key2726, 36), (key2728, 12), (key2732, 6), (key2735, -6), (key2737, 6), (key2747, -12), (key2753, -18), (key2758, 30), (key2782, -42), (key2786, -12), (key2794, 6), (key2795, -30), (key2798, 6), (key2809, 12), (key2829, -6), (key2831, -12), (key2835, -6), (key2860, 18), (key2870, -18), (key2893, 42), (key2897, 30), (key2904, 12), (key2920, 18), (key2923, -18), (key2936, 24), (key2938, 6), (key2943, 18), (key2948, 6), (key2950, -6), (key2960, 12), (key2972, -42), (key2976, -30), (key2983, -12)]

def entry9_3 : Integer.Sparse Key := [(key998, 120), (key1006, -120), (key1111, -120), (key1155, 120), (key1193, 120), (key1212, -120)]

def entry9_4 : Integer.Sparse Key := [(key2631, 120), (key2639, -120), (key2705, -120), (key2725, 120), (key2859, 120), (key2869, -120)]

def entry9_5 : Integer.Sparse Key := [(key1296, 12), (key1303, -12), (key1316, -12), (key1330, 12), (key1340, 12), (key1346, -12), (key1391, 48), (key1398, -48), (key1424, -48), (key1448, 48), (key1458, 48), (key1467, -48), (key1546, 12), (key1560, -12), (key1573, -12), (key1597, 12), (key1660, 12), (key1668, -12), (key1772, 60), (key1775, -72), (key1781, 12), (key1791, 12), (key1799, -12), (key1813, -60), (key1818, -12), (key1826, 72), (key1840, 60), (key1845, -60)]

def entry9_6 : Integer.Sparse Key := [(key2693, 144), (key2695, -84), (key2719, 12), (key2733, -12), (key2756, -12), (key2759, 24), (key2822, -96), (key2836, 96), (key3015, 48), (key3018, -84), (key3055, -24), (key3057, -36), (key3070, -12), (key3074, 12), (key3077, 12), (key3078, -24), (key3107, -24), (key3112, 72), (key3116, 24), (key3117, -36)]

def entry9_7 : Integer.Sparse Key := [(key1296, -12), (key1303, 12), (key1316, 72), (key1330, 48), (key1337, -60), (key1340, -12), (key1346, -48), (key1391, 12), (key1398, -12), (key1424, -12), (key1448, 12), (key1458, 12), (key1467, -12), (key1546, -72), (key1560, -48), (key1573, 12), (key1597, -12), (key1655, 60), (key1660, 48), (key1668, 12), (key1772, 60), (key1775, 12), (key1781, 48), (key1791, -12), (key1799, 12), (key1813, -60), (key1818, -48), (key1826, -12)]

def entry9_8 : Integer.Sparse Key := [(key998, 120), (key1005, -120), (key1111, -120), (key1154, 120), (key1192, 120), (key1211, -120)]

def entry9_9 : Integer.Sparse Key := [(key2617, 48), (key2620, -48), (key2633, 12), (key2643, -32), (key2650, 8), (key2655, 72), (key2656, -60), (key2672, 12), (key2675, -12), (key2730, 12), (key2749, 16), (key2787, -24), (key2797, 24), (key2810, -48), (key2833, 60), (key2899, -72), (key2915, 84), (key2940, 12), (key2945, -40), (key2952, 36), (key2962, -48), (key2978, 24), (key2985, -12), (key2999, 36), (key3004, -60)]

def entry10_0 : Integer.Sparse Key := [(key2380, -12), (key2391, 12), (key2402, 60), (key2408, -72), (key2468, -36), (key2481, 72), (key2505, 12), (key2535, -12), (key2537, 36), (key2542, -48), (key2553, -12), (key2596, 12), (key2605, -12), (key2770, 60), (key2775, -48), (key2847, -84), (key2878, 12), (key2884, 84), (key2917, 48), (key2926, -72), (key3020, -12), (key3029, 12)]

def entry10_1 : Integer.Sparse Key := [(key1250, 120), (key1269, -120), (key1525, -120), (key1677, 120), (key1892, 120), (key1914, -120)]

def entry10_2 : Integer.Sparse Key := [(key2370, -12), (key2376, 36), (key2388, -60), (key2398, 12), (key2404, -36), (key2435, 60), (key2478, 48), (key2501, -48), (key2583, 12), (key2589, 84), (key2604, -60), (key2762, -12), (key2768, -84), (key2916, 72), (key3005, 60), (key3019, -72)]

def entry10_3 : Integer.Sparse Key := [(key971, 120), (key979, -120), (key1085, -120), (key1164, 120), (key1228, 120), (key1245, -120)]

def entry10_4 : Integer.Sparse Key := [(key2372, 120), (key2385, -120), (key2400, -120), (key2432, 120), (key2475, 120), (key2498, -120)]

def entry10_5 : Integer.Sparse Key := [(key1526, 120), (key1534, -120), (key1604, -120), (key1640, 120), (key1679, 120), (key1693, -120)]

def entry10_6 : Integer.Sparse Key := [(key2414, 120), (key2419, -96), (key2426, 24), (key2487, -84), (key2494, 96), (key2572, 48), (key2573, -84), (key3038, -24), (key3043, -24), (key3120, -36), (key3130, 72), (key3141, 24), (key3144, -36)]

def entry10_7 : Integer.Sparse Key := [(key1259, 120), (key1271, -120), (key1534, -120), (key1679, 120), (key1894, 120), (key1916, -120)]

def entry10_8 : Integer.Sparse Key := [(key972, 120), (key978, -120), (key1086, -120), (key1163, 120), (key1227, 120), (key1244, -120)]

def entry10_9 : Integer.Sparse Key := [(key2374, 60), (key2380, -72), (key2408, -12), (key2439, 12), (key2468, -36), (key2481, 12), (key2505, 72), (key2535, -12), (key2537, 36), (key2542, -12), (key2553, -48), (key2591, 60), (key2596, -48), (key2775, 12), (key2847, -84), (key2878, 12), (key2884, 84), (key2917, -12), (key2926, 12), (key3006, -12), (key3020, 48), (key3029, -72)]

def entry10_10 : Integer.Sparse Key := [(key2353, 120), (key2359, -120), (key2448, -120), (key2515, 192), (key2566, 48), (key2578, -120)]

def entry11_0 : Integer.Sparse Key := [(key2770, 120), (key2773, -120), (key2847, -120), (key2881, 120), (key2890, 120), (key2911, -120)]

def entry11_1 : Integer.Sparse Key := [(key1249, 120), (key1262, -120), (key1524, -120), (key1645, 120), (key1762, 120), (key1803, -120)]

def entry11_2 : Integer.Sparse Key := [(key2588, 120), (key2599, -120), (key2767, -120), (key2888, 120), (key2930, 120), (key2967, -120)]

def entry11_3 : Integer.Sparse Key := [(key972, 120), (key977, -120), (key1086, -120), (key1162, 120), (key1181, 120), (key1218, -120)]

def entry11_4 : Integer.Sparse Key := [(key2369, 120), (key2384, -120), (key2397, -120), (key2431, 120), (key2474, 120), (key2497, -120)]

def entry11_5 : Integer.Sparse Key := [(key1527, 120), (key1532, -120), (key1605, -120), (key1638, 120), (key1649, 120), (key1672, -120)]

def entry11_6 : Integer.Sparse Key := [(key3034, 120), (key3037, -120), (key3121, -120), (key3129, 120), (key3133, 120), (key3139, -120)]

def entry11_7 : Integer.Sparse Key := [(key1257, 120), (key1266, -120), (key1532, -120), (key1649, 120), (key1766, 120), (key1807, -120)]

def entry11_8 : Integer.Sparse Key := [(key971, 120), (key975, -120), (key1085, -120), (key1161, 120), (key1179, 120), (key1217, -120)]

def entry11_9 : Integer.Sparse Key := [(key2591, 120), (key2594, -120), (key2847, -120), (key2881, 120), (key2969, 120), (key2990, -120)]

def entry11_10 : Integer.Sparse Key := [(key2354, 120), (key2358, -120), (key2449, -120), (key2514, 120), (key2529, 120), (key2559, -120)]

def entry11_11 : Integer.Sparse Key := [(key2353, 120), (key2356, -120), (key2448, -120), (key2513, 192), (key2527, 48), (key2558, -120)]

def entry12_0 : Integer.Sparse Key := [(key2616, 12), (key2619, -12), (key2632, -12), (key2642, 12), (key2649, 12), (key2654, -12), (key2671, -12), (key2674, 12), (key2706, 12), (key2729, -12), (key2738, -12), (key2748, 12), (key2786, 72), (key2794, -60), (key2796, -12), (key2809, -72), (key2829, 60), (key2832, 12), (key2860, 60), (key2870, -60), (key2898, 12), (key2905, -12), (key2939, 48), (key2944, -48), (key2951, -48), (key2961, 48), (key2977, 48), (key2984, -48)]

def entry12_1 : Integer.Sparse Key := [(key1288, 120), (key1308, -120), (key1383, -120), (key1416, 120), (key1538, 120), (key1565, -120)]

def entry12_2 : Integer.Sparse Key := [(key2609, 48), (key2613, 72), (key2625, -48), (key2629, -60), (key2637, -12), (key2647, -12), (key2652, 12), (key2664, -48), (key2668, -72), (key2699, 48), (key2703, 60), (key2723, 12), (key2736, 12), (key2746, -12), (key2779, 48), (key2783, 60), (key2791, 12), (key2802, -48), (key2806, -60), (key2826, -12), (key2896, -12), (key2903, 12), (key2937, 12), (key2942, -12), (key2949, -12), (key2959, 12), (key2975, 12), (key2982, -12)]

def entry12_3 : Integer.Sparse Key := [(key999, 120), (key1013, -120), (key1034, -120), (key1069, 120), (key1121, 120), (key1148, -120)]

def entry12_4 : Integer.Sparse Key := [(key2607, 120), (key2623, -120), (key2662, -120), (key2697, 120), (key2777, 120), (key2800, -120)]

def entry12_5 : Integer.Sparse Key := [(key1292, 12), (key1297, -12), (key1312, -12), (key1325, 12), (key1338, 12), (key1344, -12), (key1387, -12), (key1392, 12), (key1420, 12), (key1443, -12), (key1456, -12), (key1465, 12), (key1542, 12), (key1547, 60), (key1555, -72), (key1569, -12), (key1574, -60), (key1592, 72), (key1623, 60), (key1632, -60), (key1658, 12), (key1666, -12), (key1773, 48), (key1779, -48), (key1789, -48), (key1797, 48), (key1816, 48), (key1824, -48)]

def entry12_6 : Integer.Sparse Key := [(key3071, 120), (key3073, -120), (key3108, -120), (key3111, 120), (key3135, 120), (key3137, -120)]

def entry12_7 : Integer.Sparse Key := [(key1292, 48), (key1297, 72), (key1312, -48), (key1317, -60), (key1325, -12), (key1338, -12), (key1344, 12), (key1387, -48), (key1392, -72), (key1420, 48), (key1425, 60), (key1443, 12), (key1456, 12), (key1465, -12), (key1542, 48), (key1547, 60), (key1555, 12), (key1569, -48), (key1574, -60), (key1592, -12), (key1658, -12), (key1666, 12), (key1773, 12), (key1779, -12), (key1789, -12), (key1797, 12), (key1816, 12), (key1824, -12)]

def entry12_8 : Integer.Sparse Key := [(key997, 120), (key1012, -120), (key1032, -120), (key1068, 120), (key1120, 120), (key1147, -120)]

def entry12_9 : Integer.Sparse Key := [(key2616, -12), (key2619, 12), (key2632, 72), (key2640, -60), (key2642, -12), (key2649, 48), (key2654, -48), (key2671, 12), (key2674, -12), (key2706, -72), (key2726, 60), (key2729, 12), (key2738, -48), (key2748, 48), (key2786, -12), (key2796, 12), (key2809, 12), (key2832, -12), (key2860, 60), (key2870, -60), (key2898, 48), (key2905, -48), (key2939, 12), (key2944, -12), (key2951, -12), (key2961, 12), (key2977, 12), (key2984, -12)]

def entry12_10 : Integer.Sparse Key := [(key2375, 120), (key2387, -120), (key2403, -120), (key2434, 120), (key2477, 120), (key2500, -120)]

def entry12_11 : Integer.Sparse Key := [(key2370, -12), (key2373, 36), (key2386, -60), (key2398, 12), (key2401, -36), (key2433, 60), (key2476, 48), (key2499, -48), (key2583, 12), (key2586, 84), (key2597, -60), (key2762, -12), (key2765, -84), (key2886, 72), (key2928, 60), (key2965, -72)]

def entry12_12 : Integer.Sparse Key := [(key2608, 48), (key2611, 72), (key2624, -48), (key2627, -60), (key2636, -32), (key2645, 8), (key2651, 12), (key2663, -48), (key2666, -72), (key2698, 60), (key2701, 84), (key2722, 24), (key2745, -24), (key2778, 36), (key2781, 36), (key2790, 24), (key2801, -48), (key2804, -60), (key2825, -32), (key2895, -12), (key2902, 12), (key2947, 8), (key2958, 12), (key2974, 12), (key2981, -12)]

def entry13_0 : Integer.Sparse Key := [(key2175, 120), (key2179, -120), (key2275, -120), (key2281, 120), (key2328, 120), (key2330, -120)]

def entry13_1 : Integer.Sparse Key := [(key754, 120), (key755, -120), (key843, -120), (key844, 120), (key944, 120), (key945, -120)]

def entry13_2 : Integer.Sparse Key := [(key2079, 120), (key2085, -120), (key2176, -120), (key2187, 120), (key2279, 120), (key2287, -120)]

def entry13_3 : Integer.Sparse Key := [(key713, 120), (key715, -120), (key890, -120), (key914, 120), (key959, 120), (key966, -120)]

def entry13_4 : Integer.Sparse Key := [(key2098, 120), (key2099, -120), (key2203, -120), (key2206, 120), (key2318, 120), (key2321, -120)]

def entry13_5 : Integer.Sparse Key := [(key817, 120), (key818, -120), (key897, -120), (key902, 120), (key960, 120), (key962, -120)]

def entry13_6 : Integer.Sparse Key := [(key2182, 120), (key2183, -120), (key2284, -120), (key2285, 120), (key2345, 120), (key2346, -120)]

def entry13_7 : Integer.Sparse Key := [(key738, 120), (key743, -120), (key818, -120), (key825, 120), (key902, 120), (key908, -120)]

def entry13_8 : Integer.Sparse Key := [(key721, 120), (key722, -120), (key921, -120), (key939, 120), (key959, 120), (key966, -120)]

def entry13_9 : Integer.Sparse Key := [(key2078, 120), (key2082, -120), (key2275, -120), (key2289, 120), (key2328, 120), (key2333, -120)]

def entry13_10 : Integer.Sparse Key := [(key1998, 120), (key2000, -120), (key2267, -120), (key2292, 120), (key2340, 120), (key2349, -120)]

def entry13_11 : Integer.Sparse Key := [(key2006, 120), (key2007, -120), (key2299, -120), (key2313, 120), (key2340, 120), (key2349, -120)]

def entry13_12 : Integer.Sparse Key := [(key2092, 120), (key2095, -120), (key2194, -120), (key2200, 120), (key2305, 120), (key2310, -120)]

def entry13_13 : Integer.Sparse Key := [(key776, 120), (key778, -120), (key801, -120), (key811, 192), (key836, 48), (key839, -120)]

def entry14_0 : Integer.Sparse Key := [(key2379, 6), (key2382, -6), (key2393, 14), (key2407, 54), (key2410, -30), (key2441, 56), (key2445, -42), (key2473, -36), (key2483, 30), (key2507, -24), (key2526, 42), (key2539, 24), (key2544, -32), (key2555, -8), (key2557, 18), (key2565, -30), (key2592, -6), (key2595, 6), (key2602, -14), (key2771, 6), (key2774, -30), (key2848, -24), (key2882, 36), (key2891, 30), (key2912, -28), (key2933, 4), (key2934, -18), (key2970, -36), (key2991, 8), (key2993, 42), (key2996, 18), (key3003, -30)]

def entry14_1 : Integer.Sparse Key := [(key1254, 120), (key1263, -120), (key1529, -120), (key1646, 120), (key1763, 120), (key1804, -120)]

def entry14_2 : Integer.Sparse Key := [(key2378, 12), (key2383, 24), (key2390, -36), (key2394, -36), (key2406, -12), (key2411, -24), (key2437, 36), (key2443, 36), (key2480, 24), (key2484, 24), (key2503, -24), (key2509, -24), (key2587, 48), (key2593, 36), (key2598, -24), (key2600, -24), (key2766, -48), (key2772, -36), (key2887, 36), (key2889, 36), (key2929, 24), (key2931, 24), (key2966, -36), (key2968, -36)]

def entry14_3 : Integer.Sparse Key := [(key976, 120), (key984, -120), (key1090, -120), (key1169, 120), (key1183, 120), (key1220, -120)]

def entry14_4 : Integer.Sparse Key := [(key2377, 120), (key2389, -120), (key2405, -120), (key2436, 120), (key2479, 120), (key2502, -120)]

def entry14_5 : Integer.Sparse Key := [(key1531, 60), (key1536, -60), (key1609, -60), (key1642, 60), (key1651, 60), (key1674, -60), (key1765, 60), (key1768, -60), (key1806, -60), (key1832, 60), (key1837, 60), (key1848, -60)]

def entry14_6 : Integer.Sparse Key := [(key2428, 156), (key2430, -96), (key2444, 12), (key2496, -96), (key2510, 96), (key2574, 48), (key2577, -84), (key3040, -36), (key3042, -24), (key3044, -12), (key3132, -24), (key3140, 72), (key3145, 24), (key3148, -36)]

def entry14_7 : Integer.Sparse Key := [(key1256, 60), (key1261, 60), (key1265, -60), (key1268, -60), (key1531, -60), (key1536, -60), (key1648, 60), (key1651, 60), (key1765, 60), (key1768, 60), (key1806, -60), (key1809, -60)]

def entry14_8 : Integer.Sparse Key := [(key976, 120), (key983, -120), (key1090, -120), (key1168, 120), (key1182, 120), (key1219, -120)]

def entry14_9 : Integer.Sparse Key := [(key2379, 54), (key2382, -30), (key2393, 56), (key2395, -42), (key2407, 6), (key2410, -6), (key2441, 14), (key2473, -36), (key2483, -24), (key2507, 30), (key2526, 42), (key2539, 24), (key2544, -8), (key2545, 18), (key2555, -32), (key2565, -30), (key2592, 6), (key2595, -30), (key2602, 4), (key2603, -18), (key2771, -6), (key2774, 6), (key2848, -24), (key2882, 36), (key2891, -36), (key2912, 8), (key2914, 42), (key2933, -14), (key2970, 30), (key2991, -28), (key2996, 18), (key3003, -30)]

def entry14_10 : Integer.Sparse Key := [(key2361, 120), (key2363, -44), (key2366, -76), (key2452, -36), (key2456, -84), (key2517, 12), (key2519, 84), (key2523, 96), (key2528, -12), (key2530, 24), (key2560, -48), (key2567, 36), (key2579, -72)]

def entry14_11 : Integer.Sparse Key := [(key2361, 120), (key2364, -120), (key2456, -120), (key2520, 120), (key2531, 120), (key2561, -120)]

def entry14_12 : Integer.Sparse Key := [(key2378, 60), (key2381, 60), (key2390, -60), (key2392, -60), (key2406, -60), (key2409, -60), (key2437, 60), (key2440, 60), (key2480, 60), (key2482, 60), (key2503, -60), (key2506, -60)]

def entry14_13 : Integer.Sparse Key := [(key1999, 120), (key2003, -120), (key2268, -120), (key2294, 120), (key2324, 120), (key2336, -120)]

def entry14_14 : Integer.Sparse Key := [(key2362, 60), (key2367, -60), (key2457, -60), (key2460, -60), (key2521, 88), (key2525, 84), (key2532, 32), (key2533, 36), (key2562, -60), (key2564, -60)]

def entry15_0 : Integer.Sparse Key := [(key2616, 48), (key2618, -18), (key2621, -30), (key2628, -12), (key2632, -36), (key2640, 6), (key2641, 30), (key2644, 36), (key2646, -6), (key2648, 12), (key2653, -18), (key2658, 18), (key2660, -30), (key2671, 12), (key2673, -6), (key2676, -6), (key2706, -12), (key2728, 12), (key2732, 18), (key2735, -12), (key2737, 6), (key2747, -12), (key2753, 6), (key2758, -18), (key2786, -12), (key2794, 12), (key2795, 6), (key2798, 6), (key2805, -12), (key2809, 24), (key2829, 52), (key2831, -12), (key2835, -54), (key2860, -6), (key2870, -36), (key2885, 42), (key2893, 6), (key2897, -6), (key2904, 6), (key2920, -6), (key2923, 30), (key2927, -36), (key2938, -6), (key2943, 6), (key2948, 8), (key2950, -18), (key2960, 4), (key2972, -24), (key2976, 42), (key2997, 18), (key2998, -24), (key3000, -6), (key3017, 8), (key3023, 6), (key3026, -12), (key3030, 6)]

def entry15_1 : Integer.Sparse Key := [(key1417, 120), (key1471, -120), (key1566, -120), (key1680, 120), (key1902, 120), (key1917, -120)]

def entry15_2 : Integer.Sparse Key := [(key2608, 12), (key2614, -12), (key2624, -12), (key2638, 24), (key2659, -12), (key2663, -12), (key2669, 12), (key2698, 18), (key2704, 66), (key2724, 36), (key2752, -72), (key2757, -48), (key2778, 6), (key2784, -6), (key2792, -12), (key2801, -12), (key2807, -60), (key2827, -44), (key2858, 18), (key2868, -18), (key2918, 42), (key2919, 12), (key2922, 30), (key3009, 12), (key3011, 68), (key3016, 48), (key3021, -42), (key3022, 6), (key3025, -48)]

def entry15_3 : Integer.Sparse Key := [(key1028, 120), (key1036, -120), (key1106, -120), (key1123, 120), (key1232, 120), (key1235, -120)]

def entry15_4 : Integer.Sparse Key := [(key2780, 120), (key2789, -120), (key2803, -120), (key2824, 120), (key2855, 120), (key2865, -120)]

def entry15_5 : Integer.Sparse Key := [(key1291, 48), (key1299, -48), (key1311, -48), (key1327, 48), (key1352, 48), (key1355, -48), (key1386, 12), (key1394, -12), (key1419, -12), (key1445, 12), (key1473, 12), (key1481, -12), (key1541, -12), (key1557, 12), (key1568, 72), (key1576, -60), (key1594, -12), (key1617, -60), (key1625, 60), (key1682, 60), (key1684, -72), (key1690, 12), (key1897, 12), (key1900, -12), (key1904, -12), (key1912, 12), (key1921, 12), (key1927, -12)]

def entry15_6 : Integer.Sparse Key := [(key2679, 72), (key2684, -60), (key2691, 4), (key2710, -84), (key2717, 96), (key2754, 48), (key2755, -84), (key2813, 8), (key2820, -12), (key3014, 8), (key3047, 48), (key3053, -60), (key3058, -4), (key3061, -36), (key3068, 72), (key3075, 24), (key3076, -36), (key3096, -8), (key3113, 12), (key3115, -8)]

def entry15_7 : Integer.Sparse Key := [(key1291, 12), (key1299, -12), (key1311, -12), (key1327, 12), (key1352, 12), (key1355, -12), (key1386, -12), (key1394, 12), (key1419, 12), (key1427, 60), (key1445, 48), (key1473, -72), (key1481, -48), (key1541, 12), (key1557, -12), (key1568, -12), (key1576, -60), (key1594, -48), (key1682, 60), (key1684, 12), (key1690, 48), (key1897, -12), (key1900, 12), (key1904, 72), (key1912, 48), (key1919, -60), (key1921, -12), (key1927, -48)]

def entry15_8 : Integer.Sparse Key := [(key1029, 120), (key1035, -120), (key1107, -120), (key1122, 120), (key1231, 120), (key1234, -120)]

def entry15_9 : Integer.Sparse Key := [(key2616, 12), (key2618, -6), (key2621, -6), (key2632, -12), (key2640, 12), (key2641, 12), (key2644, 6), (key2646, -12), (key2648, 6), (key2653, -12), (key2667, -6), (key2671, 54), (key2673, -12), (key2676, -36), (key2702, -12), (key2706, 18), (key2726, 60), (key2728, 30), (key2732, -60), (key2735, -6), (key2737, 12), (key2747, -18), (key2753, -6), (key2758, 18), (key2782, -6), (key2786, -36), (key2794, 6), (key2795, -6), (key2798, 36), (key2809, -12), (key2831, 6), (key2835, 18), (key2860, -6), (key2870, -36), (key2885, 42), (key2893, 6), (key2897, 6), (key2904, -6), (key2920, 6), (key2923, -12), (key2927, 6), (key2938, -12), (key2943, -6), (key2950, -6), (key2960, 6), (key2972, -24), (key2983, 42), (key2997, 18), (key2998, -6), (key3000, -24), (key3008, 18), (key3010, -30), (key3012, 6), (key3017, -18), (key3023, -6), (key3026, 30), (key3030, -36)]

def entry15_10 : Integer.Sparse Key := [(key2370, 12), (key2376, -12), (key2388, 12), (key2398, 108), (key2404, -72), (key2464, -76), (key2478, 84), (key2501, 12), (key2568, 36), (key2570, -60), (key2575, -12), (key2583, -12), (key2589, 12), (key2604, -12), (key2762, 12), (key2768, -48), (key2839, -44), (key2876, 84), (key2916, 36), (key2925, -60), (key3019, -12), (key3028, 12)]

def entry15_11 : Integer.Sparse Key := [(key2763, 120), (key2767, -120), (key2840, -120), (key2875, 120), (key2888, 120), (key2909, -120)]

def entry15_12 : Integer.Sparse Key := [(key2609, 12), (key2613, -12), (key2625, -12), (key2637, 12), (key2647, 12), (key2652, -12), (key2664, -12), (key2668, 12), (key2699, 12), (key2723, -12), (key2736, -12), (key2746, 12), (key2779, 12), (key2783, 60), (key2791, -72), (key2802, -12), (key2806, -60), (key2826, 72), (key2857, 60), (key2867, -60), (key2896, 12), (key2903, -12), (key2937, 48), (key2942, -48), (key2949, -48), (key2959, 48), (key2975, 48), (key2982, -48)]

def entry15_13 : Integer.Sparse Key := [(key2174, 120), (key2176, -120), (key2274, -120), (key2279, 120), (key2341, 120), (key2343, -120)]

def entry15_14 : Integer.Sparse Key := [(key2383, -6), (key2390, 12), (key2394, 6), (key2406, 72), (key2411, -42), (key2437, 60), (key2443, -42), (key2472, -48), (key2484, 42), (key2503, -36), (key2509, 6), (key2524, 48), (key2569, 24), (key2571, -36), (key2576, 12), (key2580, -36), (key2593, 6), (key2598, -12), (key2600, -6), (key2766, -12), (key2772, -18), (key2843, -12), (key2880, 36), (key2889, 18), (key2910, -24), (key2931, -18), (key2966, -24), (key2968, -6), (key2989, 48), (key2995, 12), (key3002, -24)]

def entry15_15 : Integer.Sparse Key := [(key2608, 48), (key2614, -48), (key2624, -48), (key2638, 72), (key2657, 24), (key2659, -48), (key2663, 12), (key2669, -12), (key2698, -32), (key2704, 12), (key2724, 24), (key2757, -24), (key2778, 8), (key2784, -12), (key2792, 24), (key2801, 72), (key2807, -60), (key2827, -32), (key2851, -60), (key2858, 72), (key2868, 12), (key2918, 48), (key2919, -72), (key3011, 8), (key3016, 12), (key3021, -12), (key3022, 24), (key3025, -12)]

def entry16_0 : Integer.Sparse Key := [(key2616, -24), (key2619, 24), (key2632, 24), (key2642, -24), (key2649, -24), (key2654, 24), (key2671, 24), (key2674, -24), (key2706, -24), (key2729, 24), (key2738, 24), (key2748, -24), (key2786, 96), (key2796, -96), (key2809, -96), (key2832, 96), (key2898, 96), (key2905, -96), (key2939, 24), (key2944, -24), (key2951, -24), (key2961, 24), (key2977, 24), (key2984, -24)]

def entry16_1 : Integer.Sparse Key := [(key1288, 120), (key1334, -120), (key1383, -120), (key1452, 120), (key1769, 120), (key1785, -120)]

def entry16_2 : Integer.Sparse Key := [(key2609, 24), (key2613, 96), (key2625, -24), (key2637, 24), (key2647, -96), (key2652, -24), (key2664, -24), (key2668, -96), (key2699, 24), (key2723, -24), (key2736, 96), (key2746, 24), (key2779, 24), (key2791, -24), (key2802, -24), (key2826, 24), (key2896, 24), (key2903, -24), (key2937, 96), (key2942, 24), (key2949, -96), (key2959, -24), (key2975, -24), (key2982, 24)]

def entry16_3 : Integer.Sparse Key := [(key994, 120), (key1013, -120), (key1029, -120), (key1069, 120), (key1197, 120), (key1210, -120)]

def entry16_4 : Integer.Sparse Key := [(key2607, 120), (key2634, -120), (key2662, -120), (key2720, 120), (key2788, 120), (key2823, -120)]

def entry16_5 : Integer.Sparse Key := [(key1292, -24), (key1297, 24), (key1312, 24), (key1325, -24), (key1338, -24), (key1344, 24), (key1387, 24), (key1392, -24), (key1420, -24), (key1443, 24), (key1456, 24), (key1465, -24), (key1542, 96), (key1555, -96), (key1569, -96), (key1592, 96), (key1658, 96), (key1666, -96), (key1773, 24), (key1779, -24), (key1789, -24), (key1797, 24), (key1816, 24), (key1824, -24)]

def entry16_6 : Integer.Sparse Key := [(key3062, 120), (key3067, -120), (key3097, -120), (key3104, 120), (key3135, 120), (key3137, -120)]

def entry16_7 : Integer.Sparse Key := [(key1292, 24), (key1297, 96), (key1312, -24), (key1325, 24), (key1338, -96), (key1344, -24), (key1387, -24), (key1392, -96), (key1420, 24), (key1443, -24), (key1456, 96), (key1465, 24), (key1542, 24), (key1555, -24), (key1569, -24), (key1592, 24), (key1658, 24), (key1666, -24), (key1773, 96), (key1779, 24), (key1789, -96), (key1797, -24), (key1816, -24), (key1824, 24)]

def entry16_8 : Integer.Sparse Key := [(key993, 120), (key1012, -120), (key1028, -120), (key1068, 120), (key1196, 120), (key1209, -120)]

def entry16_9 : Integer.Sparse Key := [(key2616, 24), (key2619, -24), (key2632, 96), (key2642, -96), (key2649, 24), (key2654, -24), (key2671, -24), (key2674, 24), (key2706, -96), (key2729, 96), (key2738, -24), (key2748, 24), (key2786, 24), (key2796, -24), (key2809, -24), (key2832, 24), (key2898, 24), (key2905, -24), (key2939, -24), (key2944, 24), (key2951, 24), (key2961, -24), (key2977, 96), (key2984, -96)]

def entry16_10 : Integer.Sparse Key := [(key2371, 120), (key2387, -120), (key2399, -120), (key2434, 120), (key2541, 120), (key2552, -120)]

def entry16_11 : Integer.Sparse Key := [(key2370, 84), (key2373, -24), (key2386, -72), (key2398, -84), (key2401, 24), (key2433, 72), (key2476, -24), (key2499, 24), (key2540, 48), (key2551, -48), (key2583, 36), (key2586, 24), (key2597, -48), (key2762, -36), (key2765, -24), (key2886, 24), (key2908, 72), (key2928, 48), (key2965, -24), (key2987, -72)]

def entry16_12 : Integer.Sparse Key := [(key2608, 24), (key2611, 96), (key2624, -24), (key2636, -12), (key2645, -60), (key2651, -24), (key2663, -24), (key2666, -96), (key2698, 36), (key2722, 36), (key2734, 60), (key2745, 36), (key2778, 12), (key2790, 12), (key2801, -24), (key2825, -12), (key2895, 24), (key2902, -24), (key2935, 36), (key2941, 12), (key2947, -60), (key2958, -24), (key2974, -24), (key2981, 24)]

def entry16_13 : Integer.Sparse Key := [(key2091, 120), (key2095, -120), (key2193, -120), (key2200, 120), (key2343, 120), (key2347, -120)]

def entry16_14 : Integer.Sparse Key := [(key2378, 120), (key2392, -120), (key2406, -120), (key2440, 120), (key2543, 120), (key2554, -120)]

def entry16_15 : Integer.Sparse Key := [(key2609, -24), (key2613, 24), (key2625, 24), (key2637, -24), (key2647, -24), (key2652, 24), (key2664, 24), (key2668, -24), (key2699, -24), (key2723, 24), (key2736, 24), (key2746, -24), (key2779, 96), (key2791, -96), (key2802, -96), (key2826, 96), (key2896, 96), (key2903, -96), (key2937, 24), (key2942, -24), (key2949, -24), (key2959, 24), (key2975, 24), (key2982, -24)]

def entry16_16 : Integer.Sparse Key := [(key2608, 72), (key2611, 48), (key2624, 48), (key2645, -96), (key2651, -72), (key2663, -72), (key2666, -48), (key2698, -96), (key2722, 48), (key2734, 96), (key2745, 96), (key2801, 48), (key2895, -48), (key2902, 48), (key2935, 48), (key2941, 48), (key2947, -96), (key2958, -72), (key2974, 48), (key2981, -48)]

def entry17_0 : Integer.Sparse Key := [(key1296, 48), (key1302, -48), (key1316, -48), (key1329, 48), (key1339, 48), (key1345, -48), (key1391, 12), (key1397, -12), (key1424, -12), (key1447, 12), (key1457, 12), (key1466, -12), (key1546, -12), (key1559, 12), (key1573, 12), (key1596, -12), (key1659, -12), (key1667, 12), (key1774, 12), (key1780, -12), (key1788, 60), (key1790, -72), (key1798, 12), (key1813, -60), (key1817, 72), (key1825, -12), (key1839, 60), (key1841, -60)]

def entry17_1 : Integer.Sparse Key := [(key384, 120), (key393, -120), (key405, -120), (key416, 120), (key438, 120), (key448, -120)]

def entry17_2 : Integer.Sparse Key := [(key1292, 12), (key1298, -12), (key1312, -12), (key1326, 12), (key1351, 12), (key1354, -12), (key1387, -12), (key1393, 12), (key1420, 12), (key1444, -12), (key1472, -12), (key1480, 12), (key1542, 12), (key1548, 60), (key1556, -72), (key1569, -12), (key1575, -60), (key1593, 72), (key1624, 60), (key1633, -60), (key1683, 12), (key1689, -12), (key1896, 48), (key1899, -48), (key1903, -48), (key1911, 48), (key1920, 48), (key1926, -48)]

def entry17_3 : Integer.Sparse Key := [(key44, 120), (key47, -120), (key101, -120), (key114, 120), (key172, 120), (key176, -120)]

def entry17_4 : Integer.Sparse Key := [(key1540, 120), (key1552, -120), (key1567, -120), (key1589, 120), (key1620, 120), (key1629, -120)]

def entry17_5 : Integer.Sparse Key := [(key237, 48), (key240, -48), (key249, -48), (key262, 48), (key268, 48), (key273, -48), (key303, 12), (key306, -12), (key317, -12), (key330, 12), (key336, 12), (key342, -12), (key386, -12), (key399, 12), (key407, 72), (key410, -60), (key420, -12), (key436, -60), (key444, 60), (key468, 60), (key471, -72), (key477, 12), (key569, 12), (key574, -12), (key579, -12), (key585, 12), (key597, 12), (key603, -12)]

def entry17_6 : Integer.Sparse Key := [(key1406, 120), (key1409, -120), (key1434, -120), (key1438, 120), (key1476, 120), (key1478, -120)]

def entry17_7 : Integer.Sparse Key := [(key237, 12), (key240, -12), (key249, -12), (key262, 12), (key268, 12), (key273, -12), (key303, -12), (key306, 12), (key317, 12), (key320, 60), (key330, 48), (key336, -72), (key342, -48), (key386, 12), (key399, -12), (key407, -12), (key410, -60), (key420, -48), (key468, 60), (key471, 12), (key477, 48), (key569, -12), (key574, 12), (key579, 72), (key585, 48), (key594, -60), (key597, -12), (key603, -48)]

def entry17_8 : Integer.Sparse Key := [(key18, 12), (key21, -12), (key32, 12), (key43, 108), (key46, -72), (key100, -76), (key112, 84), (key134, 12), (key171, 36), (key174, -60), (key179, -12), (key206, -12), (key209, 12), (key214, -12), (key375, 12), (key378, -48), (key426, -44), (key457, 84), (key463, 36), (key480, -60), (key589, -12), (key606, 12)]

def entry17_9 : Integer.Sparse Key := [(key1296, 12), (key1302, -12), (key1316, -12), (key1329, 12), (key1339, 12), (key1345, -12), (key1391, 48), (key1397, -48), (key1424, -48), (key1447, 48), (key1457, 48), (key1466, -48), (key1546, 12), (key1559, -12), (key1573, -12), (key1596, 12), (key1659, 12), (key1667, -12), (key1772, 60), (key1774, -72), (key1780, 12), (key1790, 12), (key1798, -12), (key1813, -60), (key1817, -12), (key1825, 72), (key1839, 60), (key1844, -60)]

def entry17_10 : Integer.Sparse Key := [(key1527, 120), (key1533, -120), (key1605, -120), (key1639, 120), (key1678, 120), (key1692, -120)]

def entry17_11 : Integer.Sparse Key := [(key1526, 120), (key1530, -120), (key1604, -120), (key1637, 120), (key1647, 120), (key1671, -120)]

def entry17_12 : Integer.Sparse Key := [(key1291, 12), (key1295, -12), (key1311, -12), (key1324, 12), (key1336, 12), (key1343, -12), (key1386, -12), (key1390, 12), (key1419, 12), (key1442, -12), (key1454, -12), (key1464, 12), (key1541, 12), (key1545, 60), (key1554, -72), (key1568, -12), (key1572, -60), (key1591, 72), (key1622, 60), (key1631, -60), (key1657, 12), (key1665, -12), (key1771, 48), (key1778, -48), (key1787, -48), (key1796, 48), (key1815, 48), (key1823, -48)]

def entry17_13 : Integer.Sparse Key := [(key830, 120), (key831, -120), (key924, -120), (key928, 120), (key960, 120), (key962, -120)]

def entry17_14 : Integer.Sparse Key := [(key1531, 60), (key1535, -60), (key1609, -60), (key1641, 60), (key1650, 60), (key1673, -60), (key1765, 60), (key1767, -60), (key1806, -60), (key1831, 60), (key1836, 60), (key1847, -60)]

def entry17_15 : Integer.Sparse Key := [(key1292, 48), (key1298, -48), (key1312, -48), (key1326, 48), (key1351, 48), (key1354, -48), (key1387, 12), (key1393, -12), (key1420, -12), (key1444, 12), (key1472, 12), (key1480, -12), (key1542, -12), (key1556, 12), (key1569, 72), (key1575, -60), (key1593, -12), (key1618, -60), (key1624, 60), (key1681, 60), (key1683, -72), (key1689, 12), (key1896, 12), (key1899, -12), (key1903, -12), (key1911, 12), (key1920, 12), (key1926, -12)]

def entry17_16 : Integer.Sparse Key := [(key1291, -24), (key1295, 24), (key1311, 24), (key1324, -24), (key1336, -24), (key1343, 24), (key1386, 24), (key1390, -24), (key1419, -24), (key1442, 24), (key1454, 24), (key1464, -24), (key1541, 96), (key1554, -96), (key1568, -96), (key1591, 96), (key1657, 96), (key1665, -96), (key1771, 24), (key1778, -24), (key1787, -24), (key1796, 24), (key1815, 24), (key1823, -24)]

def entry17_17 : Integer.Sparse Key := [(key236, 48), (key239, -48), (key248, -48), (key260, 72), (key267, 24), (key271, -48), (key302, 12), (key305, -12), (key316, -32), (key319, 12), (key328, 24), (key340, -24), (key385, 8), (key388, -12), (key397, 24), (key406, 72), (key409, -60), (key418, -32), (key435, -60), (key442, 72), (key450, 12), (key467, 48), (key469, -72), (key578, 8), (key583, 12), (key593, -12), (key595, 24), (key601, -12)]

def entry18_0 : Integer.Sparse Key := [(key2616, 48), (key2619, -48), (key2632, -48), (key2642, 48), (key2649, 48), (key2654, -48), (key2671, 12), (key2674, -12), (key2706, -12), (key2729, 12), (key2738, 12), (key2748, -12), (key2786, -12), (key2796, 12), (key2809, 12), (key2829, 60), (key2832, -72), (key2870, -60), (key2883, 60), (key2898, -12), (key2905, 72), (key2913, -60), (key2939, 12), (key2944, -12), (key2951, -12), (key2961, 12), (key2977, 12), (key2984, -12)]

def entry18_1 : Integer.Sparse Key := [(key1416, 120), (key1452, -120), (key1565, -120), (key1652, 120), (key1785, 120), (key1810, -120)]

def entry18_2 : Integer.Sparse Key := [(key2609, 12), (key2613, -12), (key2625, -12), (key2637, 12), (key2647, 12), (key2652, -12), (key2664, -12), (key2668, 12), (key2699, 12), (key2703, 60), (key2723, 48), (key2736, -72), (key2746, -48), (key2779, 12), (key2791, -12), (key2802, -12), (key2806, -60), (key2826, -48), (key2894, 60), (key2896, 12), (key2903, 48), (key2937, -12), (key2942, 12), (key2949, 72), (key2959, 48), (key2973, -60), (key2975, -12), (key2982, -48)]

def entry18_3 : Integer.Sparse Key := [(key1029, 120), (key1034, -120), (key1107, -120), (key1121, 120), (key1191, 120), (key1197, -120)]

def entry18_4 : Integer.Sparse Key := [(key2777, 120), (key2788, -120), (key2800, -120), (key2823, 120), (key2854, 120), (key2864, -120)]

def entry18_5 : Integer.Sparse Key := [(key1292, 48), (key1297, -48), (key1312, -48), (key1325, 48), (key1338, 48), (key1344, -48), (key1387, 12), (key1392, -12), (key1420, -12), (key1443, 12), (key1456, 12), (key1465, -12), (key1542, -12), (key1555, 12), (key1569, 72), (key1574, -60), (key1592, -12), (key1618, -60), (key1623, 60), (key1656, 60), (key1658, -72), (key1666, 12), (key1773, 12), (key1779, -12), (key1789, -12), (key1797, 12), (key1816, 12), (key1824, -12)]

def entry18_6 : Integer.Sparse Key := [(key3048, 120), (key3052, -120), (key3062, -120), (key3067, 120), (key3071, 120), (key3073, -120)]

def entry18_7 : Integer.Sparse Key := [(key1292, 12), (key1297, -12), (key1312, -12), (key1325, 12), (key1338, 12), (key1344, -12), (key1387, -12), (key1392, 12), (key1420, 12), (key1425, 60), (key1443, 48), (key1456, -72), (key1465, -48), (key1542, 12), (key1555, -12), (key1569, -12), (key1574, -60), (key1592, -48), (key1656, 60), (key1658, 12), (key1666, 48), (key1773, -12), (key1779, 12), (key1789, 72), (key1797, 48), (key1814, -60), (key1816, -12), (key1824, -48)]

def entry18_8 : Integer.Sparse Key := [(key1028, 120), (key1032, -120), (key1106, -120), (key1120, 120), (key1189, 120), (key1196, -120)]

def entry18_9 : Integer.Sparse Key := [(key2616, 12), (key2619, -12), (key2632, -12), (key2642, 12), (key2649, 12), (key2654, -12), (key2671, 48), (key2674, -48), (key2706, 12), (key2726, 60), (key2729, -72), (key2738, -12), (key2748, 12), (key2786, -48), (key2796, 48), (key2809, -12), (key2832, 12), (key2870, -60), (key2883, 60), (key2898, 12), (key2905, -12), (key2939, 48), (key2944, -48), (key2951, 12), (key2961, -12), (key2977, -12), (key2984, 72), (key2992, -60)]

def entry18_10 : Integer.Sparse Key := [(key2399, 120), (key2403, -120), (key2465, -120), (key2477, 120), (key2536, 120), (key2541, -120)]

def entry18_11 : Integer.Sparse Key := [(key2370, 12), (key2373, -12), (key2386, 12), (key2398, 108), (key2401, -72), (key2464, -76), (key2476, 84), (key2499, 12), (key2534, 36), (key2540, -60), (key2551, -12), (key2583, -12), (key2586, 12), (key2597, -12), (key2762, 12), (key2765, -48), (key2839, -44), (key2874, 84), (key2886, 36), (key2908, -60), (key2965, -12), (key2987, 12)]

def entry18_12 : Integer.Sparse Key := [(key2608, 12), (key2611, -12), (key2624, -12), (key2636, 24), (key2651, -12), (key2663, -12), (key2666, 12), (key2698, 18), (key2701, 66), (key2722, 36), (key2734, -72), (key2745, -48), (key2778, 6), (key2781, -6), (key2790, -12), (key2801, -12), (key2804, -60), (key2825, -44), (key2856, 18), (key2866, -18), (key2892, 42), (key2895, 12), (key2902, 30), (key2941, 12), (key2947, 68), (key2958, 48), (key2971, -42), (key2974, 6), (key2981, -48)]

def entry18_13 : Integer.Sparse Key := [(key2193, 120), (key2194, -120), (key2302, -120), (key2305, 120), (key2341, 120), (key2343, -120)]

def entry18_14 : Integer.Sparse Key := [(key2406, 60), (key2409, -60), (key2437, 60), (key2440, -60), (key2472, -60), (key2482, 60), (key2503, -60), (key2522, 60), (key2538, 60), (key2543, -60), (key2554, 60), (key2563, -60)]

def entry18_15 : Integer.Sparse Key := [(key2609, 48), (key2613, -48), (key2625, -48), (key2637, 48), (key2647, 48), (key2652, -48), (key2664, 12), (key2668, -12), (key2699, -12), (key2723, 12), (key2736, 12), (key2746, -12), (key2779, -12), (key2791, 12), (key2802, 72), (key2806, -60), (key2826, -12), (key2852, -60), (key2857, 60), (key2894, 60), (key2896, -72), (key2903, 12), (key2937, 12), (key2942, -12), (key2949, -12), (key2959, 12), (key2975, 12), (key2982, -12)]

def entry18_16 : Integer.Sparse Key := [(key2608, -24), (key2611, 24), (key2624, 24), (key2636, -24), (key2645, -24), (key2651, 24), (key2663, 24), (key2666, -24), (key2698, 96), (key2701, 12), (key2722, 36), (key2734, -60), (key2745, -36), (key2778, -24), (key2781, -12), (key2790, -12), (key2801, -96), (key2825, 12), (key2856, -12), (key2866, 12), (key2892, 12), (key2895, 96), (key2902, -12), (key2935, 12), (key2941, -12), (key2947, 60), (key2958, 24), (key2971, -12), (key2974, -60), (key2981, -24)]

def entry18_17 : Integer.Sparse Key := [(key1291, 48), (key1295, -48), (key1311, -48), (key1324, 48), (key1336, 48), (key1343, -48), (key1386, 12), (key1390, -12), (key1419, -12), (key1442, 12), (key1454, 12), (key1464, -12), (key1541, -12), (key1554, 12), (key1568, 72), (key1572, -60), (key1591, -12), (key1617, -60), (key1622, 60), (key1654, 60), (key1657, -72), (key1665, 12), (key1771, 12), (key1778, -12), (key1787, -12), (key1796, 12), (key1815, 12), (key1823, -12)]

def entry18_18 : Integer.Sparse Key := [(key2608, 48), (key2611, -48), (key2624, -48), (key2636, 72), (key2645, 24), (key2651, -48), (key2663, 12), (key2666, -12), (key2698, -32), (key2701, 12), (key2722, 24), (key2745, -24), (key2778, 8), (key2781, -12), (key2790, 24), (key2801, 72), (key2804, -60), (key2825, -32), (key2851, -60), (key2856, 72), (key2866, 12), (key2892, 48), (key2895, -72), (key2947, 8), (key2958, 12), (key2971, -12), (key2974, 24), (key2981, -12)]

def entry19_0 : Integer.Sparse Key := [(key1492, 120), (key1496, -120), (key1718, -120), (key1728, 120), (key1865, 120), (key1870, -120)]

def entry19_1 : Integer.Sparse Key := [(key281, 120), (key290, -120), (key350, -120), (key367, 120), (key516, 120), (key538, -120)]

def entry19_2 : Integer.Sparse Key := [(key1367, 120), (key1376, -120), (key1493, -120), (key1515, 120), (key1725, 120), (key1743, -120)]

def entry19_3 : Integer.Sparse Key := [(key29, 60), (key33, -72), (key109, -48), (key149, 96), (key175, 24), (key185, -60), (key223, 60), (key228, -48), (key495, -72), (key554, 96), (key665, 24), (key682, -60)]

def entry19_4 : Integer.Sparse Key := [(key1361, 120), (key1373, -120), (key1487, -120), (key1512, 120), (key1722, 120), (key1740, -120)]

def entry19_5 : Integer.Sparse Key := [(key257, -12), (key261, 12), (key272, -12), (key282, 12), (key285, -12), (key295, 12), (key351, 120), (key354, -72), (key398, -48), (key439, -36), (key458, 84), (key470, 36), (key481, -60), (key508, -84), (key523, 84), (key543, 12), (key596, -12), (key607, 12), (key668, 36), (key672, -60), (key678, -12)]

def entry19_6 : Integer.Sparse Key := [(key1502, 120), (key1504, -120), (key1734, -120), (key1737, 120), (key1945, 120), (key1947, -120)]

def entry19_7 : Integer.Sparse Key := [(key257, 12), (key261, 128), (key272, -108), (key282, -12), (key285, -8), (key295, -12), (key351, 12), (key354, -36), (key371, 60), (key394, -12), (key398, -84), (key470, 72), (key523, 48), (key543, -48), (key573, 60), (key596, -72)]

def entry19_8 : Integer.Sparse Key := [(key223, 120), (key226, -120), (key495, -120), (key552, 120), (key620, 120), (key646, -120)]

def entry19_9 : Integer.Sparse Key := [(key1366, 120), (key1370, -120), (key1718, -120), (key1747, 120), (key1865, 120), (key1880, -120)]

def entry19_10 : Integer.Sparse Key := [(key1276, 120), (key1281, -120), (key1699, -120), (key1753, 120), (key1934, 120), (key1954, -120)]

def entry19_11 : Integer.Sparse Key := [(key1276, 120), (key1279, -120), (key1699, -120), (key1752, 120), (key1853, 120), (key1885, -120)]

def entry19_12 : Integer.Sparse Key := [(key1365, 120), (key1375, -120), (key1491, -120), (key1514, 120), (key1724, 120), (key1742, -120)]

def entry19_13 : Integer.Sparse Key := [(key741, 120), (key742, -120), (key900, -120), (key913, 120), (key951, 120), (key954, -120)]

def entry19_14 : Integer.Sparse Key := [(key1280, 120), (key1284, -120), (key1703, -120), (key1757, 120), (key1856, 120), (key1887, -120)]

def entry19_15 : Integer.Sparse Key := [(key1488, 120), (key1493, -120), (key1714, -120), (key1725, 120), (key1938, 120), (key1941, -120)]

def entry19_16 : Integer.Sparse Key := [(key1362, 120), (key1375, -120), (key1488, -120), (key1514, 120), (key1868, 120), (key1878, -120)]

def entry19_17 : Integer.Sparse Key := [(key351, 120), (key353, -120), (key508, -120), (key521, 120), (key628, 120), (key630, -120)]

def entry19_18 : Integer.Sparse Key := [(key1488, 120), (key1491, -120), (key1714, -120), (key1724, 120), (key1862, 120), (key1868, -120)]

def entry19_19 : Integer.Sparse Key := [(key291, 120), (key294, -120), (key518, -120), (key553, 192), (key631, 48), (key647, -120)]

def entry20_0 : Integer.Sparse Key := [(key2617, 24), (key2620, -24), (key2633, -24), (key2643, 36), (key2650, 12), (key2655, -24), (key2672, -24), (key2675, 24), (key2707, 36), (key2730, 84), (key2739, -24), (key2749, -96), (key2787, 12), (key2797, -24), (key2810, -24), (key2833, -96), (key2899, 24), (key2906, 60), (key2940, -12), (key2945, 24), (key2952, 24), (key2962, 96), (key2978, 12), (key2985, -96)]

def entry20_1 : Integer.Sparse Key := [(key1294, 120), (key1314, -120), (key1389, -120), (key1422, 120), (key1544, 120), (key1571, -120)]

def entry20_2 : Integer.Sparse Key := [(key2612, 48), (key2616, 48), (key2618, 16), (key2621, 8), (key2628, -60), (key2632, -36), (key2640, -8), (key2641, -24), (key2644, -24), (key2646, 8), (key2653, 16), (key2660, 8), (key2667, -48), (key2671, -48), (key2673, -12), (key2676, -12), (key2702, 72), (key2706, 60), (key2728, 24), (key2732, 24), (key2735, -12), (key2737, 12), (key2747, -24), (key2753, 12), (key2758, -24), (key2782, 36), (key2786, 24), (key2794, 12), (key2795, 12), (key2798, 12), (key2805, -60), (key2809, -36), (key2829, -8), (key2831, -24), (key2835, -24), (key2897, -12), (key2904, 12), (key2920, -12), (key2923, 12), (key2948, 8), (key2960, 16), (key2976, 12), (key2983, -12), (key3017, 8), (key3023, 12), (key3026, -12)]

def entry20_3 : Integer.Sparse Key := [(key1006, 120), (key1019, -120), (key1041, -120), (key1076, 120), (key1127, 120), (key1155, -120)]

def entry20_4 : Integer.Sparse Key := [(key2615, 120), (key2631, -120), (key2670, -120), (key2705, 120), (key2785, 120), (key2808, -120)]

def entry20_5 : Integer.Sparse Key := [(key1296, 24), (key1303, -24), (key1316, -24), (key1330, 24), (key1340, 24), (key1346, -24), (key1391, -24), (key1398, 24), (key1424, 24), (key1448, -24), (key1458, -24), (key1467, 24), (key1546, 24), (key1560, -24), (key1573, -24), (key1597, 24), (key1660, 24), (key1668, -24), (key1775, 96), (key1781, -96), (key1791, -96), (key1799, 96), (key1818, 96), (key1826, -96)]

def entry20_6 : Integer.Sparse Key := [(key2693, -16), (key2719, 24), (key2733, 120), (key2756, -24), (key2759, -120), (key2822, -24), (key2836, -120), (key2924, 96), (key3015, 24), (key3018, 104), (key3027, -96), (key3055, 16), (key3070, -24), (key3074, 24), (key3107, 24), (key3112, -24), (key3117, 16), (key3146, 24), (key3147, -24)]

def entry20_7 : Integer.Sparse Key := [(key1296, 96), (key1303, 24), (key1316, -96), (key1330, -24), (key1340, -24), (key1346, 24), (key1391, -96), (key1398, -24), (key1424, 96), (key1448, 24), (key1458, 24), (key1467, -24), (key1546, 96), (key1560, 24), (key1573, -96), (key1597, -24), (key1660, -24), (key1668, 24), (key1775, 24), (key1781, -24), (key1791, -24), (key1799, 24), (key1818, 24), (key1826, -24)]

def entry20_8 : Integer.Sparse Key := [(key1005, 120), (key1018, -120), (key1040, -120), (key1075, 120), (key1126, 120), (key1154, -120)]

def entry20_9 : Integer.Sparse Key := [(key2617, -24), (key2620, 24), (key2633, 24), (key2643, 96), (key2650, -24), (key2655, -96), (key2672, 24), (key2675, -24), (key2707, -24), (key2730, 36), (key2739, -24), (key2749, 36), (key2787, -24), (key2797, -48), (key2810, 24), (key2833, -36), (key2899, 96), (key2906, -12), (key2940, 12), (key2945, 36), (key2952, -12), (key2962, 24), (key2978, -60), (key2985, -24)]

def entry20_10 : Integer.Sparse Key := [(key2374, -24), (key2380, 48), (key2391, -60), (key2402, 24), (key2408, -48), (key2439, 60), (key2481, 48), (key2505, -48), (key2591, 24), (key2596, 72), (key2605, -60), (key2770, -24), (key2775, -72), (key2917, 72), (key3006, 60), (key3020, -72)]

def entry20_11 : Integer.Sparse Key := [(key2594, 120), (key2601, -120), (key2773, -120), (key2890, 120), (key2932, 120), (key2969, -120)]

def entry20_12 : Integer.Sparse Key := [(key2616, 96), (key2619, 24), (key2632, -96), (key2642, -24), (key2649, -24), (key2654, 24), (key2671, -96), (key2674, -24), (key2706, 96), (key2729, 24), (key2738, 24), (key2748, -24), (key2786, 96), (key2796, 24), (key2809, -96), (key2832, -24), (key2898, -24), (key2905, 24), (key2939, 24), (key2944, -24), (key2951, -24), (key2961, 24), (key2977, 24), (key2984, -24)]

def entry20_13 : Integer.Sparse Key := [(key2082, 120), (key2087, -120), (key2179, -120), (key2189, 120), (key2281, 120), (key2289, -120)]

def entry20_14 : Integer.Sparse Key := [(key2379, -12), (key2382, 48), (key2393, -72), (key2407, 12), (key2410, -48), (key2441, 72), (key2483, 48), (key2507, -48), (key2592, 12), (key2595, 72), (key2602, -48), (key2771, -12), (key2774, -72), (key2891, 72), (key2933, 48), (key2970, -72)]

def entry20_15 : Integer.Sparse Key := [(key2612, 12), (key2616, 12), (key2621, -24), (key2628, -12), (key2632, -12), (key2641, 12), (key2644, 24), (key2658, 12), (key2660, -24), (key2671, -24), (key2676, 24), (key2702, 12), (key2706, 24), (key2728, -12), (key2732, 96), (key2753, -24), (key2758, -96), (key2786, 12), (key2798, -24), (key2809, -24), (key2829, -8), (key2835, -96), (key2920, 24), (key2923, 60), (key2948, 8), (key2960, 16), (key2976, 36), (key2983, -36), (key3008, -12), (key3010, 24), (key3012, 24), (key3017, 80), (key3023, -24), (key3026, -60)]

def entry20_16 : Integer.Sparse Key := [(key2616, 48), (key2619, 72), (key2632, -48), (key2642, 48), (key2649, -72), (key2654, -48), (key2671, -48), (key2674, -72), (key2706, 48), (key2729, -48), (key2738, 72), (key2748, 48), (key2786, 48), (key2796, -48), (key2809, -48), (key2832, 48), (key2898, 48), (key2905, -48), (key2939, 72), (key2944, 48), (key2951, -72), (key2961, -48), (key2977, -48), (key2984, 48)]

def entry20_17 : Integer.Sparse Key := [(key1296, 24), (key1302, -24), (key1316, -24), (key1329, 24), (key1339, 24), (key1345, -24), (key1391, -24), (key1397, 24), (key1424, 24), (key1447, -24), (key1457, -24), (key1466, 24), (key1546, 24), (key1559, -24), (key1573, -24), (key1596, 24), (key1659, 24), (key1667, -24), (key1774, 96), (key1780, -96), (key1790, -96), (key1798, 96), (key1817, 96), (key1825, -96)]

def entry20_18 : Integer.Sparse Key := [(key2616, 24), (key2619, -24), (key2632, -24), (key2642, 24), (key2649, 24), (key2654, -24), (key2671, -24), (key2674, 24), (key2706, 24), (key2729, 96), (key2738, -24), (key2748, -96), (key2786, 24), (key2796, -24), (key2809, -24), (key2832, -96), (key2898, 24), (key2905, 96), (key2939, -24), (key2944, 24), (key2951, 24), (key2961, 96), (key2977, -24), (key2984, -96)]

def entry20_19 : Integer.Sparse Key := [(key1370, 120), (key1379, -120), (key1496, -120), (key1519, 120), (key1728, 120), (key1747, -120)]

def entry20_20 : Integer.Sparse Key := [(key2617, 72), (key2620, 48), (key2633, -72), (key2643, -96), (key2655, 48), (key2672, -72), (key2675, -48), (key2707, 96), (key2730, 96), (key2739, 48), (key2749, -96), (key2787, 48), (key2797, 48), (key2810, -72), (key2833, -96), (key2899, -48), (key2906, 48), (key2962, 48), (key2978, 48), (key2985, -48)]

def entries : Fin 21 → Fin 21 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0, entry5_0, entry6_0, entry7_0, entry8_0, entry9_0, entry10_0, entry11_0, entry12_0, entry13_0, entry14_0, entry15_0, entry16_0, entry17_0, entry18_0, entry19_0, entry20_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1, entry5_1, entry6_1, entry7_1, entry8_1, entry9_1, entry10_1, entry11_1, entry12_1, entry13_1, entry14_1, entry15_1, entry16_1, entry17_1, entry18_1, entry19_1, entry20_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2, entry5_2, entry6_2, entry7_2, entry8_2, entry9_2, entry10_2, entry11_2, entry12_2, entry13_2, entry14_2, entry15_2, entry16_2, entry17_2, entry18_2, entry19_2, entry20_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3, entry5_3, entry6_3, entry7_3, entry8_3, entry9_3, entry10_3, entry11_3, entry12_3, entry13_3, entry14_3, entry15_3, entry16_3, entry17_3, entry18_3, entry19_3, entry20_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4, entry5_4, entry6_4, entry7_4, entry8_4, entry9_4, entry10_4, entry11_4, entry12_4, entry13_4, entry14_4, entry15_4, entry16_4, entry17_4, entry18_4, entry19_4, entry20_4],
  ![entry5_0, entry5_1, entry5_2, entry5_3, entry5_4, entry5_5, entry6_5, entry7_5, entry8_5, entry9_5, entry10_5, entry11_5, entry12_5, entry13_5, entry14_5, entry15_5, entry16_5, entry17_5, entry18_5, entry19_5, entry20_5],
  ![entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry7_6, entry8_6, entry9_6, entry10_6, entry11_6, entry12_6, entry13_6, entry14_6, entry15_6, entry16_6, entry17_6, entry18_6, entry19_6, entry20_6],
  ![entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry8_7, entry9_7, entry10_7, entry11_7, entry12_7, entry13_7, entry14_7, entry15_7, entry16_7, entry17_7, entry18_7, entry19_7, entry20_7],
  ![entry8_0, entry8_1, entry8_2, entry8_3, entry8_4, entry8_5, entry8_6, entry8_7, entry8_8, entry9_8, entry10_8, entry11_8, entry12_8, entry13_8, entry14_8, entry15_8, entry16_8, entry17_8, entry18_8, entry19_8, entry20_8],
  ![entry9_0, entry9_1, entry9_2, entry9_3, entry9_4, entry9_5, entry9_6, entry9_7, entry9_8, entry9_9, entry10_9, entry11_9, entry12_9, entry13_9, entry14_9, entry15_9, entry16_9, entry17_9, entry18_9, entry19_9, entry20_9],
  ![entry10_0, entry10_1, entry10_2, entry10_3, entry10_4, entry10_5, entry10_6, entry10_7, entry10_8, entry10_9, entry10_10, entry11_10, entry12_10, entry13_10, entry14_10, entry15_10, entry16_10, entry17_10, entry18_10, entry19_10, entry20_10],
  ![entry11_0, entry11_1, entry11_2, entry11_3, entry11_4, entry11_5, entry11_6, entry11_7, entry11_8, entry11_9, entry11_10, entry11_11, entry12_11, entry13_11, entry14_11, entry15_11, entry16_11, entry17_11, entry18_11, entry19_11, entry20_11],
  ![entry12_0, entry12_1, entry12_2, entry12_3, entry12_4, entry12_5, entry12_6, entry12_7, entry12_8, entry12_9, entry12_10, entry12_11, entry12_12, entry13_12, entry14_12, entry15_12, entry16_12, entry17_12, entry18_12, entry19_12, entry20_12],
  ![entry13_0, entry13_1, entry13_2, entry13_3, entry13_4, entry13_5, entry13_6, entry13_7, entry13_8, entry13_9, entry13_10, entry13_11, entry13_12, entry13_13, entry14_13, entry15_13, entry16_13, entry17_13, entry18_13, entry19_13, entry20_13],
  ![entry14_0, entry14_1, entry14_2, entry14_3, entry14_4, entry14_5, entry14_6, entry14_7, entry14_8, entry14_9, entry14_10, entry14_11, entry14_12, entry14_13, entry14_14, entry15_14, entry16_14, entry17_14, entry18_14, entry19_14, entry20_14],
  ![entry15_0, entry15_1, entry15_2, entry15_3, entry15_4, entry15_5, entry15_6, entry15_7, entry15_8, entry15_9, entry15_10, entry15_11, entry15_12, entry15_13, entry15_14, entry15_15, entry16_15, entry17_15, entry18_15, entry19_15, entry20_15],
  ![entry16_0, entry16_1, entry16_2, entry16_3, entry16_4, entry16_5, entry16_6, entry16_7, entry16_8, entry16_9, entry16_10, entry16_11, entry16_12, entry16_13, entry16_14, entry16_15, entry16_16, entry17_16, entry18_16, entry19_16, entry20_16],
  ![entry17_0, entry17_1, entry17_2, entry17_3, entry17_4, entry17_5, entry17_6, entry17_7, entry17_8, entry17_9, entry17_10, entry17_11, entry17_12, entry17_13, entry17_14, entry17_15, entry17_16, entry17_17, entry18_17, entry19_17, entry20_17],
  ![entry18_0, entry18_1, entry18_2, entry18_3, entry18_4, entry18_5, entry18_6, entry18_7, entry18_8, entry18_9, entry18_10, entry18_11, entry18_12, entry18_13, entry18_14, entry18_15, entry18_16, entry18_17, entry18_18, entry19_18, entry20_18],
  ![entry19_0, entry19_1, entry19_2, entry19_3, entry19_4, entry19_5, entry19_6, entry19_7, entry19_8, entry19_9, entry19_10, entry19_11, entry19_12, entry19_13, entry19_14, entry19_15, entry19_16, entry19_17, entry19_18, entry19_19, entry20_19],
  ![entry20_0, entry20_1, entry20_2, entry20_3, entry20_4, entry20_5, entry20_6, entry20_7, entry20_8, entry20_9, entry20_10, entry20_11, entry20_12, entry20_13, entry20_14, entry20_15, entry20_16, entry20_17, entry20_18, entry20_19, entry20_20]
]

end MUB6.Certificate.GramEntries.Block1

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

def entry14_1 : Integer.Sparse Key := [(key3, -720), (key147, 720)]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row0 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row1 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row2 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key302, -2), (key305, 2), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key385, 2), (key397, -2), (key406, -2), (key418, 2), (key469, 2), (key475, -2), (key568, -2), (key572, 2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row3 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row4 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row5 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row7 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key302, 2), (key305, -2), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key385, -2), (key397, 2), (key406, 2), (key418, -2), (key469, -2), (key475, 2), (key568, 2), (key572, -2), (key578, -2), (key583, 2), (key595, 2), (key601, -2)]

def row8 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row9 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row10 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row11 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row12 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key302, 2), (key305, -2), (key316, -4), (key328, 4), (key335, 4), (key340, -4), (key406, 2), (key418, -2), (key469, -2), (key475, 2), (key578, -2), (key583, 2), (key595, 2), (key601, -2)]

def row13 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row14 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row15 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

def row16 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

def row17 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key302, -2), (key305, 2), (key316, 4), (key328, -4), (key335, -4), (key340, 4), (key406, -2), (key418, 2), (key469, 2), (key475, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row18 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row19 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -2), (key328, 2), (key335, 2), (key340, -2), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row20 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 3), (key335, -1), (key340, -1), (key385, -1), (key397, 3), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row21 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 3), (key335, -1), (key340, -1), (key385, -1), (key397, 3), (key406, 1), (key418, -3), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row22 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key319, 1), (key328, -2), (key340, 1), (key385, 2), (key388, -1), (key397, -2), (key406, -1), (key418, 2), (key442, -1), (key450, 1), (key467, 1), (key469, 1), (key475, -2), (key572, 1), (key583, -1), (key593, -1), (key601, 1)]

def row23 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key319, 1), (key328, -2), (key340, 1), (key385, 2), (key388, -1), (key397, -2), (key406, -1), (key418, 2), (key442, -1), (key450, 1), (key467, 1), (key469, 1), (key475, -2), (key572, 1), (key583, -1), (key593, -1), (key601, 1)]

def row24 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -2), (key335, 1), (key340, 2), (key385, 1), (key397, -3), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

def row25 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key328, -2), (key335, 1), (key340, 2), (key385, 1), (key397, -3), (key406, -1), (key418, 3), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key595, -1), (key601, 1)]

def row26 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -2), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, 2), (key335, -1), (key340, -2), (key385, -1), (key388, -1), (key397, 3), (key406, 1), (key418, -3), (key442, -1), (key450, 1), (key467, 1), (key469, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row27 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -2), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, 2), (key335, -1), (key340, -2), (key385, -1), (key388, -1), (key397, 3), (key406, 1), (key418, -3), (key442, -1), (key450, 1), (key467, 1), (key469, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row28 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key319, -1), (key328, 3), (key340, -1), (key385, -2), (key388, 1), (key397, 2), (key406, 1), (key418, -2), (key442, 1), (key450, -1), (key467, -1), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key583, 1), (key593, 1), (key595, 1), (key601, -1)]

def row29 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, 1), (key305, -1), (key319, -1), (key328, 3), (key340, -1), (key385, -2), (key388, 1), (key397, 2), (key406, 1), (key418, -2), (key442, 1), (key450, -1), (key467, -1), (key469, -1), (key475, 1), (key568, -1), (key572, -1), (key583, 1), (key593, 1), (key595, 1), (key601, -1)]

def row30 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 2), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key319, -1), (key328, -2), (key335, 1), (key340, 1), (key385, 1), (key388, 1), (key397, -3), (key406, -1), (key418, 3), (key442, 1), (key450, -1), (key467, -1), (key469, 1), (key475, -1), (key572, 1), (key578, -1), (key583, -1), (key593, 1), (key595, -1), (key601, 1)]

def row31 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 2), (key271, -1), (key302, -1), (key305, 1), (key316, 1), (key319, -1), (key328, -2), (key335, 1), (key340, 1), (key385, 1), (key388, 1), (key397, -3), (key406, -1), (key418, 3), (key442, 1), (key450, -1), (key467, -1), (key469, 1), (key475, -1), (key572, 1), (key578, -1), (key583, -1), (key593, 1), (key595, -1), (key601, 1)]

def row32 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key302, -2), (key305, 2), (key316, 2), (key328, -2), (key335, -2), (key340, 2), (key385, 2), (key397, -2), (key406, -2), (key418, 2), (key469, 2), (key475, -2), (key568, -2), (key572, 2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row33 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row34 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row35 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key302, 2), (key305, -2), (key316, -4), (key328, 2), (key335, 2), (key340, -2), (key397, 2), (key406, 2), (key418, -2), (key469, -2), (key475, 2), (key568, 2), (key572, -2), (key578, -2), (key583, 2), (key595, 2), (key601, -2)]

def row36 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -1), (key335, -1), (key340, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row37 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key316, 2), (key328, -1), (key335, -1), (key340, 1), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row38 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 2), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row39 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, -1), (key305, 1), (key328, -1), (key335, -1), (key340, 1), (key385, 2), (key397, -1), (key406, -1), (key418, 1), (key469, 1), (key475, -1), (key568, -1), (key572, 1), (key578, 1), (key583, -1), (key595, -1), (key601, 1)]

def row40 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row41 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, -1), (key397, 1), (key406, 1), (key418, -1), (key469, -1), (key475, 1), (key568, 1), (key572, -1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row42 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1774, 2), (key1780, -2), (key1790, -2), (key1798, 2), (key1817, 2), (key1825, -2)]

def row43 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row44 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row45 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1774, -2), (key1780, 2), (key1790, 2), (key1798, -2), (key1817, -2), (key1825, 2)]

def row46 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row47 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row48 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row49 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row50 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row51 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row52 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1774, -2), (key1780, 2), (key1790, 2), (key1798, -2), (key1817, -2), (key1825, 2)]

def row53 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row54 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row55 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1774, 2), (key1780, -2), (key1790, -2), (key1798, 2), (key1817, 2), (key1825, -2)]

def row56 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row57 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row58 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row59 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row60 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row61 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row62 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1774, 2), (key1780, -2), (key1790, -2), (key1798, 2), (key1817, 2), (key1825, -2)]

def row63 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row64 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row65 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1774, -2), (key1780, 2), (key1790, 2), (key1798, -2), (key1817, -2), (key1825, 2)]

def row66 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row67 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row68 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row69 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row70 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row71 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row72 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row73 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row74 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row75 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row76 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row77 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row78 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row79 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row80 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row81 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, -1), (key1573, -1), (key1596, 1), (key1659, 1), (key1667, -1), (key1774, -1), (key1780, 1), (key1790, 1), (key1798, -1), (key1817, -1), (key1825, 1)]

def row82 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row83 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, 1), (key1573, 1), (key1596, -1), (key1659, -1), (key1667, 1), (key1774, 1), (key1780, -1), (key1790, -1), (key1798, 1), (key1817, 1), (key1825, -1)]

def row84 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, 2), (key2940, 2), (key2945, -2), (key2952, -2), (key2962, 2), (key2978, 2), (key2985, -2)]

def row85 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row86 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row87 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2787, 2), (key2797, -2), (key2810, -2), (key2833, 2), (key2899, 2), (key2906, -2), (key2940, -2), (key2945, 2), (key2952, 2), (key2962, -2), (key2978, -2), (key2985, 2)]

def row88 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row89 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row90 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row91 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row92 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row93 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row94 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, -2), (key2672, -2), (key2675, 2), (key2707, 4), (key2730, -4), (key2739, -4), (key2749, 4), (key2810, -2), (key2833, 2), (key2899, 2), (key2906, -2), (key2952, 2), (key2962, -2), (key2978, -2), (key2985, 2)]

def row95 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row96 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row97 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2672, 2), (key2675, -2), (key2707, -4), (key2730, 4), (key2739, 4), (key2749, -4), (key2810, 2), (key2833, -4), (key2899, -2), (key2906, 2), (key2962, 2), (key2978, 2), (key2985, -2)]

def row98 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row99 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row100 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2899, 1), (key2906, -1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

def row101 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, 2), (key2810, -1), (key2899, 1), (key2906, -1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

def row102 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row103 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, -2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row104 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -4), (key2655, 2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 4), (key2749, -2), (key2787, -2), (key2797, 4), (key2810, 2), (key2833, -4), (key2899, -2), (key2906, 2), (key2945, -2), (key2962, 2), (key2978, 2), (key2985, -2)]

def row105 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row106 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row107 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -4), (key2749, 4), (key2787, 2), (key2797, -4), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, -2), (key2962, -2), (key2978, -2), (key2985, 2)]

def row108 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2749, -2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row109 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2749, -2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row110 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

def row111 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 2), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

def row112 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row113 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -2), (key2749, 1), (key2787, 1), (key2797, -2), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2945, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row114 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2650, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2739, -2), (key2749, 1), (key2787, 1), (key2810, -1), (key2899, 1), (key2906, -1), (key2940, -2), (key2945, 1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

def row115 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2650, 2), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2739, -2), (key2749, 1), (key2787, 1), (key2810, -1), (key2899, 1), (key2906, -1), (key2940, -2), (key2945, 1), (key2952, 2), (key2962, -1), (key2978, -1), (key2985, 1)]

def row116 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2940, 1), (key2945, -2), (key2952, -1), (key2962, 1), (key2978, 2), (key2985, -1)]

def row117 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2787, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2940, 1), (key2945, -2), (key2952, -1), (key2962, 1), (key2978, 2), (key2985, -1)]

def row118 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2739, 1), (key2749, -1), (key2797, 1), (key2810, 1), (key2899, -1), (key2906, 1), (key2940, 2), (key2945, -1), (key2952, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

def row119 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -2), (key2739, 1), (key2749, -1), (key2797, 1), (key2810, 1), (key2899, -1), (key2906, 1), (key2940, 2), (key2945, -1), (key2952, -2), (key2962, 1), (key2978, 1), (key2985, -1)]

def row120 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -1), (key2739, -1), (key2749, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2985, 1)]

def row121 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 2), (key2730, -1), (key2739, -1), (key2749, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2940, -1), (key2945, 1), (key2952, 1), (key2962, -1), (key2985, 1)]

def row122 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 2), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row123 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 2), (key2952, 1), (key2962, -1), (key2978, -1), (key2985, 1)]

def row124 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row125 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2952, -1), (key2962, 1), (key2978, 1), (key2985, -1)]

def row126 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row127 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row128 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1387, -2), (key1393, 2), (key1420, 2), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, 2), (key1556, -2), (key1569, -2), (key1593, 2), (key1683, 2), (key1689, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row129 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row130 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row131 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row132 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row133 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, 2), (key1393, -2), (key1420, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, -2), (key1556, 2), (key1569, 2), (key1593, -2), (key1683, -2), (key1689, 2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row134 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row135 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row136 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row137 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row138 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, 2), (key1393, -2), (key1420, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, -2), (key1556, 2), (key1569, 2), (key1593, -2), (key1683, -2), (key1689, 2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row139 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row140 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row141 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row142 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row143 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1387, -2), (key1393, 2), (key1420, 2), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, 2), (key1556, -2), (key1569, -2), (key1593, 2), (key1683, 2), (key1689, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row144 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row145 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row146 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row147 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row148 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row149 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row150 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row151 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row152 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row153 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row154 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row155 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row156 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row157 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row158 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1387, -2), (key1393, 2), (key1420, 2), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, 2), (key1556, -2), (key1569, -2), (key1593, 2), (key1683, 2), (key1689, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row159 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row416 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 2), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row417 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 2), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row418 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row419 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row420 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row421 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row422 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row423 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row424 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row425 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row426 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row427 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row428 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row429 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row430 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row431 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row432 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row433 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row434 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row435 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row436 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row437 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row438 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row439 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row440 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row441 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row442 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row443 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row444 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row445 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row446 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row447 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row448 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row449 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row450 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row451 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row452 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row453 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row454 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row455 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row456 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row457 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row458 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row459 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row460 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row461 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row462 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row463 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row464 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row465 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row466 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row467 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row468 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row469 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row470 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row471 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row472 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row473 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row474 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row475 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row476 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row477 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row478 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row479 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row480 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row481 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row482 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row483 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row484 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row485 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row486 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row487 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row488 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row489 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row490 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row491 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row492 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row493 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row494 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row495 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row496 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row497 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row498 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row499 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row500 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row501 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row502 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row503 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row504 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row505 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row506 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row507 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row508 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row509 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row510 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row511 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row512 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row513 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row514 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row515 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row516 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row517 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row518 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row519 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row520 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row521 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row522 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row523 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row524 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row525 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row526 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row527 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row528 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row529 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row530 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row531 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row532 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row533 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row534 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row535 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row536 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row537 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row538 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row539 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row540 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row541 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row542 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row543 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row544 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row545 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row546 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row547 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row548 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

def row549 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row550 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row551 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row552 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row553 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

def row554 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row555 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row556 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row557 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row558 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

def row559 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row560 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row561 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row562 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row563 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

def row564 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row565 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row566 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row567 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row568 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row569 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row570 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row571 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row572 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row573 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row574 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row575 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row576 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row577 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row578 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

def row579 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row580 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row581 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

def row582 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row583 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row584 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row585 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row586 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row587 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row588 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row589 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row590 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, 2), (key2790, -2), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2935, -2), (key2941, 2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row591 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row592 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row593 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row594 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row595 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, -2), (key2790, 2), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2935, 2), (key2941, -2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

def row596 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row597 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row598 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row599 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row600 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -4), (key2722, 4), (key2734, 4), (key2745, -4), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

def row601 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row602 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row603 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row604 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row605 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 4), (key2722, -4), (key2734, -4), (key2745, 4), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row606 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row607 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row608 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row609 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row610 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, 1), (key2722, -2), (key2745, 1), (key2778, 2), (key2781, -1), (key2790, -2), (key2801, -1), (key2825, 2), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2941, 1), (key2958, -1), (key2971, -1), (key2981, 1)]

def row611 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, 1), (key2722, -2), (key2745, 1), (key2778, 2), (key2781, -1), (key2790, -2), (key2801, -1), (key2825, 2), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2941, 1), (key2958, -1), (key2971, -1), (key2981, 1)]

def row612 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -2), (key2734, 1), (key2745, 2), (key2778, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row613 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -2), (key2734, 1), (key2745, 2), (key2778, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row614 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, 2), (key2734, -1), (key2745, -2), (key2778, -1), (key2781, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row615 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, 2), (key2734, -1), (key2745, -2), (key2778, -1), (key2781, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row616 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2701, -1), (key2722, 3), (key2745, -1), (key2778, -2), (key2781, 1), (key2790, 2), (key2801, 1), (key2825, -2), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2958, 1), (key2971, 1), (key2974, 1), (key2981, -1)]

def row617 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2701, -1), (key2722, 3), (key2745, -1), (key2778, -2), (key2781, 1), (key2790, 2), (key2801, 1), (key2825, -2), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2958, 1), (key2971, 1), (key2974, 1), (key2981, -1)]

def row618 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 2), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -1), (key2722, -2), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, 1), (key2902, -1), (key2941, 1), (key2947, -1), (key2958, -1), (key2971, 1), (key2974, -1), (key2981, 1)]

def row619 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 2), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -1), (key2722, -2), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, 1), (key2902, -1), (key2941, 1), (key2947, -1), (key2958, -1), (key2971, 1), (key2974, -1), (key2981, 1)]

def row620 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, 2), (key2790, -2), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2935, -2), (key2941, 2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row621 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row622 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row623 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2790, 2), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2935, 2), (key2941, -2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

def row624 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row625 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row626 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 2), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row627 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 2), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row628 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row629 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row630 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

def row631 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

def row632 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

def row633 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row634 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row635 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2899, -1), (key2915, -1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row636 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2899, -1), (key2915, -1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row637 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row638 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row639 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row640 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

def row641 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

def row642 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row643 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row644 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2751, 1), (key2797, -1), (key2915, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row645 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2751, 1), (key2797, -1), (key2915, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row646 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row647 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row648 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row649 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row650 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row651 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row652 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row653 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row654 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row655 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row656 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row657 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row658 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row659 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row160 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row161 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, 2), (key1393, -2), (key1420, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, -2), (key1556, 2), (key1569, 2), (key1593, -2), (key1683, -2), (key1689, 2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row162 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row163 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row164 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row165 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row166 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row167 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row168 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

def row169 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

def row170 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2667, -2), (key2673, 2), (key2702, 2), (key2728, -2), (key2737, -2), (key2747, 2), (key2782, 2), (key2795, -2), (key2805, -2), (key2831, 2), (key2897, 2), (key2904, -2), (key2938, -2), (key2943, 2), (key2950, 2), (key2960, -2), (key2976, -2), (key2983, 2)]

def row171 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

def row172 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

def row173 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

def row174 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

def row175 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2667, 2), (key2673, -2), (key2702, -2), (key2728, 2), (key2737, 2), (key2747, -2), (key2782, -2), (key2795, 2), (key2805, 2), (key2831, -2), (key2897, -2), (key2904, 2), (key2938, 2), (key2943, -2), (key2950, -2), (key2960, 2), (key2976, 2), (key2983, -2)]

def row176 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

def row177 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

def row178 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

def row179 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

def row180 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2628, 2), (key2641, -2), (key2648, -2), (key2653, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, -2), (key2728, 2), (key2732, 2), (key2737, 2), (key2747, -2), (key2753, 2), (key2758, -2), (key2805, 2), (key2831, -2), (key2897, -2), (key2904, 2), (key2950, -2), (key2960, 2), (key2976, 2), (key2983, -2)]

def row181 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2897, -1), (key2904, 1), (key2948, 1), (key2960, 1), (key2976, 1), (key2983, -1)]

def row182 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2897, -1), (key2904, 1), (key2948, 1), (key2960, 1), (key2976, 1), (key2983, -1)]

def row183 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2809, -1), (key2831, 1), (key2835, 2), (key2897, 1), (key2904, -1), (key2950, -1), (key2960, 1), (key2976, -1), (key2983, 1), (key3017, -2)]

def row184 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2809, -1), (key2831, 1), (key2835, 2), (key2897, 1), (key2904, -1), (key2950, -1), (key2960, 1), (key2976, -1), (key2983, 1), (key3017, -2)]

def row185 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2671, -2), (key2676, 2), (key2702, 2), (key2706, 2), (key2728, -2), (key2732, -2), (key2737, -2), (key2747, 2), (key2753, -2), (key2758, 2), (key2809, -2), (key2835, 2), (key2897, 2), (key2904, -2), (key2976, -2), (key2983, 2), (key3012, 2), (key3017, -2)]

def row186 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2809, 1), (key2835, -1), (key2897, -1), (key2904, 1), (key2976, 1), (key2983, -1), (key3012, -1), (key3017, 1)]

def row187 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2809, 1), (key2835, -1), (key2897, -1), (key2904, 1), (key2976, 1), (key2983, -1), (key3012, -1), (key3017, 1)]

def row188 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2644, -1), (key2646, 1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, 1), (key2706, -2), (key2726, 1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2782, 1), (key2786, -2), (key2794, 1), (key2795, 1), (key2798, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2920, -1), (key2923, 1), (key2936, -1), (key2943, -1), (key2948, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row189 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2644, -1), (key2646, 1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, 1), (key2706, -2), (key2726, 1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2782, 1), (key2786, -2), (key2794, 1), (key2795, 1), (key2798, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2920, -1), (key2923, 1), (key2936, -1), (key2943, -1), (key2948, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row190 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 2), (key2648, -1), (key2653, 1), (key2660, -2), (key2667, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 1), (key2794, 1), (key2795, -1), (key2798, -2), (key2809, -1), (key2831, 1), (key2835, 1), (key2897, -1), (key2904, 1), (key2920, 2), (key2923, -1), (key2927, -1), (key2943, 1), (key2960, -1), (key2998, 1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row191 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 2), (key2648, -1), (key2653, 1), (key2660, -2), (key2667, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 1), (key2794, 1), (key2795, -1), (key2798, -2), (key2809, -1), (key2831, 1), (key2835, 1), (key2897, -1), (key2904, 1), (key2920, 2), (key2923, -1), (key2927, -1), (key2943, 1), (key2960, -1), (key2998, 1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row192 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2671, -2), (key2673, 1), (key2702, -1), (key2706, 2), (key2728, -1), (key2732, -1), (key2735, 1), (key2747, 1), (key2758, 1), (key2782, -1), (key2786, 2), (key2794, -1), (key2795, -1), (key2798, -1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2920, 1), (key2923, -1), (key2948, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row193 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2671, -2), (key2673, 1), (key2702, -1), (key2706, 2), (key2728, -1), (key2732, -1), (key2735, 1), (key2747, 1), (key2758, 1), (key2782, -1), (key2786, 2), (key2794, -1), (key2795, -1), (key2798, -1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2920, 1), (key2923, -1), (key2948, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row194 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -1), (key2653, 1), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 2), (key2747, -1), (key2758, -2), (key2786, -1), (key2795, 1), (key2798, 1), (key2809, 1), (key2831, -1), (key2835, -2), (key2920, -1), (key2923, 2), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1), (key2998, 1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

def row195 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -1), (key2653, 1), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 2), (key2747, -1), (key2758, -2), (key2786, -1), (key2795, 1), (key2798, 1), (key2809, 1), (key2831, -1), (key2835, -2), (key2920, -1), (key2923, 2), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1), (key2998, 1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

def row196 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, -1), (key2747, 1), (key2758, -1), (key2786, -1), (key2795, 1), (key2798, 2), (key2809, 1), (key2831, -1), (key2835, -1), (key2897, 1), (key2904, -1), (key2920, -2), (key2923, 1), (key3010, -2), (key3017, 1), (key3023, 2), (key3026, -1)]

def row197 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, 1), (key2673, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, -1), (key2747, 1), (key2758, -1), (key2786, -1), (key2795, 1), (key2798, 2), (key2809, 1), (key2831, -1), (key2835, -1), (key2897, 1), (key2904, -1), (key2920, -2), (key2923, 1), (key3010, -2), (key3017, 1), (key3023, 2), (key3026, -1)]

def row198 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2671, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -2), (key2758, 2), (key2786, 1), (key2795, -1), (key2798, -1), (key2809, -1), (key2831, 1), (key2835, 2), (key2920, 1), (key2923, -2), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1), (key3010, 1), (key3017, -2), (key3023, -1), (key3026, 2)]

def row199 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2671, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -2), (key2758, 2), (key2786, 1), (key2795, -1), (key2798, -1), (key2809, -1), (key2831, 1), (key2835, 2), (key2920, 1), (key2923, -2), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1), (key3010, 1), (key3017, -2), (key3023, -1), (key3026, 2)]

def row200 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2632, -2), (key2644, 2), (key2658, 2), (key2660, -2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2835, 2), (key2920, 2), (key2923, -2), (key3008, -2), (key3010, 2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, 2)]

def row201 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

def row202 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

def row203 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, 2), (key2676, -2), (key2706, -2), (key2732, 2), (key2753, 2), (key2758, -2), (key2786, -2), (key2798, 2), (key2809, 2), (key2835, -2), (key2920, -2), (key2923, 2), (key3008, 2), (key3010, -2), (key3012, -2), (key3017, 2), (key3023, 2), (key3026, -2)]

def row204 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row205 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row206 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row207 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, -1), (key2676, 1), (key2706, 1), (key2732, -1), (key2753, -1), (key2758, 1), (key2786, 1), (key2798, -1), (key2809, -1), (key2835, 1), (key2920, 1), (key2923, -1), (key3008, -1), (key3010, 1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row208 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

def row209 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2632, 1), (key2644, -1), (key2658, -1), (key2660, 1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2786, -1), (key2798, 1), (key2809, 1), (key2835, -1), (key2920, -1), (key2923, 1), (key3008, 1), (key3010, -1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, -1)]

def row210 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row211 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row212 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, -2), (key2669, 2), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, 2), (key2792, -2), (key2801, -2), (key2827, 2), (key2919, 2), (key2922, -2), (key3007, -2), (key3009, 2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row213 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row214 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row215 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row216 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row217 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2792, 2), (key2801, 2), (key2827, -2), (key2919, -2), (key2922, 2), (key3007, 2), (key3009, -2), (key3011, -2), (key3016, 2), (key3022, 2), (key3025, -2)]

def row218 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row219 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row220 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row221 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row222 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 4), (key2752, 4), (key2757, -4), (key2801, 2), (key2827, -2), (key2919, -2), (key2922, 2), (key3011, -2), (key3016, 2), (key3022, 2), (key3025, -2)]

def row223 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1764 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

def row1765 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

def row1766 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

def row1767 : Integer.Sparse Key := [(key2402, 6), (key2408, -6), (key2468, -6), (key2481, 6), (key2537, 6), (key2542, -6)]

def row1768 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

def row1769 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

def row1770 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

def row1771 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

def row1772 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

def row1773 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

def row1774 : Integer.Sparse Key := [(key2770, -6), (key2775, 6), (key2847, 6), (key2884, -6), (key2917, -6), (key2926, 6)]

def row1775 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

def row1776 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

def row1777 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

def row1778 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1779 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1780 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1781 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, -6), (key1677, 6), (key1892, 6), (key1914, -6)]

def row1782 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1783 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1784 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1785 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1786 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1787 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1788 : Integer.Sparse Key := [(key1250, -6), (key1269, 6), (key1525, 6), (key1677, -6), (key1892, -6), (key1914, 6)]

def row1789 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1790 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1791 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1792 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

def row1793 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

def row1794 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

def row1795 : Integer.Sparse Key := [(key2376, 6), (key2388, -6), (key2404, -6), (key2435, 6), (key2478, 6), (key2501, -6)]

def row1796 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

def row1797 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

def row1798 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

def row1799 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

def row1800 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

def row1801 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

def row1802 : Integer.Sparse Key := [(key2589, -6), (key2604, 6), (key2768, 6), (key2916, -6), (key3005, -6), (key3019, 6)]

def row1803 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

def row1804 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

def row1805 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

def row1806 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1807 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1808 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1809 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1164, 6), (key1228, 6), (key1245, -6)]

def row1810 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1811 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1812 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1813 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1814 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1815 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1816 : Integer.Sparse Key := [(key971, -6), (key979, 6), (key1085, 6), (key1164, -6), (key1228, -6), (key1245, 6)]

def row1817 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1818 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1819 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1820 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1821 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1822 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1823 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, -6), (key2432, 6), (key2475, 6), (key2498, -6)]

def row1824 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1825 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1826 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1827 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1828 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1829 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1830 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, 6), (key2432, -6), (key2475, -6), (key2498, 6)]

def row1831 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1832 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1833 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1834 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1835 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1836 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1837 : Integer.Sparse Key := [(key1526, 6), (key1534, -6), (key1604, -6), (key1640, 6), (key1679, 6), (key1693, -6)]

def row1838 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1839 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1840 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1841 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1842 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1843 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1844 : Integer.Sparse Key := [(key1526, -6), (key1534, 6), (key1604, 6), (key1640, -6), (key1679, -6), (key1693, 6)]

def row1845 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1846 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1847 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1848 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

def row1849 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

def row1850 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

def row1851 : Integer.Sparse Key := [(key2414, 6), (key2419, -6), (key2487, -6), (key2494, 6), (key2572, 6), (key2573, -6)]

def row1852 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

def row1853 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

def row1854 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

def row1855 : Integer.Sparse Key := [(key2414, -6), (key2419, 6), (key2426, -4), (key2494, -2), (key3033, 4), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

def row1856 : Integer.Sparse Key := [(key2419, 6), (key2426, -4), (key2494, -2), (key3033, -2), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

def row1857 : Integer.Sparse Key := [(key2419, 6), (key2426, -4), (key2494, -2), (key3033, -2), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

def row1858 : Integer.Sparse Key := [(key2414, -6), (key2487, 6), (key3038, 6), (key3130, -6), (key3141, -6), (key3144, 6)]

def row1859 : Integer.Sparse Key := [(key2414, 6), (key3033, -4), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

def row1860 : Integer.Sparse Key := [(key3033, 2), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

def row1861 : Integer.Sparse Key := [(key3033, 2), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

def row1862 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1863 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1864 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1865 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, -6), (key1679, 6), (key1894, 6), (key1916, -6)]

def row1866 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1867 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1868 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1869 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1870 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1871 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1872 : Integer.Sparse Key := [(key1259, -6), (key1271, 6), (key1534, 6), (key1679, -6), (key1894, -6), (key1916, 6)]

def row1873 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1874 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1875 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1876 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1877 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1878 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1879 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1163, 6), (key1227, 6), (key1244, -6)]

def row1880 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1881 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1882 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1883 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1884 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1885 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1886 : Integer.Sparse Key := [(key972, -6), (key978, 6), (key1086, 6), (key1163, -6), (key1227, -6), (key1244, 6)]

def row1887 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1888 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1889 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1890 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

def row1891 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

def row1892 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

def row1893 : Integer.Sparse Key := [(key2374, 6), (key2380, -6), (key2468, -6), (key2505, 6), (key2537, 6), (key2553, -6)]

def row1894 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

def row1895 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

def row1896 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

def row1897 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

def row1898 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

def row1899 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

def row1900 : Integer.Sparse Key := [(key2591, -6), (key2596, 6), (key2847, 6), (key2884, -6), (key3020, -6), (key3029, 6)]

def row1901 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

def row1902 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

def row1903 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

def row1904 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

def row1905 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

def row1906 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

def row1907 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2515, 6), (key2566, 6), (key2578, -6)]

def row1908 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

def row1909 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

def row1910 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

def row1911 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

def row1912 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

def row1913 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

def row1914 : Integer.Sparse Key := [(key2353, -6), (key2359, 6), (key2448, 6), (key2515, -6), (key2566, -6), (key2578, 6)]

def row1915 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

def row1916 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

def row1917 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

def row1918 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1919 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1920 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1921 : Integer.Sparse Key := [(key2770, 6), (key2773, -6), (key2847, -6), (key2881, 6), (key2890, 6), (key2911, -6)]

def row1922 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1923 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1924 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1925 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1926 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1927 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1928 : Integer.Sparse Key := [(key2770, -6), (key2773, 6), (key2847, 6), (key2881, -6), (key2890, -6), (key2911, 6)]

def row1929 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1930 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1931 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1932 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1933 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1934 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1935 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, -6), (key1645, 6), (key1762, 6), (key1803, -6)]

def row1936 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1937 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1938 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1939 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1940 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1941 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1942 : Integer.Sparse Key := [(key1249, -6), (key1262, 6), (key1524, 6), (key1645, -6), (key1762, -6), (key1803, 6)]

def row1943 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1944 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1945 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1946 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1947 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1948 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1949 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, -6), (key2888, 6), (key2930, 6), (key2967, -6)]

def row1950 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1951 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1952 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1953 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1954 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1955 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1956 : Integer.Sparse Key := [(key2588, -6), (key2599, 6), (key2767, 6), (key2888, -6), (key2930, -6), (key2967, 6)]

def row1957 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1958 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1959 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1960 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1961 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1962 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1963 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1162, 6), (key1181, 6), (key1218, -6)]

def row1964 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1965 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1966 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1967 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1968 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1969 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1970 : Integer.Sparse Key := [(key972, -6), (key977, 6), (key1086, 6), (key1162, -6), (key1181, -6), (key1218, 6)]

def row1971 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1972 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1973 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1974 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1975 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1976 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1977 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, -6), (key2431, 6), (key2474, 6), (key2497, -6)]

def row1978 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1979 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1980 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1981 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1982 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1983 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1984 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, 6), (key2431, -6), (key2474, -6), (key2497, 6)]

def row1985 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1986 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1987 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1988 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1989 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1990 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1991 : Integer.Sparse Key := [(key1527, 6), (key1532, -6), (key1605, -6), (key1638, 6), (key1649, 6), (key1672, -6)]

def row1992 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row1993 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row1994 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row1995 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1996 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1997 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1998 : Integer.Sparse Key := [(key1527, -6), (key1532, 6), (key1605, 6), (key1638, -6), (key1649, -6), (key1672, 6)]

def row1999 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row2000 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row2001 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row2002 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2003 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2004 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2005 : Integer.Sparse Key := [(key3034, 6), (key3037, -6), (key3121, -6), (key3129, 6), (key3133, 6), (key3139, -6)]

def row2006 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2007 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2008 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2009 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2010 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2011 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2012 : Integer.Sparse Key := [(key3034, -6), (key3037, 6), (key3121, 6), (key3129, -6), (key3133, -6), (key3139, 6)]

def row2013 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2014 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2015 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2016 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2017 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2018 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2019 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, -6), (key1649, 6), (key1766, 6), (key1807, -6)]

def row2020 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2021 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2022 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2023 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2024 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2025 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2026 : Integer.Sparse Key := [(key1257, -6), (key1266, 6), (key1532, 6), (key1649, -6), (key1766, -6), (key1807, 6)]

def row2027 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2028 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2029 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2030 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2031 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2032 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2033 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1161, 6), (key1179, 6), (key1217, -6)]

def row2034 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2035 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2036 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2037 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2038 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2039 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2040 : Integer.Sparse Key := [(key971, -6), (key975, 6), (key1085, 6), (key1161, -6), (key1179, -6), (key1217, 6)]

def row2041 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2042 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2043 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2044 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2045 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2046 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2047 : Integer.Sparse Key := [(key2591, 6), (key2594, -6), (key2847, -6), (key2881, 6), (key2969, 6), (key2990, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row224 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row225 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row226 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row227 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, -2), (key2669, 2), (key2698, 4), (key2724, -4), (key2752, -4), (key2757, 4), (key2801, -2), (key2827, 2), (key2919, 2), (key2922, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row228 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row229 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row230 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row231 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row232 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, 1), (key2724, -2), (key2757, 1), (key2778, 2), (key2784, -1), (key2792, -2), (key2801, -1), (key2827, 2), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key3009, 1), (key3016, -1), (key3021, -1), (key3025, 1)]

def row233 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, 1), (key2724, -2), (key2757, 1), (key2778, 2), (key2784, -1), (key2792, -2), (key2801, -1), (key2827, 2), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key3009, 1), (key3016, -1), (key3021, -1), (key3025, 1)]

def row234 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2752, 1), (key2757, 2), (key2778, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row235 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2752, 1), (key2757, 2), (key2778, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row236 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, 2), (key2752, -1), (key2757, -2), (key2778, -1), (key2784, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row237 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, 2), (key2752, -1), (key2757, -2), (key2778, -1), (key2784, -1), (key2792, 3), (key2801, 1), (key2827, -3), (key2858, -1), (key2868, 1), (key2918, 1), (key2919, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row238 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2704, -1), (key2724, 3), (key2757, -1), (key2778, -2), (key2784, 1), (key2792, 2), (key2801, 1), (key2827, -2), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row239 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2704, -1), (key2724, 3), (key2757, -1), (key2778, -2), (key2784, 1), (key2792, 2), (key2801, 1), (key2827, -2), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, -1), (key2922, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row240 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -1), (key2724, -2), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, 1), (key2922, -1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, 1), (key3022, -1), (key3025, 1)]

def row241 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -1), (key2724, -2), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2792, -3), (key2801, -1), (key2827, 3), (key2858, 1), (key2868, -1), (key2918, -1), (key2919, 1), (key2922, -1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, 1), (key3022, -1), (key3025, 1)]

def row242 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, -2), (key2669, 2), (key2698, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, 2), (key2792, -2), (key2801, -2), (key2827, 2), (key2919, 2), (key2922, -2), (key3007, -2), (key3009, 2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row243 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row244 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row245 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2792, 2), (key2801, 2), (key2827, -2), (key2919, -2), (key2922, 2), (key3007, 2), (key3009, -2), (key3011, -2), (key3016, 2), (key3022, 2), (key3025, -2)]

def row246 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row247 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row248 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 2), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row249 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 2), (key2792, -1), (key2801, -1), (key2827, 1), (key2919, 1), (key2922, -1), (key3007, -1), (key3009, 1), (key3011, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row250 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row251 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2792, 1), (key2801, 1), (key2827, -1), (key2919, -1), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row252 : Integer.Sparse Key := [(key242, -2), (key244, 2), (key254, 2), (key265, -2), (key269, -2), (key274, 2), (key308, 2), (key310, -2), (key322, -2), (key333, 2), (key337, 2), (key343, -2), (key391, -2), (key402, 2), (key412, 2), (key423, -2), (key472, -2), (key478, 2), (key570, 2), (key575, -2), (key580, -2), (key586, 2), (key598, 2), (key604, -2)]

def row253 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row254 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row255 : Integer.Sparse Key := [(key242, 2), (key244, -2), (key254, -2), (key265, 2), (key269, 2), (key274, -2), (key308, -2), (key310, 2), (key322, 2), (key333, -2), (key337, -2), (key343, 2), (key391, 2), (key402, -2), (key412, -2), (key423, 2), (key472, 2), (key478, -2), (key570, -2), (key575, 2), (key580, 2), (key586, -2), (key598, -2), (key604, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2048 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2049 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2050 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2051 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2052 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2053 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2054 : Integer.Sparse Key := [(key2591, -6), (key2594, 6), (key2847, 6), (key2881, -6), (key2969, -6), (key2990, 6)]

def row2055 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2056 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2057 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2058 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2059 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2060 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2061 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2514, 6), (key2529, 6), (key2559, -6)]

def row2062 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2063 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2064 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2065 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2066 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2067 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2068 : Integer.Sparse Key := [(key2354, -6), (key2358, 6), (key2449, 6), (key2514, -6), (key2529, -6), (key2559, 6)]

def row2069 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2070 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2071 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2072 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

def row2073 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

def row2074 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

def row2075 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2513, 6), (key2527, 6), (key2558, -6)]

def row2076 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

def row2077 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

def row2078 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

def row2079 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

def row2080 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

def row2081 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

def row2082 : Integer.Sparse Key := [(key2353, -6), (key2356, 6), (key2448, 6), (key2513, -6), (key2527, -6), (key2558, 6)]

def row2083 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

def row2084 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

def row2085 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

def row2086 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row2087 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row2088 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row2089 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2090 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2091 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2092 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2093 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2094 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2095 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row2096 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row2097 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row2098 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2099 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2100 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2101 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2102 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2103 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2104 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2105 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2106 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2107 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2108 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2109 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2110 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2111 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2112 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2113 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2114 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2115 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2116 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

def row2117 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

def row2118 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

def row2119 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2120 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2121 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2122 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2123 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2124 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2125 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

def row2126 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

def row2127 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

def row2128 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2129 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2130 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2131 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2132 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2133 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2134 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2135 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2136 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2137 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2138 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2139 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2140 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2141 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2142 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2143 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2144 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2145 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2146 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

def row2147 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

def row2148 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

def row2149 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2150 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2151 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2152 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2153 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2154 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2155 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

def row2156 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

def row2157 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

def row2158 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2159 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2160 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2161 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2162 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2163 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2164 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2165 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2166 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2167 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2168 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2169 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2170 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2171 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2172 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2173 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2174 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2175 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2176 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

def row2177 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

def row2178 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

def row2179 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2180 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2181 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2182 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2183 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2184 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2185 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

def row2186 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

def row2187 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

def row2188 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2189 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2190 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2191 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2192 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2193 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2194 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2195 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2196 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2197 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2198 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2199 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2200 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2201 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2202 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2203 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2204 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2205 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2206 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

def row2207 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

def row2208 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

def row2209 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2210 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2211 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2212 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2213 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2214 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2215 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

def row2216 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

def row2217 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

def row2218 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2219 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2220 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2221 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2222 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2223 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2224 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2225 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2226 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2227 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2228 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2229 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2230 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2231 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2232 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2233 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2234 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2235 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2236 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

def row2237 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

def row2238 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

def row2239 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2240 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2241 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2242 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2243 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2244 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2245 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

def row2246 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

def row2247 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

def row2248 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2249 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2250 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2251 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2252 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2253 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2254 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2255 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2256 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2257 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2258 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2259 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2260 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2261 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2262 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2263 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2264 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2265 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2266 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

def row2267 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

def row2268 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

def row2269 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2270 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2271 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2272 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2273 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2274 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2275 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

def row2276 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

def row2277 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

def row2278 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2279 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2280 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2281 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2282 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2283 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2284 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2285 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2286 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2287 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2288 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2289 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2290 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2291 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2292 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2293 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2294 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2295 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2296 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

def row2297 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

def row2298 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

def row2299 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2300 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2301 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2302 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2303 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2304 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2305 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

def row2306 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

def row2307 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

def row2308 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2309 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2310 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2311 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2312 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2313 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2314 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2315 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2316 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2317 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2318 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2319 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2320 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2321 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2322 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2323 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2324 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2325 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2326 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

def row2327 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

def row2328 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

def row2329 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2330 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2331 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2332 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2333 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2334 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2335 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

def row2336 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

def row2337 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

def row2338 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2339 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2340 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2341 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2342 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2343 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2344 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2345 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2346 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2347 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2348 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2349 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2350 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2351 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2352 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2353 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2354 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2355 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2356 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

def row2357 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

def row2358 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

def row2359 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2360 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2361 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2362 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2363 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2364 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2365 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

def row2366 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

def row2367 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

def row2368 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2369 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2370 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2371 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2372 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2373 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2374 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2375 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2376 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2377 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2378 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2379 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2380 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2381 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2382 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2383 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2384 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2385 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2386 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

def row2387 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

def row2388 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

def row2389 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2390 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2391 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2392 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2393 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2394 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2395 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

def row2396 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

def row2397 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

def row2398 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2399 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2400 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2401 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2402 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2403 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2404 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2405 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2406 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2407 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2408 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2409 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2410 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2411 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2412 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2413 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2414 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2415 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2416 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

def row2417 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

def row2418 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

def row2419 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2420 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2421 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2422 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2423 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2424 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2425 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

def row2426 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

def row2427 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

def row2428 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2429 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2430 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2431 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2432 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2433 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2434 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2435 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2436 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2437 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2438 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2439 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2440 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2441 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2442 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2443 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2444 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2445 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2446 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

def row2447 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

def row2448 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

def row2449 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2450 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2451 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2452 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2453 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2454 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2455 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

def row2456 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

def row2457 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

def row2458 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2459 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2460 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2856, -1), (key2866, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2461 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2856, -1), (key2866, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2462 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2463 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2464 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2465 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2466 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2467 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2468 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2469 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2470 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2471 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2472 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2892, 1), (key2902, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2473 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2892, 1), (key2902, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2474 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2475 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2476 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2477 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2478 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2479 : Integer.Sparse Key := [(key2175, 6), (key2179, -6), (key2275, -6), (key2281, 6), (key2328, 6), (key2330, -6)]

def row2480 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2481 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2482 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2483 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2484 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2485 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2486 : Integer.Sparse Key := [(key2175, -6), (key2179, 6), (key2275, 6), (key2281, -6), (key2328, -6), (key2330, 6)]

def row2487 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2488 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2489 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2490 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2491 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2492 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2493 : Integer.Sparse Key := [(key754, 6), (key755, -6), (key843, -6), (key844, 6), (key944, 6), (key945, -6)]

def row2494 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2495 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2496 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2497 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2498 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2499 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2500 : Integer.Sparse Key := [(key754, -6), (key755, 6), (key843, 6), (key844, -6), (key944, -6), (key945, 6)]

def row2501 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2502 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2503 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2504 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2505 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2506 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2507 : Integer.Sparse Key := [(key2079, 6), (key2085, -6), (key2176, -6), (key2187, 6), (key2279, 6), (key2287, -6)]

def row2508 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2509 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2510 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2511 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2512 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2513 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2514 : Integer.Sparse Key := [(key2079, -6), (key2085, 6), (key2176, 6), (key2187, -6), (key2279, -6), (key2287, 6)]

def row2515 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2516 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2517 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2518 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2519 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2520 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2521 : Integer.Sparse Key := [(key713, 6), (key715, -6), (key890, -6), (key914, 6), (key959, 6), (key966, -6)]

def row2522 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2523 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2524 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2525 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2526 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2527 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2528 : Integer.Sparse Key := [(key713, -6), (key715, 6), (key890, 6), (key914, -6), (key959, -6), (key966, 6)]

def row2529 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2530 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2531 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2532 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2533 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2534 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2535 : Integer.Sparse Key := [(key2098, 6), (key2099, -6), (key2203, -6), (key2206, 6), (key2318, 6), (key2321, -6)]

def row2536 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2537 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2538 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2539 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2540 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2541 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2542 : Integer.Sparse Key := [(key2098, -6), (key2099, 6), (key2203, 6), (key2206, -6), (key2318, -6), (key2321, 6)]

def row2543 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2544 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2545 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2546 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2547 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2548 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2549 : Integer.Sparse Key := [(key817, 6), (key818, -6), (key897, -6), (key902, 6), (key960, 6), (key962, -6)]

def row2550 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2551 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2552 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2553 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2554 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2555 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2556 : Integer.Sparse Key := [(key817, -6), (key818, 6), (key897, 6), (key902, -6), (key960, -6), (key962, 6)]

def row2557 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2558 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2559 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2560 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2561 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2562 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2563 : Integer.Sparse Key := [(key2182, 6), (key2183, -6), (key2284, -6), (key2285, 6), (key2345, 6), (key2346, -6)]

def row2564 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2565 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2566 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2567 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2568 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2569 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2570 : Integer.Sparse Key := [(key2182, -6), (key2183, 6), (key2284, 6), (key2285, -6), (key2345, -6), (key2346, 6)]

def row2571 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2572 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2573 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2574 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2575 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2576 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2577 : Integer.Sparse Key := [(key738, 6), (key743, -6), (key818, -6), (key825, 6), (key902, 6), (key908, -6)]

def row2578 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2579 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2580 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2581 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2582 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2583 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2584 : Integer.Sparse Key := [(key738, -6), (key743, 6), (key818, 6), (key825, -6), (key902, -6), (key908, 6)]

def row2585 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2586 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2587 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2588 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2589 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2590 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2591 : Integer.Sparse Key := [(key721, 6), (key722, -6), (key921, -6), (key939, 6), (key959, 6), (key966, -6)]

def row2592 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2593 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2594 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2595 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2596 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2597 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2598 : Integer.Sparse Key := [(key721, -6), (key722, 6), (key921, 6), (key939, -6), (key959, -6), (key966, 6)]

def row2599 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2600 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2601 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2602 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2603 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2604 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2605 : Integer.Sparse Key := [(key2078, 6), (key2082, -6), (key2275, -6), (key2289, 6), (key2328, 6), (key2333, -6)]

def row2606 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2607 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2608 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2609 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2610 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2611 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2612 : Integer.Sparse Key := [(key2078, -6), (key2082, 6), (key2275, 6), (key2289, -6), (key2328, -6), (key2333, 6)]

def row2613 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2614 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2615 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2616 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2617 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2618 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2619 : Integer.Sparse Key := [(key1998, 6), (key2000, -6), (key2267, -6), (key2292, 6), (key2340, 6), (key2349, -6)]

def row2620 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2621 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2622 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2623 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2624 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2625 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2626 : Integer.Sparse Key := [(key1998, -6), (key2000, 6), (key2267, 6), (key2292, -6), (key2340, -6), (key2349, 6)]

def row2627 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2628 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2629 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2630 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2631 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2632 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2633 : Integer.Sparse Key := [(key2006, 6), (key2007, -6), (key2299, -6), (key2313, 6), (key2340, 6), (key2349, -6)]

def row2634 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2635 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2636 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2637 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2638 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2639 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2640 : Integer.Sparse Key := [(key2006, -6), (key2007, 6), (key2299, 6), (key2313, -6), (key2340, -6), (key2349, 6)]

def row2641 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2642 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2643 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2644 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2645 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2646 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2647 : Integer.Sparse Key := [(key2092, 6), (key2095, -6), (key2194, -6), (key2200, 6), (key2305, 6), (key2310, -6)]

def row2648 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2649 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2650 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2651 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2652 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2653 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2654 : Integer.Sparse Key := [(key2092, -6), (key2095, 6), (key2194, 6), (key2200, -6), (key2305, -6), (key2310, 6)]

def row2655 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2656 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2657 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2658 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

def row2659 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

def row2660 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

def row2661 : Integer.Sparse Key := [(key776, 6), (key778, -6), (key801, -6), (key811, 6), (key836, 6), (key839, -6)]

def row2662 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

def row2663 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

def row2664 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

def row2665 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

def row2666 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

def row2667 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

def row2668 : Integer.Sparse Key := [(key776, -6), (key778, 6), (key801, 6), (key811, -6), (key836, -6), (key839, 6)]

def row2669 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

def row2670 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

def row2671 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

def row2672 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

def row2673 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

def row2674 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

def row2675 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

def row2676 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

def row2677 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

def row2678 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

def row2679 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

def row2680 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

def row2681 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -2), (key2407, -1), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2544, -1), (key2555, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 2), (key2848, 1), (key2882, -1), (key2912, 2), (key2970, 1), (key2991, 1), (key2993, -2), (key3003, 2)]

def row2682 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -2), (key2407, -1), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2544, -1), (key2555, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 2), (key2848, 1), (key2882, -1), (key2912, 2), (key2970, 1), (key2991, 1), (key2993, -2), (key3003, 2)]

def row2683 : Integer.Sparse Key := [(key2382, 1), (key2393, -2), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 2), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2684 : Integer.Sparse Key := [(key2382, 1), (key2393, -2), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 2), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2685 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2407, -1), (key2410, 1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 1), (key2848, 1), (key2882, -1), (key2912, 1), (key2933, -1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2686 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2410, 1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 1), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2933, -1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2687 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2688 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

def row2689 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

def row2690 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2934, -1), (key2970, -1), (key2991, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2691 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2934, -1), (key2970, -1), (key2991, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2692 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2693 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2694 : Integer.Sparse Key := [(key2379, 1), (key2407, 1), (key2592, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2933, 1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2695 : Integer.Sparse Key := [(key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2933, 1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2696 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2697 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2698 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2699 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2700 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2701 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2702 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2703 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2704 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2705 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2706 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2707 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2708 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2709 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2710 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2711 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2712 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2713 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2714 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2715 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2716 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2717 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2718 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2719 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2720 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

def row2721 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

def row2722 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

def row2723 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

def row2724 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

def row2725 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

def row2726 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

def row2727 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

def row2728 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

def row2729 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2730 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2731 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2732 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2733 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2734 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2735 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

def row2736 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

def row2737 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

def row2738 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2739 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2740 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2741 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2742 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2743 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2744 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2745 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2746 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2747 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2748 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2749 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2750 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2751 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2752 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2753 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2754 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2755 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2756 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2757 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2758 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2759 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2760 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2761 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2762 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2763 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2764 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2765 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2766 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2767 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2768 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2769 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2770 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2771 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2772 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2773 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2774 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2775 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2776 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2777 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2778 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2779 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2780 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2781 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2782 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2783 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2784 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2785 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2786 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2787 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2788 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2789 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2790 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2791 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2792 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2793 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2794 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2795 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2796 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2797 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2798 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2799 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2800 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2801 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2802 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2803 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2804 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2805 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2806 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2807 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2808 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2809 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2810 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2811 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2812 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2813 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2814 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2815 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2816 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

def row2817 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

def row2818 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

def row2819 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

def row2820 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

def row2821 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

def row2822 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

def row2823 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

def row2824 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

def row2825 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2826 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2827 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2828 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2829 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2830 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2831 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

def row2832 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

def row2833 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

def row2834 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2835 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2836 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2837 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2838 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2839 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2840 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2841 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2842 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2843 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2844 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2845 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2846 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2847 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2848 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2849 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2850 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2851 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2852 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2853 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2854 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2855 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2856 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2857 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2858 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2859 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2860 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2861 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2862 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2863 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2864 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2865 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2866 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2912 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

def row2913 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

def row2914 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

def row2915 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

def row2916 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

def row2917 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

def row2918 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, -4), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

def row2919 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2366, -6), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

def row2920 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2366, -6), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

def row2921 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2922 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2923 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2924 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2925 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2926 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2927 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

def row2928 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

def row2929 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

def row2930 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2931 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2932 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2933 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2934 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2935 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2936 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2937 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2938 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2939 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2940 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2941 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2942 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2943 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2944 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2945 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2946 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2947 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2948 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2949 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2950 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2951 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2952 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2953 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2954 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2955 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2956 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2957 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2958 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2959 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2960 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2961 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2962 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2963 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2964 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2965 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2966 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2967 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2968 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2969 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2970 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2971 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2972 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2973 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2974 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2975 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2976 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2977 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2978 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2979 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2980 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2981 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2982 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2983 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2984 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row2985 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row2986 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row2987 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2988 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2989 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2990 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2991 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2992 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2993 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2994 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2995 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2996 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2997 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2998 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2999 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row3000 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row3001 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row3002 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3003 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3004 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3005 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3006 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3007 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3008 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3009 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3010 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3011 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

def row3012 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

def row3013 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

def row3014 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

def row3015 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

def row3016 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

def row3017 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3018 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3019 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -4), (key2525, -3), (key2532, 2), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3020 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -4), (key2525, -3), (key2532, 2), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3021 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3022 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3023 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3024 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3025 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3026 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3027 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3028 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 2), (key2525, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3029 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 2), (key2525, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3030 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3031 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row256 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row257 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row258 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row259 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row260 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row261 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row262 : Integer.Sparse Key := [(key242, 2), (key244, -2), (key254, -2), (key265, 2), (key269, 2), (key274, -2), (key308, -2), (key310, 2), (key322, 2), (key333, -2), (key337, -2), (key343, 2), (key391, 2), (key402, -2), (key412, -2), (key423, 2), (key472, 2), (key478, -2), (key570, -2), (key575, 2), (key580, 2), (key586, -2), (key598, -2), (key604, 2)]

def row263 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row264 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row265 : Integer.Sparse Key := [(key242, -2), (key244, 2), (key254, 2), (key265, -2), (key269, -2), (key274, 2), (key308, 2), (key310, -2), (key322, -2), (key333, 2), (key337, 2), (key343, -2), (key391, -2), (key402, 2), (key412, 2), (key423, -2), (key472, -2), (key478, 2), (key570, 2), (key575, -2), (key580, -2), (key586, 2), (key598, 2), (key604, -2)]

def row266 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row267 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row268 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row269 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row270 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row271 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row272 : Integer.Sparse Key := [(key242, -2), (key244, 2), (key254, 2), (key265, -2), (key269, -2), (key274, 2), (key308, 2), (key310, -2), (key322, -2), (key333, 2), (key337, 2), (key343, -2), (key391, -2), (key402, 2), (key412, 2), (key423, -2), (key472, -2), (key478, 2), (key570, 2), (key575, -2), (key580, -2), (key586, 2), (key598, 2), (key604, -2)]

def row273 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row274 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row275 : Integer.Sparse Key := [(key242, 2), (key244, -2), (key254, -2), (key265, 2), (key269, 2), (key274, -2), (key308, -2), (key310, 2), (key322, 2), (key333, -2), (key337, -2), (key343, 2), (key391, 2), (key402, -2), (key412, -2), (key423, 2), (key472, 2), (key478, -2), (key570, -2), (key575, 2), (key580, 2), (key586, -2), (key598, -2), (key604, 2)]

def row276 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row277 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row278 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row279 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row280 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row281 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row282 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row283 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row284 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row285 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row286 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row287 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row288 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row289 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row290 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row291 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

def row292 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row293 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

def row294 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

def row295 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row296 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row297 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

def row298 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row299 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row300 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row301 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row302 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row303 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row304 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

def row305 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row306 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row307 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

def row308 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row309 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row310 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row311 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row312 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row313 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row314 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

def row315 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row316 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row317 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

def row318 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row319 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row320 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row321 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row322 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row323 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row324 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row325 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row326 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row327 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row328 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row329 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row330 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row331 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row332 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row333 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row334 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row335 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row336 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

def row337 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row338 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row339 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

def row340 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row341 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row342 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row343 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row344 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row345 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row346 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

def row347 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row348 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row349 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

def row350 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row351 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row352 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row353 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row354 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row355 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row356 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

def row357 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row358 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row359 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

def row360 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row361 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row362 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row363 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row364 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row365 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row366 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row367 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row368 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row369 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row370 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row371 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row372 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row373 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row374 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row375 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row376 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row377 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row378 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -2), (key270, -2), (key275, 2), (key309, 2), (key311, -2), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key392, -2), (key403, 2), (key413, 2), (key424, -2), (key473, -2), (key479, 2), (key571, 2), (key576, -2), (key581, -2), (key587, 2), (key599, 2), (key605, -2)]

def row379 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row380 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row381 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 4), (key275, -2), (key309, -2), (key311, 2), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key392, 2), (key403, -2), (key413, -2), (key424, 2), (key473, 2), (key479, -2), (key571, -2), (key576, 2), (key581, 2), (key587, -2), (key599, -2), (key605, 2)]

def row382 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row383 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row384 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row385 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row386 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row387 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row388 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 2), (key270, 2), (key275, -2), (key309, -2), (key311, 2), (key323, 4), (key334, -4), (key338, -4), (key344, 4), (key413, -2), (key424, 2), (key473, 2), (key479, -2), (key581, 2), (key587, -2), (key599, -2), (key605, 2)]

def row389 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row390 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row391 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -2), (key270, -2), (key275, 2), (key309, 2), (key311, -2), (key323, -4), (key334, 4), (key338, 4), (key344, -4), (key413, 2), (key424, -4), (key473, -2), (key479, 2), (key587, 2), (key599, 2), (key605, -2)]

def row392 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key587, -1), (key599, -1), (key605, 1)]

def row393 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key587, -1), (key599, -1), (key605, 1)]

def row394 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key473, 1), (key479, -1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row395 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key473, 1), (key479, -1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row396 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row397 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row398 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -4), (key275, 2), (key309, 2), (key311, -2), (key323, -2), (key334, 4), (key344, -2), (key392, -2), (key403, 4), (key413, 2), (key424, -4), (key473, -2), (key479, 2), (key576, -2), (key587, 2), (key599, 2), (key605, -2)]

def row399 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row400 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row401 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 4), (key275, -2), (key309, -2), (key311, 2), (key323, 2), (key334, -4), (key344, 4), (key392, 2), (key403, -4), (key413, -2), (key424, 4), (key473, 2), (key479, -2), (key587, -2), (key599, -2), (key605, 2)]

def row402 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key344, -2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key587, 1), (key599, 1), (key605, -1)]

def row403 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key344, -2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key587, 1), (key599, 1), (key605, -1)]

def row404 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key576, -2), (key587, 1), (key599, 1), (key605, -1)]

def row405 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key576, -2), (key587, 1), (key599, 1), (key605, -1)]

def row406 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row407 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row408 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key270, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key338, -2), (key344, 1), (key392, 1), (key413, -1), (key473, 1), (key479, -1), (key571, -2), (key576, 1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row409 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key270, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key338, -2), (key344, 1), (key392, 1), (key413, -1), (key473, 1), (key479, -1), (key571, -2), (key576, 1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row410 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key392, -1), (key403, 2), (key413, 1), (key424, -1), (key473, -1), (key571, 1), (key576, -2), (key581, -1), (key587, 1), (key599, 2), (key605, -1)]

def row411 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key392, -1), (key403, 2), (key413, 1), (key424, -1), (key473, -1), (key571, 1), (key576, -2), (key581, -1), (key587, 1), (key599, 2), (key605, -1)]

def row412 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key338, 1), (key344, -1), (key403, 1), (key413, 1), (key473, -1), (key479, 1), (key571, 2), (key576, -1), (key581, -2), (key587, 1), (key599, 1), (key605, -1)]

def row413 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key338, 1), (key344, -1), (key403, 1), (key413, 1), (key473, -1), (key479, 1), (key571, 2), (key576, -1), (key581, -2), (key587, 1), (key599, 1), (key605, -1)]

def row414 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -1), (key338, -1), (key344, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -2), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key605, 1)]

def row415 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -1), (key338, -1), (key344, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -2), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key605, 1)]

end MUB6.Certificate.GramRows

end OAI
end


