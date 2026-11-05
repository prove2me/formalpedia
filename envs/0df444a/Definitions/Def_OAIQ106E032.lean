-- Prove2me | Definitions.Def_OAIQ106E032
-- name    : OAIQ106E032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:56:17.748508+00:00
-- url     : https://prove2.me/theorems/99d289ab-e777-4d6a-8545-785c812f91a3
-- title:
--   Definitions bundle OAIQ106E032 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2753 declarations of OpenAI's Lean: 2753 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block4.entries`, `OAI.MUB6.Certificate.GramEntries.Block4.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_1` and 2713 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block4Data`, `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block134`, `MutuallyUnbiased_GramRows_Block135`, `MutuallyUnbiased_GramRows_Block136`, `MutuallyUnbiased_GramRows_Block137`, `MutuallyUnbiased_GramRows_Block138`, `MutuallyUnbiased_GramRows_Block139`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block141`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block143`, `MutuallyUnbiased_GramRows_Block144`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block146`, `MutuallyUnbiased_GramRows_Block147`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block149`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block87`, `MutuallyUnbiased_GramRows_Block88`, `MutuallyUnbiased_GramRows_Block89`, `MutuallyUnbiased_GramRows_Block90`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E033`, `OAIQ106E034`, `OAIQ106E036` and `OAIQ106E038`; the statements `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2362, 144), (key2365, -288), (key2367, 144), (key2457, 144), (key2460, -144), (key2521, -320), (key2525, 240), (key2532, 32), (key2533, 48), (key2562, 144), (key2564, -144)]

def entry1_0 : Integer.Sparse Key := [(key1090, -288), (key1098, 288), (key1180, 288), (key1183, -288)]

def entry1_1 : Integer.Sparse Key := [(key1, 144), (key7, -144), (key84, -144), (key90, 288), (key151, -256), (key193, -32), (key202, 144)]

def entry2_0 : Integer.Sparse Key := [(key2357, -48), (key2361, 48), (key2363, 24), (key2366, -24), (key2452, -216), (key2456, -72), (key2458, 192), (key2461, 96), (key2517, 152), (key2523, -144), (key2528, 136), (key2530, -144), (key2560, -16), (key2579, 16)]

def entry2_1 : Integer.Sparse Key := [(key971, 144), (key979, -144), (key1085, -144), (key1093, 288), (key1164, -144), (key1228, -144), (key1245, 144)]

def entry2_2 : Integer.Sparse Key := [(key2353, 144), (key2359, -144), (key2448, -144), (key2454, 288), (key2515, -256), (key2566, -32), (key2578, 144)]

def entry3_0 : Integer.Sparse Key := [(key2471, 288), (key2479, -288), (key2502, -288), (key2518, 288)]

def entry3_1 : Integer.Sparse Key := [(key995, -144), (key1011, 144), (key1030, -144), (key1067, 144), (key1108, 288), (key1119, -144), (key1146, -144)]

def entry3_2 : Integer.Sparse Key := [(key2372, -144), (key2385, 144), (key2400, -144), (key2432, 144), (key2466, 288), (key2475, -144), (key2498, -144)]

def entry3_3 : Integer.Sparse Key := [(key2606, 144), (key2622, -144), (key2661, 144), (key2696, -160), (key2776, -128), (key2799, -144), (key2849, 288)]

def entry4_0 : Integer.Sparse Key := [(key1090, -288), (key1097, 288), (key1180, 288), (key1182, -288)]

def entry4_1 : Integer.Sparse Key := [(key2, 144), (key6, -144), (key85, -144), (key89, 288), (key150, -144), (key166, -144), (key186, 144)]

def entry4_2 : Integer.Sparse Key := [(key972, 144), (key978, -144), (key1086, -144), (key1092, 288), (key1163, -144), (key1227, -144), (key1244, 144)]

def entry4_3 : Integer.Sparse Key := [(key992, -144), (key1010, 144), (key1027, -144), (key1066, 144), (key1105, 288), (key1118, -144), (key1145, -144)]

def entry4_4 : Integer.Sparse Key := [(key1, 144), (key4, -144), (key84, -144), (key87, 288), (key148, -256), (key164, -32), (key184, 144)]

def entry5_0 : Integer.Sparse Key := [(key982, 144), (key986, -288), (key988, 144), (key1096, 144), (key1100, -144), (key1171, -144), (key1175, 144), (key1185, -144), (key1186, 144), (key1222, 144), (key1224, -144)]

def entry5_1 : Integer.Sparse Key := [(key5, -48), (key9, 48), (key11, 24), (key14, -24), (key88, -216), (key92, -72), (key94, 192), (key97, 96), (key153, 152), (key161, -144), (key165, 136), (key167, -144), (key187, -16), (key203, 16)]

def entry5_2 : Integer.Sparse Key := [(key1095, -288), (key1101, 288), (key1166, 288), (key1173, -288)]

def entry5_3 : Integer.Sparse Key := [(key1115, 288), (key1124, -288), (key1151, -288), (key1167, 288)]

def entry5_4 : Integer.Sparse Key := [(key92, -288), (key95, 288), (key153, 288), (key157, -288)]

def entry5_5 : Integer.Sparse Key := [(key10, 144), (key13, -288), (key15, 144), (key93, 144), (key96, -144), (key158, -320), (key163, 240), (key169, 32), (key170, 48), (key189, 144), (key192, -144)]

def entry6_0 : Integer.Sparse Key := [(key2378, -24), (key2383, 36), (key2390, 80), (key2394, -60), (key2411, 12), (key2437, 56), (key2443, -36), (key2472, -48), (key2480, 72), (key2484, -12), (key2509, 60), (key2524, -72), (key2580, 16), (key2587, -120), (key2593, 108), (key2598, 64), (key2600, -84), (key2766, -72), (key2772, 60), (key2843, -24), (key2880, 72), (key2887, 72), (key2889, -60), (key2910, -72), (key2929, 16), (key2931, -36), (key2966, -72), (key2968, 84), (key2989, -72), (key3002, 56)]

def entry6_1 : Integer.Sparse Key := [(key1028, 144), (key1036, -144), (key1106, -144), (key1114, 288), (key1123, -144), (key1232, -144), (key1235, 144)]

def entry6_2 : Integer.Sparse Key := [(key2370, 24), (key2376, 12), (key2388, -20), (key2398, 120), (key2404, -72), (key2435, -8), (key2464, -100), (key2470, 144), (key2478, -108), (key2501, -12), (key2568, -36), (key2570, 68), (key2575, 20), (key2583, -24), (key2589, -12), (key2604, 20), (key2762, 24), (key2768, -72), (key2839, -44), (key2845, 144), (key2876, -108), (key2916, -36), (key2925, 76), (key3005, 8), (key3019, 12), (key3028, -20)]

def entry6_3 : Integer.Sparse Key := [(key2780, -144), (key2789, 144), (key2803, -144), (key2824, 144), (key2853, 288), (key2855, -144), (key2865, -144)]

def entry6_4 : Integer.Sparse Key := [(key1029, 144), (key1035, -144), (key1107, -144), (key1113, 288), (key1122, -144), (key1231, -144), (key1234, 144)]

def entry6_5 : Integer.Sparse Key := [(key1003, -144), (key1009, 144), (key1017, 144), (key1022, -144), (key1038, -72), (key1044, 72), (key1073, 72), (key1080, -72), (key1116, -72), (key1125, 144), (key1130, -72), (key1152, -72), (key1159, 144), (key1174, -72), (key1233, 72), (key1236, -72), (key1243, -72), (key1247, 72)]

def entry6_6 : Integer.Sparse Key := [(key2608, 72), (key2614, -72), (key2624, -72), (key2630, 144), (key2638, -120), (key2657, -24), (key2659, 72), (key2663, 36), (key2669, -36), (key2698, -80), (key2704, 84), (key2724, -72), (key2757, 56), (key2778, 8), (key2784, 60), (key2792, -72), (key2801, 72), (key2807, -36), (key2827, -80), (key2851, -36), (key2858, -24), (key2868, 84), (key2918, -48), (key2919, 72), (key3009, 16), (key3011, 8), (key3016, 36), (key3021, 60), (key3022, -72), (key3025, -36)]

def entry7_0 : Integer.Sparse Key := [(key2420, 288), (key2427, -576), (key2438, 288)]

def entry7_1 : Integer.Sparse Key := [(key1050, -288), (key1058, 288), (key1136, 288), (key1138, -288)]

def entry7_2 : Integer.Sparse Key := [(key2416, -288), (key2423, 288), (key2489, 288), (key2491, -288)]

def entry7_3 : Integer.Sparse Key := [(key2677, 336), (key2708, -240), (key2811, -224), (key2861, 192), (key3045, -48), (key3059, -48), (key3094, -64), (key3122, 96)]

def entry7_4 : Integer.Sparse Key := [(key1047, -288), (key1057, 288), (key1133, 288), (key1137, -288)]

def entry7_5 : Integer.Sparse Key := [(key1055, 288), (key1063, -576), (key1074, 288)]

def entry7_6 : Integer.Sparse Key := [(key2681, -288), (key2688, 288), (key2712, 288), (key2714, -288)]

def entry7_7 : Integer.Sparse Key := [(key3079, 288), (key3084, -576), (key3099, 288)]

def entry8_0 : Integer.Sparse Key := [(key2456, -288), (key2459, 288), (key2517, 288), (key2520, -288)]

def entry8_1 : Integer.Sparse Key := [(key972, 144), (key977, -144), (key1086, -144), (key1091, 288), (key1162, -144), (key1181, -144), (key1218, 144)]

def entry8_2 : Integer.Sparse Key := [(key2354, 144), (key2358, -144), (key2449, -144), (key2453, 288), (key2514, -144), (key2529, -144), (key2559, 144)]

def entry8_3 : Integer.Sparse Key := [(key2369, -144), (key2384, 144), (key2397, -144), (key2431, 144), (key2463, 288), (key2474, -144), (key2497, -144)]

def entry8_4 : Integer.Sparse Key := [(key971, 144), (key975, -144), (key1085, -144), (key1089, 288), (key1161, -144), (key1179, -144), (key1217, 144)]

def entry8_5 : Integer.Sparse Key := [(key1095, -288), (key1099, 288), (key1166, 288), (key1170, -288)]

def entry8_6 : Integer.Sparse Key := [(key2763, 144), (key2767, -144), (key2840, -144), (key2844, 288), (key2875, -144), (key2888, -144), (key2909, 144)]

def entry8_7 : Integer.Sparse Key := [(key2413, -288), (key2422, 288), (key2486, 288), (key2490, -288)]

def entry8_8 : Integer.Sparse Key := [(key2353, 144), (key2356, -144), (key2448, -144), (key2451, 288), (key2513, -256), (key2527, -32), (key2558, 144)]

def entry9_0 : Integer.Sparse Key := [(key1975, 288), (key1980, -576), (key1996, 288)]

def entry9_1 : Integer.Sparse Key := [(key55, -288), (key61, 288), (key123, 288), (key126, -288)]

def entry9_2 : Integer.Sparse Key := [(key1972, -288), (key1984, 288), (key2208, 288), (key2225, -288)]

def entry9_3 : Integer.Sparse Key := [(key2010, 288), (key2039, -288), (key2124, -288), (key2211, 288)]

def entry9_4 : Integer.Sparse Key := [(key53, -288), (key59, 288), (key121, 288), (key124, -288)]

def entry9_5 : Integer.Sparse Key := [(key57, 288), (key64, -576), (key77, 288)]

def entry9_6 : Integer.Sparse Key := [(key2012, -288), (key2025, 288), (key2041, 288), (key2054, -288)]

def entry9_7 : Integer.Sparse Key := [(key2100, 288), (key2105, -576), (key2130, 288)]

def entry9_8 : Integer.Sparse Key := [(key1971, -288), (key1979, 288), (key2207, 288), (key2216, -288)]

def entry9_9 : Integer.Sparse Key := [(key756, 288), (key760, -576), (key787, 288)]

def entry10_0 : Integer.Sparse Key := [(key2378, -144), (key2381, 144), (key2390, 144), (key2392, -144), (key2406, -72), (key2409, 72), (key2437, 72), (key2440, -72), (key2472, -72), (key2480, 144), (key2482, -72), (key2503, -72), (key2506, 144), (key2522, -72), (key2538, 72), (key2543, -72), (key2554, -72), (key2563, 72)]

def entry10_1 : Integer.Sparse Key := [(key1029, 144), (key1034, -144), (key1107, -144), (key1112, 288), (key1121, -144), (key1191, -144), (key1197, 144)]

def entry10_2 : Integer.Sparse Key := [(key2399, 144), (key2403, -144), (key2465, -144), (key2469, 288), (key2477, -144), (key2536, -144), (key2541, 144)]

def entry10_3 : Integer.Sparse Key := [(key2777, -144), (key2788, 144), (key2800, -144), (key2823, 144), (key2850, 288), (key2854, -144), (key2864, -144)]

def entry10_4 : Integer.Sparse Key := [(key1028, 144), (key1032, -144), (key1106, -144), (key1110, 288), (key1120, -144), (key1189, -144), (key1196, 144)]

def entry10_5 : Integer.Sparse Key := [(key1003, -144), (key1007, 144), (key1017, 144), (key1020, -144), (key1038, -72), (key1042, 72), (key1073, 72), (key1077, -72), (key1116, -72), (key1125, 144), (key1128, -72), (key1152, -72), (key1156, 144), (key1172, -72), (key1194, 72), (key1200, -72), (key1213, -72), (key1223, 72)]

def entry10_6 : Integer.Sparse Key := [(key2609, 72), (key2613, -72), (key2625, -72), (key2629, 144), (key2637, -72), (key2647, -72), (key2652, 72), (key2664, 36), (key2668, -36), (key2699, -36), (key2703, 72), (key2723, -36), (key2736, -36), (key2746, 36), (key2779, -36), (key2783, 72), (key2791, -36), (key2802, 72), (key2806, -36), (key2826, -36), (key2852, -36), (key2857, -36), (key2867, 72), (key2894, -36), (key2896, 72), (key2903, -36), (key2937, -36), (key2942, 36), (key2949, -36), (key2959, 36), (key2973, 72), (key2975, -36), (key2982, -36)]

def entry10_7 : Integer.Sparse Key := [(key2678, -288), (key2687, 288), (key2709, 288), (key2713, -288)]

def entry10_8 : Integer.Sparse Key := [(key2370, 24), (key2373, 12), (key2386, -20), (key2398, 120), (key2401, -72), (key2433, -8), (key2464, -100), (key2467, 144), (key2476, -108), (key2499, -12), (key2534, -36), (key2540, 68), (key2551, 20), (key2583, -24), (key2586, -12), (key2597, 20), (key2762, 24), (key2765, -72), (key2839, -44), (key2842, 144), (key2874, -108), (key2886, -36), (key2908, 76), (key2928, 8), (key2965, 12), (key2987, -20)]

def entry10_9 : Integer.Sparse Key := [(key2011, -288), (key2020, 288), (key2040, 288), (key2048, -288)]

def entry10_10 : Integer.Sparse Key := [(key2608, 72), (key2611, -72), (key2624, -72), (key2627, 144), (key2636, -120), (key2645, -24), (key2651, 72), (key2663, 36), (key2666, -36), (key2698, -80), (key2701, 84), (key2722, -72), (key2745, 56), (key2778, 8), (key2781, 60), (key2790, -72), (key2801, 72), (key2804, -36), (key2825, -80), (key2851, -36), (key2856, -24), (key2866, 84), (key2892, -48), (key2895, 72), (key2941, 16), (key2947, 8), (key2958, 36), (key2971, 60), (key2974, -72), (key2981, -36)]

def entry11_0 : Integer.Sparse Key := [(key1700, -288), (key1706, 288), (key1851, 288), (key1855, -288)]

def entry11_1 : Integer.Sparse Key := [(key220, 144), (key225, -144), (key492, -144), (key497, 288), (key551, -144), (key664, -144), (key681, 144)]

def entry11_2 : Integer.Sparse Key := [(key1273, 144), (key1278, -144), (key1696, -144), (key1701, 288), (key1751, -144), (key1933, -144), (key1953, 144)]

def entry11_3 : Integer.Sparse Key := [(key1360, -144), (key1372, 144), (key1486, -144), (key1511, 144), (key1712, 288), (key1721, -144), (key1739, -144)]

def entry11_4 : Integer.Sparse Key := [(key221, 144), (key225, -144), (key493, -144), (key497, 288), (key551, -144), (key619, -144), (key645, 144)]

def entry11_5 : Integer.Sparse Key := [(key496, -288), (key502, 288), (key618, 288), (key622, -288)]

def entry11_6 : Integer.Sparse Key := [(key1484, 144), (key1490, -144), (key1710, -144), (key1716, 288), (key1723, -144), (key1937, -144), (key1940, 144)]

def entry11_7 : Integer.Sparse Key := [(key1501, -288), (key1506, 288), (key1733, 288), (key1735, -288)]

def entry11_8 : Integer.Sparse Key := [(key1274, 144), (key1278, -144), (key1697, -144), (key1701, 288), (key1751, -144), (key1852, -144), (key1884, 144)]

def entry11_9 : Integer.Sparse Key := [(key358, -288), (key363, 288), (key528, 288), (key532, -288)]

def entry11_10 : Integer.Sparse Key := [(key1485, 144), (key1490, -144), (key1711, -144), (key1716, 288), (key1723, -144), (key1861, -144), (key1867, 144)]

def entry11_11 : Integer.Sparse Key := [(key288, 144), (key289, -144), (key513, -144), (key515, 288), (key547, -256), (key670, -32), (key680, 144)]

def entry12_0 : Integer.Sparse Key := [(key2362, 72), (key2365, -144), (key2367, 72), (key2457, 216), (key2460, -216), (key2521, -40), (key2525, 72), (key2532, -104), (key2533, 72), (key2562, -72), (key2564, 72)]

def entry12_1 : Integer.Sparse Key := [(key976, -144), (key984, 144), (key1090, -144), (key1169, 144), (key1180, 288), (key1183, -144), (key1220, -144)]

def entry12_2 : Integer.Sparse Key := [(key2357, -48), (key2361, -96), (key2363, 68), (key2366, 76), (key2452, -132), (key2456, -12), (key2458, 48), (key2461, -48), (key2517, 180), (key2519, 108), (key2523, -24), (key2528, 108), (key2530, -120), (key2560, -72), (key2567, 36), (key2579, -72)]

def entry12_3 : Integer.Sparse Key := [(key2377, 144), (key2389, -144), (key2405, 144), (key2436, -144), (key2479, -144), (key2502, -144), (key2518, 288)]

def entry12_4 : Integer.Sparse Key := [(key976, -144), (key983, 144), (key1090, -144), (key1168, 144), (key1180, 288), (key1182, -144), (key1219, -144)]

def entry12_5 : Integer.Sparse Key := [(key982, 72), (key986, -144), (key988, 72), (key1096, 216), (key1100, -216), (key1171, -216), (key1175, 216), (key1185, 72), (key1186, -72), (key1222, -72), (key1224, 72)]

def entry12_6 : Integer.Sparse Key := [(key2378, -24), (key2383, 6), (key2390, 36), (key2394, -6), (key2406, -72), (key2411, 42), (key2437, -36), (key2443, 42), (key2472, -48), (key2480, 144), (key2484, -42), (key2503, 60), (key2509, -54), (key2524, 24), (key2569, 24), (key2571, -36), (key2576, 12), (key2580, -36), (key2587, -48), (key2593, 66), (key2598, 36), (key2600, -66), (key2766, -36), (key2772, 66), (key2843, -60), (key2880, 84), (key2887, 72), (key2889, -66), (key2910, -72), (key2931, -6), (key2966, -24), (key2968, -18), (key2989, 24), (key2995, 12)]

def entry12_7 : Integer.Sparse Key := [(key2420, 288), (key2427, -288), (key2495, -288), (key2504, 288)]

def entry12_8 : Integer.Sparse Key := [(key2361, -144), (key2364, 144), (key2456, -144), (key2517, 288), (key2520, -144), (key2531, 144), (key2561, -144)]

def entry12_9 : Integer.Sparse Key := [(key1975, 288), (key1980, -288), (key2217, -288), (key2261, 288)]

def entry12_10 : Integer.Sparse Key := [(key2378, -72), (key2381, 72), (key2390, 72), (key2392, -72), (key2406, -108), (key2409, 108), (key2437, -36), (key2440, 36), (key2472, -108), (key2480, 216), (key2482, -108), (key2503, 36), (key2506, -72), (key2522, 36), (key2538, 108), (key2543, -108), (key2554, 36), (key2563, -36)]

def entry12_11 : Integer.Sparse Key := [(key1277, -144), (key1283, 144), (key1700, -144), (key1756, 144), (key1851, 288), (key1855, -144), (key1886, -144)]

def entry12_12 : Integer.Sparse Key := [(key2362, 108), (key2365, -72), (key2367, -36), (key2457, 180), (key2460, -36), (key2521, -104), (key2525, -36), (key2532, -256), (key2533, 108), (key2562, -108), (key2564, 252)]

def entry13_0 : Integer.Sparse Key := [(key2390, 32), (key2437, 32), (key2580, 16), (key2587, -72), (key2593, 72), (key2598, 40), (key2600, -72), (key2766, -72), (key2772, 72), (key2843, 144), (key2880, 144), (key2887, -72), (key2889, -72), (key2910, -144), (key2929, 40), (key2931, -72), (key2966, -72), (key2968, -72), (key2989, -144), (key2995, 144), (key3002, 128)]

def entry13_1 : Integer.Sparse Key := [(key1001, -144), (key1015, 144), (key1036, -144), (key1071, 144), (key1114, 288), (key1123, -144), (key1150, -144)]

def entry13_2 : Integer.Sparse Key := [(key2370, 24), (key2376, -36), (key2388, 76), (key2398, 24), (key2404, -36), (key2435, 76), (key2464, -24), (key2470, 96), (key2478, -72), (key2501, -72), (key2570, 8), (key2575, 8), (key2583, -24), (key2589, -108), (key2604, 68), (key2762, -24), (key2768, -108), (key2839, 24), (key2845, 192), (key2916, -72), (key2925, -8), (key3005, 68), (key3019, -72), (key3028, -8)]

def entry13_3 : Integer.Sparse Key := [(key2610, 144), (key2626, -144), (key2665, 144), (key2700, -144), (key2780, -144), (key2803, -144), (key2853, 288)]

def entry13_4 : Integer.Sparse Key := [(key1000, -144), (key1014, 144), (key1035, -144), (key1070, 144), (key1113, 288), (key1122, -144), (key1149, -144)]

def entry13_5 : Integer.Sparse Key := [(key1003, -72), (key1009, 72), (key1017, 72), (key1022, -72), (key1038, -72), (key1044, 72), (key1073, 72), (key1080, -72), (key1116, 144), (key1125, -72), (key1130, -72), (key1152, -72), (key1159, -72), (key1174, 144), (key1233, 144), (key1236, -144), (key1243, -144), (key1247, 144)]

def entry13_6 : Integer.Sparse Key := [(key2608, 36), (key2614, -36), (key2624, -36), (key2630, 72), (key2638, -72), (key2659, 36), (key2663, 36), (key2669, -36), (key2698, -54), (key2704, -6), (key2724, -108), (key2752, 72), (key2757, 80), (key2778, -18), (key2784, 42), (key2792, -36), (key2801, -36), (key2807, -36), (key2827, -68), (key2851, 72), (key2858, 66), (key2868, 102), (key2918, -30), (key2919, -36), (key2922, -42), (key3009, 28), (key3011, 68), (key3016, 72), (key3021, 6), (key3022, -66), (key3025, -72)]

def entry13_7 : Integer.Sparse Key := [(key2688, 288), (key2714, -288), (key2817, -288), (key2863, 288)]

def entry13_8 : Integer.Sparse Key := [(key2588, -144), (key2599, 144), (key2767, -144), (key2844, 288), (key2888, -144), (key2930, 144), (key2967, -144)]

def entry13_9 : Integer.Sparse Key := [(key2025, 288), (key2054, -288), (key2143, -288), (key2227, 288)]

def entry13_10 : Integer.Sparse Key := [(key2609, 36), (key2613, -36), (key2625, -36), (key2629, 72), (key2637, -36), (key2647, -36), (key2652, 36), (key2664, 36), (key2668, -36), (key2699, -36), (key2703, -36), (key2723, -72), (key2736, 72), (key2746, 72), (key2779, -36), (key2783, 72), (key2791, -36), (key2802, -36), (key2806, -36), (key2826, -72), (key2852, 72), (key2857, 72), (key2867, 144), (key2894, -36), (key2896, -36), (key2903, -72), (key2937, -36), (key2942, 36), (key2949, 72), (key2959, 72), (key2973, -36), (key2975, -36), (key2982, -72)]

def entry13_11 : Integer.Sparse Key := [(key1364, -144), (key1374, 144), (key1490, -144), (key1513, 144), (key1716, 288), (key1723, -144), (key1741, -144)]

def entry13_12 : Integer.Sparse Key := [(key2378, 12), (key2383, 24), (key2390, -36), (key2394, -36), (key2406, 12), (key2411, 24), (key2437, -36), (key2443, -36), (key2472, -48), (key2480, 48), (key2484, -24), (key2503, 48), (key2509, -24), (key2524, 72), (key2587, 24), (key2593, 84), (key2600, -72), (key2766, 24), (key2772, 84), (key2843, -24), (key2880, 72), (key2887, -12), (key2889, -84), (key2910, -72), (key2931, -72), (key2966, -12), (key2968, -84), (key2989, -72), (key2995, 144), (key3002, 72)]

def entry13_13 : Integer.Sparse Key := [(key2608, 72), (key2614, 72), (key2624, -72), (key2630, -36), (key2638, -80), (key2657, 8), (key2659, 36), (key2663, 72), (key2669, 72), (key2698, -84), (key2704, -60), (key2724, -72), (key2757, 56), (key2778, -60), (key2784, -12), (key2792, -72), (key2801, -72), (key2807, -36), (key2827, -80), (key2851, 144), (key2858, 120), (key2868, 120), (key2918, 24), (key2919, -36), (key2922, -36), (key3009, 16), (key3011, 8), (key3016, 36), (key3021, 24), (key3022, -36), (key3025, -36)]

def entry14_0 : Integer.Sparse Key := [(key2378, 24), (key2383, -24), (key2390, -24), (key2394, 24), (key2406, -24), (key2411, 24), (key2437, 24), (key2443, -24), (key2480, -72), (key2484, 72), (key2503, 72), (key2509, -72), (key2587, 48), (key2593, -48), (key2598, -48), (key2600, 48), (key2766, -48), (key2772, 48), (key2887, -144), (key2889, 144), (key2929, 48), (key2931, -48), (key2966, 144), (key2968, -144)]

def entry14_1 : Integer.Sparse Key := [(key993, 144), (key1001, -144), (key1028, -144), (key1036, 144), (key1123, 144), (key1150, -144), (key1235, -144), (key1242, 144)]

def entry14_2 : Integer.Sparse Key := [(key2370, 96), (key2376, -84), (key2388, 12), (key2398, -96), (key2404, 84), (key2435, -12), (key2478, 96), (key2501, -96), (key2570, -48), (key2575, 48), (key2583, 48), (key2589, -60), (key2604, -12), (key2762, -48), (key2768, 60), (key2916, 48), (key2925, -96), (key3005, 12), (key3019, -48), (key3028, 96)]

def entry14_3 : Integer.Sparse Key := [(key2626, -144), (key2635, 144), (key2700, -144), (key2721, 144), (key2780, 144), (key2789, -144), (key2803, 144), (key2824, -144)]

def entry14_4 : Integer.Sparse Key := [(key994, 144), (key1000, -144), (key1029, -144), (key1035, 144), (key1122, 144), (key1149, -144), (key1234, -144), (key1241, 144)]

def entry14_5 : Integer.Sparse Key := [(key1003, 72), (key1009, -72), (key1017, -72), (key1022, 72), (key1038, -72), (key1044, 72), (key1073, 72), (key1080, -72), (key1125, -216), (key1130, 216), (key1152, 216), (key1159, -216)]

def entry14_6 : Integer.Sparse Key := [(key2608, -36), (key2614, 36), (key2624, 36), (key2630, -72), (key2638, 48), (key2657, 24), (key2659, -36), (key2663, 36), (key2669, -36), (key2698, 114), (key2704, -42), (key2724, -24), (key2752, -12), (key2757, 12), (key2778, -42), (key2784, 6), (key2792, -24), (key2801, -108), (key2807, 108), (key2827, 8), (key2858, 54), (key2868, -54), (key2918, 54), (key2919, -108), (key2922, 18), (key3007, -12), (key3009, 24), (key3011, -8), (key3021, -54), (key3022, 90)]

def entry14_7 : Integer.Sparse Key := [(key2712, -288), (key2714, 288), (key2815, 288), (key2817, -288)]

def entry14_8 : Integer.Sparse Key := [(key2584, 144), (key2588, -144), (key2763, -144), (key2767, 144), (key2888, 144), (key2909, -144), (key2967, -144), (key2988, 144)]

def entry14_9 : Integer.Sparse Key := [(key2041, -288), (key2054, 288), (key2126, 288), (key2143, -288)]

def entry14_10 : Integer.Sparse Key := [(key2609, -36), (key2613, 36), (key2625, 36), (key2629, -72), (key2637, 36), (key2647, 36), (key2652, -36), (key2664, 36), (key2668, -36), (key2699, 108), (key2703, -108), (key2779, -36), (key2783, 72), (key2791, -36), (key2802, -108), (key2806, 108), (key2894, 108), (key2896, -108), (key2937, -36), (key2942, 36), (key2973, -108), (key2975, 108)]

def entry14_11 : Integer.Sparse Key := [(key1358, 144), (key1364, -144), (key1484, -144), (key1490, 144), (key1723, 144), (key1741, -144), (key1940, -144), (key1949, 144)]

def entry14_12 : Integer.Sparse Key := [(key2378, -48), (key2383, 36), (key2390, -72), (key2394, 48), (key2406, 48), (key2411, -36), (key2437, 72), (key2443, -48), (key2480, -84), (key2484, -12), (key2503, 84), (key2509, 12), (key2571, 48), (key2576, -48), (key2587, 12), (key2598, -36), (key2600, 60), (key2766, -12), (key2887, -96), (key2889, 48), (key2910, 96), (key2929, 36), (key2931, -60), (key2966, 96), (key2968, -48), (key2989, -96)]

def entry14_13 : Integer.Sparse Key := [(key2630, -108), (key2638, 4), (key2657, 68), (key2659, 36), (key2698, 36), (key2704, 24), (key2724, 108), (key2752, -84), (key2757, -12), (key2778, -36), (key2784, -24), (key2792, -60), (key2807, 108), (key2827, -4), (key2858, 36), (key2868, -36), (key2918, 36), (key2919, -36), (key2922, -24), (key3007, 36), (key3009, 12), (key3011, -68), (key3016, -36), (key3021, -36), (key3022, 24), (key3025, 36)]

def entry14_14 : Integer.Sparse Key := [(key2608, 72), (key2614, -72), (key2624, 72), (key2630, -36), (key2638, -56), (key2657, -16), (key2659, 36), (key2663, -72), (key2669, 72), (key2698, -132), (key2704, 60), (key2724, 48), (key2752, 24), (key2757, -48), (key2778, -12), (key2784, 12), (key2792, 48), (key2801, 72), (key2807, -36), (key2827, -56), (key2919, 108), (key2922, -108), (key3007, 24), (key3009, -24), (key3011, -16), (key3016, 36), (key3022, -108), (key3025, 108)]

def entry15_0 : Integer.Sparse Key := [(key2378, 72), (key2381, -72), (key2390, -72), (key2392, 72), (key2406, -72), (key2409, 72), (key2437, 72), (key2440, -72), (key2480, -216), (key2482, 216), (key2503, 216), (key2506, -216)]

def entry15_1 : Integer.Sparse Key := [(key994, 144), (key999, -144), (key1029, -144), (key1034, 144), (key1121, 144), (key1148, -144), (key1197, -144), (key1210, 144)]

def entry15_2 : Integer.Sparse Key := [(key2371, 144), (key2375, -144), (key2399, -144), (key2403, 144), (key2477, 144), (key2500, -144), (key2541, -144), (key2552, 144)]

def entry15_3 : Integer.Sparse Key := [(key2623, -144), (key2634, 144), (key2697, -144), (key2720, 144), (key2777, 144), (key2788, -144), (key2800, 144), (key2823, -144)]

def entry15_4 : Integer.Sparse Key := [(key993, 144), (key997, -144), (key1028, -144), (key1032, 144), (key1120, 144), (key1147, -144), (key1196, -144), (key1209, 144)]

def entry15_5 : Integer.Sparse Key := [(key1003, 72), (key1007, -72), (key1017, -72), (key1020, 72), (key1038, -72), (key1042, 72), (key1073, 72), (key1077, -72), (key1125, -216), (key1128, 216), (key1152, 216), (key1156, -216)]

def entry15_6 : Integer.Sparse Key := [(key2609, -36), (key2613, 36), (key2625, 36), (key2629, -72), (key2637, 36), (key2647, 36), (key2652, -36), (key2664, 36), (key2668, -36), (key2699, -36), (key2703, 72), (key2723, -36), (key2736, -36), (key2746, 36), (key2779, 108), (key2783, -108), (key2802, -108), (key2806, 108), (key2857, 108), (key2867, -108), (key2896, -108), (key2903, 108)]

def entry15_7 : Integer.Sparse Key := [(key2709, -288), (key2713, 288), (key2812, 288), (key2816, -288)]

def entry15_8 : Integer.Sparse Key := [(key2370, 96), (key2373, -84), (key2386, 12), (key2398, -96), (key2401, 84), (key2433, -12), (key2476, 96), (key2499, -96), (key2540, -48), (key2551, 48), (key2583, 48), (key2586, -60), (key2597, -12), (key2762, -48), (key2765, 60), (key2886, 48), (key2908, -96), (key2928, 12), (key2965, -48), (key2987, 96)]

def entry15_9 : Integer.Sparse Key := [(key2040, -288), (key2048, 288), (key2125, 288), (key2135, -288)]

def entry15_10 : Integer.Sparse Key := [(key2608, -36), (key2611, 36), (key2624, 36), (key2627, -72), (key2636, 48), (key2645, 24), (key2651, -36), (key2663, 36), (key2666, -36), (key2698, 114), (key2701, -42), (key2722, -24), (key2734, -12), (key2745, 12), (key2778, -42), (key2781, 6), (key2790, -24), (key2801, -108), (key2804, 108), (key2825, 8), (key2856, 54), (key2866, -54), (key2892, 54), (key2895, -108), (key2902, 18), (key2935, -12), (key2941, 24), (key2947, -8), (key2971, -54), (key2974, 90)]

def entry15_11 : Integer.Sparse Key := [(key1359, 144), (key1364, -144), (key1485, -144), (key1490, 144), (key1723, 144), (key1741, -144), (key1867, -144), (key1877, 144)]

def entry15_12 : Integer.Sparse Key := [(key2378, -36), (key2381, 36), (key2390, -108), (key2392, 108), (key2406, 36), (key2409, -36), (key2437, 108), (key2440, -108), (key2480, -180), (key2482, 36), (key2503, 180), (key2506, -36), (key2543, 144), (key2554, -144)]

def entry15_13 : Integer.Sparse Key := [(key2629, -108), (key2637, -36), (key2647, 108), (key2652, 36), (key2703, 108), (key2723, 36), (key2736, -108), (key2746, -36), (key2783, -108), (key2791, -36), (key2806, 108), (key2826, 36), (key2857, 72), (key2867, -72), (key2896, -36), (key2903, 36), (key2937, 108), (key2942, 36), (key2949, -108), (key2959, -36), (key2975, -36), (key2982, 36)]

def entry15_14 : Integer.Sparse Key := [(key2609, 72), (key2613, -72), (key2625, 72), (key2629, -36), (key2637, -36), (key2647, -36), (key2652, 36), (key2664, -72), (key2668, 72), (key2699, -72), (key2703, 36), (key2723, 36), (key2736, 36), (key2746, -36), (key2779, -72), (key2783, 36), (key2791, 36), (key2802, 72), (key2806, -36), (key2826, -36), (key2896, 108), (key2903, -108), (key2937, 36), (key2942, -36), (key2949, -36), (key2959, 36), (key2975, -108), (key2982, 108)]

def entry15_15 : Integer.Sparse Key := [(key2608, 72), (key2611, -72), (key2624, 72), (key2627, -36), (key2636, -56), (key2645, -16), (key2651, 36), (key2663, -72), (key2666, 72), (key2698, -132), (key2701, 60), (key2722, 48), (key2734, 24), (key2745, -48), (key2778, -12), (key2781, 12), (key2790, 48), (key2801, 72), (key2804, -36), (key2825, -56), (key2895, 108), (key2902, -108), (key2935, 24), (key2941, -24), (key2947, -16), (key2958, 36), (key2974, -108), (key2981, 108)]

def entry16_0 : Integer.Sparse Key := [(key2379, 36), (key2382, -60), (key2393, -68), (key2395, 72), (key2407, 36), (key2410, -36), (key2441, -80), (key2445, 60), (key2473, 16), (key2483, -36), (key2507, -72), (key2526, 60), (key2544, 8), (key2545, 24), (key2555, 8), (key2557, -12), (key2565, -36), (key2592, 108), (key2595, -84), (key2602, -76), (key2603, 72), (key2771, 36), (key2774, -36), (key2848, 56), (key2882, -72), (key2891, -36), (key2912, -80), (key2914, 120), (key2933, 8), (key2934, 12), (key2991, 136), (key2993, -60), (key2996, 12), (key3003, -36)]

def entry16_1 : Integer.Sparse Key := [(key1033, -144), (key1041, 144), (key1111, -144), (key1127, 144), (key1190, 288), (key1193, -144), (key1199, -144)]

def entry16_2 : Integer.Sparse Key := [(key2374, -60), (key2380, 24), (key2391, 12), (key2402, -108), (key2408, 96), (key2468, -72), (key2481, 96), (key2505, 24), (key2535, 108), (key2537, -72), (key2542, -72), (key2553, -48), (key2591, 60), (key2596, -24), (key2605, -12), (key2770, -36), (key2775, 48), (key2847, -72), (key2878, 180), (key2884, -72), (key2917, 48), (key2926, -72), (key3020, -24), (key3029, 48)]

def entry16_3 : Integer.Sparse Key := [(key2785, 144), (key2793, -144), (key2808, 144), (key2828, -144), (key2859, -144), (key2869, -144), (key2879, 288)]

def entry16_4 : Integer.Sparse Key := [(key1033, -144), (key1040, 144), (key1111, -144), (key1126, 144), (key1190, 288), (key1192, -144), (key1198, -144)]

def entry16_5 : Integer.Sparse Key := [(key1004, 144), (key1008, -144), (key1021, -144), (key1023, 144), (key1039, 72), (key1043, -72), (key1078, -72), (key1081, 72), (key1117, 72), (key1129, -72), (key1157, -72), (key1176, 72), (key1195, -72), (key1201, -72), (key1202, 144), (key1214, 144), (key1216, -72), (key1225, -72)]

def entry16_6 : Integer.Sparse Key := [(key2612, -36), (key2616, -36), (key2618, 42), (key2621, 30), (key2628, -36), (key2632, -36), (key2640, 102), (key2641, 54), (key2644, -36), (key2646, 42), (key2648, -36), (key2653, -42), (key2658, 18), (key2660, -30), (key2667, -36), (key2673, 30), (key2676, 6), (key2702, -12), (key2706, -12), (key2726, 72), (key2728, 36), (key2732, -30), (key2735, 36), (key2737, -30), (key2747, -36), (key2753, 6), (key2758, -18), (key2782, -24), (key2786, -24), (key2794, 36), (key2795, 30), (key2798, -6), (key2809, -36), (key2829, -28), (key2831, 36), (key2835, 54), (key2860, 42), (key2870, -12), (key2885, -30), (key2893, 30), (key2897, -30), (key2904, -30), (key2920, -6), (key2923, 30), (key2927, -36), (key2938, -6), (key2943, -18), (key2948, -8), (key2950, 18), (key2960, -28), (key2972, -24), (key2976, 42), (key2983, -12), (key2997, -6), (key3000, 18), (key3017, -8), (key3023, -6), (key3026, -24), (key3030, 54)]

def entry16_7 : Integer.Sparse Key := [(key2685, 288), (key2692, -288), (key2718, -288), (key2727, 288)]

def entry16_8 : Integer.Sparse Key := [(key2770, -144), (key2773, 144), (key2847, -144), (key2878, 288), (key2881, -144), (key2890, 144), (key2911, -144)]

def entry16_9 : Integer.Sparse Key := [(key2016, 288), (key2021, -288), (key2049, -288), (key2074, 288)]

def entry16_10 : Integer.Sparse Key := [(key2616, -72), (key2619, 72), (key2632, -72), (key2640, 144), (key2642, -72), (key2649, 72), (key2654, -72), (key2671, -36), (key2674, 36), (key2706, -36), (key2726, 72), (key2729, -36), (key2738, 36), (key2748, -36), (key2786, -36), (key2794, 72), (key2796, -36), (key2809, -36), (key2829, -36), (key2832, 72), (key2860, 72), (key2870, -36), (key2883, -36), (key2898, -36), (key2905, 72), (key2913, -36), (key2939, 36), (key2944, -36), (key2951, 36), (key2961, -36), (key2977, -36), (key2984, -36), (key2992, 72)]

def entry16_11 : Integer.Sparse Key := [(key1489, -144), (key1495, 144), (key1715, -144), (key1727, 144), (key1860, 288), (key1864, -144), (key1869, -144)]

def entry16_12 : Integer.Sparse Key := [(key2379, 30), (key2382, -18), (key2393, -10), (key2395, 12), (key2407, 78), (key2410, -42), (key2441, 32), (key2445, -30), (key2473, 52), (key2483, -42), (key2526, -30), (key2539, -48), (key2544, -56), (key2545, 84), (key2555, -80), (key2557, 54), (key2565, 42), (key2592, 42), (key2595, -54), (key2602, -62), (key2603, 60), (key2771, 30), (key2774, -66), (key2848, 56), (key2882, -60), (key2891, -66), (key2912, -52), (key2914, 132), (key2933, 4), (key2934, -6), (key2970, 36), (key2991, 8), (key2993, -18), (key2996, -6), (key3003, -6)]

def entry16_13 : Integer.Sparse Key := [(key2612, -24), (key2616, -12), (key2618, 36), (key2628, -12), (key2632, -24), (key2640, 54), (key2641, 36), (key2644, -6), (key2646, 18), (key2648, -30), (key2653, -36), (key2667, -36), (key2673, 36), (key2702, 72), (key2706, -24), (key2726, 54), (key2728, 72), (key2732, -6), (key2735, -36), (key2737, -36), (key2747, -72), (key2782, -12), (key2795, 36), (key2805, 72), (key2829, -16), (key2831, 72), (key2860, -6), (key2870, -6), (key2885, 12), (key2893, -30), (key2897, -36), (key2904, -54), (key2936, 18), (key2938, -30), (key2943, -36), (key2948, -20), (key2950, -36), (key2960, -64), (key2972, -30), (key2976, -36), (key2983, -54), (key2997, 60), (key2998, 72), (key3000, 84), (key3017, -8), (key3023, -18), (key3026, -18), (key3030, 60)]

def entry16_14 : Integer.Sparse Key := [(key2616, 36), (key2618, -12), (key2621, -24), (key2628, 12), (key2632, 24), (key2640, -30), (key2641, -24), (key2644, 6), (key2646, -42), (key2648, 30), (key2653, 24), (key2658, -12), (key2660, 12), (key2667, -24), (key2671, -12), (key2673, 24), (key2676, 12), (key2706, -24), (key2726, 30), (key2732, -6), (key2735, -72), (key2737, 72), (key2753, 12), (key2758, -12), (key2782, -12), (key2794, -36), (key2795, 24), (key2798, 36), (key2805, -12), (key2809, 12), (key2829, 64), (key2835, -60), (key2860, -54), (key2870, 54), (key2893, -54), (key2897, 72), (key2904, 18), (key2920, 36), (key2923, -36), (key2936, 42), (key2938, -30), (key2943, -24), (key2948, 44), (key2950, -48), (key2960, -8), (key2972, 54), (key2976, -72), (key2983, -18), (key3017, 8), (key3023, -18), (key3026, 18)]

def entry16_15 : Integer.Sparse Key := [(key2616, 36), (key2619, -36), (key2632, 36), (key2640, -72), (key2642, 36), (key2649, -36), (key2654, 36), (key2671, -36), (key2674, 36), (key2706, -36), (key2726, 72), (key2729, -36), (key2738, 36), (key2748, -36), (key2794, -108), (key2796, 108), (key2829, 108), (key2832, -108), (key2860, -108), (key2870, 108), (key2898, 108), (key2905, -108)]

def entry16_16 : Integer.Sparse Key := [(key2617, 72), (key2620, -72), (key2633, 72), (key2643, -84), (key2650, -60), (key2655, -72), (key2656, 144), (key2672, 36), (key2675, -36), (key2707, 56), (key2730, -72), (key2739, -36), (key2749, -80), (key2751, 120), (key2787, 16), (key2797, -36), (key2810, 36), (key2833, -80), (key2899, -36), (key2906, -72), (key2915, 120), (key2945, 8), (key2946, 24), (key2952, 8), (key2962, 72), (key2964, -36), (key2985, 72), (key2994, -60), (key2999, 24), (key3001, -12), (key3004, -36)]

def entry17_0 : Integer.Sparse Key := [(key1989, -144), (key1994, 144), (key1999, 144), (key2003, -144), (key2234, 144), (key2259, 144), (key2268, -144), (key2272, -144), (key2294, -288), (key2324, 144), (key2336, 144)]

def entry17_1 : Integer.Sparse Key := [(key706, -288), (key722, 288), (key860, 288), (key922, -288)]

def entry17_2 : Integer.Sparse Key := [(key1990, -288), (key2007, 288), (key2235, 288), (key2300, -288)]

def entry17_3 : Integer.Sparse Key := [(key2029, 288), (key2059, -288), (key2148, -288), (key2241, 288)]

def entry17_4 : Integer.Sparse Key := [(key706, -288), (key715, 288), (key860, 288), (key892, -288)]

def entry17_5 : Integer.Sparse Key := [(key705, -144), (key710, 144), (key714, 144), (key718, -144), (key859, 144), (key886, 144), (key891, -144), (key895, -144), (key916, -288), (key948, 144), (key955, 144)]

def entry17_6 : Integer.Sparse Key := [(key2027, 72), (key2033, -72), (key2057, -72), (key2063, 144), (key2069, -72), (key2092, -72), (key2095, 72), (key2146, -72), (key2152, -72), (key2166, -144), (key2194, 144), (key2200, 144), (key2239, 72), (key2246, 72), (key2253, 144), (key2303, -72), (key2305, -72), (key2310, -144)]

def entry17_7 : Integer.Sparse Key := [(key2120, 288), (key2160, -576), (key2249, 288)]

def entry17_8 : Integer.Sparse Key := [(key1990, -288), (key2000, 288), (key2235, 288), (key2269, -288)]

def entry17_9 : Integer.Sparse Key := [(key779, 288), (key804, -576), (key873, 288)]

def entry17_10 : Integer.Sparse Key := [(key2028, 72), (key2033, -72), (key2058, -72), (key2063, 144), (key2069, -72), (key2079, -72), (key2085, 72), (key2147, -72), (key2152, -72), (key2166, -144), (key2176, 144), (key2187, 144), (key2240, 72), (key2246, 72), (key2253, 144), (key2276, -72), (key2279, -72), (key2287, -144)]

def entry17_11 : Integer.Sparse Key := [(key360, 48), (key362, -72), (key366, 152), (key529, -24), (key531, 96), (key537, -144), (key676, 16), (key731, -48), (key733, -216), (key750, 136), (key865, 24), (key867, 192), (key927, -144), (key938, -16)]

def entry17_12 : Integer.Sparse Key := [(key1989, 72), (key1994, 216), (key1999, -72), (key2003, -216), (key2234, -72), (key2259, 72), (key2268, 72), (key2272, -216), (key2294, -144), (key2324, 216), (key2336, 72)]

def entry17_13 : Integer.Sparse Key := [(key2027, 144), (key2033, 144), (key2057, -144), (key2063, -72), (key2069, -72), (key2092, -72), (key2095, 72), (key2146, -144), (key2152, -72), (key2166, -72), (key2194, -72), (key2200, 72), (key2239, 144), (key2246, 72), (key2253, 72), (key2303, 144), (key2305, -72), (key2310, -72)]

def entry17_14 : Integer.Sparse Key := [(key2063, -216), (key2069, -72), (key2092, 216), (key2095, 72), (key2152, 216), (key2166, 72), (key2194, -216), (key2200, -72), (key2246, 72), (key2253, -72), (key2305, -72), (key2310, 72)]

def entry17_15 : Integer.Sparse Key := [(key2063, -216), (key2069, -72), (key2079, 216), (key2085, 72), (key2152, 216), (key2166, 72), (key2176, -216), (key2187, -72), (key2246, 72), (key2253, -72), (key2279, -72), (key2287, 72)]

def entry17_16 : Integer.Sparse Key := [(key2032, -72), (key2037, 72), (key2062, -72), (key2072, 72), (key2078, 144), (key2082, -72), (key2087, -72), (key2151, 144), (key2169, 144), (key2175, -72), (key2179, -72), (key2189, -144), (key2275, -72), (key2281, -72), (key2289, -144), (key2328, 72), (key2330, 72), (key2333, 144)]

def entry17_17 : Integer.Sparse Key := [(key776, 144), (key778, 144), (key801, -288), (key803, -144), (key811, -320), (key836, 32), (key839, 144), (key871, 144), (key876, 240), (key931, 48), (key934, -144)]

def entry18_0 : Integer.Sparse Key := [(key1976, -288), (key1981, 288), (key1983, 288), (key1997, -288)]

def entry18_1 : Integer.Sparse Key := [(key54, 96), (key56, 96), (key63, -288), (key122, -84), (key128, 96), (key198, -48), (key199, 84), (key693, 48), (key697, 48), (key845, -60), (key848, -96), (key854, 48), (key855, 60)]

def entry18_2 : Integer.Sparse Key := [(key1973, 144), (key1978, 144), (key1985, -288), (key2209, -144), (key2215, -144), (key2226, 144), (key2230, 144)]

def entry18_3 : Integer.Sparse Key := [(key2015, -288), (key2044, 144), (key2045, 144), (key2129, 144), (key2132, 144), (key2212, -144), (key2213, -144)]

def entry18_4 : Integer.Sparse Key := [(key694, 144), (key696, 144), (key699, -288), (key846, -144), (key847, -144), (key850, 144), (key852, 144)]

def entry18_5 : Integer.Sparse Key := [(key58, -96), (key65, 168), (key68, 96), (key82, -168), (key695, -192), (key698, 120), (key700, 192), (key712, -120)]

def entry18_6 : Integer.Sparse Key := [(key2013, 144), (key2019, 144), (key2026, -288), (key2042, -144), (key2047, -144), (key2055, 144), (key2056, 144)]

def entry18_7 : Integer.Sparse Key := [(key2103, -288), (key2108, 288), (key2109, 288), (key2131, -288)]

def entry18_8 : Integer.Sparse Key := [(key1974, 144), (key1977, 144), (key1982, -288), (key2210, -144), (key2214, -144), (key2219, 144), (key2223, 144)]

def entry18_9 : Integer.Sparse Key := [(key758, -288), (key762, 288), (key764, 288), (key789, -288)]

def entry18_10 : Integer.Sparse Key := [(key2014, 144), (key2018, 144), (key2023, -288), (key2043, -144), (key2046, -144), (key2051, 144), (key2052, 144)]

def entry18_11 : Integer.Sparse Key := [(key357, 144), (key359, 144), (key365, -288), (key527, -144), (key535, 144), (key674, -144), (key675, 144)]

def entry18_12 : Integer.Sparse Key := [(key1976, -288), (key1981, 144), (key1983, 144), (key2218, 144), (key2224, 144), (key2262, -144), (key2266, -144)]

def entry18_13 : Integer.Sparse Key := [(key2026, -288), (key2055, 144), (key2056, 144), (key2144, 144), (key2145, 144), (key2228, -144), (key2229, -144)]

def entry18_14 : Integer.Sparse Key := [(key2042, 144), (key2047, 144), (key2055, -144), (key2056, -144), (key2127, -144), (key2134, -144), (key2144, 144), (key2145, 144)]

def entry18_15 : Integer.Sparse Key := [(key2043, 144), (key2046, 144), (key2051, -144), (key2052, -144), (key2128, -144), (key2133, -144), (key2138, 144), (key2141, 144)]

def entry18_16 : Integer.Sparse Key := [(key2017, -288), (key2022, 144), (key2024, 144), (key2050, 144), (key2053, 144), (key2075, -144), (key2076, -144)]

def entry18_17 : Integer.Sparse Key := [(key783, -288), (key808, 288), (key837, 288), (key932, -288)]

def entry18_18 : Integer.Sparse Key := [(key757, 144), (key759, 144), (key761, -144), (key766, -160), (key768, -128), (key769, -144), (key793, 288)]

def entry19_0 : Integer.Sparse Key := [(key1854, 288), (key1856, -576), (key1858, 288)]

def entry19_1 : Integer.Sparse Key := [(key620, -288), (key624, 288), (key646, 288), (key652, -288)]

def entry19_2 : Integer.Sparse Key := [(key1853, -288), (key1857, 288), (key1885, 288), (key1888, -288)]

def entry19_3 : Integer.Sparse Key := [(key1959, 288), (key1961, -288), (key1967, -288), (key1970, 288)]

def entry19_4 : Integer.Sparse Key := [(key665, -288), (key666, 288), (key682, 288), (key683, -288)]

def entry19_5 : Integer.Sparse Key := [(key621, 288), (key623, -576), (key625, 288)]

def entry19_6 : Integer.Sparse Key := [(key1862, -288), (key1866, 288), (key1868, 288), (key1871, -288)]

def entry19_7 : Integer.Sparse Key := [(key1963, 288), (key1965, -576), (key1968, 288)]

def entry19_8 : Integer.Sparse Key := [(key1934, -288), (key1935, 288), (key1954, 288), (key1955, -288)]

def entry19_9 : Integer.Sparse Key := [(key688, 288), (key689, -576), (key691, 288)]

def entry19_10 : Integer.Sparse Key := [(key1938, -288), (key1939, 288), (key1941, 288), (key1942, -288)]

def entry19_11 : Integer.Sparse Key := [(key517, -288), (key524, 288), (key549, 288), (key555, -288)]

def entry19_12 : Integer.Sparse Key := [(key1854, 288), (key1856, -288), (key1887, -288), (key1890, 288)]

def entry19_13 : Integer.Sparse Key := [(key1866, 288), (key1871, -288), (key1881, -288), (key1889, 288)]

def entry19_14 : Integer.Sparse Key := [(key1868, -288), (key1871, 288), (key1878, 288), (key1881, -288)]

def entry19_15 : Integer.Sparse Key := [(key1941, -288), (key1942, 288), (key1950, 288), (key1951, -288)]

def entry19_16 : Integer.Sparse Key := [(key1863, 288), (key1865, -288), (key1870, -288), (key1872, 288)]

def entry19_17 : Integer.Sparse Key := [(key536, 288), (key544, -576), (key556, 288)]

def entry19_18 : Integer.Sparse Key := [(key633, -288), (key635, 288), (key638, 288), (key644, -288)]

def entry19_19 : Integer.Sparse Key := [(key291, 288), (key294, -576), (key298, 288)]

def entry20_0 : Integer.Sparse Key := [(key1992, -144), (key1995, 144), (key2002, 144), (key2004, -144), (key2237, 144), (key2260, 144), (key2271, -144), (key2273, -144), (key2295, -288), (key2325, 144), (key2337, 144)]

def entry20_1 : Integer.Sparse Key := [(key60, 40), (key62, -72), (key72, 152), (key125, -24), (key127, 96), (key135, -144), (key180, 16), (key704, -40), (key709, -216), (key723, 136), (key858, 24), (key863, 192), (key923, -144), (key940, -16)]

def entry20_2 : Integer.Sparse Key := [(key1993, -288), (key2008, 288), (key2238, 288), (key2301, -288)]

def entry20_3 : Integer.Sparse Key := [(key2030, 288), (key2060, -288), (key2149, -288), (key2242, 288)]

def entry20_4 : Integer.Sparse Key := [(key707, -288), (key716, 288), (key861, 288), (key893, -288)]

def entry20_5 : Integer.Sparse Key := [(key78, 48), (key191, 16), (key708, -144), (key711, 144), (key717, 96), (key719, -144), (key862, 144), (key887, 144), (key894, -144), (key896, -144), (key917, -288), (key949, 144), (key956, 128)]

def entry20_6 : Integer.Sparse Key := [(key2031, 72), (key2036, -72), (key2061, -72), (key2066, 144), (key2071, -72), (key2093, -72), (key2096, 72), (key2150, -72), (key2155, -72), (key2168, -144), (key2195, 144), (key2201, 144), (key2243, 72), (key2248, 72), (key2255, 144), (key2304, -72), (key2306, -72), (key2311, -144)]

def entry20_7 : Integer.Sparse Key := [(key2121, 288), (key2161, -576), (key2250, 288)]

def entry20_8 : Integer.Sparse Key := [(key1991, -288), (key2001, 288), (key2236, 288), (key2270, -288)]

def entry20_9 : Integer.Sparse Key := [(key780, 288), (key805, -576), (key874, 288)]

def entry20_10 : Integer.Sparse Key := [(key2031, 72), (key2034, -72), (key2061, -72), (key2064, 144), (key2070, -72), (key2080, -72), (key2086, 72), (key2150, -72), (key2153, -72), (key2167, -144), (key2177, 144), (key2188, 144), (key2243, 72), (key2247, 72), (key2254, 144), (key2277, -72), (key2280, -72), (key2288, -144)]

def entry20_11 : Integer.Sparse Key := [(key364, -288), (key368, 288), (key534, 288), (key540, -288)]

def entry20_12 : Integer.Sparse Key := [(key1992, 72), (key1995, 216), (key2002, -72), (key2004, -216), (key2237, -72), (key2260, 72), (key2271, 72), (key2273, -216), (key2295, -144), (key2325, 216), (key2337, 72)]

def entry20_13 : Integer.Sparse Key := [(key2031, 144), (key2036, 144), (key2061, -144), (key2066, -72), (key2071, -72), (key2093, -72), (key2096, 72), (key2150, -144), (key2155, -72), (key2168, -72), (key2195, -72), (key2201, 72), (key2243, 144), (key2248, 72), (key2255, 72), (key2304, 144), (key2306, -72), (key2311, -72)]

def entry20_14 : Integer.Sparse Key := [(key2066, -216), (key2071, -72), (key2093, 216), (key2096, 72), (key2155, 216), (key2168, 72), (key2195, -216), (key2201, -72), (key2248, 72), (key2255, -72), (key2306, -72), (key2311, 72)]

def entry20_15 : Integer.Sparse Key := [(key2064, -216), (key2070, -72), (key2080, 216), (key2086, 72), (key2153, 216), (key2167, 72), (key2177, -216), (key2188, -72), (key2247, 72), (key2254, -72), (key2280, -72), (key2288, 72)]

def entry20_16 : Integer.Sparse Key := [(key2035, -72), (key2038, 72), (key2065, -72), (key2073, 72), (key2081, 144), (key2083, -72), (key2088, -72), (key2154, 144), (key2170, 144), (key2178, -72), (key2180, -72), (key2190, -144), (key2278, -72), (key2282, -72), (key2290, -144), (key2329, 72), (key2331, 72), (key2334, 144)]

def entry20_17 : Integer.Sparse Key := [(key777, 144), (key782, 144), (key802, -288), (key807, -144), (key812, -144), (key821, -144), (key824, 144), (key872, 144), (key877, 144), (key905, 144), (key907, -144)]

def entry20_18 : Integer.Sparse Key := [(key763, 48), (key765, 40), (key767, -48), (key773, -48), (key775, -40), (key785, -240), (key788, -24), (key790, -24), (key791, 72), (key792, 88), (key800, 24), (key810, 216), (key835, 24), (key838, 200), (key851, -96), (key933, -192)]

def entry20_19 : Integer.Sparse Key := [(key637, 288), (key643, -576), (key651, 288)]

def entry20_20 : Integer.Sparse Key := [(key781, 144), (key784, 144), (key806, -288), (key809, -144), (key814, -320), (key822, 32), (key827, 144), (key875, 144), (key879, 240), (key906, 48), (key910, -144)]

def entry21_0 : Integer.Sparse Key := [(key2421, -288), (key2428, 288), (key2429, 288), (key2442, -288)]

def entry21_1 : Integer.Sparse Key := [(key1049, 144), (key1052, 144), (key1060, -288), (key1135, -144), (key1140, 144), (key1205, -144), (key1207, 144)]

def entry21_2 : Integer.Sparse Key := [(key2415, 144), (key2418, 144), (key2425, -288), (key2488, -144), (key2493, 144), (key2547, -144), (key2549, 144)]

def entry21_3 : Integer.Sparse Key := [(key3046, -288), (key3060, 144), (key3064, 144), (key3095, 144), (key3101, 144), (key3123, -144), (key3125, -144)]

def entry21_4 : Integer.Sparse Key := [(key1048, 144), (key1051, 144), (key1059, -288), (key1134, -144), (key1139, 144), (key1204, -144), (key1206, 144)]

def entry21_5 : Integer.Sparse Key := [(key1056, -288), (key1064, 288), (key1065, 288), (key1079, -288)]

def entry21_6 : Integer.Sparse Key := [(key2680, 144), (key2683, 144), (key2690, -288), (key2711, -144), (key2716, 144), (key2741, -144), (key2743, 144)]

def entry21_7 : Integer.Sparse Key := [(key3080, -288), (key3085, 288), (key3087, 288), (key3100, -288)]

def entry21_8 : Integer.Sparse Key := [(key2414, 96), (key2417, 96), (key2424, -288), (key2487, -84), (key2492, 96), (key2546, -48), (key2548, 84), (key3033, 48), (key3035, 48), (key3120, -60), (key3128, -96), (key3131, 48), (key3138, 60)]

def entry21_9 : Integer.Sparse Key := [(key2101, -288), (key2106, 288), (key2111, 288), (key2139, -288)]

def entry21_10 : Integer.Sparse Key := [(key2679, 48), (key2682, 36), (key2689, -196), (key2710, -84), (key2715, 96), (key2740, -48), (key2742, 84), (key2813, 8), (key2818, -12), (key2955, -8), (key3047, 96), (key3050, 108), (key3054, -92), (key3061, -60), (key3066, -96), (key3069, 48), (key3072, 60), (key3096, -8), (key3106, 12), (key3110, 8)]

def entry21_11 : Integer.Sparse Key := [(key1500, 144), (key1503, 144), (key1507, -288), (key1732, -144), (key1736, 144), (key1874, -144), (key1875, 144)]

def entry21_12 : Integer.Sparse Key := [(key2421, -288), (key2428, 144), (key2429, 144), (key2496, 144), (key2508, -144), (key2550, 144), (key2556, -144)]

def entry21_13 : Integer.Sparse Key := [(key2690, -288), (key2716, 144), (key2743, 144), (key2819, 144), (key2901, -144), (key2956, 144), (key2980, -144)]

def entry21_14 : Integer.Sparse Key := [(key2711, 144), (key2716, -144), (key2741, 144), (key2743, -144), (key2814, -144), (key2819, 144), (key2954, -144), (key2956, 144)]

def entry21_15 : Integer.Sparse Key := [(key2679, 24), (key2682, 36), (key2689, -32), (key2710, 120), (key2715, -120), (key2740, 72), (key2742, -120), (key2813, -92), (key2818, 108), (key2953, -48), (key2955, 92), (key3047, -24), (key3050, -36), (key3054, 32), (key3061, 24), (key3066, 72), (key3069, -24), (key3072, -24), (key3096, -52), (key3103, -96), (key3106, 36), (key3110, 52)]

def entry21_16 : Integer.Sparse Key := [(key2686, -288), (key2693, 144), (key2694, 144), (key2719, 144), (key2731, -144), (key2744, 144), (key2750, -144)]

def entry21_17 : Integer.Sparse Key := [(key2122, -288), (key2162, 288), (key2185, 288), (key2285, -288)]

def entry21_18 : Integer.Sparse Key := [(key2102, 144), (key2104, 144), (key2107, -144), (key2110, -144), (key2112, -144), (key2113, -144), (key2140, 288)]

def entry21_19 : Integer.Sparse Key := [(key1945, -288), (key1947, 288), (key1948, 288), (key1952, -288)]

def entry21_20 : Integer.Sparse Key := [(key2123, -288), (key2163, 288), (key2186, 288), (key2286, -288)]

def entry21_21 : Integer.Sparse Key := [(key3081, 144), (key3082, 144), (key3086, -144), (key3088, -160), (key3090, -128), (key3091, -144), (key3109, 288)]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization

def entry10_1 : Integer.Sparse Key := [(key222, 2880), (key494, 8640), (key548, 2880)]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13187 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

def row13188 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

def row13189 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

def row13190 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13191 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13192 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13193 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13194 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13195 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13196 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13197 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13198 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13199 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13200 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13201 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13202 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

def row13203 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

def row13204 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13593 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13594 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13595 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13596 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13597 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13598 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13599 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

def row13600 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

def row13601 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

def row13602 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13603 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13604 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13605 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13606 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13607 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13608 : Integer.Sparse Key := [(key2390, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2929, 4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13609 : Integer.Sparse Key := [(key2390, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2929, 4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13610 : Integer.Sparse Key := [(key2437, 4), (key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13611 : Integer.Sparse Key := [(key2437, 4), (key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13612 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2580, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4)]

def row13613 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2580, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4)]

def row13620 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

def row13621 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

def row13622 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

def row13629 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13630 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13631 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13632 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13633 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13634 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13635 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13636 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13637 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13638 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13639 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13640 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13641 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13642 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13643 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13644 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13645 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13646 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13647 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13648 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13649 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13656 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13657 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13658 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13665 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13666 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13667 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13668 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13669 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13670 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13671 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

def row13672 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

def row13673 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

def row13674 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13675 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13676 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13677 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13678 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13679 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13680 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3005, 2), (key3028, 2)]

def row13681 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3005, 2), (key3028, 2)]

def row13682 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, -4), (key2604, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3028, 2)]

def row13683 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, -4), (key2604, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3028, 2)]

def row13684 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4)]

def row13685 : Integer.Sparse Key := [(key2388, 2), (key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2583, 2), (key2589, -4), (key2768, -4), (key2845, 6), (key2876, -4)]

def row13692 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

def row13693 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

def row13694 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13701 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13702 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13703 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13704 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13705 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13706 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13707 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13708 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13709 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13710 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13711 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13712 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13713 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13714 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13715 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13716 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13717 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13718 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13719 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13720 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13721 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13728 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13729 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13730 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13737 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13738 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13739 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13740 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13741 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13742 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13743 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13744 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13745 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13746 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13747 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13748 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13749 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13750 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13751 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13752 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13753 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13754 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13755 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13756 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13757 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13764 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13765 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13766 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13773 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13774 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13775 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13776 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13777 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13778 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13779 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13780 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13781 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13782 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13783 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13784 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13785 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13786 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13787 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13788 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13789 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13790 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13791 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13792 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13793 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13800 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13801 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13802 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13809 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13810 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13811 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13812 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13813 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13814 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13815 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

def row13816 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

def row13817 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

def row13818 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13819 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13820 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13821 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13822 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13823 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13824 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13825 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13826 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 4), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13827 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 4), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13828 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13829 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13836 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

def row13837 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

def row13838 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14205 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14206 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14207 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14208 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14209 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14210 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14211 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14212 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14213 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14214 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14215 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14216 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14217 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14218 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14219 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14220 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14221 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14222 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14223 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14224 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14225 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14226 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14227 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14228 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14229 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14230 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14231 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14232 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14233 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14234 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14235 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14236 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14237 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14238 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14239 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14240 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14241 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14242 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14243 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14244 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14245 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14246 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14247 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14248 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14249 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14250 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14251 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14252 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14253 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14254 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14255 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14256 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14257 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14258 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14259 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14260 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14261 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14262 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14263 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14264 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14265 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14266 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14267 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14268 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14269 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14270 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14271 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14272 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14273 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14274 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14275 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14276 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14277 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14278 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14279 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14280 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14281 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14282 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14283 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14284 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14285 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14286 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14287 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14288 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14289 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14290 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14291 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14292 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14293 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14294 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14295 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14296 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14297 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14298 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14299 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14300 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14301 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14302 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14303 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14304 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14305 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14306 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14307 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14308 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14309 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14310 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14311 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14312 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14313 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14314 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14315 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14316 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14317 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14318 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14319 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14320 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14321 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14322 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14323 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14324 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14325 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14326 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14327 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14328 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14329 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14330 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14331 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14332 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14333 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14334 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14335 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14336 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14337 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14338 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14339 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14340 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14341 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14342 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14343 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14344 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14345 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14346 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14347 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14348 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14349 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14350 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14351 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14352 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14353 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14354 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14355 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14356 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14357 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14358 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14359 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14360 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14361 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14362 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14363 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14364 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14365 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14366 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14367 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14368 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14369 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14370 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14371 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14372 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14373 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14374 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14375 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14376 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14377 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14378 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14379 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14380 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14381 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14382 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14383 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14384 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14385 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14386 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14387 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14388 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14389 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14390 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14391 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14392 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14393 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14394 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14395 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14396 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14397 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14398 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14399 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14400 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14401 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14402 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14403 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14404 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14405 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14406 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14407 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14408 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14409 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14410 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14411 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14412 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14413 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14414 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14415 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14416 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14417 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14418 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14419 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14420 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14421 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14422 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14423 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14424 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14425 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14426 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14427 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14428 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14429 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14430 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14431 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14432 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14433 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14434 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14435 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14436 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14437 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14438 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14439 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14440 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14441 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14442 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14443 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14444 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14445 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14446 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14447 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14448 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14449 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14450 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14451 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14452 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14453 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14454 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14455 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14456 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14457 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14458 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14459 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14460 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14461 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14462 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14463 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14464 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14465 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14466 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14467 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14468 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14469 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14470 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14471 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14472 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14473 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14474 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14475 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14476 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14477 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14478 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14479 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14480 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14481 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14482 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14483 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14484 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14485 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14486 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14487 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14488 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14489 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14490 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14491 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14492 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14493 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14494 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14495 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14496 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14497 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14498 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14499 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

def row14500 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

def row14501 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

def row14502 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14503 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14504 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14505 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14506 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14507 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14508 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2928, 2), (key2987, 2)]

def row14509 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2928, 2), (key2987, 2)]

def row14510 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, -4), (key2597, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2987, 2)]

def row14511 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, -4), (key2597, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2987, 2)]

def row14512 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4)]

def row14513 : Integer.Sparse Key := [(key2386, 2), (key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2583, 2), (key2586, -4), (key2765, -4), (key2842, 6), (key2874, -4)]

def row14514 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14515 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14516 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14517 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14518 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 4), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2842, -2), (key2874, 6)]

def row14519 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 4), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2842, -2), (key2874, 6)]

def row14520 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

def row14521 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

def row14522 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

def row14523 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2), (key2839, -2)]

def row14524 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2), (key2839, -2)]

def row14525 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2), (key2839, -2)]

def row14526 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2), (key2839, -2)]

def row14527 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 4), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2)]

def row14528 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 4), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2)]

def row14529 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14530 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14531 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14532 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14533 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14534 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14535 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14536 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14537 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14538 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14539 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14540 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14541 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14542 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14543 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14544 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14545 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14546 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14547 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14548 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14549 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14550 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14551 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14552 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14553 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14554 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14555 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14556 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14557 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14558 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14559 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14560 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14561 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14562 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14563 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14564 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14565 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14566 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14567 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14568 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14569 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14570 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14571 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

def row14572 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

def row14573 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

def row14574 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14575 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14576 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14577 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14578 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14579 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14580 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14581 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14582 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 4), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14583 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 4), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14584 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14585 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14586 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14587 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14588 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14589 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14590 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14591 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14592 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

def row14593 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

def row14594 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

def row14595 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14596 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14597 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14598 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14599 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14600 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14601 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14602 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14603 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14604 : Integer.Sparse Key := [(key1700, -12), (key1706, 12), (key1851, 12), (key1855, -12)]

def row14605 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14606 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14607 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14608 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14609 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14610 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14611 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14612 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14613 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14614 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14615 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14616 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14617 : Integer.Sparse Key := [(key1700, -12), (key1706, 12), (key1851, 12), (key1855, -12)]

def row14618 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14619 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14620 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14621 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14622 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14623 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14624 : Integer.Sparse Key := [(key220, 6), (key225, -6), (key492, -6), (key497, 12), (key551, -6), (key664, -6), (key681, 6)]

def row14625 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14626 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14627 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14628 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14629 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14630 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14631 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14632 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14633 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14634 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14635 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14636 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14637 : Integer.Sparse Key := [(key220, 6), (key225, -6), (key492, -6), (key497, 12), (key551, -6), (key664, -6), (key681, 6)]

def row14638 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14639 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14640 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14641 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14642 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14643 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14644 : Integer.Sparse Key := [(key1273, 6), (key1278, -6), (key1696, -6), (key1701, 12), (key1751, -6), (key1933, -6), (key1953, 6)]

def row14645 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14646 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14647 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14648 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14649 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14650 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14651 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14652 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14653 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14654 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14655 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14656 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14657 : Integer.Sparse Key := [(key1273, 6), (key1278, -6), (key1696, -6), (key1701, 12), (key1751, -6), (key1933, -6), (key1953, 6)]

def row14658 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14659 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14660 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14661 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14662 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14663 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14664 : Integer.Sparse Key := [(key1360, -6), (key1372, 6), (key1486, -6), (key1511, 6), (key1712, 12), (key1721, -6), (key1739, -6)]

def row14665 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14666 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14667 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14668 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14669 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14670 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14671 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14672 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14673 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14674 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14675 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14676 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14677 : Integer.Sparse Key := [(key1360, -6), (key1372, 6), (key1486, -6), (key1511, 6), (key1712, 12), (key1721, -6), (key1739, -6)]

def row14678 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14679 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14680 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14681 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14682 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14683 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14684 : Integer.Sparse Key := [(key221, 6), (key225, -6), (key493, -6), (key497, 12), (key551, -6), (key619, -6), (key645, 6)]

def row14685 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14686 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14687 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14688 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14689 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14690 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14691 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14692 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14693 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14694 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14695 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14696 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14697 : Integer.Sparse Key := [(key221, 6), (key225, -6), (key493, -6), (key497, 12), (key551, -6), (key619, -6), (key645, 6)]

def row14698 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14699 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14700 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14701 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14702 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14703 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14704 : Integer.Sparse Key := [(key496, -12), (key502, 12), (key618, 12), (key622, -12)]

def row14705 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14706 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14707 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14708 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14709 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14710 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14711 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14712 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14713 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14714 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14715 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14716 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14717 : Integer.Sparse Key := [(key496, -12), (key502, 12), (key618, 12), (key622, -12)]

def row14718 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14719 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14720 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14721 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14722 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14723 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14724 : Integer.Sparse Key := [(key1484, 6), (key1490, -6), (key1710, -6), (key1716, 12), (key1723, -6), (key1937, -6), (key1940, 6)]

def row14725 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14726 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14727 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14728 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14729 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14730 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14731 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14732 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14733 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14734 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14735 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14736 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14737 : Integer.Sparse Key := [(key1484, 6), (key1490, -6), (key1710, -6), (key1716, 12), (key1723, -6), (key1937, -6), (key1940, 6)]

def row14738 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14739 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14740 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14741 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14742 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14743 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14744 : Integer.Sparse Key := [(key1501, -12), (key1506, 12), (key1733, 12), (key1735, -12)]

def row14745 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14746 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14747 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14748 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14749 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14750 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14751 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14752 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14753 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14754 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14755 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14756 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14757 : Integer.Sparse Key := [(key1501, -12), (key1506, 12), (key1733, 12), (key1735, -12)]

def row14758 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14759 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14760 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14761 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14762 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14763 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14764 : Integer.Sparse Key := [(key1274, 6), (key1278, -6), (key1697, -6), (key1701, 12), (key1751, -6), (key1852, -6), (key1884, 6)]

def row14765 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14766 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14767 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14768 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14769 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14770 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14771 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14772 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14773 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14774 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14775 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14776 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14777 : Integer.Sparse Key := [(key1274, 6), (key1278, -6), (key1697, -6), (key1701, 12), (key1751, -6), (key1852, -6), (key1884, 6)]

def row14778 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14779 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14780 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14781 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14782 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14783 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14784 : Integer.Sparse Key := [(key358, -12), (key363, 12), (key528, 12), (key532, -12)]

def row14785 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14786 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14787 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14788 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14789 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14790 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14791 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14792 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14793 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14794 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14795 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14796 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14797 : Integer.Sparse Key := [(key358, -12), (key363, 12), (key528, 12), (key532, -12)]

def row14798 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14799 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14800 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14801 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14802 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14803 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14804 : Integer.Sparse Key := [(key1485, 6), (key1490, -6), (key1711, -6), (key1716, 12), (key1723, -6), (key1861, -6), (key1867, 6)]

def row14805 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14806 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14807 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14808 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14809 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14810 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14811 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14812 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14813 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14814 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14815 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14816 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14817 : Integer.Sparse Key := [(key1485, 6), (key1490, -6), (key1711, -6), (key1716, 12), (key1723, -6), (key1861, -6), (key1867, 6)]

def row14818 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14819 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14820 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14821 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14822 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14823 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14824 : Integer.Sparse Key := [(key288, 6), (key289, -6), (key513, -6), (key515, 12), (key547, -6), (key670, -6), (key680, 6)]

def row14825 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14826 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14827 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14828 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14829 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14830 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -4), (key680, 2)]

def row14831 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -4), (key680, 2)]

def row14832 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14833 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14834 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14835 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14836 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14837 : Integer.Sparse Key := [(key288, 6), (key289, -6), (key513, -6), (key515, 12), (key547, -6), (key670, -6), (key680, 6)]

def row14838 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14839 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14840 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14841 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14842 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14843 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14844 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

def row14845 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

def row14846 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

def row14847 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14848 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14849 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14850 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

def row14851 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

def row14852 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

def row14853 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14854 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14855 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14856 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14857 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14858 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14859 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14860 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14861 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14862 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14863 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14864 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14865 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14866 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14867 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14868 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14869 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14870 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14871 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14872 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14873 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14874 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14875 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14876 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14877 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

def row14878 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

def row14879 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

def row14880 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

def row14881 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

def row14882 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

def row14883 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

def row14884 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

def row14885 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

def row14886 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

def row14887 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

def row14888 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

def row14889 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14890 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14891 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14892 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14893 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14894 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14895 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

def row14896 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

def row14897 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

def row14898 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14899 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14900 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14901 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14902 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14903 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14904 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

def row14905 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

def row14906 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

def row14907 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14908 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14909 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14910 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14911 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14912 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14913 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14914 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14915 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14916 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14917 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14918 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14919 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14920 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14921 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14922 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14923 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14924 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14925 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14926 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14927 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14928 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14929 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14930 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14931 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

def row14932 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

def row14933 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

def row14934 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14935 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14936 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14937 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14938 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14939 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14940 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14941 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14942 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14943 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14944 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14945 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14946 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14947 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14948 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14949 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14950 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14951 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14952 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14953 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14954 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14955 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14956 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14957 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14958 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

def row14959 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

def row14960 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

def row14961 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14962 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14963 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14964 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14965 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14966 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14967 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14968 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14969 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14970 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14971 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14972 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14973 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14974 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14975 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14976 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14977 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14978 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14979 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14980 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14981 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14982 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14983 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14984 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14985 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

def row14986 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

def row14987 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

def row14988 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

def row14989 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

def row14990 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

def row14991 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

def row14992 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

def row14993 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

def row14994 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

def row14995 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

def row14996 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

def row14997 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row14998 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row14999 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15000 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15001 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15002 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15003 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

def row15004 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

def row15005 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

def row15006 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15007 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15008 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15009 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15010 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15011 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15012 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

def row15013 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

def row15014 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

def row15015 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15016 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15017 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15018 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15019 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15020 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15021 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15022 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15023 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15024 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15025 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15026 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15027 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15028 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15029 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15030 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15031 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15032 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15033 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15034 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15035 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15036 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15037 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15038 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15039 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

def row15040 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

def row15041 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

def row15042 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15043 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15044 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15045 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15046 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15047 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15048 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15049 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15050 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15051 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15052 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15053 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15054 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15055 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15056 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15057 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15058 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15059 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15060 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15061 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15062 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15063 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15064 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15065 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15066 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

def row15067 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

def row15068 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

def row15069 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15070 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15071 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15072 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15073 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15074 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15075 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15076 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15077 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15078 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15079 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15080 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15081 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15082 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15083 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15084 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15085 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15086 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15087 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15088 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15089 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15090 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15091 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15092 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15093 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

def row15094 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

def row15095 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

def row15096 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15097 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15098 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15099 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15100 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15101 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15102 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15103 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15104 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15105 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15106 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15107 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15108 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15109 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15110 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15111 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15112 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15113 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15114 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15115 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15116 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15117 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15118 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15119 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15120 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

def row15121 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

def row15122 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

def row15123 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15124 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15125 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15126 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15127 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15128 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15129 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15130 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15131 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15132 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15133 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15134 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15135 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15136 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15137 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15138 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15139 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15140 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15141 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15142 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15143 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15144 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15145 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15146 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15147 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

def row15148 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

def row15149 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

def row15150 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

def row15151 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

def row15152 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

def row15153 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

def row15154 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

def row15155 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

def row15156 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

def row15157 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

def row15158 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

def row15159 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15160 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15161 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2525, -1), (key2532, 2), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15162 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2525, -1), (key2532, 2), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15163 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15164 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15165 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

def row15166 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

def row15167 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

def row15168 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15169 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15170 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 2), (key2525, 1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15171 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 2), (key2525, 1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15172 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15173 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15174 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

def row15175 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

def row15176 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

def row15177 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15178 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15179 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15180 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15181 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15182 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15183 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15184 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15185 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15186 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15187 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15188 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15189 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15190 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15191 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15192 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15193 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15194 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15195 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15196 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15197 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15198 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15199 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15200 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15201 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15202 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15203 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15204 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15205 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15206 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15207 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15208 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15209 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15210 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15211 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15212 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15213 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

def row15214 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

def row15215 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

def row15216 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15217 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15218 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15219 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15220 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15221 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15222 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

def row15223 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

def row15224 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

def row15225 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15226 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15227 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15228 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15229 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15230 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15231 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15232 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15233 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15234 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15235 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15236 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15237 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15238 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15239 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15240 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15241 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15242 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15243 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15244 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15245 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15246 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15247 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15248 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15249 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15250 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15251 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15252 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15253 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15254 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15255 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15256 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15257 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15258 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15259 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15260 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15261 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15262 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15263 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15264 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15265 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15266 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15267 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15268 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15269 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15270 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15271 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15272 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15273 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15274 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15275 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15276 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15277 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15278 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15279 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15280 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15281 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15282 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15283 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15284 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15285 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15286 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15287 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15288 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15289 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15290 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15291 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15292 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15293 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15294 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15295 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15296 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15297 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15298 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15299 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15300 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15301 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15302 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15303 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15304 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15305 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15306 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15307 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15308 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15309 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15310 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15311 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15312 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15313 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15314 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15315 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15316 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15317 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15318 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15319 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15320 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15321 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15322 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15323 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15324 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15325 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15326 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15327 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15328 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15329 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15330 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15331 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15332 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15333 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15334 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15335 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15336 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15337 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15338 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15339 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15340 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15341 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15342 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15343 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15344 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15345 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15346 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15347 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15348 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15349 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15350 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15351 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15352 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15353 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15354 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15355 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15356 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15357 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15358 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15359 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15360 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15361 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15362 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15363 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15364 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15365 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15366 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15367 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15368 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15369 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15370 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15371 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15372 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15373 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15374 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15375 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15376 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15377 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15378 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15379 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15380 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15381 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15382 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15383 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15384 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15385 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15386 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15387 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15388 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15389 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15390 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15391 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15392 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15393 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15394 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15395 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15396 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15397 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15398 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15399 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15400 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15401 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15402 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15403 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15404 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15405 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15406 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15407 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15408 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15409 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15410 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15411 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15412 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15413 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15414 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15415 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15416 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15417 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15418 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15419 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15420 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15421 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15422 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15423 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15424 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15425 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15426 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15427 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15428 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15429 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15430 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15431 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15432 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15433 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15434 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15435 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15436 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15437 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15438 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15439 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15440 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15441 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15442 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15443 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15444 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15445 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15446 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15447 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15448 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15449 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15450 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15451 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15452 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15453 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15454 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15455 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15456 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15457 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15458 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15459 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15460 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15461 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15462 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15463 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15464 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15465 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15466 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15467 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15468 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15469 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15470 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15471 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15472 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15473 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15474 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15475 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15476 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15477 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15478 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15479 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15480 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15481 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15482 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15483 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15484 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15485 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15486 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15487 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15488 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15489 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15490 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15491 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15492 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15493 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15494 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15495 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15496 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15497 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15498 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15499 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15500 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15501 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15502 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15503 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15504 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15505 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15506 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15507 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15508 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15509 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15510 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15511 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15512 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15513 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15514 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15515 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15516 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15517 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15518 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15519 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15520 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15521 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15522 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15523 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15524 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15525 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15526 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15527 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15528 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15529 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15530 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15531 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15532 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15533 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15534 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15535 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15536 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15537 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15538 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15539 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15540 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15541 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15542 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15543 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15544 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15545 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15546 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15547 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15548 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15549 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15550 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15551 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 4), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15552 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 4), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15553 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15554 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15555 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

def row15556 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

def row15557 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

def row15558 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

def row15559 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

def row15560 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

def row15561 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15562 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15563 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15564 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15565 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15566 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15567 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

def row15568 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

def row15569 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

def row15570 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

def row15571 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

def row15572 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

def row15573 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15574 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15575 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15576 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15577 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15578 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15579 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15580 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15581 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15582 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15583 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15584 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15585 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15586 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15587 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15588 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15589 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15590 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15591 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

def row15592 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

def row15593 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

def row15594 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

def row15595 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

def row15596 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

def row15597 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15598 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15599 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15600 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15601 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15602 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15603 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15604 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15605 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15606 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15607 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15608 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15609 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15610 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15611 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15612 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15613 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15614 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15615 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15616 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15617 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15618 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15619 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15620 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15621 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15622 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15623 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15624 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15625 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15626 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15627 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15628 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15629 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15630 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15631 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15632 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15633 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15634 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15635 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15636 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15637 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15638 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15639 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15640 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15641 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15642 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15643 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15644 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15645 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15646 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15647 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15648 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15649 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15650 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15651 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15652 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15653 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15654 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15655 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15656 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15657 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

def row15658 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

def row15659 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

def row15660 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

def row15661 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

def row15662 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

def row15663 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

def row15664 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

def row15665 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

def row15666 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

def row15667 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

def row15668 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

def row15669 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

def row15670 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

def row15671 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

def row15672 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row15673 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row15674 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row15675 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

def row15676 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

def row15677 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

def row15678 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

def row15679 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

def row15680 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

def row15681 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15682 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15683 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15684 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15685 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15686 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15687 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

def row15688 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

def row15689 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

def row15690 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15691 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15692 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15693 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15694 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15695 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15696 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

def row15697 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

def row15698 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

def row15699 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15700 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15701 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15702 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15703 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15704 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15705 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15706 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15707 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2918, -1), (key2919, 2), (key2922, -1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15708 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2918, -1), (key2919, 2), (key2922, -1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15709 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15710 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15711 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

def row15712 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

def row15713 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

def row15714 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

def row15715 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

def row15716 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

def row15717 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15718 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15719 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15720 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15721 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15722 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15723 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15724 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15725 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15726 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15727 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15728 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15729 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15730 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15731 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15732 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15733 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15734 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15735 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15736 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15737 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15738 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15739 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15740 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15741 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15742 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15743 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15744 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15745 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15746 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15747 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15748 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15749 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15750 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15751 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15752 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15753 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15754 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15755 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15756 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15757 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15758 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15759 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15760 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15761 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15762 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15763 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15764 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15765 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15766 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15767 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15768 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15769 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15770 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15771 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15772 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15773 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15774 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15775 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15776 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15777 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15778 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15779 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15780 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15781 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15782 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15783 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15784 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15785 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15786 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15787 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15788 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15789 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15790 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15791 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15792 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15793 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15794 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15795 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15796 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15797 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15798 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15799 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15800 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15801 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15802 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15803 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15804 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15805 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15806 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15807 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15808 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15809 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15810 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15811 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15812 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15813 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15814 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15815 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15816 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15817 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15818 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15819 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15820 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15821 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15822 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15823 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15824 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15825 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15826 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15827 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15828 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15829 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15830 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15831 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15832 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15833 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15834 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15835 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15836 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15837 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15838 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15839 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15840 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15841 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15842 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15843 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15844 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15845 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15846 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15847 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15848 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15849 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15850 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15851 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15852 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15853 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15854 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15855 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15856 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15857 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15858 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15859 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15860 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15861 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15862 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15863 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15864 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15865 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15866 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15867 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

def row15868 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

def row15869 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

def row15870 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15871 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15872 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15873 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15874 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15875 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15876 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

def row15877 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

def row15878 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

def row15879 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15880 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15881 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15882 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15883 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15884 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15885 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15886 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15887 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15888 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15897 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15898 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15899 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15900 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15901 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15902 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15903 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

def row15904 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

def row15905 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

def row15906 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15907 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15908 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15909 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15910 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15911 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15912 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

def row15913 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

def row15914 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

def row15915 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15916 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15917 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15918 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15919 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15920 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15921 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15922 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15923 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15924 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15925 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15926 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15927 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15928 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15929 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15930 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15931 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15932 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15933 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15934 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15935 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15936 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15937 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15938 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15939 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15940 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15941 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15942 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15943 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15944 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15945 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15946 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15947 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15948 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15949 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15950 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15951 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15952 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15953 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15954 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15955 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15956 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15957 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15958 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15959 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15960 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15961 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15962 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15963 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15964 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15965 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15966 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15967 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15968 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15969 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15970 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15971 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15972 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15973 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15974 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15975 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15976 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15977 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15978 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15979 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15980 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15981 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15982 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15983 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15984 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15985 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15986 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15987 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15988 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15989 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15990 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15991 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15992 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15993 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row15994 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row15995 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row15996 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row15997 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row15998 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row15999 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16000 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16001 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16002 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16003 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16004 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16005 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16006 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16007 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16008 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16009 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16010 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16011 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16012 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16013 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16014 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16015 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16016 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16017 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row16018 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row16019 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row16020 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16021 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16022 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16023 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16024 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16025 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16026 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16027 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16028 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16029 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16030 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16031 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16032 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16033 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16034 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16035 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16036 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16037 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16038 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16039 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16040 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16041 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16042 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16043 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16044 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16045 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16046 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16047 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16048 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16049 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16050 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16051 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16052 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16053 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16054 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16055 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16056 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16057 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16058 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16059 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16060 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16061 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16062 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16063 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16064 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16065 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

def row16066 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

def row16067 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

def row16068 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16069 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16070 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16071 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16072 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16073 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16074 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

def row16075 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

def row16076 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

def row16077 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16078 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16079 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16080 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16081 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16082 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16083 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16084 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16085 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2892, -1), (key2895, 2), (key2902, -1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16086 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2892, -1), (key2895, 2), (key2902, -1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16087 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16088 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16089 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

def row16090 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

def row16091 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

def row16092 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

def row16093 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

def row16094 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8054 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8055 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8056 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8057 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8058 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8059 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8060 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8061 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8062 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8063 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8064 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8065 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8066 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8067 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8068 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8069 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8070 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8071 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8072 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8073 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8074 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8075 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8076 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8077 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8078 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8079 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8080 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8081 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8082 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8083 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8084 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8085 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8086 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8087 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8088 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8089 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8090 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8091 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8092 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8093 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8094 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8095 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8096 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8097 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8098 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8099 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8100 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8101 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8102 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8103 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8104 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8105 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8106 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8107 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8108 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8109 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8110 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8111 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8112 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8113 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8114 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8115 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8116 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8117 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8118 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8119 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8120 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8121 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8122 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8123 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8124 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8125 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8126 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8127 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8128 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8129 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8130 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8131 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8132 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8133 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8134 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8135 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8136 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8137 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8138 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8139 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8140 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8141 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8142 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8143 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8144 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8145 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8146 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8147 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8148 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8149 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8150 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8151 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8152 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8153 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8154 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8155 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8156 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8157 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8158 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8159 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8160 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8162 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8163 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8164 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8165 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8166 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8167 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8168 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8169 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8170 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8171 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8172 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8173 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8174 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8175 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8176 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8177 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8178 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8179 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8180 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8181 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8182 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8183 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8184 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8185 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8186 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8187 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8188 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8189 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8190 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8191 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8192 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8193 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8194 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8195 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8196 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8197 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8198 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8199 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8200 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8201 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8202 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8203 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8204 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8205 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8206 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8207 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8208 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8209 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8210 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8211 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8212 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8213 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8214 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8215 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8216 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8217 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8218 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8219 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8220 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8221 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8222 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8223 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8224 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8225 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8226 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8227 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8228 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8229 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8230 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8231 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8232 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8233 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8234 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8235 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8236 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8237 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8238 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -8), (key435, 2), (key445, 2), (key453, 2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8239 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -8), (key435, 2), (key445, 2), (key453, 2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8240 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8241 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8242 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8243 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8244 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8245 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8246 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8247 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8248 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8249 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8250 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8251 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8252 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8253 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8254 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8255 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8256 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8257 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8258 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8259 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 2), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8260 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 2), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8261 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8262 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8263 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8264 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8265 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8266 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8267 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8268 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8269 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8270 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8271 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8272 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8273 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8274 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8275 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8276 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8277 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8278 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8279 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8280 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8281 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8282 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8283 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8284 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8285 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8286 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8287 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8288 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8289 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8290 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8291 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8292 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8293 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8294 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8295 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8296 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8297 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8298 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8299 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8300 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8301 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8302 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8303 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8304 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8305 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8306 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8307 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8308 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8309 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8310 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8311 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8312 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8313 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8314 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8315 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8316 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8317 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8318 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8319 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8320 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8321 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8322 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8323 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8324 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8325 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8326 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8327 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8328 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8329 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8330 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8331 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8332 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8333 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8334 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8335 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8336 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8337 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8338 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8339 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8340 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8341 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8342 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8343 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8344 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8345 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8346 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8347 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8348 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8349 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8350 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8351 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8352 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8353 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8354 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8355 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8356 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8357 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8358 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8359 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8360 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8361 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8362 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8363 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8364 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8365 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8366 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8367 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8368 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8369 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8370 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8371 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8372 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8373 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8374 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8375 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8376 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8377 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8378 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8379 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8380 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8381 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8382 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8383 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8384 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8385 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8386 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8387 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8388 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8389 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8390 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8391 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8392 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8393 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8394 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8395 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8396 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8397 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8398 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8399 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8400 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8401 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8402 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8403 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8404 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8405 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8406 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8407 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8408 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8409 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8410 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8411 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8412 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8413 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8414 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8415 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8416 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8417 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8418 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8419 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8420 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8421 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8422 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8423 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8424 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8425 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8426 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8427 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8428 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8429 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8430 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8431 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8432 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8433 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8434 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8435 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8436 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8437 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8438 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8439 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8440 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8441 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8442 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8443 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8444 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8445 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8446 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8447 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8448 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8449 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8450 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8451 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8452 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8453 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8454 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8455 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8460 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8461 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8462 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8463 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 2), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8464 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 2), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8465 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8466 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8467 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8468 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8469 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8470 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8471 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8472 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8473 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8474 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8475 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8476 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8477 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8478 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8479 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8480 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8481 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -6), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8482 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -6), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8483 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8484 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

end MUB6.Certificate.GramRows

end OAI
end


