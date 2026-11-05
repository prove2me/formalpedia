-- Prove2me | Definitions.Def_OAIQ106E028
-- name    : OAIQ106E028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:50:48.444074+00:00
-- url     : https://prove2.me/theorems/7db95baf-4ed2-4f1d-9d3d-718db28ff25f
-- title:
--   Definitions bundle OAIQ106E028 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entries`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Data.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E013` and `OAIQ106E025` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E025

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


