-- Prove2me | Definitions.Def_OAIQ106E038
-- name    : OAIQ106E038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:55:34.647864+00:00
-- url     : https://prove2.me/theorems/9d11af73-bbba-4c22-be4c-fb675183faf7
-- title:
--   Definitions bundle OAIQ106E038 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.entries`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block5Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Data.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E032` and `OAIQ106E035` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E035

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


