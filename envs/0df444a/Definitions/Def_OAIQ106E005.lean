-- Prove2me | Definitions.Def_OAIQ106E005
-- name    : OAIQ106E005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:07:52.317786+00:00
-- url     : https://prove2.me/theorems/0002c40f-458a-4a1a-baec-8e790843def0
-- title:
--   Definitions bundle OAIQ106E005 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block2.rows`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries`, `OAI.MUB6.Certificate.GramAssembly.Block3.entryRow0`, `OAI.MUB6.Certificate.GramAssembly.Block3.entryRows`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramAssembly_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block2.lean), [`MutuallyUnbiased_GramAssembly_Block3Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block3Data.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E001` and `OAIQ106E175` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_17_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_21_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_7_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9_e` and `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_17_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_21_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_7_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8_e`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9_e` and `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E001
import Definitions.Def_OAIQ106E175

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

open scoped BigOperators

def rows (i : Fin 11) : Integer.Sparse (Fin 2886) :=
  (#[node9, node19, node29, node39, node49, node59, node69, node79, node89, node99, node109]).getD i.val []

end MUB6.Certificate.GramAssembly.Block2

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

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7, entry_0_8, entry_0_9, entry_0_10, entry_0_11, entry_0_12, entry_0_13, entry_0_14, entry_0_15, entry_0_16, entry_0_17, entry_0_18, entry_0_19, entry_0_20, entry_0_21, entry_0_22, entry_0_23, entry_0_24, entry_0_25, entry_0_26]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4, entryRow5, entryRow6, entryRow7, entryRow8, entryRow9, entryRow10, entryRow11, entryRow12, entryRow13, entryRow14, entryRow15, entryRow16, entryRow17, entryRow18, entryRow19, entryRow20, entryRow21, entryRow22, entryRow23, entryRow24, entryRow25, entryRow26]

def entries (i j : Fin 27) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

end MUB6.Certificate.GramAssembly.Block3

end OAI
end


