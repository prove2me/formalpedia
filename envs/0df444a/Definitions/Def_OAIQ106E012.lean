-- Prove2me | Definitions.Def_OAIQ106E012
-- name    : OAIQ106E012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T23:48:18.598077+00:00
-- url     : https://prove2.me/theorems/3733c21c-068b-4363-8aa0-0e151eaaaa1b
-- title:
--   Definitions bundle OAIQ106E012 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block4.node471`, `OAI.MUB6.Certificate.GramAssembly.Block4.rows`, `OAI.MUB6.Certificate.GramAssembly.Block5.entries`, `OAI.MUB6.Certificate.GramAssembly.Block5.entryRow0`, `OAI.MUB6.Certificate.GramAssembly.Block5.entryRows`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramAssembly_Block4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4.lean), [`MutuallyUnbiased_GramAssembly_Block4Part14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Part14.lean), [`MutuallyUnbiased_GramAssembly_Block5Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block5Data.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E007`, `OAIQ106E178`, `OAIQ106E179` and `OAIQ106E011` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval_e` and `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e` and `OAI.MUB6.Certificate.GramAssembly.interpretation_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E178
import Definitions.Def_OAIQ106E179
import Definitions.Def_OAIQ106E011

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

def node471 : Integer.Sparse (Fin 2886) := ((((node471part0 ++ node471part1) ++ (node471part2 ++ node471part3)) ++ ((node471part4 ++ node471part5) ++ (node471part6 ++ (node471part7 ++ node471part8)))) ++ (((node471part9 ++ node471part10) ++ (node471part11 ++ (node471part12 ++ node471part13))) ++ ((node471part14 ++ node471part15) ++ (node471part16 ++ (node471part17 ++ node471part18)))))

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

def rows (i : Fin 22) : Integer.Sparse (Fin 2886) :=
  (#[node20, node41, node62, node83, node104, node125, node146, node167, node188, node209, node230, node251, node272, node293, node314, node335, node356, node377, node398, node419, node440, node461]).getD i.val []

end MUB6.Certificate.GramAssembly.Block4

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

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7, entry_0_8, entry_0_9, entry_0_10, entry_0_11]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4, entryRow5, entryRow6, entryRow7, entryRow8, entryRow9, entryRow10, entryRow11]

def entries (i j : Fin 12) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

end MUB6.Certificate.GramAssembly.Block5

end OAI
end


