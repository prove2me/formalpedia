-- Prove2me | Definitions.Def_OAIQ106E009
-- name    : OAIQ106E009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:36:24.688717+00:00
-- url     : https://prove2.me/theorems/9c990576-3214-4475-8546-2eac155e43d0
-- title:
--   Definitions bundle OAIQ106E009 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block3.rows`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramAssembly_Block3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block3.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E175`, `OAIQ106E176`, `OAIQ106E006` and `OAIQ106E007` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e` and `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E175
import Definitions.Def_OAIQ106E176
import Definitions.Def_OAIQ106E006
import Definitions.Def_OAIQ106E007

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

def rows (i : Fin 27) : Integer.Sparse (Fin 2886) :=
  (#[node25, node51, node77, node103, node129, node155, node181, node207, node233, node259, node285, node311, node337, node363, node389, node415, node441, node467, node493, node519, node545, node571, node597, node623, node649, node675, node701]).getD i.val []

end MUB6.Certificate.GramAssembly.Block3

end OAI
end


