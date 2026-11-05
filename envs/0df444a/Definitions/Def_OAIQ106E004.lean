-- Prove2me | Definitions.Def_OAIQ106E004
-- name    : OAIQ106E004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:26:36.968361+00:00
-- url     : https://prove2.me/theorems/f9f71fda-74e0-4a31-b2a6-0e645a4cfbeb
-- title:
--   Definitions bundle OAIQ106E004 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramAssembly_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block2.lean).
--
--   **Imports.** It imports the bundle `OAIQ106E001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_eval_e` and `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_interpretation_e`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_interpretation_e` and `OAI.MUB6.Certificate.GramAssembly.interpretation_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E001

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

open scoped BigOperators

def polynomial : Integer.Sparse (Fin 2886) := node119

end MUB6.Certificate.GramAssembly.Block2

end OAI
end


