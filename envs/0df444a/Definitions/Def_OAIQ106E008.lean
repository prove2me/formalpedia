-- Prove2me | Definitions.Def_OAIQ106E008
-- name    : OAIQ106E008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:21:57.541747+00:00
-- url     : https://prove2.me/theorems/9633309b-c5e4-4f5d-8bf0-76e236b7ccb1
-- title:
--   Definitions bundle OAIQ106E008 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block3.node726`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramAssembly_Block3Part22`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block3Part22.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E177` and `OAIQ106E007` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E177
import Definitions.Def_OAIQ106E007

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node726 : Integer.Sparse (Fin 2886) := ((((node726part0 ++ node726part1) ++ (node726part2 ++ (node726part3 ++ node726part4))) ++ ((node726part5 ++ (node726part6 ++ node726part7)) ++ (node726part8 ++ (node726part9 ++ node726part10)))) ++ (((node726part11 ++ node726part12) ++ (node726part13 ++ (node726part14 ++ node726part15))) ++ ((node726part16 ++ (node726part17 ++ node726part18)) ++ (node726part19 ++ (node726part20 ++ node726part21)))))

end MUB6.Certificate.GramAssembly.Block3

end OAI
end


