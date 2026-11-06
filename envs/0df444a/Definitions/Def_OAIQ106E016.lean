-- Prove2me | Definitions.Def_OAIQ106E016
-- name    : OAIQ106E016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:04:58.910206+00:00
-- url     : https://prove2.me/theorems/7d92bff5-7ae2-4c3d-abe2-e0896bd67723
-- title:
--   Definitions bundle OAIQ106E016 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows14_8`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block1Row14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row14.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E196`, `OAIQ106E013` and `OAIQ106E015` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E015

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_8 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2864, row2865, row2866, row2867, row2868, row2869, row2870, row2871, row2872, row2873, row2874, row2875, row2876, row2877, row2878, row2879, row2880, row2881, row2882, row2883, row2884, row2885, row2886, row2887]

end MUB6.Certificate.GramEntries.Block1

end OAI
end


