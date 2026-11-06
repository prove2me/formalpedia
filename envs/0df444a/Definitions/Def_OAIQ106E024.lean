-- Prove2me | Definitions.Def_OAIQ106E024
-- name    : OAIQ106E024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:42:57.302485+00:00
-- url     : https://prove2.me/theorems/98b3ac3f-7cb2-43ea-89eb-7000d3b389e6
-- title:
--   Definitions bundle OAIQ106E024 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows9_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block1Row9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row9.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E013`, `OAIQ106E015`, `OAIQ106E018` and `OAIQ106E021` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_0_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E015
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E021

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1476, row1477, row1478, row1479, row1480, row1481, row1482, row1483, row1484, row1485, row1486, row1487, row642, row643, row644, row645, row646, row647, row1488, row1489, row1490, row1491, row1492, row1493, row654, row655, row656, row657, row658, row659]

end MUB6.Certificate.GramEntries.Block1

end OAI
end


