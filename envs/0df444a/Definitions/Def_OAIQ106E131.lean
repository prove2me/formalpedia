-- Prove2me | Definitions.Def_OAIQ106E131
-- name    : OAIQ106E131
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:49:00.625028+00:00
-- url     : https://prove2.me/theorems/fcf0ed09-651f-4159-be88-be6dedbb5efc
-- title:
--   Definitions bundle OAIQ106E131 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedTargets_OriginalMerge0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge0.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E120` and `OAIQ106E121` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E132`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E121

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode0 : Integer.Sparse (Fin 2886) := keyPolynomialBlock0 ++ keyPolynomialBlock1

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


