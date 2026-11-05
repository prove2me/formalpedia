-- Prove2me | Definitions.Def_OAIQ106E134
-- name    : OAIQ106E134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:31:30.677535+00:00
-- url     : https://prove2.me/theorems/d27e778a-c14a-4bc8-beb1-64a2fbf62a98
-- title:
--   Definitions bundle OAIQ106E134 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.originalLess`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Certificate_MixedTargetBasic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Certificate/MixedTargetBasic.lean).
--
--   **Imports.** It imports the bundle `OAIQ106E105` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e` and `OAI.MUB6.family_size_le_five_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E105

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalLess (a b : OriginalKey) : Bool :=
  match a, b with
  | .inl i, .inl j => decide (i < j)
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr i, .inr j => decide (i < j)

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


