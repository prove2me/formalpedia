-- Prove2me | Definitions.Def_OAIQ106E152
-- name    : OAIQ106E152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T21:01:26.975364+00:00
-- url     : https://prove2.me/theorems/22b22195-c351-4899-8caa-f561c6816369
-- title:
--   Definitions bundle OAIQ106E152 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Moments_GramNormalization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Moments/GramNormalization.lean).
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundle `OAIQ106E010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E153`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E010

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

theorem rowOrder_nodup (a v : Charge) : (rowOrder a v).Nodup := by
  exact (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_finRange 6)

end MUB6.GramNormalization

end OAI
end


