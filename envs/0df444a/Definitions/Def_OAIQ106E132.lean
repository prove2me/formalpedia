-- Prove2me | Definitions.Def_OAIQ106E132
-- name    : OAIQ106E132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T00:38:59.896598+00:00
-- url     : https://prove2.me/theorems/33173ac3-b34f-48a0-9f04-efc95201c332
-- title:
--   Definitions bundle OAIQ106E132 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode20`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode3`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode43`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode89`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedTargets_OriginalMerge0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge0.lean), [`MutuallyUnbiased_MixedTargets_OriginalMerge1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge1.lean), [`MutuallyUnbiased_MixedTargets_OriginalMerge2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge2.lean), [`MutuallyUnbiased_MixedTargets_OriginalMerge5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge5.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E123` and `OAIQ106E131` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.family_size_le_five_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E131

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode3 : Integer.Sparse (Fin 2886) := keyPolynomialNode0 ++ keyPolynomialNode2

def keyPolynomialNode9 : Integer.Sparse (Fin 2886) := keyPolynomialNode3 ++ keyPolynomialNode8

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode20 : Integer.Sparse (Fin 2886) := keyPolynomialNode9 ++ keyPolynomialNode19

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode43 : Integer.Sparse (Fin 2886) := keyPolynomialNode20 ++ keyPolynomialNode42

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialNode89 : Integer.Sparse (Fin 2886) := keyPolynomialNode43 ++ keyPolynomialNode88

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


