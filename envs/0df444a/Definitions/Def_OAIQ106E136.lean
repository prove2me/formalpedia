-- Prove2me | Definitions.Def_OAIQ106E136
-- name    : OAIQ106E136
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T00:30:31.206227+00:00
-- url     : https://prove2.me/theorems/c7ab8bce-6e60-4a89-8458-5b63d17a1c71
-- title:
--   Definitions bundle OAIQ106E136 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge1917`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge500`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge504`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge505`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge506`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge536`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge596`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge716`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge956`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge957`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedTargets_ReductionMergeData15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeData15.lean), [`MutuallyUnbiased_MixedTargets_ReductionMergeData16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeData16.lean), [`MutuallyUnbiased_MixedTargets_ReductionMergeData18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeData18.lean), [`MutuallyUnbiased_MixedTargets_ReductionMergeData22`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeData22.lean), [`MutuallyUnbiased_MixedTargets_ReductionMergeData29`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeData29.lean), [`MutuallyUnbiased_MixedTargets_ReductionMergeData59`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeData59.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E130` and `OAIQ106E135` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval716_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`; the proofs of `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval716_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E135

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge500 : Integer.Sparse OriginalKey := originalMerge498 ++ originalMerge499

def originalMerge504 : Integer.Sparse OriginalKey := originalMerge500 ++ originalMerge503

def originalMerge505 : Integer.Sparse OriginalKey := originalMerge497 ++ originalMerge504

def originalMerge506 : Integer.Sparse OriginalKey := originalMerge491 ++ originalMerge505

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge536 : Integer.Sparse OriginalKey := originalMerge506 ++ originalMerge535

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge596 : Integer.Sparse OriginalKey := originalMerge536 ++ originalMerge595

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge716 : Integer.Sparse OriginalKey := originalMerge596 ++ originalMerge715

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge956 : Integer.Sparse OriginalKey := originalMerge716 ++ originalMerge955

def originalMerge957 : Integer.Sparse OriginalKey := originalMerge477 ++ originalMerge956

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def originalMerge1917 : Integer.Sparse OriginalKey := originalMerge957 ++ originalMerge1916

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


