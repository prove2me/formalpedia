-- Prove2me | Definitions.Def_OAIQ081S044
-- name    : OAIQ081S044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:33:34.001999+00:00
-- url     : https://prove2.me/theorems/0b880b91-1242-4cfe-9019-bd0c57320ac1
-- title:
--   Definitions bundle OAIQ081S044 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.freeHeadInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_HeadSignatureLocality`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSignatureLocality.lean).
--
--   **Imports.** It imports the bundle `OAIQ081S003` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S003

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSignatureLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact full-integer head labels and fixed-high cancellation, extracted
unchanged from HeadSourceLocality. All raw rows and original coordinate IDs
are retained; source-product locality remains in the importing module. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog

def freeHeadInclusion {n r : ℕ} (H : Finset (Fin n))
    (head : Fin n → Fin r) (g : Fin r) :
    Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g ↪ Moments.Head head g :=
  ⟨fun v => ⟨v.val.val,v.property⟩, by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : Moments.Head head g => v.val) h⟩


open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end
end


