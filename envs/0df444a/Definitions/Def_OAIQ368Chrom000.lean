-- Prove2me | Definitions.Def_OAIQ368Chrom000
-- name    : OAIQ368Chrom000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:01:39.840748+00:00
-- url     : https://prove2.me/theorems/a2f6df91-8ea3-4511-b921-2ba7a2dda606
-- title:
--   Definitions bundle OAIQ368Chrom000 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 2 definitions and 2 instances. The definitions and types are `OAI.ElementaryPositivity.ExactMasks.Exact`, `OAI.ElementaryPositivity.ExactMasks.Required`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Witness_ProfilePartition`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ProfilePartition.lean), [`Chromatic_Witness_WitnessTransport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/WitnessTransport.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom060`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_WitnessTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity
namespace ExactMasks

variable {A B I W : Type*} [DecidableEq I]

def Exact (mask : A → Finset I) (J : Finset I) := {a // mask a = J}
def Required (mask : A → Finset I) (J : Finset I) := {a // J ⊆ mask a}

end ExactMasks
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ProfilePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ExactMasks
open Classical
noncomputable section
instance requiredFintype {A I:Type*} [Fintype A] [DecidableEq I] (mask:A → Finset I) (J:Finset I) :
    Fintype (Required mask J):=inferInstanceAs (Fintype {a:A // J⊆mask a})
instance exactFintype {A I:Type*} [Fintype A] [DecidableEq I] (mask:A → Finset I) (J:Finset I) :
    Fintype (Exact mask J):=inferInstanceAs (Fintype {a:A // mask a=J})
end
end ElementaryPositivity.ExactMasks

end

end OAI
end


