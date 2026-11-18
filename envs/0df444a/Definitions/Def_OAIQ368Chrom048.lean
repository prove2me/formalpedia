-- Prove2me | Definitions.Def_OAIQ368Chrom048
-- name    : OAIQ368Chrom048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:01:40.976929+00:00
-- url     : https://prove2.me/theorems/c85c6d02-10f2-4868-a030-5ed9ad59c090
-- title:
--   Definitions bundle OAIQ368Chrom048 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.ElementaryPositivity.ColorAdmissible`, `OAI.ElementaryPositivity.colorWordSpan`, `OAI.ElementaryPositivity.wordLengthFiltration`, `OAI.ElementaryPositivity.wordProduct`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Histories_ColorWordReordering`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/ColorWordReordering.lean), [`Chromatic_Walls_WordLengthFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/WordLengthFiltration.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WordLengthFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
variable {J A : Type*} [Ring A]

noncomputable def wordProduct (b : J → A) (l : List J) : A := (l.map b).prod

variable [Algebra ℚ A]

noncomputable def wordLengthFiltration (b : J → A) (n : ℕ) : Submodule ℚ A :=
  Submodule.span ℚ {x | ∃ l : List J,l.length ≤ n ∧ wordProduct b l=x}

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_ColorWordReordering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
variable {J A : Type*} [Ring A] [Algebra ℚ A]
variable (b : J → A) (ε : J → J → ℚ)

section Ordered
variable [LinearOrder J]

def ColorAdmissible (l : List J) : Prop :=
  l.Pairwise (fun i j=>i≤j ∧ (i=j → ε i i=1))

noncomputable def colorWordSpan : Submodule ℚ A :=
  Submodule.span ℚ {x | ∃ l : List J,ColorAdmissible ε l ∧ wordProduct b l=x}

end Ordered
end ElementaryPositivity

end

end OAI
end


