-- Prove2me | Definitions.Def_OAIQ368Chrom073
-- name    : OAIQ368Chrom073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:07:43.65049+00:00
-- url     : https://prove2.me/theorems/6a8d5538-d82d-4acb-aa23-5e3b8a877247
-- title:
--   Definitions bundle OAIQ368Chrom073 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Walls_DegreeIsolatedReordering`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/DegreeIsolatedReordering.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom018` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom018

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DegreeIsolatedReordering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
@[simp] lemma patchTop_last (n : ℕ) (G F : PowerSeries A) :
    coeff (n+1) (patchTop n G F)=coeff (n+1) F := by simp
end
end RootTruncation
end ElementaryPositivity

end

end OAI
end


