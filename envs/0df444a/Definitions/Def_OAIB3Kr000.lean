-- Prove2me | Definitions.Def_OAIB3Kr000
-- name    : OAIB3Kr000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T15:52:56.714783+00:00
-- url     : https://prove2.me/theorems/eb560d51-aa65-42cb-8abd-06a7e57444d0
-- title:
--   Definitions bundle OAIB3Kr000 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 inductive type or structure and 1 instance. The definitions and types are `OAI.KirchbergRordam.GenericRW.MaxTensor.CStarPack`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_MaxTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/MaxTensor.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Kr003`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MaxTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct

namespace KirchbergRordam.GenericRW

namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}

variable {C : Type*} [CStarAlgebra C]


open scoped CStarAlgebra


universe u


structure CStarPack where
  carrier : Type u
  inst : CStarAlgebra carrier

attribute [instance] CStarPack.inst
instance instCoeSortCStarPackType : CoeSort CStarPack (Type u) := ⟨CStarPack.carrier⟩


end MaxTensor
end KirchbergRordam.GenericRW
end

end OAI
end


