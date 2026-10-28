-- Prove2me | Definitions.Def_OAIB3Kr001
-- name    : OAIB3Kr001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T15:52:56.437085+00:00
-- url     : https://prove2.me/theorems/0beab56d-8794-4710-8193-4414ede512c0
-- title:
--   Definitions bundle OAIB3Kr001 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 inductive type or structure and 1 instance. The definitions and types are `OAI.KirchbergRordam.MultiplicativeChannel.Channel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_MultiplicativeChannels`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/MultiplicativeChannels.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Kr003`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MultiplicativeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.MultiplicativeChannel
open scoped CStarAlgebra ComplexOrder
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


structure Channel where
  linear : A →ₗ[ℂ] B
  norm_le : ∀ a, ‖linear a‖≤‖a‖
  mul_eq : ∀ a b, linear a*linear b=linear 1*linear (a*b)
variable {A B}
instance instCoeFunChannelForall : CoeFun (Channel A B) (fun _ => A→B) := ⟨fun φ => φ.linear⟩
end KirchbergRordam.MultiplicativeChannel
end

end OAI
end


