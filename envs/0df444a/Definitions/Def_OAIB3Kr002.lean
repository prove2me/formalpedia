-- Prove2me | Definitions.Def_OAIB3Kr002
-- name    : OAIB3Kr002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T15:52:58.509392+00:00
-- url     : https://prove2.me/theorems/de70602f-052d-45fc-ad98-e4f77611bd58
-- title:
--   Definitions bundle OAIB3Kr002 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 inductive type or structure and 1 instance. The definitions and types are `OAI.KirchbergRordam.UnitaryConjugacySquare.Flow`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_SymmetryFlow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/SymmetryFlow.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Kr004`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SymmetryFlow
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


namespace KirchbergRordam.UnitaryConjugacySquare
open Filter Topology
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

structure Flow (A : Type*) [CStarAlgebra A] where
  toFun : ℝ → unitary A
  continuous_toFun : Continuous toFun
  zero : toFun 0=1
  add : ∀ s t, toFun (s+t)=toFun s*toFun t
instance instCoeFunFlowForallRealSubtypeMemSubmonoidUnitary : CoeFun (Flow A) (fun _ => ℝ → unitary A) := ⟨Flow.toFun⟩
end KirchbergRordam.UnitaryConjugacySquare


end

end OAI
end


