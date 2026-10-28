-- Prove2me | Definitions.Def_OAIB3Kr015
-- name    : OAIB3Kr015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:26:45.103864+00:00
-- url     : https://prove2.me/theorems/be970662-89ab-4448-9e5c-8cef92036343
-- title:
--   Definitions bundle OAIB3Kr015 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageLeft`, `OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight`, `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.mappedUnitary`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_PrimeChannels`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean), [`CharacterCriterion_PrimePresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimePresentation.lean).
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundle `OAIB3Kr013` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound`; the proofs of `OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control`, `OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound` and `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr013

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
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
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
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

namespace KirchbergRordam.PrimeDropPresentation.HalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open PrimeDropPresentation.Iteration
open UnitaryDisplacement BalancedDropHalfFlip
def mappedUnitary {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) :
    unitary (MaxTensor.Algebra B B) :=
  Unitary.map (StarMonoidHom.ofClass (squareMap φ)) w

end KirchbergRordam.PrimeDropPresentation.HalfFlip
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeChannels
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
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
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

namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath DiagonalIteration PrimeDropPresentation.Iteration
open GeneralDropSystem DropChannels
open BalancedDropSystem (half)
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

def stageLeft (n k : ℕ) : Channel DimensionDrop23 (S.Stage (n+k+1)) :=
  DropChannels.left (S.size (n+k+1)) (S.size (n+k+1)+1)
    (finalPath S n k) (normalizedPath_continuous S n (k+1)) (normalizedPath_zero S n (k+1))
    (zeroRep S (n+k) (normalizedPath S n k half))
def stageRight (n k : ℕ) : Channel DimensionDrop23 (S.Stage (n+k+1)) :=
  DropChannels.right (S.size (n+k+1)) (S.size (n+k+1)+1)
    (endPath S n k) (endPath_continuous S n k) (endPath_one S n k)
    (oneRep S (n+k)
      (normalizedPath S n k half*star (normalizedPath S n k 1)))
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end


