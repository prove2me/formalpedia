-- Prove2me | Definitions.Def_OAIQ039C053
-- name    : OAIQ039C053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:27:05.711432+00:00
-- url     : https://prove2.me/theorems/2986b8fe-42a4-4815-89e8-d63bfde91ced
-- title:
--   Definitions bundle OAIQ039C053 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.Kadison.TracialSequence.restrictBoundedUnitary`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeSequenceUnitary`.
--
--   **Imports.** It imports the bundles `OAIQ039C035` and `OAIQ039C037` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C037

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSequenceUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

section Relative

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R≤M)

variable (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def restrictBoundedUnitary (u : ℕ → unitary M) (hu : ∀ n,((u n:M):H →L[ℂ] H)∈R) : ℕ →ᵇ R :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => ⟨u n,hu n⟩) 1
    (fun n => (PartialUnitary.ofUnitary (u n)).norm_le_one)

end Relative

end Kadison.TracialSequence

end

end OAI
end


