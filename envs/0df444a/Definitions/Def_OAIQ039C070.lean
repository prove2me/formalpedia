-- Prove2me | Definitions.Def_OAIQ039C070
-- name    : OAIQ039C070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:39:31.716985+00:00
-- url     : https://prove2.me/theorems/abd456af-0e73-4e37-9800-755a1630fb89
-- title:
--   Definitions bundle OAIQ039C070 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_VectorFreeGeneration`.
--
--   **Imports.** It imports the bundle `OAIQ039C060` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Kadison.VectorGNS.factorTrace_generated` and `OAI.Kadison.VectorGNS.factorTrace_inclusion_normal`; the proofs of `OAI.Kadison.VectorGNS.factorTrace_generated`, `OAI.Kadison.VectorGNS.factorTrace_inclusion_normal` and `OAI.Kadison.VectorGNS.free_original_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C060

section
-- module Solutions.OAIQ039_CM.Commutator_VectorFreeGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

lemma inclusion_injective (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    Function.Injective (inclusion M D hDM) := StarSubalgebra.inclusion_injective hDM

end Kadison.VectorGNS

end

end
end

end OAI
end


