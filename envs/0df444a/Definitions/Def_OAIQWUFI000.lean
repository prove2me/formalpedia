-- Prove2me | Definitions.Def_OAIQWUFI000
-- name    : OAIQWUFI000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:44:48.20481+00:00
-- url     : https://prove2.me/theorems/135533c9-a046-4121-9d3a-35ec4c72e13a
-- title:
--   OpenAI universal F∞ group split: benign subgroups and words (definitions bundle 1 of 9)
-- statement:
--   The four definitions behind the Higman-embedding statements of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, and the bundle uses only Mathlib.
--
--   - `Higman.IsBenign A`: a subgroup $A$ of $G$ is benign (Higman 1961) if $G$ embeds in a finitely presented group $K$ in which $A$ is the preimage of a finitely generated subgroup.
--   - `Higman.CentralExtension G A`: Mathlib's HNN extension `HNNExtension G A A (MulEquiv.refl A)`, $G$ with a new generator commuting with $A$.
--   - `Higman.NormalWords.Alphabet` $=$ `Bool ⊕ Unit` and `Higman.NormalWords.Raw` $=$ `List (Alphabet × Bool)`, the words on three letters and their inverses.
--
--   Modules: `CentralHNN.lean`, `HigmanEmbedding.lean`, `RopeTrick.lean`.
--
--   The statements `OAI.Higman.embeds_of_benign_kernel`, `OAI.Higman.benign_iff_centralExtension_embeds`, `OAI.Higman.NormalWords.benign_normalClosure` and `OAI.Higman.NormalWords.embeds_presentation` (Higman's embedding theorem) import only this bundle. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_UniversalFInfinity.CentralHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman
open HNNExtension

abbrev CentralExtension (G : Type u) [Group G] (A : Subgroup G) :=
  HNNExtension G A A (MulEquiv.refl A)

end Higman

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.RopeTrick
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman
variable {G : Type u} [Group G]

def IsBenign (A : Subgroup G) : Prop :=
  ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
    (i : G →* K), Function.Injective i ∧
    ∃ B : Subgroup K, B.FG ∧ B.comap i = A

end Higman

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.HigmanEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

noncomputable section

namespace Higman.NormalWords

section
abbrev Alphabet := Bool ⊕ Unit
abbrev Raw := List (Alphabet × Bool)

end

end Higman.NormalWords

end

end OAI
end


