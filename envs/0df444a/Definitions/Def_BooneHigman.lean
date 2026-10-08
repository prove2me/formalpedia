-- Prove2me | Definitions.Def_BooneHigman
-- name    : BooneHigman
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.273723+00:00
-- url     : https://prove2.me/theorems/614317bc-4b3b-4c0c-84c6-3f492207d0c3
-- statement:
--   For a nonnegative integer n, a word in n generators is a finite list of pairs consisting of an index from 0 to n−1 and a Boolean sign. Given n elements of a group G, evaluating a word replaces each true-signed letter by its indexed generator and each false-signed letter by that generator’s inverse, then multiplies the resulting elements in order; the empty word evaluates to the identity. HasDecidableWordProblem(G) is the proposition that some finite family generates G as a subgroup and that the predicate asserting that a word in this family evaluates to the identity is computable. Thus finite generation is part of this definition. EmbedsInFinitelyPresentedSimpleGroup(G) is the proposition that there exists a finitely presented simple group H, in the same universe as G, together with an injective group homomorphism from G to H. The block defines these two properties without asserting any implication or equivalence between them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BooneHigman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BooneHigman.lean; bytes 16..1021
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace FiniteAlgebraicEnvelopes

universe u

abbrev Word (generatorCount : ℕ) := List (Fin generatorCount × Bool)

def evalWord {GroupType : Type u} [Group GroupType] {generatorCount : ℕ}
    (generators : Fin generatorCount → GroupType) (word : Word generatorCount) : GroupType :=
  (word.map fun letter =>
    if letter.2 then generators letter.1 else (generators letter.1)⁻¹).prod

def HasDecidableWordProblem (GroupType : Type u) [Group GroupType] : Prop :=
  ∃ (generatorCount : ℕ) (generators : Fin generatorCount → GroupType),
    Subgroup.closure (Set.range generators) = ⊤ ∧
    ComputablePred (fun word : Word generatorCount => evalWord generators word = 1)

def EmbedsInFinitelyPresentedSimpleGroup (GroupType : Type u) [Group GroupType] : Prop :=
  ∃ (TargetGroup : Type u) (_ : Group TargetGroup),
    Group.IsFinitelyPresented TargetGroup ∧ IsSimpleGroup TargetGroup ∧
    ∃ embedding : GroupType →* TargetGroup, Function.Injective embedding



end FiniteAlgebraicEnvelopes
end OAI


