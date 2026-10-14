-- Prove2me | Definitions.Def_BooneHigman_MonoidWordProblem
-- name    : BooneHigman_MonoidWordProblem
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-14T09:15:25.893373+00:00
-- url     : https://prove2.me/theorems/c157c902-41a2-4b7a-83bb-fe8ca0ea1d64
-- title:
--   Decidable word problem and finite presentation for monoids
-- statement:
--   Monoid analogues of the group-theoretic notions `Word`/`evalWord`/`HasDecidableWordProblem` already published for groups (`Definitions.Def_BooneHigman`), needed to state Theorem 6.2 of OpenAI's "Finite algebraic envelopes and the Boone-Higman conjecture" preprint (Section 6, 'a finitely generated monoid H with decidable word problem', 'a finitely presented monoid K'). `HasDecidableWordProblemMonoid M` says `M` has a finite generating set for which equality of two monoid words' values is computable (a monoid word has no sign bit, since a general monoid need not have inverses). `IsFinitelyPresentedMonoid M` says `M` is isomorphic to a monoid presented by finitely many generators and relations, via Mathlib's `PresentedMonoid`.
-- source:
--   OpenAI, "Finite algebraic envelopes and the Boone-Higman conjecture", OpenAI Math Release, 2026-09-23, Section 6, Theorem 6.2's statement (monoid analogues of the group notions used throughout Sections 1-2).

import Mathlib

/-!
Monoid analogues of the group-theoretic notions in `Def_BooneHigman.lean`
(`Word`, `evalWord`, `HasDecidableWordProblem`), needed to state Theorem 6.2 of OpenAI's
"Finite algebraic envelopes and the Boone-Higman conjecture" preprint, Section 6
("a finitely generated monoid H with decidable word problem", "a finitely presented monoid K").
A monoid word problem compares the values of two monoid words (no inverses, since a general
monoid need not have them), rather than testing a single word against the identity.
-/

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

/-- A monoid word: a list of generator indices (no sign bit, since a monoid need not have
inverses). -/
abbrev MonoidWord (generatorCount : ℕ) := List (Fin generatorCount)

def evalMonoidWord {M : Type u} [Monoid M] {generatorCount : ℕ}
    (generators : Fin generatorCount → M) (word : MonoidWord generatorCount) : M :=
  (word.map generators).prod

/-- A monoid has decidable word problem if it has a finite generating set for which equality
of two words' values is computable. -/
def HasDecidableWordProblemMonoid (M : Type u) [Monoid M] : Prop :=
  ∃ (generatorCount : ℕ) (generators : Fin generatorCount → M),
    Submonoid.closure (Set.range generators) = ⊤ ∧
    ComputablePred (fun p : MonoidWord generatorCount × MonoidWord generatorCount =>
      evalMonoidWord generators p.1 = evalMonoidWord generators p.2)

/-- A monoid is finitely presented if it is isomorphic to a monoid presented by finitely many
generators subject to finitely many relations. -/
def IsFinitelyPresentedMonoid (M : Type u) [Monoid M] : Prop :=
  ∃ (n : ℕ) (rels : Finset (FreeMonoid (Fin n) × FreeMonoid (Fin n)))
    (e : M ≃* PresentedMonoid (fun a b => (a, b) ∈ rels)), True

end FiniteAlgebraicEnvelopes
end OAI


