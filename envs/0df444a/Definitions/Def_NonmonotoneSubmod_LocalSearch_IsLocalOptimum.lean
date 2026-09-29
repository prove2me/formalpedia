-- Prove2me | Definitions.Def_NonmonotoneSubmod_LocalSearch_IsLocalOptimum
-- name    : NonmonotoneSubmod_LocalSearch_IsLocalOptimum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:59:30.609977+00:00
-- url     : https://prove2.me/theorems/e55095ff-2533-405f-a67d-15634c829850
-- title:
--   Local optimum of a set function under single-element additions and removals
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a set function on a finite ground set $X$. A set $S \subseteq X$ is a **local optimum** of $f$ if neither including a new element in $S$ nor discarding one of the elements of $S$ increases the value of $S$:
--
--   $$f(S \cup \{a\}) \le f(S) \ \text{ for every } a \in X \setminus S, \qquad f(S \setminus \{a\}) \le f(S) \ \text{ for every } a \in S.$$
--
--   Lemma 3.1 of the paper compares the value of a local optimum with that of its subsets and supersets.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1140, §3.1, first paragraph (definition of local optimum)

import Mathlib

namespace NonmonotoneSubmod.LocalSearch

/-- Local optimum (Feige–Mirrokni–Vondrák 2011, §3.1, p. 1140): `S` is a local optimum of `f` if
neither including a new element in `S` nor discarding one of the elements of `S` increases the
value of `S`, i.e. `f (S ∪ {a}) ≤ f S` for every `a ∉ S` and `f (S \ {a}) ≤ f S` for every
`a ∈ S`. -/
def IsLocalOptimum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (S : Finset X) :
    Prop :=
  (∀ a, a ∉ S → f (insert a S) ≤ f S) ∧ (∀ a, a ∈ S → f (S.erase a) ≤ f S)

end NonmonotoneSubmod.LocalSearch


