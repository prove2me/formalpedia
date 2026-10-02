-- Prove2me | Definitions.Def_AppliedComb_InclExcl_N
-- name    : AppliedComb_InclExcl_N
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:01.309814+00:00
-- url     : https://prove2.me/theorems/168a2cf1-662a-4e85-b60d-43ca64066947
-- title:
--   The count N(S) of elements satisfying a set of properties (Section 7.2)
-- statement:
--   Let $X$ be a finite set and let $\mathcal P = \{P_1, P_2, \dots, P_m\}$ be a family of **properties**: for every $x \in X$ and each $i = 1, \dots, m$, either $x$ satisfies $P_i$ or it does not. For each subset $S \subseteq [m] = \{1, \dots, m\}$, let
--   $$N(S) = \bigl|\{x \in X : x \text{ satisfies } P_i \text{ for all } i \in S\}\bigr|.$$
--   In particular $N(\emptyset) = |X|$, since every element vacuously satisfies every property in the empty set.
--
--   This is the quantity summed with alternating signs in the Principle of Inclusion-Exclusion (Theorem 7.7), and it is computed for two concrete families of properties in Lemmas 7.8 and 7.10.
--
--   **Formalization Note.** $X$ is a type with `[Fintype X]`; the properties are a predicate family `P : Fin m → X → Prop` with decidable instances, so $[m]$ is re-indexed as `Fin m` $= \{0, \dots, m-1\}$. `N P S` is the cardinality of the `Finset.filter` of `Finset.univ` by `∀ i ∈ S, P i x`, a natural number.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 144, Section 7.2 (definition of N(S))

import Mathlib

namespace AppliedComb.InclExcl

/-- The count `N(S)` of the Principle of Inclusion-Exclusion (Keller & Trotter, *Applied
Combinatorics*, 2017 Edition, p. 144, Section 7.2). `X` is a finite set, `P i` for `i : Fin m`
is the `i`-th property of the family `P = {P_1, …, P_m}` (the book's `[m] = {1, …, m}` is
re-indexed as the 0-based `Fin m`), and for `S ⊆ [m]`, `N P S` is the number of elements of
`X` which satisfy property `P i` for all `i ∈ S`. In particular `N P ∅ = |X|`. -/
def N {X : Type*} [Fintype X] {m : ℕ} (P : Fin m → X → Prop) [∀ i, DecidablePred (P i)]
    (S : Finset (Fin m)) : ℕ :=
  (Finset.univ.filter (fun x : X => ∀ i ∈ S, P i x)).card

end AppliedComb.InclExcl


