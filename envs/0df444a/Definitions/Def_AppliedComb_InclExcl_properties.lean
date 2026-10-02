-- Prove2me | Definitions.Def_AppliedComb_InclExcl_properties
-- name    : AppliedComb_InclExcl_properties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:24.178529+00:00
-- url     : https://prove2.me/theorems/b459f5cf-7b53-432c-97f4-95f2f5a1c77c
-- title:
--   The properties 'i is not in the range of f' and 'σ(i) = i' (Examples 7.4 and 7.5)
-- statement:
--   Two families of properties used in Chapter 7.
--
--   *Functions (Example 7.4, Section 7.3).* Let $n, m \ge 0$ and let $X$ be the set of all functions $f : [n] \to [m]$. For $i \in [m]$, the function $f$ satisfies property $P_i$ if there is no $j \in [n]$ with $f(j) = i$, that is, $i$ is not in the range of $f$:
--   $$f \text{ satisfies } P_i \iff \forall j \in [n],\ f(j) \ne i.$$
--   The functions satisfying none of these properties are exactly the surjections $[n] \to [m]$.
--
--   *Permutations (Example 7.5, Section 7.4).* Let $n \ge 0$ and let $X$ be the set of all permutations $\sigma$ of $[n]$. For $i \in [n]$, $\sigma$ satisfies property $P_i$ if $\sigma(i) = i$. The permutations satisfying none of these properties are the derangements.
--
--   **Formalization Note.** `NotInRange n m i f` is `∀ j : Fin n, f j ≠ i` for `f : Fin n → Fin m` and `i : Fin m`; `FixesPoint n i σ` is `σ i = i` for `σ : Equiv.Perm (Fin n)` and `i : Fin n`. The book's $[n] = \{1, \dots, n\}$ is re-indexed as `Fin n` $= \{0, \dots, n-1\}$. Each family comes with its `DecidablePred` instance so that it can be passed to `N`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 143, Examples 7.4 and 7.5; p. 146 (Section 7.3); p. 147 (Section 7.4)

import Mathlib

namespace AppliedComb.InclExcl

/-- The properties of Example 7.4 and Section 7.3 (Keller & Trotter, pp. 143 and 146): `X` is
the set of all functions from `[n]` to `[m]` (here `Fin n → Fin m`), and a function `f`
satisfies property `P_i` if there is no `j` with `f j = i`, i.e. `i` is not in the range of `f`. -/
def NotInRange (n m : ℕ) (i : Fin m) (f : Fin n → Fin m) : Prop :=
  ∀ j : Fin n, f j ≠ i

instance (n m : ℕ) (i : Fin m) : DecidablePred (NotInRange n m i) :=
  fun f => inferInstanceAs (Decidable (∀ j : Fin n, f j ≠ i))

/-- The properties of Example 7.5 and Section 7.4 (Keller & Trotter, pp. 143 and 147): `X` is
the set of all permutations of `[n]` (here `Equiv.Perm (Fin n)`), and a permutation `σ`
satisfies property `P_i` if `σ(i) = i`. -/
def FixesPoint (n : ℕ) (i : Fin n) (σ : Equiv.Perm (Fin n)) : Prop :=
  σ i = i

instance (n : ℕ) (i : Fin n) : DecidablePred (FixesPoint n i) :=
  fun σ => inferInstanceAs (Decidable (σ i = i))

end AppliedComb.InclExcl


