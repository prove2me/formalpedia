-- Prove2me | Definitions.Def_WhitneyMatroid_Binary_IsStrictFundamentalSet
-- name    : WhitneyMatroid_Binary_IsStrictFundamentalSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:43:11.508342+00:00
-- url     : https://prove2.me/theorems/508c3211-ef98-4747-ada1-e0c305c0efd6
-- title:
--   Strict fundamental set of circuits with respect to $e_{n-q+1}, \dots, e_n$ (§9)
-- statement:
--   Let $M$ be a matroid on the elements $e_1, \dots, e_n$ with $n = r + q$, and let $P_1, \dots, P_q$ be subsets of these elements. Following Whitney (§9), $P_1, \dots, P_q$ form a **strict fundamental set of circuits with respect to** $e_{n-q+1}, \dots, e_n$ when
--
--   1. $q = n(M)$, the **nullity** of $M$, that is, the number of elements of $M$ minus its rank: $r(M) + q = \rho(M)$;
--   2. each $P_i$ is a circuit of $M$;
--   3. $P_i$ contains $e_{n-q+i}$ but no $e_{n-q+j}$ for $j \neq i$:
--
--   $$P_i \cap \{e_{n-q+1}, \dots, e_n\} = \{e_{n-q+i}\} \qquad (i = 1, \dots, q).$$
--
--   (Whitney's non-strict fundamental sets only forbid $e_{n-q+j}$ with $j > i$; only the strict notion is used here.) A strict fundamental set is the matroid counterpart of a matrix in which the columns of $e_{n-q+1}, \dots, e_n$ have been reduced to a unit matrix.
--
--   **Formalization Note** The elements $e_1, \dots, e_n$ are `Fin (r + q)` with $e_k \mapsto k - 1$, so $e_1, \dots, e_{n-q}$ is the range of `Fin.castAdd q` and $e_{n-q+i}$ is `Fin.natAdd r (i - 1)`; the family is indexed by `Fin q`, so Lean's `P i` is Whitney's $P_{i+1}$. Writing $n = r + q$ avoids natural-number subtraction. The nullity condition is stated without subtraction as `M.eRank + q = M.E.encard` in $\mathbb N_\infty$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 517, §9 (fundamental set of circuits, strict, with respect to e_{n−q+1}, ⋯, e_n); p. 510, §2 (nullity n(M) = ρ(M) − r(M))

import Mathlib

namespace WhitneyMatroid.Binary

/-- Strict fundamental set of circuits (§9, p. 517). The elements `e₁, …, eₙ` of the matroid,
`n = r + q`, are `Fin (r + q)` with `e_k ↦ k - 1`; so `e₁, …, e_{n-q}` is the range of
`Fin.castAdd q` and `e_{n-q+i}` (`i = 1, …, q`) is `Fin.natAdd r (i - 1)`. The family
`P : Fin q → Set (Fin (r + q))` (Whitney's `P₁, …, P_q`, index shifted by one) is a strict
fundamental set of circuits of `M` with respect to `e_{n-q+1}, …, eₙ` when
* `q = n(M)`: the nullity of `M` (number of elements minus rank) is `q`, i.e.
  `r(M) + q = ρ(M)`;
* each `Pᵢ` is a circuit of `M`;
* `Pᵢ` contains `e_{n-q+i}` but no `e_{n-q+j}` with `j ≠ i`. -/
def IsStrictFundamentalSet {r q : ℕ} (M : Matroid (Fin (r + q)))
    (P : Fin q → Set (Fin (r + q))) : Prop :=
  M.eRank + q = M.E.encard ∧
  (∀ i, M.IsCircuit (P i)) ∧
  ∀ i j : Fin q, Fin.natAdd r j ∈ P i ↔ j = i

end WhitneyMatroid.Binary


