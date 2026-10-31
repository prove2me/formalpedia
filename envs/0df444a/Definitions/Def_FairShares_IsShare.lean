-- Prove2me | Definitions.Def_FairShares_IsShare
-- name    : FairShares_IsShare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:20.839886+00:00
-- url     : https://prove2.me/theorems/97aacc32-f3c8-4407-a360-6e86abbae41a
-- title:
--   Share for a class of valuations (Definition 2)
-- statement:
--   A **class** $\mathcal C$ assigns to each number $m$ of goods a set $\mathcal C_m$ of valuations on the bundles of $\{0,\dots,m-1\}$. A function $s$ giving a real number $s_{m,n}(v)$ for $m$ goods, $n$ agents and a valuation $v$ is a **share for $\mathcal C$** if, for every $m$ and every $n\ge 1$, $s_{m,n}$ is realizable and name independent on $\mathcal C_m$ (Definition 2; see `FairShares.IsShareAt`).
--
--   **Formalization Note** A share is a function `(m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ`; the set of $m$ items is `Fin m`, which name independence allows; $n$ ranges over $n\ge1$.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Definition 2, p.9; §3, p.9

import Mathlib
import Definitions.Def_FairShares_IsShareAt

namespace FairShares

/-- **Share for a class of valuations (Definition 2).**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Definition 2, p.9 (see `FairShares.IsShareAt`); §3, p.9: "A share for a class of valuations
C is a function mapping the set M of items, a valuation v in C and number n of agents, to a real
value."

A share is `s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ`, the value `s m n v` for `m` items, `n`
agents and valuation `v`; a class is `C : (m : ℕ) → Set (Finset (Fin m) → ℝ)`. `IsShare C s`:
for all `m` and all `n ≥ 1`, `s m n` is realizable and name independent on `C m`.

**Formalization Note.** The set of `m` items is `Fin m` (name independence makes the choice of
names irrelevant). The number of agents ranges over `n ≥ 1`. -/
def IsShare (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ n → IsShareAt (C m) (s m n)

end FairShares


