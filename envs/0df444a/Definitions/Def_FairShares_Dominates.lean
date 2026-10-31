-- Prove2me | Definitions.Def_FairShares_Dominates
-- name    : FairShares_Dominates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:38.864595+00:00
-- url     : https://prove2.me/theorems/1b93a6f3-5225-4760-aa86-ecee0588cc49
-- title:
--   Domination between shares
-- statement:
--   A share $s$ **dominates** a share $s'$ for the class $\mathcal C$ if
--   $$
--   s_{m,n}(v)\ \ge\ s'_{m,n}(v)\qquad\text{for every } m,\ \text{every } n\ge 1 \text{ and every } v\in\mathcal C_m .
--   $$
--
--   **Formalization Note** "For every $n$ for which $s$ and $s'$ are defined" is every $n\ge1$; the number of goods is quantified as well.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §3.3, p.13

import Mathlib

namespace FairShares

/-- **Domination between shares.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §3.3, p.13: "A share (function) s dominates share (function) s′ for a class of valuations
functions C, if for every n (for which s and s′ are defined) and every valuation v ∈ C it holds
that s(v, n) ≥ s′(v, n)."

`Dominates C s s'`: `s' m n v ≤ s m n v` for every `m`, every `n ≥ 1` and every `v ∈ C m`.

**Formalization Note.** Shares are defined for every `n ≥ 1` (see `FairShares.IsShare`); the
number of items `m` is quantified as well, since the paper's `v ∈ C` ranges over valuations on
every item set. -/
def Dominates (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (s s' : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ n → ∀ v ∈ C m, s' m n v ≤ s m n v

end FairShares


