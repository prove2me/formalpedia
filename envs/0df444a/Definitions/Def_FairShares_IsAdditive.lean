-- Prove2me | Definitions.Def_FairShares_IsAdditive
-- name    : FairShares_IsAdditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:35.469292+00:00
-- url     : https://prove2.me/theorems/e0667e3b-f227-494f-bf6c-ac58242c74ce
-- title:
--   Additive valuation over goods
-- statement:
--   Let the set of goods be $M=\{0,\dots,m-1\}$. A valuation $v:2^M\to\mathbb R$ is **additive** if each good $j\in M$ has a value $w_j\ge 0$ and
--   $$
--   v(S)=\sum_{j\in S} w_j\qquad\text{for every } S\subseteq M .
--   $$
--   Additive valuations are normalized ($v(\emptyset)=0$) and non-decreasing, so they are valuations over goods. Theorem 1 concerns every class of valuations that contains all of them.
--
--   **Formalization Note** Goods are `Fin m` and bundles are `Finset (Fin m)`.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §2, p.8

import Mathlib

namespace FairShares

/-- **Additive valuation over goods.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §2, p.8: "A valuation v over the set of goods M is called additive if each good j ∈ M is
associated with a value v(j) ≥ 0, and the value of a set of goods S ⊆ M is v(S) = Σ_{j∈S} v(j)."

A valuation `v` on the bundles of the items `Fin m` is additive when there are nonnegative item
values `w j` with `v S = ∑ j ∈ S, w j` for every bundle `S`.

**Formalization Note.** Items are `Fin m` and bundles are `Finset (Fin m)`; by name
independence any set of `m` items can be named `0, …, m-1`. An additive valuation is
automatically normalized (`v ∅ = 0`) and non-decreasing, i.e. a valuation over goods. -/
def IsAdditive {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ w : Fin m → ℝ, (∀ j, 0 ≤ w j) ∧ ∀ S : Finset (Fin m), v S = ∑ j ∈ S, w j

end FairShares


