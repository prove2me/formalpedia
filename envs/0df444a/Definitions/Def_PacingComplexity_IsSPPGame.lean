-- Prove2me | Definitions.Def_PacingComplexity_IsSPPGame
-- name    : PacingComplexity_IsSPPGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:23.126474+00:00
-- url     : https://prove2.me/theorems/992d6373-a724-40ec-beea-5412351686a8
-- title:
--   Second-price pacing game (SPP game)
-- statement:
--   In a **second-price pacing game** (SPP game) $G=(n,m,(v_{ij}),(B_i))$ there are $n$ buyers and $m$ indivisible goods, each sold through its own single-slot second-price auction. Buyer $i$ has value $v_{ij}$ for good $j$ and budget $B_i$. The data form an SPP game when
--
--   1. $v_{ij}\ge 0$ for all $i,j$ and $B_i>0$ for all $i$;
--   2. every good is valued by someone: for each $j$ there is $i$ with $v_{ij}>0$;
--   3. every buyer values something: for each $i$ there is $j$ with $v_{ij}>0$.
--
--   Each buyer plays by choosing a pacing multiplier $\alpha_i\in[0,1]$ and bidding $\alpha_i v_{ij}$ on every good $j$.
--
--   **Formalization Note** Buyers and goods are arbitrary types; values and budgets are real. The search problem APPROX-PACING$_c$ instantiates them with $n$ and $m$ elements and rational data.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, §2, p.6 (SPP game G = (n, m, (vij), (Bi)), conditions (1) and (2))

import Mathlib

namespace PacingComplexity

/-- **Second-price pacing game** (SPP game) of Chen, Kroer, Kumar, *The Complexity of Pacing for
Second-Price Auctions*, arXiv:2103.13969v2, §2, p.6: "there are n buyers and m (indivisible)
goods … We use vij ≥ 0 … to denote the value of good j to buyer i, and Bi > 0 to denote the budget
of buyer i. We will require (1) for each j ∈ [m], vij > 0 for some i ∈ [n], and (2) for each
i ∈ [n], vij > 0 for some j ∈ [m]."

`IsSPPGame v B` holds iff all values are non-negative, all budgets are positive, every good is
valued positively by some buyer (condition (1)) and every buyer values some good positively
(condition (2)).

**Formalization Note** Buyers and goods are arbitrary types `N`, `G` (finite wherever the game is
played); values `v : N → G → ℝ` and budgets `B : N → ℝ` are real. The search problem
`ApproxPacing` uses `N = Fin n`, `G = Fin m` with rational data. -/
def IsSPPGame {N G : Type} (v : N → G → ℝ) (B : N → ℝ) : Prop :=
  (∀ i j, 0 ≤ v i j) ∧ (∀ i, 0 < B i) ∧ (∀ j, ∃ i, 0 < v i j) ∧ (∀ i, ∃ j, 0 < v i j)

end PacingComplexity


