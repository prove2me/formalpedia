-- Prove2me | Definitions.Def_MultPacing_Existence_Model
-- name    : MultPacing_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:18.544693+00:00
-- url     : https://prove2.me/theorems/0b648600-5468-476d-884c-5cd5cf9eb73d
-- title:
--   §3, Definition 2, pp. 6, 9 — pacing game, highest other paced bid, second price pacing equilibrium (SPPE)
-- statement:
--   **Pacing game.** A finite set $N$ of buyers targets a finite set $G$ of divisible goods (the paper's $N=\{1,\dots,n\}$ and $M=\{1,\dots,m\}$). Each buyer $i$ has a valuation $v_{ij}\ge 0$ for each good $j$ and a budget $B_i>0$. Each buyer chooses a pacing multiplier $\alpha_i\in[0,1]$ and bids $\alpha_i v_{ij}$ on every good $j$; each good is sold in a single-slot second price auction.
--
--   **Highest other bid.** For a profile $\alpha$, a buyer $i$ and a good $j$,
--   $$
--   \operatorname{ho}_{ij}(\alpha)=\max_{k\ne i}\ \alpha_k v_{kj},
--   $$
--   with the convention $\operatorname{ho}_{ij}(\alpha)=0$ when $i$ is the only buyer.
--
--   **Second price pacing equilibrium (SPPE).** A vector of pacing multipliers $\alpha\in[0,1]^N$, allocations $x_{ij}\in[0,1]$ of good $j$ to buyer $i$, and per-unit prices $p_j$ form an SPPE when, writing $s_{ij}=p_j x_{ij}$ for the spend of buyer $i$ on good $j$:
--
--   1. for every good $j$, $\sum_i x_{ij}\le 1$, with equality if some buyer $i$ has $v_{ij}>0$;
--   2. if $x_{ij}>0$ then $i$'s bid is (possibly tied for) the highest on $j$: $\alpha_k v_{kj}\le \alpha_i v_{ij}$ for all $k$;
--   3. if $x_{ij}>0$ then $p_j=\operatorname{ho}_{ij}(\alpha)$ (second price);
--   4. for every buyer $i$, $\sum_j s_{ij}\le B_i$ (budget);
--   5. if $\sum_j s_{ij}<B_i$ then $\alpha_i=1$ (no unnecessary pacing).
--
--   This is the equilibrium notion whose existence is the goal of the mission (Theorem 1).
--
--   **Formalization Note** Buyers and goods are arbitrary finite types `N`, `G`. The game is the structure `PacingGame N G` carrying $v\ge 0$ and $B>0$. The highest other bid is a `Finset.sup'` over the other buyers, with value $0$ when there is none; since all bids are nonnegative in an SPPE this agrees with $\max(0,\cdot)$. The price vector $p$ is an argument of `IsSPPE`; it is pinned to the highest other bid on every good someone wins.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, pp. 6, 9 (PDF 6, 9), §3 (model) and Definition 2

import Mathlib

namespace MultPacing.Existence

/-- A pacing game (§3, p. 6): a finite set `N` of buyers, a finite set `G` of divisible goods,
valuations `v i j ≥ 0` and budgets `B i > 0`. -/
structure PacingGame (N G : Type*) where
  /-- valuation `v_ij` of buyer `i` for good `j` -/
  v : N → G → ℝ
  /-- budget `B_i` of buyer `i` -/
  B : N → ℝ
  v_nonneg : ∀ i j, 0 ≤ v i j
  B_pos : ∀ i, 0 < B i

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- The highest paced bid `α_k v_kj` on good `j` among buyers `k ≠ i`; it is `0` when `i` is the
only buyer (a lone bidder pays nothing, p. 16). -/
noncomputable def highestOther (v : N → G → ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  if h : (Finset.univ.erase i).Nonempty then
    (Finset.univ.erase i).sup' h (fun k => α k * v k j)
  else 0

/-- Second price pacing equilibrium (Definition 2, p. 9). `α` are the pacing multipliers, `x i j`
the fraction of good `j` allocated to buyer `i`, and `p j` the per-unit price of good `j`; the spend
of buyer `i` on good `j` is `s_ij = p_j x_ij`. -/
structure IsSPPE (P : PacingGame N G) (α : N → ℝ) (x : N → G → ℝ) (p : G → ℝ) : Prop where
  /-- `α ∈ [0,1]^N` -/
  alpha_mem : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1
  /-- `x_ij ∈ [0,1]` -/
  alloc_mem : ∀ i j, x i j ∈ Set.Icc (0 : ℝ) 1
  /-- `∑_i x_ij ≤ 1` for every good `j` -/
  supply : ∀ j, ∑ i, x i j ≤ 1
  /-- equality when some buyer values good `j` -/
  full_alloc : ∀ j, (∃ i, 0 < P.v i j) → ∑ i, x i j = 1
  /-- a buyer with `x_ij > 0` has a (possibly tied) highest bid on `j` -/
  winner_top : ∀ i j, 0 < x i j → ∀ k, α k * P.v k j ≤ α i * P.v i j
  /-- second price: if `x_ij > 0` then `p_j` is the highest bid other than `i`'s -/
  second_price : ∀ i j, 0 < x i j → p j = highestOther P.v α i j
  /-- budget constraint `∑_j p_j x_ij ≤ B_i` -/
  budget : ∀ i, ∑ j, p j * x i j ≤ P.B i
  /-- no unnecessary pacing: a buyer with budget slack has `α_i = 1` -/
  no_unnecessary_pacing : ∀ i, ∑ j, p j * x i j < P.B i → α i = 1

end MultPacing.Existence


