-- Prove2me | Definitions.Def_NontruthfulPA_Model
-- name    : NontruthfulPA_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:39.705228+00:00
-- url     : https://prove2.me/theorems/fa68b6ea-ffef-4e2e-a139-ec9999d7c192
-- title:
--   Position auctions: $\mathbb R^k_\ge$, rankings, $\alpha$-VCG and $\alpha$-GSP payments, position-deviation equilibrium, efficiency, envy-freeness (22)
-- statement:
--   This module sets up the complete-information position auction of §2 and §3 of the paper.
--
--   1. **Position vectors.** $\mathbb R^k_\ge = \{x \in \mathbb R^k : x_j > 0,\ x_j \ge x_{j'} \text{ if } j < j'\}$, extended by $x_j = 0$ for $j > k$. The bidders' true relative values are $\beta \in \mathbb R^k_\ge$; the auctioneer uses an estimate $\alpha \in \mathbb R^k_\ge$.
--   2. **Rankings.** There are $n$ bidders. A ranking $\sigma$ assigns each bidder a distinct position; $\sigma$ *orders* a vector $x$ if a bidder ranked strictly higher never has a smaller entry. The mechanisms assign positions in non-increasing order of bids, so an allocation is a ranking that orders the bids; ties are resolved by the ranking.
--   3. **Bids in rank order.** $b_{(t)}$ is the bid at position $t$, and $b_{(t)} = 0$ for $t > n$.
--   4. **Payments.** The bidder in position $g$ pays
--   $$p^V = \sum_{j=g}^{k} (\alpha_j - \alpha_{j+1})\, b_{(j+1)} \quad (\alpha\text{-VCG}), \qquad p^S = \alpha_g\, b_{(g+1)} \quad (\alpha\text{-GSP}).$$
--   5. **Equilibrium.** A non-negative bid profile $b$ with an allocation $\sigma$ is an equilibrium if no bidder $i$ gains by being moved to any other position $r$, the others keeping their order, and paying what the mechanism charges at $r$ on the new order. The utility of bidder $i$ in position $g$ at price $p$ is $\beta_g v_i - p$.
--   6. **Efficiency.** The equilibrium is efficient if $\sigma$ also orders the values $v$: positions are assigned in order of valuations. A mechanism *possesses an efficient equilibrium* if some $(b, \sigma)$ is one.
--   7. **Envy-freeness (22).** $(b, \sigma)$ is envy-free if no bidder prefers the position of another bidder at that bidder's current payment:
--   $$\beta_{\sigma(i)} v_i - p_i(b) = \max_{j} \big(\beta_{\sigma(j)} v_i - p_j(b)\big).$$
--
--   Every statement of the mission is phrased in these terms.
--
--   **Formalization Note** Bidders are `Fin n`, positions are 0-based ranks `Fin n` (rank $r$ is position $r+1$), rankings are `Equiv.Perm (Fin n)`, and $\alpha, \beta$ are functions $\mathbb N \to \mathbb R$ that are $0$ from index $k$ on. A payment rule maps the bids in rank order (padded by $0$) and a rank to a price. The deviation moves bidder $i$ to rank $r$ and charges the payment of rank $r$ on the deviated rank list; this position-deviation equilibrium is the notion of §3.1 (p.8) and §3.2 (p.11) and replaces the real-valued deviations of p.6, under which Theorem 1 fails (for $k=2$, $n=3$, $\alpha=(0.6,0.3)$, $\beta=(0.7,0.4)$, $v=(8,7,6)$). Bids are non-negative.
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, §2, pp.6–7 (ℝ^k_≥, allocation rule g, utility, Nash equilibrium, efficiency, b_(i), p^V, p^S); §3.1, p.8 (equilibrium as position deviations); §3.2, p.11 ((22), (23)–(24))

import Mathlib

namespace NontruthfulPA

/-- **Position vectors `ℝ^k_≥`, extended by zero.** Dütting–Fischer–Parkes, *Non-Truthful
Position Auctions Are More Robust to Misspecification*, arXiv:1602.07593v4, §2, p.6:
`ℝ^k_≥ = {x ∈ ℝ^k : x_j > 0, x_j ≥ x_{j'} if j < j'}`, with the conventions `β_j = 0` when
`j > k` (p.6) and `α_j = 0` when `j > k` (p.7).

**Formalization Note.** Positions are 0-based: the entry `x j` (`j : ℕ`) is the paper's
`x_{j+1}`. `IsPosVec k x` says the first `k` entries are positive and non-increasing and every
entry from index `k` on is `0`; this bakes the zero-extension convention into the vector. -/
def IsPosVec (k : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ j, j < k → 0 < x j) ∧ (∀ i j, i ≤ j → j < k → x j ≤ x i) ∧ (∀ j, k ≤ j → x j = 0)

/-- **A ranking orders a vector**, arXiv:1602.07593v4, §2, p.6 ("mechanisms that assign
positions in non-increasing order of bids ... breaks ties in an arbitrary but consistent
manner"). `σ i` is the (0-based) rank of bidder `i`; `Orders σ x` says that a bidder ranked
strictly higher never has a smaller entry: `σ i < σ j → x j ≤ x i`.

**Formalization Note.** Ties in `x` are resolved by `σ`; this is the paper's consistent
tie-breaking. Applied to the bids it says `σ` is an allocation of the rule `g`; applied to the
values it says the allocation is efficient (positions in order of valuations, p.6). -/
def Orders {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, σ i < σ j → x j ≤ x i

/-- **A vector indexed by rank, padded by zero**, arXiv:1602.07593v4, §2, p.7 ("using the
convention that `b_(i) = 0` when `i > n`"). `padBids x t = x_t` (0-based) for `t < n` and `0`
for `t ≥ n`. -/
def padBids {n : ℕ} (x : Fin n → ℝ) (t : ℕ) : ℝ :=
  if h : t < n then x ⟨t, h⟩ else 0

/-- **The bids in rank order (order statistics)**, arXiv:1602.07593v4, §2, p.7: denoting by
`b_(i)` the `(n−i+1)`st order statistic of `b`, `b_(1) ≥ ⋯ ≥ b_(n)`, and `b_(i) = 0` for
`i > n`. `rankBids σ b t` is the bid of the bidder holding rank `t` under `σ`, `0` past the
end.

**Formalization Note.** When `σ` orders `b`, `rankBids σ b t` is the paper's `b_(t+1)`. -/
def rankBids {n : ℕ} (σ : Equiv.Perm (Fin n)) (b : Fin n → ℝ) : ℕ → ℝ :=
  padBids fun r => b (σ.symm r)

/-- A payment rule of a position auction: given the bids in rank order `c` (zero past the end)
and a rank `r`, the payment `pay c r` charged to the bidder holding rank `r`
(arXiv:1602.07593v4, §2, p.7). -/
abbrev PayRule : Type := (ℕ → ℝ) → ℕ → ℝ

/-- **The α-VCG payment** `p^V`, arXiv:1602.07593v4, §2, p.7:
`p^V_i(b) = Σ_{j=g_i(b)}^{k} (α_j − α_{j+1}) b_(j+1)`, with `α_j = 0` for `j > k`.

**Formalization Note.** 0-based: the bidder at rank `r` pays
`Σ_{j ∈ [r, k)} (α j − α (j+1)) · c (j+1)`; the sum is empty, so `0`, when `r ≥ k`. -/
def payV (k : ℕ) (α : ℕ → ℝ) : PayRule := fun c r =>
  ∑ j ∈ Finset.Ico r k, (α j - α (j + 1)) * c (j + 1)

/-- **The α-GSP payment** `p^S`, arXiv:1602.07593v4, §2, p.7:
`p^S_i(b) = α_{g_i(b)} b_(g_i(b)+1)` (the next-lower bid, weighted by `α`).

**Formalization Note.** 0-based: the bidder at rank `r` pays `α r · c (r+1)`; this is `0` for
`r ≥ k` because `α r = 0` there. -/
def payS (α : ℕ → ℝ) : PayRule := fun c r => α r * c (r + 1)

/-- The rank list with the occupant of rank `p` removed: the others keep their order and the
ranks after `p` move up by one (zero past the end). Auxiliary to the position deviations of
arXiv:1602.07593v4, §3.1, p.8. -/
def removeRank (c : ℕ → ℝ) (p : ℕ) : ℕ → ℝ := fun t => if t < p then c t else c (t + 1)

/-- The rank list `c` with the value `x` inserted at rank `r`: ranks below `r` are unchanged,
the rest move down by one. Auxiliary to the position deviations of arXiv:1602.07593v4, §3.1,
p.8. -/
def insertRank (c : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℕ → ℝ := fun t =>
  if t < r then c t else if t = r then x else c (t - 1)

/-- **The rank list after a position deviation**, arXiv:1602.07593v4, §3.1, p.8 ("raising or
lowering their respective bid and being assigned a different position") and §3.2, p.11: the
bidder at rank `p` (with bid `x`) is moved to rank `r`, the other bidders keep their relative
order. -/
def devBids (c : ℕ → ℝ) (p r : ℕ) (x : ℝ) : ℕ → ℝ := insertRank (removeRank c p) r x

/-- **Equilibrium of a position auction (position-deviation form)**, arXiv:1602.07593v4, §2,
p.6 (utility `u_i(b, v_i) = β_{g_i(b)} v_i − p_i(b)`), §3.1, p.8 ("For b to be an equilibrium,
none of the bidders may benefit from raising or lowering their respective bid and being assigned
a different position") and §3.2, p.11 (conditions (23)–(24), which "constrain the utility of
bidder i if instead of position i it was assigned a position j").

`IsPDEquilibrium pay β v b σ`: the bids are non-negative, the ranking `σ` orders the bids (it is
the allocation of `g`), and for every bidder `i` and every rank `r`, moving `i` to rank `r`
(others keeping their order) and charging it what the payment rule charges at rank `r` on the
deviated rank list does not raise `i`'s utility.

**Formalization Note.** This is a declared correction of the p.6 definition (deviations to any
real bid `x` under a fixed tie-breaking allocation), under which Theorem 1 fails
(counterexample: `k = 2`, `n = 3`, `α = (0.6, 0.3)`, `β = (0.7, 0.4)`, `v = (8, 7, 6)`). The
proofs of §3.2 use the position-deviation conditions (23)–(24). Bids and deviation bids are in
`[0, ∞)` (p.6: payments are non-negative; p.8: `b_3 ≥ 0`). Ranks are `Fin n`, 0-based; rank `r`
is position `r + 1`, and ranks `r ≥ k` are unassigned positions worth `0` at price `0`. The bid
written at the deviator's new rank is never read by `payV` or `payS` at that rank. -/
def IsPDEquilibrium {n : ℕ} (pay : PayRule) (β : ℕ → ℝ) (v b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, 0 ≤ b i) ∧ Orders σ b ∧
    ∀ (i r : Fin n),
      β r * v i - pay (devBids (rankBids σ b) (σ i) r (b i)) r ≤
        β (σ i) * v i - pay (rankBids σ b) (σ i)

/-- **Efficient equilibrium**, arXiv:1602.07593v4, §2, p.6 (an efficient assignment is one
"where positions are assigned in order of valuations"): `b` with ranking `σ` is an equilibrium
(`IsPDEquilibrium`) and `σ` also orders the values `v`.

**Formalization Note.** The p.6 wording "`b_i > b_j` whenever `v_i > v_j`" is replaced by the
ranking form: the allocation `σ` of the bids orders the values (part of the declared
correction). -/
def IsEfficientEquilibrium {n : ℕ} (pay : PayRule) (β : ℕ → ℝ) (v b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  IsPDEquilibrium pay β v b σ ∧ Orders σ v

/-- **"The mechanism possesses an efficient Nash equilibrium"** (arXiv:1602.07593v4,
Theorem 1, p.11): some bid profile `b` with some ranking `σ` is an efficient equilibrium. -/
def HasEfficientEquilibrium {n : ℕ} (pay : PayRule) (β : ℕ → ℝ) (v : Fin n → ℝ) : Prop :=
  ∃ (b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), IsEfficientEquilibrium pay β v b σ

/-- **Envy-freeness (22)**, arXiv:1602.07593v4, §3.2, p.11: "bid profile b is called
envy-free if no bidder prefers a different position to the one it is currently assigned at the
current payment for the former, i.e., if for all `i ∈ {1, …, n}`,
`β_{g_i(b)} v_i − p_i(b) = max_{j∈{1,…,n}} β_{g_j(b)} v_i − p_j(b)`."

**Formalization Note.** The maximum is written as: for all bidders `j`,
`β_{σ j} v_i − p_j(b) ≤ β_{σ i} v_i − p_i(b)` (the term `j = i` attains it). Payments are those
of the rank list `rankBids σ b` under the given payment rule. -/
def IsEnvyFree {n : ℕ} (pay : PayRule) (β : ℕ → ℝ) (v b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n,
    β (σ j) * v i - pay (rankBids σ b) (σ j) ≤ β (σ i) * v i - pay (rankBids σ b) (σ i)

end NontruthfulPA


