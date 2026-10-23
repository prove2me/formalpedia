-- Prove2me | Definitions.Def_AnyPriceShare_Bidding_Basic
-- name    : AnyPriceShare_Bidding_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:13:39.993035+00:00
-- url     : https://prove2.me/theorems/5f5f4784-7bae-4670-8abd-869b3e33e30c
-- title:
--   Definitions 1.1, 3.1, 4.1, pp. 4, 7–9, 12 — additive values, allocations, proportional share, AnyPrice share (price and packing forms), truncated proportional share, ranked item
-- statement:
--   This file fixes the share notions of Babaioff, Ezra and Feige for a set of $m$ indivisible items. Throughout, $S\subseteq M$ is the set of items being shared (in the main results $S=M$, the set of all items), and every share takes $S$ explicitly.
--
--   1. **Additive valuation** (§2, p. 7). An agent with item values $u(j)$ values a bundle $T$ at $u(T)=\sum_{j\in T}u(j)$.
--   2. **Allocation** (§2, p. 7). An allocation of all items to $n$ agents is a map $\sigma$ sending each item $j$ to an agent $\sigma(j)$; the bundle of agent $i$ is $A_i=\{j:\sigma(j)=i\}$ (possibly empty). Every item is allocated.
--   3. **Proportional share** (p. 7). $\mathrm{Proportional}(\beta,u,S)=\beta\cdot u(S)$.
--   4. **AnyPrice share, price form** (Definition 1.1, p. 4). For a valuation $w$ on bundles and an entitlement $\beta$,
--   $$\mathrm{AnyPrice}(\beta,w,S)=\min_{p}\ \max\Big\{w(T)\ \Big|\ T\subseteq S,\ \sum_{j\in T}p_j\le\beta\Big\},$$
--   where $p$ ranges over price vectors with $p_j\ge0$ for $j\in S$ and $\sum_{j\in S}p_j=1$: the value the agent can guarantee herself with budget $\beta$ when the items are priced adversarially with total price $1$.
--   5. **AnyPrice share, packing form** (Definition 3.1, pp. 8–9). $\mathrm{AnyPrice}^{D}(\beta,w,S)$ is the largest $z$ for which there are weights $\lambda_T$, $T\subseteq S$, with
--      - $\sum_{T\subseteq S}\lambda_T=1$ and $\lambda_T\ge0$ for all $T$,
--      - $\lambda_T=0$ whenever $w(T)<z$,
--      - $\sum_{T\ni j}\lambda_T\le\beta$ for every item $j\in S$.
--   6. **Truncated Proportional Share** (Definition 4.1, display (1), p. 12). For an additive valuation $u$,
--   $$\mathrm{TPS}(\beta,u,S)=\max\Big\{z\ \Big|\ \beta\cdot\sum_{j\in S}\min(u(j),z)=z\Big\}.$$
--   7. **Ranked item** (Theorem 4.3, p. 14). The value of the $k$-th ranked item of $S$ is the $k$-th largest of the values $u(j)$, $j\in S$, counted with multiplicity.
--
--   Proposition 3.2 of the paper shows that the two AnyPrice forms agree; the main theorem is stated with the price form.
--
--   **Formalization Note** Items are `Fin m` (0-based) and values are real. The minimum over prices is an infimum over the price vectors constrained on $S$ only (prices off $S$ are irrelevant); for $S\ne\emptyset$ the family is nonempty and bounded below by $w(\emptyset)$, and it takes finitely many values, so the infimum is the paper's minimum; for $S=\emptyset$ there is no price vector and the value is $0$. The inner maximum is a supremum over the finitely many affordable bundles (nonempty since $\emptyset$ is affordable for $\beta\ge0$). The packing-form and TPS sets are written as real suprema: for $\beta\ge0$ (and non-negative values for TPS) the sets are nonempty ($z=w(\emptyset)$, resp. $z=0$) and bounded above (by some $w(T)$, resp. by $\beta\,u(S)$), and the suprema are attained. The ranked value is $0$ for $k=0$ or $k>|S|$, a convention the paper does not need to fix.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, pp. 4, 7–9, 12, 14; Definitions 1.1, 3.1, 4.1 (display (1))

import Mathlib

namespace AnyPriceShare.Bidding

/-- §2, p. 7: the additive valuation with item values `u j`, `v(T) = ∑_{j ∈ T} u j`. -/
def addVal {m : ℕ} (u : Fin m → ℝ) (T : Finset (Fin m)) : ℝ :=
  ∑ j ∈ T, u j

/-- §2, p. 7: an allocation of all items to the `n` agents, item `j` going to agent `σ j`;
`allocBundle σ i` is the bundle `A_i` of agent `i` (possibly empty). -/
def allocBundle {n m : ℕ} (σ : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => σ j = i)

/-- §2, p. 7: the proportional share `Proportional(β, u, S) = β · u(S)` of an additive valuation. -/
def proportional {m : ℕ} (β : ℝ) (u : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  β * ∑ j ∈ S, u j

/-- Definition 1.1, p. 4 (restated p. 8): the AnyPrice share, price form, of a valuation `w` with
entitlement `β` over the item set `S`,
`min_{p ≥ 0, ∑_{j ∈ S} p_j = 1} max { w(T) | T ⊆ S, ∑_{j ∈ T} p_j ≤ β }`.
Prices are only constrained on `S`. For `S = ∅` there is no price vector and the value is `0`. -/
noncomputable def anyPrice {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) : ℝ :=
  ⨅ p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
    ⨆ T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β}, w T.1

/-- Definition 3.1, pp. 8–9: the AnyPrice share, packing (dual) form: the maximum `z` for which
there are weights `λ_T` (`T ⊆ S`) with `∑_T λ_T = 1`, `λ_T ≥ 0`, `λ_T = 0` whenever `w(T) < z`,
and `∑_{T ∋ j} λ_T ≤ β` for every item `j ∈ S`. -/
noncomputable def anyPriceDual {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) : ℝ :=
  sSup {z : ℝ | ∃ lam : Finset (Fin m) → ℝ,
    (∑ T ∈ S.powerset, lam T = 1) ∧
    (∀ T ∈ S.powerset, 0 ≤ lam T) ∧
    (∀ T ∈ S.powerset, w T < z → lam T = 0) ∧
    (∀ j ∈ S, ∑ T ∈ S.powerset with j ∈ T, lam T ≤ β)}

/-- Definition 4.1, display (1), p. 12: the Truncated Proportional Share of an additive valuation
with item values `u`, `TPS(β, u, S) = max { z | β · ∑_{j ∈ S} min(u j, z) = z }`. -/
noncomputable def tps {m : ℕ} (β : ℝ) (u : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  sSup {z : ℝ | β * ∑ j ∈ S, min (u j) z = z}

/-- Theorem 4.3, p. 14 (third bullet): the value of the `k`-th ranked item of `S` under `u`, i.e.
the `k`-th largest of the values `u j`, `j ∈ S`, counted with multiplicity (1-based).
Convention: `0` when `k = 0` or `k > |S|`. -/
noncomputable def rankedValue {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (k : ℕ) : ℝ :=
  if k = 0 then 0 else ((S.val.map u).sort (· ≥ ·)).getD (k - 1) 0

end AnyPriceShare.Bidding


