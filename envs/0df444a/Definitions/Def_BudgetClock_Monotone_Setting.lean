-- Prove2me | Definitions.Def_BudgetClock_Monotone_Setting
-- name    : BudgetClock_Monotone_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:10.272978+00:00
-- url     : https://prove2.me/theorems/fe059e10-d11c-49a8-b022-0e435eb37b4f
-- title:
--   §2, p. 5 — monotone valuations, marginal values, list prices and the longest budget-feasible prefix
-- statement:
--   The procurement model of §2. A set $N$ of $n$ bidders is identified with $\{0, \dots, n-1\}$; the auctioneer has a valuation $v : 2^N \to \mathbb R$ on sets of bidders, each bidder $i$ a private cost $c_i \ge 0$, and the auctioneer a budget $B$.
--
--   1. The valuation $v$ is **monotone** if $v(S) \le v(T)$ whenever $S \subseteq T \subseteq N$.
--   2. The **marginal contribution** of $T$ added to $S$ is
--   $$v(T \mid S) = v(S \cup T) - v(S).$$
--   3. The mechanism keeps sets of bidders as lists in the order in which bidders were added. For prices $p = (p_i)_{i \in N}$ and a list $\ell$, the **price of $\ell$** is $\sum_{i \in \ell} p_i$, and $\ell$ is **budget feasible** if its price is at most $B$.
--   4. The **prefix of length $k$** of a list consists of its first $k$ entries. The **longest budget-feasible prefix** of $\ell$ is the prefix of the largest length $k \le |\ell|$ whose price is at most $B$.
--
--   These are the objects in terms of which Mechanism 1 (Iterative-Pruning) and Algorithm 2 (Maximize-Value) are written.
--
--   **Formalization Note** Bidders are `Fin n`, sets are `Finset (Fin n)`, ordered sets are `List (Fin n)`. Submodularity is the published definition `NonmonotoneSubmod.Shared.Submodular` (the lattice inequality of §2). Non-negativity of $v$ and of the costs is kept as a hypothesis of each theorem rather than built into the types, so that subtraction is real subtraction. If no prefix is budget feasible (only possible when $B < 0$), the longest budget-feasible prefix is the empty list.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 5, §2 Preliminaries; p. 6, §3 (prefixes)

import Mathlib

namespace BudgetClock.Monotone

/-! §2, p. 5 (Balkanski et al., arXiv:2107.09239v2): the procurement model. Bidders are `Fin n`,
sets of bidders are `Finset (Fin n)`, a valuation is `v : Finset (Fin n) → ℝ`, costs and prices
are `Fin n → ℝ`. Sets the mechanism builds in insertion order are `List (Fin n)`. -/

/-- §2, p. 5: `v` is monotone if `v S ≤ v T` whenever `S ⊆ T`. -/
def IsMonotone {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S T : Finset (Fin n), S ⊆ T → v S ≤ v T

/-- §2, p. 5: the marginal contribution `v(T | S) = v(S ∪ T) - v(S)` of `T` added to `S`. -/
def marg {n : ℕ} (v : Finset (Fin n) → ℝ) (T S : Finset (Fin n)) : ℝ :=
  v (S ∪ T) - v S

/-- Total price `∑_{i ∈ l} p i` of the bidders of a list `l` (the lists the mechanism builds
have no repeated bidder, so this is the price of the set `l.toFinset`). -/
def listCost {n : ℕ} (p : Fin n → ℝ) (l : List (Fin n)) : ℝ :=
  (l.map p).sum

/-- The longest budget-feasible prefix of the list `l` at prices `p` and budget `B`: the prefix
`l.take k` for the largest `k ≤ l.length` with `∑_{i ∈ l.take k} p i ≤ B` (`k = 0` if no prefix,
not even the empty one, is feasible). -/
noncomputable def longestFeasiblePrefix {n : ℕ} (p : Fin n → ℝ) (B : ℝ) (l : List (Fin n)) :
    List (Fin n) :=
  l.take (Nat.findGreatest (fun k => listCost p (l.take k) ≤ B) l.length)

end BudgetClock.Monotone


