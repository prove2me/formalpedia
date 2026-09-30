-- Prove2me | Definitions.Def_SupplyChainTheory_auctions
-- name    : SupplyChainTheory_auctions
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T01:13:13.45832+00:00
-- url     : https://prove2.me/theorems/b6f54243-92fa-44df-a4cd-24d76499b303
-- title:
--   The VCG auction as a cooperative game, Chapter 15: coalitional value functions, the combinatorial auction value, the core, the VCG payoff vector, bidder dominance and bidder-submodularity
-- statement:
--   The cooperative-game view of the Vickrey-Clarke-Groves auction in Sect. 15.4.3 of Snyder and
--   Shen. Players are `Fin (n+1)`: $0$ is the auctioneer and $1, \dots, n$ are the bidders.
--
--   A **coalitional value function** (`IsCoalitionalValue V`) assigns to every coalition $T$ the
--   value it can create: $V(T) = 0$ when the auctioneer is not in $T$, and $V$ is monotone, adding
--   players never lowers the value. For a combinatorial auction with objects `Fin m` and
--   valuations $v_{iS}$ of bidder $i$ for bundle $S$, `capValue v T` is the coalitional value
--   function of the book: the optimal value of the auctioneer's allocation problem restricted to
--   the bidders of $T$, each receiving at most one bundle, bundles pairwise disjoint, and $0$ when
--   $0 \notin T$.
--
--   The **core** `InCore V S π` of the game on a coalition $S \ni 0$ is the set of payoff vectors
--   $\pi$ with $\sum_{k \in S} \pi_k = V(S)$ and $V(T) \le \sum_{k \in T} \pi_k$ for every
--   sub-coalition $T \subseteq S$. The **VCG payoff vector** `vcgPayoff V S` of (15.23)-(15.24) gives
--   bidder $k$ its marginal contribution $\bar\pi_k(S) = V(S) - V(S \setminus k)$ and the
--   auctioneer $\bar\pi_0(S) = V(S) - \sum_{k \ne 0} \bar\pi_k(S)$. A vector is **bidder dominant**
--   (`BidderDominant V S π`) if it lies in the core and every bidder weakly prefers it to every
--   other core vector. $V$ is **bidder-submodular** (`BidderSubmodular V`) if for every bidder $k$
--   and coalitions $0 \in S \subseteq S'$, $V(S' \cup k) - V(S') \le V(S \cup k) - V(S)$.
--
--   **Formalization Note** The book writes the core's budget equation as a sum over the bidders,
--   but its proofs use the sum over all players including the auctioneer, which is the standard
--   definition and the one used here. The theorems are stated for any coalitional value function
--   with the two properties, which `capValue` has (`cap_value_is_coalitional`), so they cover the
--   book's auction and any monotone game with a null coalition condition.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, Sect. 15.4.3 pp. 605-607 (the coalitional value function, the core, Eq. 15.23-15.24, bidder dominance, bidder-submodularity)

import Mathlib

namespace SupplyChainTheory

/-! ### The VCG auction as a cooperative game, Sect. 15.4.3 -/

/-- Players are `Fin (n+1)`: `0` is the auctioneer and `1, …, n` are the bidders. A function on
coalitions is a coalitional value function when coalitions without the auctioneer create no
value and adding players never lowers the value. -/
def IsCoalitionalValue {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) : Prop :=
  (∀ T, (0 : Fin (n + 1)) ∉ T → V T = 0) ∧ Monotone V

/-- `V(T)` for the combinatorial auction: the optimal value of the auctioneer's problem (CAP) with
the bidders restricted to `T`, each bidder receiving at most one bundle, bundles pairwise
disjoint, and `V(T) = 0` when the auctioneer is not in `T`. Bidder `i : Fin n` is player `i.succ`. -/
noncomputable def capValue {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (T : Finset (Fin (n + 1))) :
    ℝ :=
  if (0 : Fin (n + 1)) ∈ T then
    sSup {w | ∃ y : Fin n → Option (Finset (Fin m)), (∀ i, i.succ ∉ T → y i = none)
      ∧ (∀ i j, i ≠ j → ∀ A B, y i = some A → y j = some B → Disjoint A B)
      ∧ w = ∑ i, (y i).elim 0 (v i)}
  else 0

/-- The core `C(S, V)` of the game restricted to the coalition `S`: payoff vectors whose total
on `S` is `V(S)` and which no sub-coalition can improve upon. -/
def InCore {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1)))
    (π : Fin (n + 1) → ℝ) : Prop :=
  ∑ k ∈ S, π k = V S ∧ ∀ T ⊆ S, V T ≤ ∑ k ∈ T, π k

/-- (15.23)-(15.24): the VCG payoff vector `π̄(S)` of the game on `S`: bidder `k` receives
`V(S) − V(S ∖ k)` and the auctioneer the remainder. -/
def vcgPayoff {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    ℝ :=
  if k = 0 then V S - ∑ l ∈ S.erase 0, (V S - V (S.erase l)) else V S - V (S.erase k)

/-- A payoff vector is bidder dominant on `S` if it lies in the core and gives every bidder at
least as much as every other core vector. -/
def BidderDominant {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1)))
    (π : Fin (n + 1) → ℝ) : Prop :=
  InCore V S π ∧ ∀ π', InCore V S π' → ∀ k ∈ S, k ≠ 0 → π' k ≤ π k

/-- Bidder-submodularity: the marginal value of a bidder is weakly decreasing in the coalition. -/
def BidderSubmodular {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) : Prop :=
  ∀ k : Fin (n + 1), k ≠ 0 → ∀ S S' : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → S ⊆ S' →
    V (insert k S') - V S' ≤ V (insert k S) - V S
end SupplyChainTheory


