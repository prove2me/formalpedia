-- Prove2me | Definitions.Def_DraftPoA_Auction
-- name    : DraftPoA_Auction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:35.61621+00:00
-- url     : https://prove2.me/theorems/57184244-dce1-4e9c-8559-8613dddf59b1
-- title:
--   The draft auction: bid grid, public nodes, pure strategies, play and outcomes
-- statement:
--   The **draft auction** sells $m$ items $M$ to $n\ge1$ bidders in rounds while items remain. In each round every bidder submits a per-item bid $\beta\ge0$ and a nonempty set $X$ of remaining items; the highest bidder wins, ties being broken by a fixed priority order $\succ$; the winner receives $X$ and pays $\beta\,|X|$; the winner's identity, bid and set are announced, losing bids are not.
--
--   1. **Bid grid.** Bids lie in $\{0,\delta,2\delta,\dots\}\cap[0,\bar M]$, where $\delta\ge0$ is the bid increment and $\bar M$ caps every item value $v_i(\{j\})$; $\delta=0$ allows every real bid in $[0,\bar M]$.
--   2. **Nodes.** A node is the public history: the sequence of announced (winner, bid, set) triples. It determines the remaining items and every bidder's holdings $H_i$ and payments. A node is legal when every triple carries a grid bid and a nonempty set of items still remaining before it.
--   3. **Pure strategies.** A pure strategy maps every node to an action (bid, set) and plays a legal action at every legal node at which an item remains.
--   4. **Play and outcomes.** A pure profile $b$ determines its path, and thereby bidder $i$'s final bundle $B_i(b)$, payment $P_i(b)$, utility $u_i(b)=v_i(B_i(b))-P_i(b)$, the price $p_j(b)$ of every item and the welfare $\mathrm{SW}(b)=\sum_i v_i(B_i(b))$. Utilities in the subgame at a node are read at the end of the play from that node.
--   5. **Valuations.** $v_i(\emptyset)=0$ and $v_i$ is monotone; it is *subadditive* if $v_i(S\cup T)\le v_i(S)+v_i(T)$, *additive* if $v_i(S)=\sum_{j\in S}c_i(j)$ with $c_i(j)\ge0$. $\mathrm{OPT}$ is the largest welfare $\sum_i v_i(S_i)$ of an allocation, a tuple of pairwise disjoint sets.
--
--   These objects are the game on which every equilibrium concept and both bounds of the paper are stated.
--
--   **Formalization Note** Nodes are lists of triples, oldest first, with no record of losing bids. The priority order is a permutation giving each bidder a rank; rank $0$ wins ties. The play is computed with $m$ rounds of fuel, which always suffice because every round at a legal node sells an item. Valuation predicates reuse the published `ComplementFreeCA.CFRounding` definitions.
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), §2, pp.4–5 (PDF 5–6) and §3 "Outcome of a pure profile", p.6 (PDF 7)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

namespace DraftPoA

/-!
# The draft auction: bid grid, public nodes, pure strategies, play and outcomes

H. T. Truong, N. Thach, H. Chan, M. Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027
submission (manuscript sha256 270ffdaa…), §2, pp.4–5 (PDF 5–6), and §3 "Outcome of a pure
profile", p.6 (PDF 7).

There are `m` items `Fin m` and `n` bidders `Fin n`. In each round every bidder submits a per-item
bid `β ≥ 0` and a nonempty set `X` of remaining items; the highest bidder wins, ties broken by a
fixed priority order; the winner receives `X` and pays `β · |X|`; the winner, her bid and her set
are announced, losing bids are not. The auction ends when no item remains.

**Formalization Note.**
* A *node* is the public history: the list of announced `(winner, bid, set)` triples, **oldest
  first**. Losing bids are not recorded, so strategies cannot see them. A node is *legal*
  (`IsNode`) when every triple carries a grid bid and a nonempty set of items still remaining
  before it; nothing is required of who could have won, which nobody can observe. All legal
  nodes, including off-path ones, are nodes.
* The bid grid is `{0, δ, 2δ, …} ∩ [0, M̄]`; for `δ = 0` it is the whole interval `[0, M̄]`.
* A pure strategy (`Strategy`) maps every node to an action and must play a legal action (grid
  bid, nonempty set of remaining items) at every legal node at which an item remains. Its value
  at other nodes is never used.
* The priority order is a permutation `prio : Equiv.Perm (Fin n)`: `prio i` is the rank of bidder
  `i`, and rank `0` is the highest priority. The winner of a round is the bidder of smallest rank
  among those submitting the highest bid. At least one bidder is required (`[NeZero n]`).
* `playFrom prio b k ν` plays at most `k` rounds from `ν`, stopping when no item remains; every
  round at a legal node sells at least one item, so `m` rounds always reach the end. `play` starts
  at the empty node.
* Utilities are value of the final bundle minus total payment; `uFrom` evaluates them at the end of
  the play from a node, so payments and holdings already in the node appear on both sides of every
  comparison of continuations.
* Valuations are functions `Finset (Fin m) → ℝ`; the classes reuse the published
  `ComplementFreeCA.CFRounding` predicates (normalized, monotone, subadditive). Nonnegativity
  follows from normalized and monotone.
-/

open ComplementFreeCA.CFRounding

variable {n m : ℕ}

/-- A grid price: an element of `{0, δ, 2δ, …} ∩ [0, M̄]`, with `δ = 0` allowing every real
bid in `[0, M̄]` (§2, p.5). -/
def IsGridBid (δ Mbar β : ℝ) : Prop :=
  0 ≤ β ∧ β ≤ Mbar ∧ (δ = 0 ∨ ∃ k : ℕ, β = k * δ)

/-- A node: the public history of announced `(winner, bid, set)` triples, oldest first (p.5). -/
abbrev Node (n m : ℕ) := List (Fin n × ℝ × Finset (Fin m))

/-- The items sold along a node. -/
def soldItems (ν : Node n m) : Finset (Fin m) :=
  ν.foldr (fun t s => t.2.2 ∪ s) ∅

/-- The items remaining at a node. -/
def remaining (ν : Node n m) : Finset (Fin m) :=
  Finset.univ \ soldItems ν

/-- The items bidder `i` holds at a node (her bundle once the auction has ended). -/
def holdings (ν : Node n m) (i : Fin n) : Finset (Fin m) :=
  ν.foldr (fun t s => if t.1 = i then t.2.2 ∪ s else s) ∅

/-- What bidder `i` has paid along a node: `β · |X|` for every round she won. -/
def payment (ν : Node n m) (i : Fin n) : ℝ :=
  (ν.map fun t => if t.1 = i then t.2.1 * (t.2.2.card : ℝ) else 0).sum

/-- The price `p_j` of item `j`: the winning bid of the round in which it sold (`0` if unsold). -/
def price (ν : Node n m) (j : Fin m) : ℝ :=
  ((ν.find? fun t => decide (j ∈ t.2.2)).map fun t => t.2.1).getD 0

/-- The buyer of item `j` (bidder `⟨0, _⟩` if `j` is unsold, which never happens at the end). -/
def buyer [NeZero n] (ν : Node n m) (j : Fin m) : Fin n :=
  ((ν.find? fun t => decide (j ∈ t.2.2)).map fun t => t.1).getD ⟨0, Nat.pos_of_neZero n⟩

/-- The outcome map of a node: buyer and price of every item. It determines every bundle,
payment, utility and the welfare. -/
def outcomeMap [NeZero n] (ν : Node n m) : Fin m → Fin n × ℝ :=
  fun j => (buyer ν j, price ν j)

/-- A legal action at node `ν`: a grid bid and a nonempty set of remaining items (§2, (1)). -/
def IsLegalAction (δ Mbar : ℝ) (ν : Node n m) (a : ℝ × Finset (Fin m)) : Prop :=
  IsGridBid δ Mbar a.1 ∧ a.2.Nonempty ∧ a.2 ⊆ remaining ν

/-- A legal node: each announced triple has a grid bid and a nonempty set of items that were
still remaining before it. Nothing about the winning condition is required (losing bids are
unobservable). -/
def IsNode (δ Mbar : ℝ) (ν : Node n m) : Prop :=
  ∀ k (hk : k < ν.length), IsLegalAction δ Mbar (ν.take k) (ν[k]).2

/-- A pure strategy: an action at every node, legal at every legal node at which an item
remains (p.5). -/
structure Strategy (n m : ℕ) (δ Mbar : ℝ) where
  /-- The action `(bid, set)` played at a node. -/
  act : Node n m → ℝ × Finset (Fin m)
  /-- Legality at every legal node at which the auction has not ended. -/
  legal : ∀ ν : Node n m, IsNode δ Mbar ν → (remaining ν).Nonempty → IsLegalAction δ Mbar ν (act ν)

/-- The highest bid among the actions `a`. -/
noncomputable def topBid [NeZero n] (a : Fin n → ℝ × Finset (Fin m)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (a i).1)

/-- The winner of a round: among the bidders submitting the highest bid, the one of smallest
rank `prio i` (§2, (2)). -/
noncomputable def winner [NeZero n] (prio : Equiv.Perm (Fin n)) (a : Fin n → ℝ × Finset (Fin m)) :
    Fin n :=
  prio.symm ((Finset.univ.filter fun r : Fin n => (a (prio.symm r)).1 = topBid a).min'
    (by
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n))
        (fun i => (a i).1)
      exact ⟨prio i, by simp [topBid, hi]⟩))

/-- One round at node `ν` under the pure profile `b`: the winner's triple is appended. -/
noncomputable def step [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (b : Fin n → Strategy n m δ Mbar) (ν : Node n m) : Node n m :=
  let a := fun i => (b i).act ν
  let w := winner prio a
  ν ++ [(w, (a w).1, (a w).2)]

/-- At most `k` rounds of play from node `ν`, stopping as soon as no item remains. -/
noncomputable def playFrom [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (b : Fin n → Strategy n m δ Mbar) : ℕ → Node n m → Node n m
  | 0, ν => ν
  | k + 1, ν => if remaining ν = ∅ then ν else playFrom prio b k (step prio b ν)

/-- The path of the pure profile `b`: the terminal node reached from the empty node (each round
sells an item, so `m` rounds suffice). -/
noncomputable def play [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (b : Fin n → Strategy n m δ Mbar) : Node n m :=
  playFrom prio b m []

/-- Bidder `i`'s utility at a node, for her valuation `vi`: value of her holdings minus her
payments. -/
def uAt (vi : Finset (Fin m) → ℝ) (ν : Node n m) (i : Fin n) : ℝ :=
  vi (holdings ν i) - payment ν i

/-- `u_i(b) = v_i(B_i(b)) − P_i(b)` (p.6). -/
noncomputable def u [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) (i : Fin n) : ℝ :=
  uAt (v i) (play prio b) i

/-- Bidder `i`'s utility at the end of the play of `b` from node `ν` (the subgame at `ν`). -/
noncomputable def uFrom [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) (ν : Node n m)
    (i : Fin n) : ℝ :=
  uAt (v i) (playFrom prio b m ν) i

/-- The welfare of the terminal node of a play: `Σ_i v_i(B_i)`. -/
def SWAt (v : Fin n → Finset (Fin m) → ℝ) (ν : Node n m) : ℝ :=
  welfare v (holdings ν)

/-- `SW(b) = Σ_i v_i(B_i(b))` (p.6). -/
noncomputable def SW [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) : ℝ :=
  SWAt v (play prio b)

open Classical in
/-- The optimal welfare `OPT`: the largest welfare of an allocation (tuple of pairwise disjoint
sets) (p.5). -/
noncomputable def OPT (v : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  (Finset.univ.filter fun A : Fin n → Finset (Fin m) => IsAllocation A).sup'
    ⟨fun _ => ∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ _ => Finset.disjoint_empty_left _⟩⟩
    (welfare v)

/-- An additive valuation: `v(S) = Σ_{j ∈ S} c(j)` with item values `c(j) ≥ 0` (p.4). -/
def IsAdditive (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ S, v S = ∑ j ∈ S, c j

/-- The two valuation classes of the headline. -/
inductive ValClass
  | additive
  | subadditive

/-- Membership of a valuation in a class: additive, or normalized monotone subadditive (pp.4–5). -/
def ValClass.Mem : ValClass → (Finset (Fin m) → ℝ) → Prop
  | .additive, v => IsAdditive v
  | .subadditive, v => IsNormalized v ∧ IsMonotone v ∧ IsSubadditive v

/-- `M̄` caps every item value `v_i({j})` (p.5). -/
def IsCapped (v : Fin n → Finset (Fin m) → ℝ) (Mbar : ℝ) : Prop :=
  ∀ i j, v i {j} ≤ Mbar

end DraftPoA


