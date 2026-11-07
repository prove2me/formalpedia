-- Prove2me | Definitions.Def_DSICHardRev_Protocol
-- name    : DSICHardRev_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:51.061335+00:00
-- url     : https://prove2.me/theorems/a28e61ac-1899-415a-b304-61ffb0b80f4f
-- title:
--   Communication protocols, strategies and deterministic IR/NNT/DSIC mechanisms
-- statement:
--   A combinatorial auction allocates a finite set of items $\iota$ among a finite set of bidders $N$; bidder $i$ holds a valuation $v_i : 2^{\iota}\to\mathbb R$.
--
--   1. **Protocol.** A communication protocol in the blackboard model is a finite rooted tree. At an internal node every bidder $i$ simultaneously sends a message from an alphabet of size $k_i\ge 1$, which may depend on the bidder and the node, and every profile of messages leads to its own child. A leaf designates an **outcome**: an allocation $(S_i)_{i\in N}$ of pairwise disjoint bundles together with payments $(p_i)_{i\in N}\in\mathbb R^N$.
--   2. **Communication.** A node costs $\sum_i \lceil \log_2 k_i\rceil$ bits, and the communication of the protocol is the largest total cost along any root-to-leaf path of the tree.
--   3. **Strategies.** A strategy of bidder $i$ assigns to every node of the tree a message of $i$ that is valid there; a strategy profile determines the path from the root to a leaf, and hence the outcome. Nodes are addressed by positions (the root, or a message profile followed by a position in the corresponding child); one can restrict a strategy to the subtree at a position, ask whether a profile reaches a position, and read the message a strategy sends at the root.
--   4. **Mechanism.** A deterministic mechanism is a protocol together with a strategy prescription $\sigma_i$ for each bidder, a map from valuations to strategies. On a domain $\mathcal D$ of valuations it is
--      - *individually rational (IR)* if prescribed play on every profile from $\mathcal D$ gives every bidder utility $v_i(S_i)-p_i\ge 0$;
--      - *no-negative-transfers (NNT)* if prescribed play on every profile from $\mathcal D$ gives payments $p_i\ge 0$;
--      - *dominant-strategy incentive compatible (DSIC)* if for every bidder $i$ with $v_i\in\mathcal D$ and **every** strategy profile $\psi$ of all bidders, switching $i$ to $\sigma_i(v_i)$ does not decrease $i$'s utility;
--      - an *$\eta$-approximation* if on every profile from $\mathcal D$ every allocation $(T_i)$ satisfies $\sum_i v_i(T_i)\le \eta\sum_i v_i(S_i)$.
--
--   These objects are the model in which every DSIC lower bound of the paper is stated.
--
--   **Formalization Note** The tree is an inductive type whose nodes carry alphabets $\mathrm{Fin}\,k_i$ with $k_i\ge1$; strategies are the tree decorated with one message of the bidder at each node, so every function from nodes to valid messages is a strategy. Mechanisms are deterministic by construction. The approximation is written $\mathrm{OPT}\le\eta\cdot\mathrm{welfare}$, so no division by $\eta$ occurs.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.1–§2.2, pp.7–9: blackboard model (p.8), Definition 2.2, Definitions 2.3, 2.6, 2.7, 2.8, 2.9, 2.11

import Mathlib

namespace DSICHardRev

/-!
# Communication protocols and deterministic mechanisms (blackboard model)

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.1–§2.2, pp.7–9: the blackboard model (p.8),
Definition 2.3 (Strategy), Definitions 2.6–2.7 (Payment Rule, Mechanism), Definition 2.8 (IR),
Definition 2.9 (NNT), Definition 2.11 (DSIC), Definition 2.2 (Approximation Ratio).

**Formalization Note.**
* Bidders form a finite type `N`, items a finite type `ι`. A protocol is a finite rooted tree
  (`Protocol N ι`). At an internal node every bidder `i` simultaneously sends a message from the
  alphabet `Fin (k i)` with `k i ≥ 1` (the alphabet may depend on the bidder and the node), and
  every message profile `a : (i : N) → Fin (k i)` leads to its own child. A leaf designates an
  `Outcome`: an allocation (pairwise disjoint bundles, items may stay unallocated) and payments.
* Bit cost: a node charges `∑ i, ⌈log₂ (k i)⌉` bits (`Nat.clog 2`), and the communication `comm`
  of a protocol is the maximum, over **all** root-to-leaf paths of the tree, of the sum of the
  node costs ("the worst-case length of the transcript", Definitions 2.4, 2.7).
* A strategy of bidder `i` (`Strat i P`) assigns a valid message to **every** node of `P`
  (Definition 2.3): it is the tree `P` decorated at each internal node with a message of `i`.
  `run P σ` follows the strategy profile `σ` from the root to a leaf.
* Nodes of `P` are positions `Pos P` (the root, or a message profile at the root followed by a
  position in that child). `subtree`, `Strat.restrict`, `Reaches` and `rootMsg` let statements
  talk about the message sent at a given node and about which nodes a profile passes through.
* A mechanism (`Mechanism N ι`) is a protocol together with a strategy prescription for each
  bidder (a map from valuations `Finset ι → ℝ` to strategies). It is deterministic by
  construction. IR, NNT and the approximation guarantee are required on every profile of
  valuations from the domain `D` under prescribed play; DSIC quantifies over **all** strategy
  profiles of the other bidders, not only prescribed ones. The approximation guarantee is written
  `OPT ≤ η · welfare` (no division by `η`).
-/

/-- The output of a leaf: an allocation (pairwise disjoint bundles) and a payment per bidder. -/
structure Outcome (N ι : Type) where
  /-- The bundle allocated to each bidder. -/
  alloc : N → Finset ι
  /-- The payment of each bidder. -/
  pay : N → ℝ
  /-- Bundles of distinct bidders are disjoint. -/
  disjoint : Pairwise fun a b => Disjoint (alloc a) (alloc b)

/-- A communication protocol: a finite rooted tree. At a node, bidder `i` sends a message from the
alphabet `Fin (k i)` (`k i ≥ 1`); every message profile leads to a distinct child. -/
inductive Protocol (N ι : Type) : Type
  /-- A leaf designates a fixed outcome. -/
  | leaf (o : Outcome N ι) : Protocol N ι
  /-- An internal node with alphabet sizes `k` and one child per message profile. -/
  | node (k : N → ℕ) (hk : ∀ i, 0 < k i)
      (child : ((i : N) → Fin (k i)) → Protocol N ι) : Protocol N ι

namespace Protocol

variable {N ι : Type}

/-- A strategy of bidder `i` on protocol `P`: a valid message of `i` at every node of `P`
(Definition 2.3). At a node it is the message sent there together with a strategy on every
child. -/
def Strat (i : N) : Protocol N ι → Type
  | .leaf _ => PUnit
  | .node k _ child => Fin (k i) × ((a : (j : N) → Fin (k j)) → Strat i (child a))

/-- The outcome reached when every bidder `j` follows the strategy `σ j`. -/
def run : (P : Protocol N ι) → ((i : N) → Strat i P) → Outcome N ι
  | .leaf o, _ => o
  | .node _ _ child, σ =>
      run (child fun j => (σ j).1) (fun j => (σ j).2 fun j' => (σ j').1)

/-- The bit cost of a node with alphabet sizes `k`: `∑ i, ⌈log₂ (k i)⌉`. -/
def nodeCost [Fintype N] (k : N → ℕ) : ℕ := ∑ i, Nat.clog 2 (k i)

/-- The communication of a protocol: the maximum over all root-to-leaf paths of the total bit cost
of the nodes on the path. -/
def comm [Fintype N] [DecidableEq N] : Protocol N ι → ℕ
  | .leaf _ => 0
  | .node k _ child => nodeCost k + Finset.univ.sup fun a => comm (child a)

/-- The nodes (positions) of a protocol: the root, or a message profile at the root followed by a
position in the corresponding child. -/
def Pos : Protocol N ι → Type
  | .leaf _ => PUnit
  | .node k _ child => Option ((a : (j : N) → Fin (k j)) × Pos (child a))

/-- The subtree rooted at a position. -/
def subtree : (P : Protocol N ι) → Pos P → Protocol N ι
  | .leaf o, _ => .leaf o
  | .node k hk child, q =>
      match (q : Option ((a : (j : N) → Fin (k j)) × Pos (child a))) with
      | none => .node k hk child
      | some ⟨a, q'⟩ => subtree (child a) q'

/-- The root of a protocol as a position. -/
def root : (P : Protocol N ι) → Pos P
  | .leaf _ => PUnit.unit
  | .node _ _ _ => (none : Option _)

/-- The restriction of a strategy to the subtree rooted at a position. -/
def Strat.restrict {i : N} : (P : Protocol N ι) → Strat i P → (q : Pos P) → Strat i (subtree P q)
  | .leaf _, s, _ => s
  | .node k _ child, s, q =>
      match (q : Option ((a : (j : N) → Fin (k j)) × Pos (child a))) with
      | none => s
      | some ⟨a, q'⟩ => Strat.restrict (child a) (s.2 a) q'

/-- The strategy profile `σ` reaches the position `q`: following `σ` from the root passes through
`q`. -/
def Reaches : (P : Protocol N ι) → ((i : N) → Strat i P) → Pos P → Prop
  | .leaf _, _, _ => True
  | .node k _ child, σ, q =>
      match (q : Option ((a : (j : N) → Fin (k j)) × Pos (child a))) with
      | none => True
      | some ⟨a, q'⟩ => (∀ j, (σ j).1 = a j) ∧ Reaches (child a) (fun j => (σ j).2 a) q'

/-- The message a strategy sends at the root, as a natural number; `none` if the root is a leaf. -/
def rootMsg {i : N} : (P : Protocol N ι) → Strat i P → Option ℕ
  | .leaf _, _ => none
  | .node _ _ _, s => some (s.1 : ℕ)

end Protocol

/-- A deterministic mechanism: a communication protocol whose leaves carry allocations and
payments, together with a strategy prescription (a map from valuations to strategies) for every
bidder (Definitions 2.3, 2.6, 2.7). -/
structure Mechanism (N ι : Type) where
  /-- The communication protocol. -/
  protocol : Protocol N ι
  /-- The strategy prescription of each bidder. -/
  prescribe : (i : N) → (Finset ι → ℝ) → protocol.Strat i

namespace Mechanism

variable {N ι : Type} [Fintype N] [DecidableEq N]

/-- The outcome under prescribed play when the bidders' valuations are `v`. -/
def outcome (M : Mechanism N ι) (v : N → Finset ι → ℝ) : Outcome N ι :=
  M.protocol.run fun i => M.prescribe i (v i)

/-- Quasilinear utility of bidder `i` with valuation `vi` at outcome `o`: `vi(S_i) − p_i`. -/
def utility (vi : Finset ι → ℝ) (o : Outcome N ι) (i : N) : ℝ := vi (o.alloc i) - o.pay i

/-- Welfare `∑ i, v_i(S_i)` of an assignment of bundles. -/
def welfare (v : N → Finset ι → ℝ) (S : N → Finset ι) : ℝ := ∑ i, v i (S i)

/-- Individual rationality on the domain `D` (Definition 2.8): on every profile of valuations from
`D`, prescribed play gives every bidder non-negative utility. -/
def IsIR (M : Mechanism N ι) (D : Set (Finset ι → ℝ)) : Prop :=
  ∀ v : N → Finset ι → ℝ, (∀ j, v j ∈ D) → ∀ i, 0 ≤ utility (v i) (M.outcome v) i

/-- No negative transfers on the domain `D` (Definition 2.9): on every profile of valuations from
`D`, prescribed play yields non-negative payments. -/
def IsNNT (M : Mechanism N ι) (D : Set (Finset ι → ℝ)) : Prop :=
  ∀ v : N → Finset ι → ℝ, (∀ j, v j ∈ D) → ∀ i, 0 ≤ (M.outcome v).pay i

/-- Dominant-strategy incentive compatibility on the domain `D` (Definition 2.11): for every bidder
`i` with valuation in `D` and **every** strategy profile `ψ` (arbitrary strategies of the others,
which may react to the messages sent), replacing `ψ i` by the prescribed strategy does not lower
`i`'s utility. -/
def IsDSIC (M : Mechanism N ι) (D : Set (Finset ι → ℝ)) : Prop :=
  ∀ i, ∀ vi ∈ D, ∀ ψ : (j : N) → M.protocol.Strat j,
    utility vi (M.protocol.run ψ) i ≤
      utility vi (M.protocol.run (Function.update ψ i (M.prescribe i vi))) i

/-- The mechanism attains an `η`-approximation on the domain `D` (Definition 2.2, deterministic
case): on every profile from `D`, every allocation `T` has welfare at most `η` times the welfare of
the mechanism's allocation. -/
def IsApprox (M : Mechanism N ι) (D : Set (Finset ι → ℝ)) (η : ℝ) : Prop :=
  ∀ v : N → Finset ι → ℝ, (∀ j, v j ∈ D) →
    ∀ T : N → Finset ι, (Pairwise fun a b => Disjoint (T a) (T b)) →
      welfare v T ≤ η * welfare v (M.outcome v).alloc

/-- The communication used by the mechanism. -/
def comm (M : Mechanism N ι) : ℕ := M.protocol.comm

end Mechanism

end DSICHardRev


