-- Prove2me | Definitions.Def_WeightedCoordGames_Model
-- name    : WeightedCoordGames_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:09.09286+00:00
-- url     : https://prove2.me/theorems/86e7d2d4-56bd-4c9f-83d3-2f2d7d4f3269
-- title:
--   Strategic games, improvement paths, coordination games on weighted directed graphs, simple cycles and open chains of cycles
-- statement:
--   This file sets up the objects of §§2–5 of Apt, Simon and Wojtczak.
--
--   **Strategic games** (§2, p.7). A strategic game has players $i\in\iota$, a set $S_i$ of strategies for each player and payoff functions $p_i$ on joint strategies $s=(s_i)_i$, $s_i\in S_i$. A strategy $s_i$ is a *best response* in $s$ if $p_i(s)\ge p_i(c,s_{-i})$ for every $c\in S_i$; $s$ is a *Nash equilibrium* if every player plays a best response.
--
--   **Improvement paths** (§2, pp.7–8). An *improvement step* $s\to s'$ is a profitable deviation of a single player: $s'=(c,s_{-i})$ with $c\in S_i$, $c\neq s_i$ and $p_i(s')>p_i(s)$. An improvement path is a sequence of improvement steps that, if finite, cannot be extended, so it ends in a Nash equilibrium. A game *ensures improvement paths of length at most $X$* if from every joint strategy $s_0$ there are joint strategies $s_0,s_1,\dots,s_L$ with $L\le X$, every $s_k\to s_{k+1}$ an improvement step and $s_L$ a Nash equilibrium. The length is the number $L$ of steps.
--
--   **Schedules** (§2, p.8). Given a schedule (a sequence of players), the generated path $\mathrm{path}(s,\mathrm{seq})$ skips a scheduled player who already plays a best response and otherwise switches that player to a best response, possibly subject to an extra rule on which best response is chosen.
--
--   **Coordination games** (§3, p.9). Given a directed graph on a finite vertex set $V$, a weight $w_{j\to i}$ on each edge, bonuses $\beta(i,c)\in\mathbb N$ and a colour assignment $C(i)\subseteq M$, the coordination game has the nodes as players, $C(i)$ as the strategies of node $i$, and payoffs
--   $$
--   p_i(s)=\sum_{j\in N_i,\ s_j=s_i} w_{j\to i}+\beta(i,s_i),
--   $$
--   where $N_i$ is the set of in-neighbours of $i$.
--
--   **Simple cycles** (§4, p.10). The weighted simple cycle $1\to2\to\dots\to n\to1$ with arbitrary weights, bonuses and colour sets.
--
--   **Open chains of cycles** (§5, p.15). There are $m\ge2$ cycles $\mathcal C_1,\dots,\mathcal C_m$, each with $v\ge3$ nodes. Cycle $\mathcal C_j$ is $[j,1]\to[j,2]\to\dots\to[j,v]\to[j,1]$. For $j\le m-1$ the node $[j,1]$ is also the node $[j+1,k_j]$ of the next cycle, for some $k_j\in\{2,\dots,v\}$. Two positions name the same vertex only in this way, so consecutive cycles share exactly one node and the others are disjoint. The coordination game on an open chain is unweighted and has no bonuses, as everywhere in the paper unless stated otherwise (§3, p.9), so $p_u(s)=|\{x\in N_u : s_x=s_u\}|$.
--
--   **Formalization Note** Joint strategies are functions $s:V\to M$, and they are joint strategies of the game when $s_i\in C(i)$ for all $i$. Edges are a relation, so there are no parallel edges, and edge weights are read only on edges. Cycle nodes and cycle indices are 0-based: Lean's `node j i` is the paper's $[j+1,i+1]$, and `k j` is $k_{j+1}-1$. The standing assumptions $m\ge2$, $v\ge3$ of §5 are fields of the open-chain structure. Positivity of weights and non-emptiness of colour sets are hypotheses of the theorems, not part of the data.
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint, 12 Mar 2021), §2 Preliminaries pp.7–8 (strategic games, best response, Nash equilibrium, improvement paths, "ensures improvement paths of length X", schedules and path(s, seq)); §3 p.9 (coordination games, payoff p_i); §4 p.10 (simple cycle 1 → 2 → … → n → 1); §5 p.15 (open chain of m ≥ 2 cycles with v ≥ 3 nodes)

import Mathlib

namespace WeightedCoordGames

/-- A **strategic game** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §2, p.7): players `ι`, for each
player `i` a set `S i` of strategies, and for each player `i` a payoff function
`payoff i : (ι → M) → ℝ` on joint strategies.

**Formalization Note.** All strategy sets are subsets of one ambient type `M` (for coordination
games: the colours), so a joint strategy is a function `s : ι → M`, and it is a joint strategy of
the game when `s i ∈ S i` for every `i` (`IsJoint`). The paper's requirement that each `S i` be
non-empty is not a field: the coordination-game theorems assume non-empty colour sets
explicitly. -/
structure StrategicGame (ι : Type*) (M : Type*) where
  /-- The strategy set `S_i` of player `i`. -/
  S : ι → Set M
  /-- The payoff `p_i(s)` of player `i` at the joint strategy `s`. -/
  payoff : ι → (ι → M) → ℝ

namespace StrategicGame

variable {ι M : Type*} [DecidableEq ι] (Γ : StrategicGame ι M)

/-- `s` is a joint strategy: every player plays one of its own strategies (§2, p.7). -/
def IsJoint (s : ι → M) : Prop := ∀ i, s i ∈ Γ.S i

/-- Player `i` plays a best response in `s` (§2, p.7): for every `c ∈ S_i`,
`p_i(c, s_{-i}) ≤ p_i(s)`. -/
def PlaysBR (i : ι) (s : ι → M) : Prop :=
  ∀ c ∈ Γ.S i, Γ.payoff i (Function.update s i c) ≤ Γ.payoff i s

/-- `s` is a **Nash equilibrium** (§2, p.7): a joint strategy in which every player plays a best
response. -/
def IsNash (s : ι → M) : Prop := Γ.IsJoint s ∧ ∀ i, Γ.PlaysBR i s

/-- An **improvement step** `s → s'` (§2, pp.7–8): a profitable deviation of a single player,
i.e. `s' = (c, s_{-i})` with `c ∈ S_i`, `c ≠ s_i` (so the deviating coalition is `{i}`) and
`p_i(s') > p_i(s)`. -/
def ImprovStep (s s' : ι → M) : Prop :=
  ∃ i c, c ∈ Γ.S i ∧ c ≠ s i ∧ s' = Function.update s i c ∧ Γ.payoff i s < Γ.payoff i s'

/-- The game **ensures improvement paths of length (at most) `X`** (§2, p.8): for each joint
strategy `s₀` there is an improvement path that starts at `s₀` and has length at most `X`.

**Formalization Note.** An improvement path is a sequence of improvement steps that, if finite,
cannot be extended, i.e. its last element admits no profitable unilateral deviation; a finite
improvement path is therefore a list `ρ 0 = s₀, ρ 1, …, ρ L` of joint strategies with every
`ρ k → ρ (k+1)` an improvement step and `ρ L` a Nash equilibrium. Its length is the number `L` of
steps (deviations), which is how the paper counts (Example 4, p.11). -/
def EnsuresImprovementPaths (X : ℕ) : Prop :=
  ∀ s₀ : ι → M, Γ.IsJoint s₀ →
    ∃ (L : ℕ) (ρ : Fin (L + 1) → ι → M), L ≤ X ∧ ρ 0 = s₀ ∧
      (∀ k : Fin L, Γ.ImprovStep (ρ k.castSucc) (ρ k.succ)) ∧ Γ.IsNash (ρ (Fin.last L))

/-- `c` is a best response of player `i` to `s_{-i}` (§2, p.7): `c ∈ S_i` and
`p_i(c', s_{-i}) ≤ p_i(c, s_{-i})` for every `c' ∈ S_i`. -/
def IsBRValue (i : ι) (s : ι → M) (c : M) : Prop :=
  c ∈ Γ.S i ∧ ∀ c' ∈ Γ.S i, Γ.payoff i (Function.update s i c') ≤ Γ.payoff i (Function.update s i c)

/-- One slot of a schedule (§2, p.8, the definition of `path(s, seq : i)`): if the scheduled
player `p` plays a best response in `t`, nothing changes (`t' = t`); otherwise `p` switches to a
best response `c`, chosen subject to the extra side condition `rule t p c` (the proofs of
Theorems 5 and 7 "additionally specify how players update their strategies to best
responses"; `rule = fun _ _ _ => True` imposes nothing). -/
def SchedSlot (rule : (ι → M) → ι → M → Prop) (p : ι) (t t' : ι → M) : Prop :=
  (Γ.PlaysBR p t ∧ t' = t) ∨
    (¬ Γ.PlaysBR p t ∧ ∃ c, Γ.IsBRValue p t c ∧ rule t p c ∧ t' = Function.update t p c)

/-- The first `K` slots of the schedule `seq` run from `t 0` (§2, p.8): `t (k+1)` arises from
`t k` by the slot of player `seq k`, for every `k < K`. The last element `t K` is the last element
of `path(t 0, seq 0 … seq (K-1))`. -/
def ScheduleRun (rule : (ι → M) → ι → M → Prop) (seq : ℕ → ι) (K : ℕ) (t : ℕ → ι → M) :
    Prop :=
  ∀ k < K, Γ.SchedSlot rule (seq k) (t k) (t (k + 1))

end StrategicGame

/-- A **coordination game on a weighted directed graph** (§3, p.9), given by its data:
an edge relation `adj` (`adj j i` is the edge `j → i`), edge weights `w j i` (the weight
`w_{j→i}`), bonuses `β i c ∈ ℕ` and a colour assignment `C i ⊆ M`.

**Formalization Note.** The data carries no side conditions; the theorems state the paper's
(positive weights on edges, non-empty colour sets, no self-loops by the choice of graph). Edges are
a relation, so there are no parallel edges; weights off the edges are never read. -/
structure CoordGame (V : Type*) (M : Type*) where
  /-- `adj j i` : there is an edge `j → i`, i.e. `j ∈ N_i`. -/
  adj : V → V → Prop
  /-- `w j i` : the weight `w_{j→i}` of the edge `j → i`. -/
  w : V → V → ℝ
  /-- `β i c` : the bonus of node `i` for colour `c`. -/
  β : V → M → ℕ
  /-- `C i` : the set of colours available to node `i`. -/
  C : V → Finset M

namespace CoordGame

variable {V M : Type*} [Fintype V]

open scoped Classical in
/-- The payoff of node `i` (§3, p.9):
`p_i(s) = Σ_{j ∈ N_i, s_i = s_j} w_{j→i} + β(i, s_i)`. -/
noncomputable def payoff (G : CoordGame V M) (i : V) (s : V → M) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => G.adj j i ∧ s j = s i), G.w j i) + (G.β i (s i) : ℝ)

/-- The strategic game `𝒢(G, w, C, β)` (§3, p.9): the players are the nodes, the strategies of
node `i` are the colours `C(i)`, and the payoffs are `payoff`. -/
noncomputable def toGame (G : CoordGame V M) : StrategicGame V M where
  S i := (G.C i : Set M)
  payoff := G.payoff

end CoordGame

/-- The simple cycle `1 → 2 → … → n → 1` (§4, p.10) on `Fin n`: `a → b` iff `b = a + 1 (mod n)`.

**Formalization Note.** Nodes are 0-based: the paper's node `i` is `i - 1 : Fin n`. For `n = 2`
this is the 2-cycle `0 → 1 → 0`. -/
def cycleAdj (n : ℕ) (a b : Fin n) : Prop := b = finRotate n a

/-- The coordination game on the weighted simple cycle on `n` nodes (§4, p.10) with weights `w`
(the weight of the edge `a → a + 1` is `w a (a + 1)`), bonuses `β` and colour assignment `C`. -/
def cycleGame {M : Type*} (n : ℕ) (w : Fin n → Fin n → ℝ) (β : Fin n → M → ℕ)
    (C : Fin n → Finset M) : CoordGame (Fin n) M where
  adj := cycleAdj n
  w := w
  β := β
  C := C

/-- An **open chain of `m` simple cycles of `v` nodes each** on the vertex set `V`
(§5, p.15). The cycle `C_j` is `[j,1] → [j,2] → … → [j,v] → [j,1]`; for `j ≤ m − 1` its node
`[j,1]` is the node `[j+1, k_j]` of the next cycle, with `k_j ∈ {2, …, v}`; consecutive cycles
share exactly one node and non-consecutive cycles are disjoint, so `|V| = vm − (m − 1)`.

* `node j i` is the paper's node `[j+1, i+1]` (0-based `Fin m`, `Fin v`);
* `k j` is the paper's `k_{j+1}` minus one (so `k j ≠ 0` is `k_{j+1} ≥ 2`); its value at the last
  cycle is never used;
* `node_surj`: every vertex is a node of some cycle;
* `link`: `[j,1] = [j+1, k_j]`;
* `node_eq`: two positions name the same vertex only if they are equal or are the two names of a
  link node.

**Formalization Note.** The standing assumptions of §5 (p.15) are fields: `m ≥ 2` cycles, each
with `v ≥ 3` nodes. -/
structure OpenChain (V : Type*) (m v : ℕ) where
  two_le_m : 2 ≤ m
  three_le_v : 3 ≤ v
  node : Fin m → Fin v → V
  node_surj : ∀ u : V, ∃ j i, node j i = u
  k : Fin m → Fin v
  k_ne_zero : ∀ j : Fin m, j.val + 1 < m → (k j).val ≠ 0
  link : ∀ (j : Fin m) (h : j.val + 1 < m),
    node j ⟨0, by omega⟩ = node ⟨j.val + 1, h⟩ (k j)
  node_eq : ∀ (j j' : Fin m) (i i' : Fin v), node j i = node j' i' →
    (j = j' ∧ i = i') ∨ (j'.val = j.val + 1 ∧ i.val = 0 ∧ i' = k j) ∨
      (j.val = j'.val + 1 ∧ i'.val = 0 ∧ i = k j')

namespace OpenChain

variable {V : Type*} {m v : ℕ} (O : OpenChain V m v)

/-- The edges of the open chain (§5, p.15): exactly the edges `[j,i] → [j,i+1]` (indices mod `v`)
of the cycles `C_j`. -/
def Adj (a b : V) : Prop := ∃ (j : Fin m) (i : Fin v), a = O.node j i ∧ b = O.node j (finRotate v i)

end OpenChain

/-- The coordination game on an open chain (§5, p.15). As everywhere in the paper unless stated
otherwise (§3, p.9; Table 1, p.6), the graph is unweighted and there are no bonuses: `w = 1`,
`β = 0`, so `p_u(s) = |{x ∈ N_u | s_x = s_u}|`. -/
def chainGame {V M : Type*} {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) :
    CoordGame V M where
  adj := O.Adj
  w := fun _ _ => 1
  β := fun _ _ => 0
  C := C

end WeightedCoordGames


