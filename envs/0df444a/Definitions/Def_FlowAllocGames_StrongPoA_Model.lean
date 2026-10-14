-- Prove2me | Definitions.Def_FlowAllocGames_StrongPoA_Model
-- name    : FlowAllocGames_StrongPoA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:51.079885+00:00
-- url     : https://prove2.me/theorems/5ae95429-2ea1-48a8-935c-f1ba9ce0a380
-- title:
--   §2.1–2.3, pp. 9–16 and §3.1, p. 17 — flow allocation games, unit-ranking profiles, feasible flows (4), clearing state, utilities, Flow (8), strong equilibrium, circulations of G′
-- statement:
--   This module fixes the model of Bertschinger, Hoefer and Schmand's *flow allocation games* in their unit-ranking form.
--
--   A **flow allocation game** $\Gamma=(G,(b_v)_{v\in V},(c_e)_{e\in E})$ consists of a finite directed graph $G=(V,E)$ (parallel edges and loops allowed), a **fixed supply** $b_v\in\mathbb N_0$ at every node and a **capacity** $c_e\in\mathbb N_0$ on every edge. For a node $v$ write $E^+(v)$ and $E^-(v)$ for its outgoing and incoming edges and $c_v^+=\sum_{e\in E^+(v)}c_e$ for its **saturating output**. Every node is a player.
--
--   A **unit-ranking strategy profile** $\mathbf a=(a_e)_{e\in E}$ assigns to each edge $e$ a function $a_e:\mathbb N_0\to\mathbb N_0$, chosen by the tail of $e$, such that for every edge $e$, node $v$ and amount $y$:
--   1. $a_e(y)\le c_e$ (capacity constraint (1));
--   2. $\sum_{e\in E^+(v)}a_e(y)\le y$ (weak flow conservation (2));
--   3. $\sum_{e\in E^+(v)}a_e(y)=\min\{c_v^+,y\}$ (no-fraud constraint (3));
--   4. each $a_e$ is non-decreasing (monotonicity (5)).
--
--   Given $\mathbf a$, an integral flow $f:E\to\mathbb N_0$ is **feasible** if it satisfies the fixed point constraint (4)
--   $$f_{(v,w)}=a_{(v,w)}(f_v),\qquad f_v=b_v+\sum_{e\in E^-(v)}f_e .$$
--   The **clearing state** $\hat f$ of $\mathbf a$ is the coordinatewise supremum of the feasible flows; the **utility** of player $v$ is $u_v(\mathbf a)=\sum_{e\in E^+(v)}\hat f_e$, and the **total flow** is $\mathrm{Flow}(\mathbf a)=\sum_{e\in E}\hat f_e$ (equation (8)).
--
--   A coalition $C\subseteq V$ has a **profitable deviation** $\mathbf a'_C$ if every $v\in C$ strictly gains, $u_v(\mathbf a'_C,\mathbf a_{-C})>u_v(\mathbf a)$. A unit-ranking profile is a **strong equilibrium** if no non-empty coalition has a profitable deviation to another unit-ranking profile.
--
--   The **circulation network** $G'$ adds an auxiliary node $s$, an edge $(v,s)$ of unbounded capacity and an edge $(s,v)$ of capacity $b_v$ for every $v\in V$. A **circulation** of $G'$ is an integral flow on its edges that respects the capacities and conserves flow at every node, including $s$; an **optimal circulation** $f^*$ maximizes the total flow value $\sum_{e\in E'}f^*_e$ over all integral circulations.
--
--   These objects are the vocabulary of the paper's results on strong equilibria in unit-ranking games, including the price of anarchy bound of Theorem 16.
--
--   **Formalization Note** Strategies and flows are $\mathbb N$-valued, as the paper prescribes for unit-ranking games (p. 13). With (3) and (5), raising the supply by one unit raises exactly one $a_e$ by one while $y<c_v^+$: this is "each node ranks single units of capacity" (pp. 4, 14). Constraint (2) is implied by (3) and kept because the page lists it. The clearing state is defined with `sSup` in $\mathbb N$, which is $0$ on an empty or unbounded set; for a unit-ranking profile the set of values is non-empty and bounded by $c_e$, and that a single feasible flow attains the supremum is Theorem 2, which the definition does not assume. Coalitions are required to be non-empty: with $C=\emptyset$ the condition "every member gains" holds vacuously and no profile would be a strong equilibrium; the paper reads it the same way (Proposition 4, p. 16; proof of Proposition 17, p. 32). The edge $(s,v)$ exists on p. 17 only when $b_v>0$; an edge of capacity $0$ carries no flow, so the network is the same. Optimal circulations are optimal among integral circulations; the paper takes an optimal circulation and assumes it integral (p. 23), and the optimal values coincide.
-- source:
--   arXiv:1908.01714v3, §2.1–2.3, pp. 9–16 (constraints (1)–(5), clearing state p. 13, strong equilibrium p. 15, Flow (8) p. 16); §3.1, p. 17 (circulation network G′); proof of Theorem 9, p. 23 (optimal circulation)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongPoA

open Finset

/-- A flow allocation game `Γ = (G, (b_v)_{v∈V}, (c_e)_{e∈E})` (arXiv:1908.01714v3, §2.1, p. 9):
a finite directed (multi)graph `G = (V, E)` whose edge `e` runs from `tail e` to `head e`, with
integral fixed supplies `b v ≥ 0` and integral capacities `c e ≥ 0`. -/
structure Game (V E : Type*) where
  tail : E → V
  head : E → V
  b : V → ℕ
  c : E → ℕ

/-- A flow in the circulation network `G′` of §3.1 (p. 17): `G` plus an auxiliary node `s`, an edge
`(v, s)` of capacity `∞` for every `v`, and an edge `(s, v)` of capacity `b_v`. `g` is the flow on the
edges of `G`, `toS v` the flow on `(v, s)`, `fromS v` the flow on `(s, v)`. -/
structure ExtFlow (V E : Type*) where
  g : E → ℕ
  toS : V → ℕ
  fromS : V → ℕ

/-- `Σ_{e ∈ E′} x_e`, the total flow value of a flow of `G′` (p. 23). -/
def ExtFlow.total {V E : Type*} [Fintype V] [Fintype E] (x : ExtFlow V E) : ℕ :=
  ∑ e, x.g e + ∑ v, x.toS v + ∑ v, x.fromS v

namespace Game

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Game V E)

/-- `E⁺(v)`, the outgoing edges of `v` (p. 9). -/
def outEdges (v : V) : Finset E := univ.filter (fun e => G.tail e = v)

/-- `E⁻(v)`, the incoming edges of `v` (p. 9). -/
def inEdges (v : V) : Finset E := univ.filter (fun e => G.head e = v)

/-- The saturating output `c⁺_v = Σ_{e ∈ E⁺(v)} c_e` (p. 9). -/
def cplus (v : V) : ℕ := ∑ e ∈ G.outEdges v, G.c e

/-- The total supply `f_v = b_v + Σ_{e ∈ E⁻(v)} f_e` of `v` under a flow `f` (p. 10). -/
def supply (f : E → ℕ) (v : V) : ℕ := G.b v + ∑ e ∈ G.inEdges v, f e

/-- A profile of unit-ranking strategies (p. 13): every `a_e : ℕ₀ → ℕ₀` satisfies the capacity
constraint (1), and every player's strategy the weak flow conservation constraint (2), the no-fraud
constraint (3) and the monotonicity constraint (5). -/
def IsUnitRanking (a : FlowAllocGames.StrongEq.Profile E) : Prop :=
  (∀ e y, a e y ≤ G.c e) ∧
  (∀ v y, ∑ e ∈ G.outEdges v, a e y ≤ y) ∧
  (∀ v y, ∑ e ∈ G.outEdges v, a e y = min (G.cplus v) y) ∧
  (∀ e, Monotone (a e))

/-- A feasible flow for `a` (the fixed point constraint (4), p. 10): `f_(v,w) = a_(v,w)(f_v)`. -/
def IsFeasible (a : FlowAllocGames.StrongEq.Profile E) (f : E → ℕ) : Prop :=
  ∀ e, f e = a e (G.supply f (G.tail e))

/-- The clearing state `f̂` of `a` (p. 13): the supremum, coordinatewise, of the feasible flows. -/
noncomputable def clearingState (a : FlowAllocGames.StrongEq.Profile E) : E → ℕ :=
  fun e => sSup ((fun f : E → ℕ => f e) '' {f | G.IsFeasible a f})

/-- The utility `u_v(a) = Σ_{e ∈ E⁺(v)} f̂_e` (p. 13). -/
noncomputable def utility (a : FlowAllocGames.StrongEq.Profile E) (v : V) : ℕ :=
  ∑ e ∈ G.outEdges v, G.clearingState a e

/-- `Flow(a) = Σ_{e ∈ E} f̂_e`, the total flow (8), p. 16. -/
noncomputable def flow (a : FlowAllocGames.StrongEq.Profile E) : ℕ :=
  ∑ e, G.clearingState a e

/-- The profile `(a′_C, a_{−C})` (p. 15): players in `C` use `a′`, all others `a`. -/
def deviate (a a' : FlowAllocGames.StrongEq.Profile E) (C : Finset V) : FlowAllocGames.StrongEq.Profile E :=
  fun e => if G.tail e ∈ C then a' e else a e

/-- A strong equilibrium (p. 15) of the unit-ranking game: a unit-ranking profile such that no
non-empty coalition `C ⊆ V` has a joint unit-ranking deviation that strictly improves every member. -/
def IsStrongEquilibrium (a : FlowAllocGames.StrongEq.Profile E) : Prop :=
  G.IsUnitRanking a ∧
    ∀ (C : Finset V) (a' : FlowAllocGames.StrongEq.Profile E), C.Nonempty → G.IsUnitRanking (G.deviate a a' C) →
      ¬ ∀ v ∈ C, G.utility a v < G.utility (G.deviate a a' C) v

/-- A circulation of `G′` (§3.1, p. 17): capacities `c` on `E` and `b_v` on `(s, v)`, none on `(v, s)`,
and exact flow conservation at every node of `V` and at `s`. -/
def IsCirculation (x : ExtFlow V E) : Prop :=
  (∀ e, x.g e ≤ G.c e) ∧ (∀ v, x.fromS v ≤ G.b v) ∧
  (∀ v, x.fromS v + ∑ e ∈ G.inEdges v, x.g e = ∑ e ∈ G.outEdges v, x.g e + x.toS v) ∧
  ∑ v, x.toS v = ∑ v, x.fromS v

/-- An optimal circulation `f*` of `G′` (p. 23): an integral circulation maximizing `Σ_{e ∈ E′} f*_e`. -/
def IsOptimalCirculation (x : ExtFlow V E) : Prop :=
  G.IsCirculation x ∧ ∀ y : ExtFlow V E, G.IsCirculation y → y.total ≤ x.total

end Game

end FlowAllocGames.StrongPoA


