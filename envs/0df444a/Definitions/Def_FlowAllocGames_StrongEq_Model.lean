-- Prove2me | Definitions.Def_FlowAllocGames_StrongEq_Model
-- name    : FlowAllocGames_StrongEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:44.356247+00:00
-- url     : https://prove2.me/theorems/d8478812-3643-4c91-bbcf-353422168297
-- title:
--   §2.1–2.3, pp. 9–16 and §3.1, p. 17 — flow allocation games, unit-ranking profiles, feasible flows (4), clearing state, utilities, Flow (8), strong equilibrium, circulations of G′
-- statement:
--   This file sets up the model of flow allocation games of Bertschinger, Hoefer and Schmand in its integral (unit-ranking) form.
--
--   **Games.** A *flow allocation game* $\Gamma = (G, (b_v)_{v\in V}, (c_e)_{e\in E})$ consists of a finite directed multigraph $G = (V,E)$, in which every edge $e$ runs from its tail to its head, a *fixed supply* $b_v \in \mathbb{N}_0$ for every node $v$ and a *capacity* $c_e \in \mathbb{N}_0$ for every edge $e$. We write $E^+(v)$ and $E^-(v)$ for the outgoing and incoming edges of $v$, and $c^+_v = \sum_{e\in E^+(v)} c_e$ for its *saturating output*.
--
--   **Strategies.** Every node is a player. A strategy profile $\mathbf a = (a_e)_{e\in E}$ assigns to every edge an allocation function $a_e : \mathbb{N}_0 \to \mathbb{N}_0$; the tail $v$ of $e$ forwards $a_e(y)$ units on $e$ when its total supply is $y$. The profile is *unit-ranking* if for every $y \in \mathbb{N}_0$, every edge $e$ and every node $v$
--
--   $$0 \le a_e(y) \le c_e, \qquad \sum_{e\in E^+(v)} a_e(y) \le y, \qquad \sum_{e\in E^+(v)} a_e(y) = \min\{c^+_v, y\}, \qquad a_e \text{ non-decreasing},$$
--
--   i.e. the capacity (1), weak flow conservation (2), no-fraud (3) and monotonicity (5) constraints hold.
--
--   **Feasible flows and clearing state.** A flow $\mathbf f = (f_e)_{e\in E}$ with values in $\mathbb{N}_0$ gives every node the total supply $f_v = b_v + \sum_{e\in E^-(v)} f_e$. It is *feasible* for $\mathbf a$ if $f_{(v,w)} = a_{(v,w)}(f_v)$ for every edge $(v,w)$ (fixed point constraint (4)). The *clearing state* $\hat{\mathbf f}$ of $\mathbf a$ is the coordinatewise supremum of the feasible flows, $\hat f_e = \sup\{f_e : \mathbf f \text{ feasible for } \mathbf a\}$. The *utility* of player $v$ is $u_v(\mathbf a) = \sum_{e\in E^+(v)} \hat f_e$, and the total flow is $\mathrm{Flow}(\mathbf a) = \sum_{e\in E}\hat f_e$ (8).
--
--   **Strong equilibrium.** For a coalition $C \subseteq V$ and a profile $\mathbf a'$, $(\mathbf a'_C, \mathbf a_{-C})$ is the profile in which the out-edges of members of $C$ use $\mathbf a'$ and all other edges use $\mathbf a$. A unit-ranking profile $\mathbf a$ is a *strong equilibrium* if there is no non-empty coalition $C$ and no deviation $\mathbf a'_C$ such that $(\mathbf a'_C, \mathbf a_{-C})$ is again unit-ranking and $u_v(\mathbf a'_C,\mathbf a_{-C}) > u_v(\mathbf a)$ for every $v \in C$.
--
--   **The circulation network $G'$.** $G'$ adds to $G$ an auxiliary node $s$, an edge $(v,s)$ of unbounded capacity and an edge $(s,v)$ of capacity $b_v$ for every $v \in V$. A flow of $G'$ consists of integral values on the edges of $G$, on the edges $(v,s)$ and on the edges $(s,v)$. It is a *circulation* if it respects the capacities and is conserved at every node of $V$ and at $s$; its total value is the sum of its values over all edges of $G'$. An *optimal circulation* $f^*$ is a circulation of maximal total value among the integral circulations.
--
--   These are the objects about which the existence of an optimal strong equilibrium (Theorem 9) and its proof are stated.
--
--   **Formalization Note.** Players' strategies are the families $(a_e)_{e\in E^+(v)}$, so a profile is a single function on edges. Constraints (1), (3) and (5) together say exactly that each node ranks single units of capacity (pp. 4, 14): while $y < c^+_v$, raising $y$ by one raises exactly one $a_e$ by one. Constraint (2) is implied by (3) and is kept because the paper lists it. The clearing state is taken as a supremum in $\mathbb{N}$, which is $0$ on an empty or unbounded set; for unit-ranking profiles the set is non-empty and bounded by $c_e$, and that a single feasible flow attains all coordinatewise suprema is Theorem 2 (a milestone), not part of the definition. Coalitions are non-empty: with $C = \emptyset$ the condition "for every $v \in C$" would hold vacuously and no profile would be a strong equilibrium; the paper reads it the same way (Proposition 4, p. 16, calls every profile on a DAG a strong equilibrium; the proof of Proposition 17, p. 32, speaks of a "non-empty coalition"). The edge $(s,v)$ exists on p. 17 only when $b_v > 0$; an edge of capacity $0$ carries no flow, so the network is the same. Optimal circulations are optimal among integral circulations; the paper takes a real optimal circulation and notes that by integrality of capacities it may be assumed integral (p. 23), so the optimal values coincide. Multi-edges and self-loops are allowed, as in the paper.
-- source:
--   arXiv:1908.01714v3, §2.1 pp. 9–13 (constraints (1)–(5), clearing state p. 13), §2.2 p. 13 (unit-ranking strategies), §2.3 p. 15 (strong equilibrium), (8) p. 16, §3.1 p. 17 (circulation network G′), proof of Theorem 9 p. 23 (optimal circulation)

import Mathlib

namespace FlowAllocGames.StrongEq

open Finset

/-- A flow allocation game `Γ = (G, (b_v)_{v∈V}, (c_e)_{e∈E})` (arXiv:1908.01714v3, §2.1, p. 9):
a finite directed (multi)graph `G = (V, E)` whose edge `e` runs from `tail e` to `head e`, with
integral fixed supplies `b v ≥ 0` and integral capacities `c e ≥ 0`. -/
structure Game (V E : Type*) where
  tail : E → V
  head : E → V
  b : V → ℕ
  c : E → ℕ

/-- A strategy profile: `a e : ℕ → ℕ` is the allocation function `a_e` that the tail of `e` uses on
its outgoing edge `e` (pp. 9, 13); player `v`'s strategy is the family `(a e)_{e ∈ E⁺(v)}`. -/
abbrev Profile (E : Type*) := E → ℕ → ℕ

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
def IsUnitRanking (a : Profile E) : Prop :=
  (∀ e y, a e y ≤ G.c e) ∧
  (∀ v y, ∑ e ∈ G.outEdges v, a e y ≤ y) ∧
  (∀ v y, ∑ e ∈ G.outEdges v, a e y = min (G.cplus v) y) ∧
  (∀ e, Monotone (a e))

/-- A feasible flow for `a` (the fixed point constraint (4), p. 10): `f_(v,w) = a_(v,w)(f_v)`. -/
def IsFeasible (a : Profile E) (f : E → ℕ) : Prop :=
  ∀ e, f e = a e (G.supply f (G.tail e))

/-- The clearing state `f̂` of `a` (p. 13): the supremum, coordinatewise, of the feasible flows. -/
noncomputable def clearingState (a : Profile E) : E → ℕ :=
  fun e => sSup ((fun f : E → ℕ => f e) '' {f | G.IsFeasible a f})

/-- The utility `u_v(a) = Σ_{e ∈ E⁺(v)} f̂_e` (p. 13). -/
noncomputable def utility (a : Profile E) (v : V) : ℕ :=
  ∑ e ∈ G.outEdges v, G.clearingState a e

/-- `Flow(a) = Σ_{e ∈ E} f̂_e`, the total flow (8), p. 16. -/
noncomputable def flow (a : Profile E) : ℕ :=
  ∑ e, G.clearingState a e

/-- The profile `(a′_C, a_{−C})` (p. 15): players in `C` use `a′`, all others `a`. -/
def deviate (a a' : Profile E) (C : Finset V) : Profile E :=
  fun e => if G.tail e ∈ C then a' e else a e

/-- A strong equilibrium (p. 15) of the unit-ranking game: a unit-ranking profile such that no
non-empty coalition `C ⊆ V` has a joint unit-ranking deviation that strictly improves every member. -/
def IsStrongEquilibrium (a : Profile E) : Prop :=
  G.IsUnitRanking a ∧
    ∀ (C : Finset V) (a' : Profile E), C.Nonempty → G.IsUnitRanking (G.deviate a a' C) →
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

end FlowAllocGames.StrongEq


