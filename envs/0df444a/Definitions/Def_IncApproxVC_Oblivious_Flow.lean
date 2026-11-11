-- Prove2me | Definitions.Def_IncApproxVC_Oblivious_Flow
-- name    : IncApproxVC_Oblivious_Flow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:42:36.045259+00:00
-- url     : https://prove2.me/theorems/b08976fd-10b2-4944-bfef-d89271ab9c35
-- title:
--   Flow networks with lower and upper bounds, $s$–$t$ and $s$–$T$ flows, cut capacity $u^+(S)$, and the network $G_\alpha$
-- statement:
--   A **flow network** is a finite directed multigraph in which every edge $e$ has a tail, a head, an upper bound (capacity) $u(e)$ and a lower bound $l(e)$; a network without lower bounds has $l=0$. For $f\in\mathbb R^E$, $(B^\top f)(v)$ is the total flow on edges entering $v$ minus the total flow on edges leaving $v$. A **flow** is a vector with $l\le f\le u$; it **routes** a demand $d$ if $B^\top f=d$. An **$s$–$t$ flow of value $F$** routes $F(\mathbf 1_t-\mathbf 1_s)$. An **$s$–$T$ flow of value $F$**, for a vertex set $T$, routes $F(b-\mathbf 1_s)$ for some $b\ge 0$ supported on $T$ with $\|b(T)\|_1=1$: it sends $F$ units out of $s$ into $T$. The maximum $s$–$t$ flow has value at least $F$ if some $s$–$t$ flow has value at least $F$. The capacity of the edges leaving $S$ is $u^+(S)$.
--
--   For a simple graph $G=(V,E)$ with capacities $u$ and $\alpha>0$, the network **$G_\alpha$** adds a new vertex $t$ and, for every $v\in V$, an edge $(v,t)$ of capacity $\alpha\deg^+_G(v)$:
--   $$u^+_{G_\alpha}(S)=\sum_{e\in\partial^+_{G_\alpha}(S)}u(e),\qquad u^+_G(S)=\sum_{e\in\partial^+_G(S)}u(e).$$
--
--   **Formalization Note.** `FlowNet V E` has a finite edge type `E` (parallel edges and arbitrary vertex types allowed, as for the paper's "capacitated (multi-)graphs", p. 13). The page writes the demand of an $s$–$T$ flow as $F(\mathbf 1_s-b)$, which would make it a flow from $T$ into $s$; the definition uses the sign of the $s$–$t$ flow, out of $s$ and into $T$, the reading under which Theorem 5.2's guarantee is used (proof of Lemma 5.5), and requires $b$ to vanish outside $T$. In `alphaNet G u α` the vertices are `some v` and $t$ is `none`; the edges are the edges of $G$ followed by one sink edge per vertex.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), pp. 13–14, §4 (Min-Cost Flow Graphs; Flows, Circulations, Paths and Cycles); p. 7 and p. 14 (G_α)

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph

/-!
# Flow networks, flows, `s–t` and `s–T` flows, cut capacities and the network `G_α`

Adena, Henzinger, Rutschmann, *Incremental Approximate Vertex Connectivity via Almost-Linear Time
Local Cut Algorithms*, STOC 2027 submission (manuscript sha256 d6baac6b…), pp. 13–14, §4
("Min-Cost Flow Graphs", "Flows, Circulations, Paths and Cycles"); p. 7 and p. 14 (`G_α`);
p. 14 (lower bounds `l`, Theorem 5.2).

* A `FlowNet V E` is a capacitated (multi-)graph: a finite edge type `E`, each edge with a tail, a
  head, an upper bound (capacity) `up e` and a lower bound `low e`. A network without lower bounds
  has `low = 0`.
* `netIn N f v` is `(B_Gᵀ f)(v)`: the flow on edges with head `v` minus the flow on edges with tail
  `v` (`B_G(e, v) = 1` at the head, `−1` at the tail).
* `IsFlow N f`: `low ≤ f ≤ up` (with `low = 0` this is `0 ≤ f ≤ u`). `Routes N f d`: `B_Gᵀ f = d`.
* `IsSTFlow N s t f F`: `f` is a flow routing `F (1_t − 1_s)`; `F = |f|` is its value.
* `IsSetFlow N s T f F`: `f` is a flow from `s` into the set `T` of value `F`: it routes
  `F (b − 1_s)` for some `b ≥ 0` supported on `T` with `‖b(T)‖₁ = 1`. The page prints the demand
  as `F (1_s − b)`; this file uses the sign of the `s–t` flow (out of `s`, into `T`), the reading
  under which Theorem 5.2's guarantee is used in the proof of Lemma 5.5.
* `capOut N S` is `u⁺(S)`, the total capacity of the edges leaving `S`.
* `alphaNet G u α` is `G_α`: the graph `G` with capacities `u`, plus a new vertex `t` (`none`) and
  an edge `(v, t)` of capacity `α · deg⁺_G(v)` for every vertex `v`; vertices of `G` are `some v`.
* `capOutG G u S` is `u⁺_G(S) = Σ_{e ∈ ∂⁺_G(S)} u(e)`.
-/

namespace IncApproxVC.Oblivious

/-- A capacitated directed multigraph with lower and upper bounds on the flow of each edge. -/
structure FlowNet (V E : Type*) where
  /-- The tail of each edge. -/
  tail : E → V
  /-- The head of each edge. -/
  head : E → V
  /-- The upper bound (capacity) `u(e)` of each edge. -/
  up : E → ℝ
  /-- The lower bound `l(e)` of each edge (`0` when the network has no lower bounds). -/
  low : E → ℝ

namespace FlowNet

variable {V E : Type*} [DecidableEq V] [Fintype E]

/-- `(B_Gᵀ f)(v)`: flow into `v` minus flow out of `v`. -/
def netIn (N : FlowNet V E) (f : E → ℝ) (v : V) : ℝ :=
  (∑ e ∈ Finset.univ.filter (fun e => N.head e = v), f e) -
    ∑ e ∈ Finset.univ.filter (fun e => N.tail e = v), f e

/-- `f` is a flow: it respects the bounds `l ≤ f ≤ u`. -/
def IsFlow (N : FlowNet V E) (f : E → ℝ) : Prop :=
  ∀ e, N.low e ≤ f e ∧ f e ≤ N.up e

/-- `f` routes the demand `d`: `B_Gᵀ f = d`. -/
def Routes (N : FlowNet V E) (f : E → ℝ) (d : V → ℝ) : Prop :=
  ∀ v, N.netIn f v = d v

/-- `f` is an `s–t` flow of value `F`: a flow routing `F (1_t − 1_s)`. -/
def IsSTFlow (N : FlowNet V E) (s t : V) (f : E → ℝ) (F : ℝ) : Prop :=
  N.IsFlow f ∧
    N.Routes f (fun v => F * ((if v = t then 1 else 0) - (if v = s then 1 else 0)))

/-- `f` is an `s–T` flow of value `F`: a flow routing `F (b − 1_s)` for some `b ≥ 0` supported on
`T` with `Σ_{v ∈ T} b(v) = 1`. -/
def IsSetFlow (N : FlowNet V E) (s : V) (T : Finset V) (f : E → ℝ) (F : ℝ) : Prop :=
  N.IsFlow f ∧ ∃ b : V → ℝ, (∀ v, 0 ≤ b v) ∧ (∀ v, v ∉ T → b v = 0) ∧ ∑ v ∈ T, b v = 1 ∧
    N.Routes f (fun v => F * (b v - (if v = s then 1 else 0)))

/-- The maximum `s–t` flow has value at least `F`: some `s–t` flow has value `≥ F`. -/
def MaxFlowAtLeast (N : FlowNet V E) (s t : V) (F : ℝ) : Prop :=
  ∃ f : E → ℝ, ∃ F' : ℝ, F ≤ F' ∧ N.IsSTFlow s t f F'

/-- `u⁺(S)`: the total capacity of the edges leaving `S`. -/
def capOut (N : FlowNet V E) (S : Finset V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => N.tail e ∈ S ∧ N.head e ∉ S), N.up e

end FlowNet

namespace Digraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `u⁺_G(S) = Σ_{e ∈ ∂⁺_G(S)} u(e)` for capacities `u` on the edges of `G`. -/
def capOutG (G : Digraph V) (u : V × V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.outBoundary S, u e

/-- The network `G_α` (pp. 7, 14): the edges of `G` with capacities `u`, a new vertex `t = none`,
and a sink edge `(v, t)` of capacity `α · deg⁺_G(v)` for every vertex `v`; no lower bounds. -/
def alphaNet (G : Digraph V) (u : V × V → ℝ) (α : ℝ) : FlowNet (Option V) (G.edges ⊕ V) where
  tail := fun x => match x with
    | Sum.inl e => some e.1.1
    | Sum.inr v => some v
  head := fun x => match x with
    | Sum.inl e => some e.1.2
    | Sum.inr _ => none
  up := fun x => match x with
    | Sum.inl e => u e.1
    | Sum.inr v => α * (G.outDeg v : ℝ)
  low := fun _ => 0

end Digraph

end IncApproxVC.Oblivious


