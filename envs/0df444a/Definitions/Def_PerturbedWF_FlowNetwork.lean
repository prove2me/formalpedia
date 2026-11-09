-- Prove2me | Definitions.Def_PerturbedWF_FlowNetwork
-- name    : PerturbedWF_FlowNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:23.339205+00:00
-- url     : https://prove2.me/theorems/13ae0854-afdf-42c7-8d61-e31f1f1651c9
-- title:
--   The flow model (B.1): a DAG with bounds, demands, arc costs and a sink, and its value function $W$
-- statement:
--   Let $G=(V,A)$ be a finite directed acyclic graph with bounds $\ell_a,u_a\in\mathbb R_{\ge0}\cup\{\infty\}$ on each arc, a demand vector $b\in\mathbb R^V$ with $\sum_vb_v=0$, and lower semicontinuous arc costs $\phi_a:\mathbb R_{\ge0}\to\mathbb R$. The feasible flows are
--   $$\mathcal F=\Big\{f\in\mathbb R^A_{\ge0}:\ \ell_a\le f_a\le u_a\ \forall a,\ \ \sum_{a\in\delta^+(v)}f_a-\sum_{a\in\delta^-(v)}f_a=b_v\ \forall v\Big\}.$$
--   The graph contains a sink $s$ of in-degree $n$ and out-degree $0$; its incoming arcs $a_i=(v_i,s)$, one for each point $i\in[n]$, have zero cost. The function
--   $$W(x)=\min_{f\in\mathcal F}\Big\{\sum_{a\in A}\phi_a(f_a):\ f_{a_i}=x_i\ \forall i\in[n]\Big\}\qquad(B.1)$$
--   is the value of the cheapest feasible flow whose sink arcs carry $x$ ($\infty$ if there is none).
--
--   Every work function considered in the paper is of this form; Lemma B.1 derives the exchange property from it.
--
--   **Formalization Note.** Acyclicity is a rank function on the nodes strictly increasing along every arc. Bounds are in $[0,\infty]$; arc costs are functions $\mathbb R\to\mathbb R$ used on $[0,\infty)$; $\delta^+(v)$ are the arcs leaving $v$. `flowW` is the infimum in `EReal` over the feasible flows with the prescribed sink values ($+\infty$ when there are none).
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Appendix B, the two paragraphs before Lemma B.1, p.32 (PDF p.33), the set F and eq. (B.1)

import Mathlib

namespace PerturbedWF

/-!
# The flow model (B.1) of Appendix B

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), Appendix B, the paragraphs before Lemma B.1, p.32
(PDF p.33), the feasible flows `F` and eq. (B.1).

A finite directed acyclic graph `G = (V, A)` with arc bounds `ℓ_a, u_a ∈ ℝ_{≥0} ∪ {∞}`, a demand
vector `b` with `∑_v b_v = 0`, lower semicontinuous arc costs `φ_a : ℝ_{≥0} → ℝ`, and a sink `s`
of in-degree `n` and out-degree `0` whose incoming arcs `a_i = (v_i, s)`, one per point `i ∈ [n]`,
have zero cost. `flowW N x` is the function `W` of (B.1).

**Formalization Note.**
* Nodes and arcs are finite types `Node`, `Arc`; an arc `a` goes from `tail a` to `head a`.
  Acyclicity is encoded by a rank function `rank : Node → ℕ` that strictly increases along every
  arc (a finite digraph is acyclic iff it has such a function).
* Bounds are in `ℝ≥0∞` (`⊤` is the paper's `∞`); a flow value `f a ≥ 0` is compared through
  `ENNReal.ofReal`.
* A cost `φ_a : ℝ_{≥0} → ℝ` is a function `ℝ → ℝ` of which only the values on `[0, ∞)` are used;
  lower semicontinuity is required on `[0, ∞)`.
* The sink arcs are an injective map `sinkArc : ι → Arc` with head `s`; every arc with head `s`
  is a sink arc, no arc leaves `s`, and the cost of each sink arc is the zero function.
* Flow conservation is `∑_{a ∈ δ⁺(v)} f_a − ∑_{a ∈ δ⁻(v)} f_a = b_v`, with `δ⁺(v)` the arcs
  leaving `v` and `δ⁻(v)` the arcs entering `v`.
* `flowW N x` is the infimum in `EReal` of the total cost over feasible flows with `f_{a_i} = x_i`
  for every `i`; it is `⊤` when no such flow exists (the paper's `min` of an empty set, `∞`).
-/

/-- The data of Appendix B (p.32): a finite DAG with bounds, demands, lower semicontinuous arc
costs, and a sink whose `n` incoming zero-cost arcs correspond to the points of the metric. -/
structure FlowNetwork (ι Node Arc : Type) [Fintype Node] where
  /-- The tail of an arc. -/
  tail : Arc → Node
  /-- The head of an arc. -/
  head : Arc → Node
  /-- A rank function strictly increasing along arcs (acyclicity). -/
  rank : Node → ℕ
  rank_lt : ∀ a, rank (tail a) < rank (head a)
  /-- Lower bound `ℓ_a ∈ ℝ_{≥0} ∪ {∞}`. -/
  lower : Arc → ENNReal
  /-- Upper bound `u_a ∈ ℝ_{≥0} ∪ {∞}`. -/
  upper : Arc → ENNReal
  /-- The demand vector `b`. -/
  demand : Node → ℝ
  demand_sum : ∑ v, demand v = 0
  /-- The arc costs `φ_a`, used on `[0, ∞)`. -/
  cost : Arc → ℝ → ℝ
  cost_lsc : ∀ a, LowerSemicontinuousOn (cost a) (Set.Ici 0)
  /-- The sink `s`. -/
  sink : Node
  /-- The arc `a_i = (v_i, s)` of the point `i`. -/
  sinkArc : ι → Arc
  sinkArc_injective : Function.Injective sinkArc
  head_sinkArc : ∀ i, head (sinkArc i) = sink
  sinkArc_of_head : ∀ a, head a = sink → ∃ i, sinkArc i = a
  tail_ne_sink : ∀ a, tail a ≠ sink
  cost_sinkArc : ∀ i, cost (sinkArc i) = 0

namespace FlowNetwork

variable {ι Node Arc : Type} [Fintype Node] [Fintype Arc] [DecidableEq Node]

/-- `f` is a feasible flow (the set `F` of p.32): nonnegative, within the bounds, and satisfying
the demands. -/
def IsFeasible (N : FlowNetwork ι Node Arc) (f : Arc → ℝ) : Prop :=
  (∀ a, 0 ≤ f a) ∧ (∀ a, N.lower a ≤ ENNReal.ofReal (f a) ∧ ENNReal.ofReal (f a) ≤ N.upper a) ∧
    ∀ v, (∑ a ∈ Finset.univ.filter (fun a => N.tail a = v), f a) -
      (∑ a ∈ Finset.univ.filter (fun a => N.head a = v), f a) = N.demand v

/-- The function `W` of (B.1): `W(x) = min {∑_a φ_a(f_a) : f ∈ F, f_{a_i} = x_i ∀ i}`, an
infimum in `EReal` (`⊤` if no feasible flow has sink values `x`). -/
noncomputable def flowW (N : FlowNetwork ι Node Arc) (x : ι → ℝ) : EReal :=
  ⨅ f ∈ {f : Arc → ℝ | N.IsFeasible f ∧ ∀ i, f (N.sinkArc i) = x i},
    ((∑ a, N.cost a (f a) : ℝ) : EReal)

end FlowNetwork

end PerturbedWF


