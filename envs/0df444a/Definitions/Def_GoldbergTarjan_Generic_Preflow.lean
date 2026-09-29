-- Prove2me | Definitions.Def_GoldbergTarjan_Generic_Preflow
-- name    : GoldbergTarjan_Generic_Preflow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:22:11.255412+00:00
-- url     : https://prove2.me/theorems/1b9315a5-c177-4081-b1aa-15870e455956
-- title:
--   Flows, preflows, excess, flow value, maximum flow, residual capacity and residual reachability
-- statement:
--   Let $N$ be a flow network with vertex set $V$, source $s$, sink $t$ and capacity $c$. All objects below are real-valued functions $f$ on **all** ordered vertex pairs (they may be negative).
--
--   1. The **flow excess** of a vertex $v$ is the net flow into $v$: $e(v) = \sum_{u \in V} f(u,v)$.
--   2. $f$ is a **preflow** if it satisfies the capacity constraint (1) $f(v,w) \le c(v,w)$ for all $(v,w)$, the antisymmetry constraint (2) $f(v,w) = -f(w,v)$ for all $(v,w)$, and the nonnegativity constraint (4) $e(v) \ge 0$ for every $v \ne s$.
--   3. $f$ is a **flow** if it satisfies (1), (2) and flow conservation (3): $e(v) = 0$ for every $v \in V - \{s,t\}$.
--   4. The **value** of $f$ is the net flow into the sink,
--   $$|f| = \sum_{v \in V} f(v,t).$$
--   5. A **maximum flow** is a flow $f$ with $|g| \le |f|$ for every flow $g$.
--   6. The **residual capacity** of a pair is $r_f(v,w) = c(v,w) - f(v,w)$; $(v,w)$ is a **residual edge** if $r_f(v,w) > 0$, and the **residual graph** $G_f$ has vertex set $V$ and the residual edges as edges.
--   7. $w$ is **reachable** from $v$ in $G_f$ if there is a path of zero or more residual edges from $v$ to $w$.
--
--   These are the objects of §2 of the paper; the correctness part of the mission (Theorem 3.2, Lemmas 3.3, 3.5, Theorem 3.4) is stated in terms of them.
--
--   **Formalization Note.** A maximum flow is expressed as a predicate ("a flow whose value is at least that of every flow"), not through a supremum. Reachability is the reflexive–transitive closure of the residual-edge relation; for $v \ne w$ it is the existence of a (simple) path in $G_f$.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, pp. 923–924, §2, constraints (1)–(4), value, maximum flow, flow excess, residual capacity, residual graph

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Network

namespace GoldbergTarjan.Generic

variable {V : Type} [Fintype V]

/-- Flow excess `e(v) = ∑_{u ∈ V} f(u, v)`, the net flow into `v` (p. 924). -/
def excess (f : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, f u v

/-- A preflow (p. 924): a real-valued function on vertex pairs satisfying the capacity
constraint (1), the antisymmetry constraint (2) and the nonnegativity constraint (4):
`∑_u f(u, v) ≥ 0` for every `v ≠ s`. -/
def IsPreflow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, f v w ≤ N.c v w) ∧ (∀ v w, f v w = -f w v) ∧
    (∀ v, v ≠ N.s → 0 ≤ excess f v)

/-- A flow (p. 923): a real-valued function on vertex pairs satisfying the capacity
constraint (1), the antisymmetry constraint (2) and flow conservation (3):
`∑_u f(u, v) = 0` for every `v ∉ {s, t}`. -/
def IsFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, f v w ≤ N.c v w) ∧ (∀ v w, f v w = -f w v) ∧
    (∀ v, v ≠ N.s → v ≠ N.t → excess f v = 0)

/-- The value `|f| = ∑_{v ∈ V} f(v, t)` of a flow, the net flow into the sink (p. 924). -/
def value (N : Network V) (f : V → V → ℝ) : ℝ :=
  ∑ v, f v N.t

/-- A maximum flow (p. 924): a flow whose value is at least the value of every flow. -/
def IsMaxFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  IsFlow N f ∧ ∀ g : V → V → ℝ, IsFlow N g → value N g ≤ value N f

/-- Residual capacity `r_f(v, w) = c(v, w) - f(v, w)` (p. 924). -/
def residualCap (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  N.c v w - f v w

/-- `(v, w)` is a residual edge, i.e. an edge of the residual graph `G_f`, iff
`r_f(v, w) > 0` (p. 924). -/
def IsResidualEdge (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  0 < residualCap N f v w

/-- `ResidualReachable N f v w`: `w` is reachable from `v` in the residual graph `G_f`
(a path of zero or more residual edges from `v` to `w`). -/
def ResidualReachable (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  Relation.ReflTransGen (IsResidualEdge N f) v w

end GoldbergTarjan.Generic


