-- Prove2me | Definitions.Def_GoldbergTarjan_FIFO_Network
-- name    : GoldbergTarjan_FIFO_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:31:38.075893+00:00
-- url     : https://prove2.me/theorems/b503b9cb-ef99-4f98-840d-ea4caf50f19e
-- title:
--   Flow network, excess, residual capacity, preflow, residual reachability, active vertex (Goldberg–Tarjan §2)
-- statement:
--   This file sets up the basic objects of §2 of Goldberg and Tarjan's paper.
--
--   A **flow network** consists of a finite vertex set $V$ with $n = |V|$, a capacity $c(v,w) \ge 0$ for every ordered pair of vertices, a source $s$ and a sink $t$ with $s \neq t$. The edge set is $E = \{(v,w) : c(v,w) > 0\}$: the paper gives each edge a positive capacity and extends $c$ by $0$ to all other pairs. The graph has no loops, $c(v,v) = 0$.
--
--   For a real-valued function $f$ on vertex pairs:
--
--   1. the **excess** of $v$ is the net flow into $v$, $$e(v) = \sum_{u \in V} f(u,v);$$
--   2. the **residual capacity** of $(v,w)$ is $r_f(v,w) = c(v,w) - f(v,w)$, and $(v,w)$ is a **residual edge** if $r_f(v,w) > 0$;
--   3. $f$ is a **preflow** if $f(v,w) \le c(v,w)$ and $f(v,w) = -f(w,v)$ for all pairs, and $e(v) \ge 0$ for every $v \neq s$;
--   4. $w$ is **reachable from $v$ in the residual graph** $G_f$ if there is a directed path (possibly of length $0$) from $v$ to $w$ using residual edges only.
--
--   For a labeling $d : V \to \mathbb{N} \cup \{\infty\}$, a vertex $v$ is **active** if $v \notin \{s,t\}$, $d(v) < \infty$ and $e(v) > 0$.
--
--   These are the objects on which the push and relabel operations and the first-in, first-out algorithm of the mission act.
--
--   **Formalization Note** Flows are antisymmetric functions on all ordered pairs and may be negative; they are not nonnegative arc flows. The excess is computed from $f$ rather than stored. Labels take values in `ℕ∞`. The hypothesis $c(v,v) = 0$ is added: with a loop at $s$ the initialization of Fig. 2 would not be antisymmetric.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, pp. 923–925, §2 (flow network p. 923, preflow and excess p. 924, residual graph p. 924, active vertex p. 925)

import Mathlib

namespace GoldbergTarjan.FIFO

/-- A flow network (Goldberg–Tarjan 1988, §2, p. 923). The vertex set is the finite type `V`
(`n = Fintype.card V`). The capacity `c v w` is defined on **all** ordered vertex pairs: it is
positive exactly on the edges `(v, w) ∈ E` and `0` on every other pair ("we extend the capacity
function to all vertex pairs by defining `c(v, w) = 0` if `(v, w) ∉ E`"), so `E` is the support of
`c`. The graph has no loops (`c v v = 0`). The source `s` and the sink `t` are distinct. -/
structure Network (V : Type) [Fintype V] [DecidableEq V] where
  /-- capacity of the ordered vertex pair `(v, w)`; `0` when `(v, w)` is not an edge -/
  c : V → V → ℝ
  /-- the source -/
  s : V
  /-- the sink -/
  t : V
  c_nonneg : ∀ v w, 0 ≤ c v w
  c_self : ∀ v, c v v = 0
  s_ne_t : s ≠ t

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The flow excess `e(v) = ∑_{u ∈ V} f(u, v)`, the net flow into `v` (p. 924). Here `f` is any
real-valued function on vertex pairs. -/
def excess (f : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, f u v

/-- The residual capacity `r_f(v, w) = c(v, w) − f(v, w)` (p. 924). -/
def residual (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  N.c v w - f v w

/-- A preflow (p. 924): a real-valued function on vertex pairs satisfying the capacity
constraint (1) `f(v, w) ≤ c(v, w)` and the antisymmetry constraint (2) `f(v, w) = −f(w, v)` for
all pairs, and the nonnegativity constraint (4) `∑_u f(u, v) ≥ 0` for all `v ∈ V − {s}`. -/
def IsPreflow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, f v w ≤ N.c v w) ∧ (∀ v w, f v w = -f w v) ∧ (∀ v, v ≠ N.s → 0 ≤ excess f v)

/-- `w` is reachable from `v` in the residual graph `G_f = (V, E_f)`, whose edges are the residual
edges `(a, b)` with `r_f(a, b) > 0` (p. 924): there is a (possibly empty) directed path of residual
edges from `v` to `w`. -/
def ResidualReachable (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  Relation.ReflTransGen (fun a b => 0 < residual N f a b) v w

/-- A vertex `v` is active (p. 925) if `v ∈ V − {s, t}`, `d(v) < ∞` and `e(v) > 0`. Labels take
values in `ℕ∞` (the nonnegative integers and infinity). -/
def IsActive (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  v ≠ N.s ∧ v ≠ N.t ∧ d v < ⊤ ∧ 0 < excess f v

end GoldbergTarjan.FIFO


