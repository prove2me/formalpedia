-- Prove2me | Definitions.Def_EdmondsKarp_Scaling_Transport
-- name    : EdmondsKarp_Scaling_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:22:17.686131+00:00
-- url     : https://prove2.me/theorems/7def9978-b148-40fa-8e49-9bb9c81f4400
-- title:
--   The Hitchcock network of Figure 1: flows, maximum flows, cost, extreme and pseudo-extreme flows
-- statement:
--   Fix integers $m, n \ge 0$. The **network of Figure 1** (Edmonds–Karp, p. 259) has a source $s$, a sink $t$, supply nodes $s_1, \dots, s_m$ and demand nodes $t_1, \dots, t_n$. Its arcs are $(s, s_i)$ for every $i$, $(s_i, t_j)$ for every $i, j$, $(t_j, t)$ for every $j$, and the return arc $(t, s)$. A **problem** on this network is given by real numbers $a_i$ (the capacity of $(s, s_i)$), $b_j$ (the capacity of $(t_j, t)$) and $d_{ij}$ (the cost of $(s_i, t_j)$); the arcs $(s_i, t_j)$ and $(t, s)$ have capacity $+\infty$, and the arcs $(s, s_i)$, $(t_j, t)$, $(t, s)$ have cost $0$.
--
--   Write $f_{0i} = f(s, s_i)$, $f_{ij} = f(s_i, t_j)$, $f_{j0} = f(t_j, t)$ and $f(t, s)$ for the value of a function $f$ on the arcs. Such an $f$ is a **flow** if it is nonnegative on every arc, $f_{0i} \le a_i$, $f_{j0} \le b_j$, and flow is conserved at every node:
--   $$\sum_i f_{0i} = f(t,s), \qquad \sum_j f_{ij} = f_{0i}, \qquad \sum_i f_{ij} = f_{j0}, \qquad \sum_j f_{j0} = f(t,s).$$
--   A flow is a **maximum flow** if $f(t,s) \ge g(t,s)$ for every flow $g$. The **cost** of $f$ is $\sum_{i,j} d_{ij} f_{ij}$. A flow is **extreme** if its cost is at most that of every flow $g$ with $g(t,s) = f(t,s)$. A flow is **pseudo-extreme** if there are real numbers $u_1,\dots,u_m$ and $v_1,\dots,v_n$ with
--   $$u_i - v_j + d_{ij} \ge 0 \quad (5a), \qquad u_i - v_j + d_{ij} > 0 \Rightarrow f_{ij} = 0 \quad (5b)$$
--   for all $i, j$.
--
--   These are the objects of the Hitchcock transportation problem, which asks for a maximum flow of minimum cost; every statement of the mission is phrased in them.
--
--   **Formalization Note** Nodes form an inductive type `Node m n`. A flow is a structure with four components `f0`, `fx`, `fz`, `ret`, so only the arcs of Figure 1 carry values; the infinite capacities are encoded by the absence of an upper bound on `fx` and `ret`. Capacities are real so that Theorem 8 is stated in the paper's generality; positivity, integrality and $\sum a_i = \sum b_j$ are hypotheses of the theorems. A maximum flow is a predicate, not a supremum. `IsExtreme` includes that the flow is a flow.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249 §1.1 (network, flow, maximum flow); p. 255 §2.1 (cost, extreme flow); pp. 258–259 §2.2 (Hitchcock problem, Figure 1, pseudo-extreme flow, (5a)–(5b))

import Mathlib

namespace EdmondsKarp.Scaling

/-- The nodes of the network of Figure 1 (Edmonds–Karp 1972, p. 259): the source `s`, the sink `t`,
the supply nodes `s_1, …, s_m` (`src i`) and the demand nodes `t_1, …, t_n` (`dst j`). -/
inductive Node (m n : ℕ) where
  | s : Node m n
  | t : Node m n
  | src : Fin m → Node m n
  | dst : Fin n → Node m n
  deriving DecidableEq

/-- Data of a problem on the network of Figure 1 (§2.2, p. 258): the capacity `a i` of the arc
`(s, s_i)`, the capacity `b j` of the arc `(t_j, t)`, and the cost `d i j` of the arc `(s_i, t_j)`.
The arcs `(s_i, t_j)` and the return arc `(t, s)` have capacity `+∞`; the arcs `(s, s_i)`, `(t_j, t)`
and the return arc have cost `0`. Sign and integrality conditions on the data are stated as
hypotheses where the paper assumes them. -/
structure Transport (m n : ℕ) where
  a : Fin m → ℝ
  b : Fin n → ℝ
  d : Fin m → Fin n → ℝ

/-- A function on the arcs of the network of Figure 1, in the paper's notation (p. 258):
`f0 i = f_{0i} = f(s, s_i)`, `fx i j = f_{ij} = f(s_i, t_j)`, `fz j = f_{j0} = f(t_j, t)`,
and `ret = f(t, s)`, the value on the return arc. -/
structure Flow (m n : ℕ) where
  f0 : Fin m → ℝ
  fx : Fin m → Fin n → ℝ
  fz : Fin n → ℝ
  ret : ℝ

variable {m n : ℕ}

/-- The zero function on the arcs. -/
instance : Zero (Flow m n) := ⟨⟨0, 0, 0, 0⟩⟩

/-- Scalar multiple `c • f` (arcwise); the scaling method uses `2 • f` (p. 260). -/
instance : SMul ℝ (Flow m n) := ⟨fun c x => ⟨c • x.f0, c • x.fx, c • x.fz, c * x.ret⟩⟩

/-- A flow in the network of Figure 1 (§1.1, p. 249): nonnegative on every arc including the return
arc, at most the capacity on the finite-capacity arcs `(s, s_i)` and `(t_j, t)`, and conserving
flow (outflow minus inflow equals zero) at every node `s`, `s_i`, `t_j`, `t`. -/
def IsFlow (T : Transport m n) (x : Flow m n) : Prop :=
  (∀ i, 0 ≤ x.f0 i) ∧ (∀ i j, 0 ≤ x.fx i j) ∧ (∀ j, 0 ≤ x.fz j) ∧ 0 ≤ x.ret ∧
  (∀ i, x.f0 i ≤ T.a i) ∧ (∀ j, x.fz j ≤ T.b j) ∧
  (∑ i, x.f0 i) - x.ret = 0 ∧
  (∀ i, (∑ j, x.fx i j) - x.f0 i = 0) ∧
  (∀ j, x.fz j - ∑ i, x.fx i j = 0) ∧
  x.ret - ∑ j, x.fz j = 0

/-- A maximum flow (§1.1, p. 249): a flow whose return-arc value is at least that of every flow. -/
def IsMaxFlow (T : Transport m n) (x : Flow m n) : Prop :=
  IsFlow T x ∧ ∀ y : Flow m n, IsFlow T y → y.ret ≤ x.ret

/-- The cost of a flow (§2.1, p. 255): `∑_{(u,v) ∈ A} d(u,v) f(u,v)`; only the arcs `(s_i, t_j)`
have nonzero cost in the network of Figure 1. -/
def cost (T : Transport m n) (x : Flow m n) : ℝ :=
  ∑ i, ∑ j, T.d i j * x.fx i j

/-- An extreme flow (§2.1, p. 255): a flow of minimum cost among the flows with the same value
`f(t, s)`. -/
def IsExtreme (T : Transport m n) (x : Flow m n) : Prop :=
  IsFlow T x ∧ ∀ y : Flow m n, IsFlow T y → y.ret = x.ret → cost T x ≤ cost T y

/-- A pseudo-extreme flow (§2.2, p. 259): a flow for which there exist real numbers `u_i`, `v_j`
satisfying (5a) `u_i - v_j + d_ij ≥ 0` for all `i, j`, and (5b) `u_i - v_j + d_ij > 0 ⇒ f_ij = 0`. -/
def IsPseudoExtreme (T : Transport m n) (x : Flow m n) : Prop :=
  IsFlow T x ∧ ∃ (u : Fin m → ℝ) (v : Fin n → ℝ),
    (∀ i j, 0 ≤ u i - v j + T.d i j) ∧
    (∀ i j, 0 < u i - v j + T.d i j → x.fx i j = 0)

end EdmondsKarp.Scaling


