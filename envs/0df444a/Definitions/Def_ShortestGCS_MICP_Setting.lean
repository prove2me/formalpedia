-- Prove2me | Definitions.Def_ShortestGCS_MICP_Setting
-- name    : ShortestGCS_MICP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:57.408947+00:00
-- url     : https://prove2.me/theorems/95c25ebb-46c4-4f1e-899b-a66e32fc9153
-- title:
--   §2 (2.1), §5.1–5.3 (5.1), (5.2), (5.5) — the graph of convex sets, s-t paths, the SPP in GCS and the MICP (5.5)
-- statement:
--   **Graph of convex sets.** $G = (\mathcal V, \mathcal E)$ is a directed graph with edge set $\mathcal E \subseteq \mathcal V \times \mathcal V$, a source $s$ and a target $t$. Each vertex $v$ carries a set $\mathcal X_v \subseteq \mathbb R^n$ and each edge $e = (u,v)$ a length $\ell_e : \mathbb R^n \times \mathbb R^n \to \mathbb R \cup \{\infty\}$, evaluated at $(x_u, x_v)$. The **standing assumptions** of §2 are: $s \ne t$; every $\mathcal X_v$ is nonempty, compact and convex; every $\ell_e$ is nonnegative, proper, closed and convex. The separate assumption of §5.1 (p. 7) is that no edge enters $s$ and no edge leaves $t$: $|\mathcal E^{\mathrm{in}}_s| = |\mathcal E^{\mathrm{out}}_t| = 0$.
--
--   For a vertex $v$, $\mathcal E^{\mathrm{in}}_v := \{(u,v)\in\mathcal E\}$, $\mathcal E^{\mathrm{out}}_v := \{(v,u)\in\mathcal E\}$ and $\mathcal E_v := \mathcal E^{\mathrm{in}}_v \cup \mathcal E^{\mathrm{out}}_v$.
--
--   **The SPP in GCS (2.1).** An $s$-$t$ path is a sequence of distinct vertices $p = (v_0,\dots,v_K)$ with $v_0 = s$, $v_K = t$ and $(v_k, v_{k+1}) \in \mathcal E$; $\mathcal E_p$ is the set of its edges. The optimal value of (2.1) is
--
--   $$
--   \operatorname{SPP}(G) := \inf\Big\{ \sum_{e=(u,v)\in\mathcal E_p} \ell_e(x_u,x_v) \;:\; p \text{ an } s\text{-}t \text{ path},\ x_v \in \mathcal X_v \ \forall v \in p \Big\}.
--   $$
--
--   **The MICP (5.5).** Its variables are flows $y_e$ and vectors $z_e, z'_e \in \mathbb R^n$ for $e \in \mathcal E$. Its constraints are
--
--   $$
--   \begin{aligned}
--   &\textstyle\sum_{e\in\mathcal E^{\mathrm{out}}_s} y_e = 1,\quad \sum_{e\in\mathcal E^{\mathrm{in}}_t} y_e = 1, && \text{(5.5b)}\\
--   &\textstyle\sum_{e\in\mathcal E^{\mathrm{out}}_v} y_e \le 1 \quad \forall v \ne s,t, && \text{(5.5c)}\\
--   &\textstyle\sum_{e\in\mathcal E^{\mathrm{in}}_v} (z'_e, y_e) = \sum_{e\in\mathcal E^{\mathrm{out}}_v} (z_e, y_e) \quad \forall v \ne s,t, && \text{(5.5d)}\\
--   &(z_e, y_e) \in \tilde{\mathcal X}_u,\ (z'_e, y_e) \in \tilde{\mathcal X}_v \quad \forall e = (u,v) \in \mathcal E, && \text{(5.5e)}\\
--   &y_e \in \{0,1\} \quad \forall e \in \mathcal E, && \text{(5.5f)}
--   \end{aligned}
--   $$
--
--   and its optimal value is $\operatorname{MICP}(G) := \inf \sum_{e\in\mathcal E} \tilde\ell_e(z_e, z'_e, y_e)$ over these constraints, with $\tilde\ell_e$ the perspective of $\ell_e$ as a function on $\mathbb R^{2n}$ (Definition 4.4, footnote 3).
--
--   **The biconvex program (5.2).** Its feasible points $(y, x, z, z')$ satisfy the constraints (5.1b)–(5.1d) of the shortest-path LP (5.1) — (5.5b), (5.5c), flow conservation $\sum_{\mathcal E^{\mathrm{in}}_v} y_e = \sum_{\mathcal E^{\mathrm{out}}_v} y_e$ for $v \ne s,t$, and $y_e \ge 0$ — together with $x_v \in \mathcal X_v$ for every vertex (5.2c) and $z_e = y_e x_u$, $z'_e = y_e x_v$ for every $e = (u,v)$ (5.2d).
--
--   These are the objects of Theorem 5.7, which states $\operatorname{MICP}(G) = \operatorname{SPP}(G)$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; lengths and optimal values are in `EReal`, and both optimal values are infima, equal to $+\infty$ when the feasible set is empty (no $s$-$t$ path). Paths are lists of vertices without repetition; $\mathcal E_p$ is the list of consecutive pairs. The flows and vectors are functions on $\mathcal V\times\mathcal V$ whose values off $\mathcal E$ are never read. The standing assumptions are bundled as `IsGCS`, and the §5.1 assumption is the separate predicate `NoInSNoOutT`, so every theorem states which it uses.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, §2, pp. 3–4, (2.1); §5.1, p. 7, (5.1) and ℰ_v^in, ℰ_v^out; §5.2, p. 8, (5.2); §5.3, p. 9, ℰ_v and (5.5)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun

namespace ShortestGCS.MICP

/-- The data of a shortest-path problem in a graph of convex sets (§2, arXiv:2101.11565v5, pp. 3–4):
a directed graph with vertex type `V` and edge set `E ⊆ V × V`, a source `s`, a target `t`,
a set `X v ⊆ ℝⁿ` for every vertex, and an edge length `ℓ e : ℝⁿ × ℝⁿ → ℝ ∪ {±∞}` for every edge.
Values of `ℓ` off `E` are never read. -/
structure GCS (V : Type*) (n : ℕ) where
  /-- the edge set `ℰ` -/
  E : Finset (V × V)
  /-- the source vertex `s` -/
  s : V
  /-- the target vertex `t` -/
  t : V
  /-- the convex set `𝒳_v ⊆ ℝⁿ` of each vertex -/
  X : V → Set (Fin n → ℝ)
  /-- the edge length `ℓ_e(x_u, x_v)` -/
  ℓ : V × V → (Fin n → ℝ) × (Fin n → ℝ) → EReal

variable {V : Type*} {n : ℕ}

/-- The standing assumptions of §2 (pp. 3–4): `s ≠ t`; every `𝒳_v` is nonempty, compact and convex;
every edge length takes values in `ℝ≥0 ∪ {∞}` and is proper, closed and convex. -/
structure IsGCS (G : GCS V n) : Prop where
  s_ne_t : G.s ≠ G.t
  X_nonempty : ∀ v, (G.X v).Nonempty
  X_compact : ∀ v, IsCompact (G.X v)
  X_convex : ∀ v, Convex ℝ (G.X v)
  ℓ_nonneg : ∀ e ∈ G.E, ∀ p, 0 ≤ G.ℓ e p
  ℓ_pcc : ∀ e ∈ G.E, IsProperClosedConvex (G.ℓ e)

/-- The assumption of §5.1, p. 7: `|ℰ_s^in| = |ℰ_t^out| = 0`, i.e. no edge enters the source and
no edge leaves the target. -/
def NoInSNoOutT (G : GCS V n) : Prop :=
  ∀ e ∈ G.E, e.2 ≠ G.s ∧ e.1 ≠ G.t

variable [DecidableEq V]

/-- `ℰ_v^in := {(u, v) ∈ ℰ}` (§5.1, p. 7). -/
def inEdges (G : GCS V n) (v : V) : Finset (V × V) := G.E.filter (fun e => e.2 = v)

/-- `ℰ_v^out := {(v, u) ∈ ℰ}` (§5.1, p. 7). -/
def outEdges (G : GCS V n) (v : V) : Finset (V × V) := G.E.filter (fun e => e.1 = v)

/-- `ℰ_v := ℰ_v^in ∪ ℰ_v^out`, the edges incident with `v` (§5.3, p. 9). -/
def edgesAt (G : GCS V n) (v : V) : Finset (V × V) := G.E.filter (fun e => e.1 = v ∨ e.2 = v)

/-- An `s`-`t` path (§2, p. 4): a sequence of distinct vertices `(v_0, …, v_K)` with `v_0 = s`,
`v_K = t` and `(v_k, v_{k+1}) ∈ ℰ` for all `k`. -/
def IsPath (G : GCS V n) (p : List V) : Prop :=
  p.head? = some G.s ∧ p.getLast? = some G.t ∧ p.Nodup ∧ p.IsChain (fun u v => (u, v) ∈ G.E)

/-- `ℰ_p := {(v_0, v_1), …, (v_{K-1}, v_K)}`, the edges traversed by `p` (§2, p. 4), in order. -/
def pathEdges (p : List V) : List (V × V) := p.zip p.tail

/-- The cost (2.1a) of a path `p` with vertex positions `x`: `∑_{e = (u,v) ∈ ℰ_p} ℓ_e(x_u, x_v)`. -/
noncomputable def pathCost (G : GCS V n) (p : List V) (x : V → Fin n → ℝ) : EReal :=
  ((pathEdges p).map fun e => G.ℓ e (x e.1, x e.2)).sum

/-- The optimal value of the SPP in GCS (2.1), p. 4: the infimum, in `EReal`, of the cost (2.1a)
over all `s`-`t` paths `p` (2.1b) and all positions with `x_v ∈ 𝒳_v` for `v ∈ p` (2.1c). It is
`⊤` when there is no `s`-`t` path. Positions of vertices off `p` are free and do not enter. -/
noncomputable def sppValue (G : GCS V n) : EReal :=
  ⨅ (p : List V) (_ : IsPath G p) (x : V → Fin n → ℝ) (_ : ∀ v ∈ p, x v ∈ G.X v), pathCost G p x

/-- The constraints (5.5b)–(5.5f) of the MICP (5.5), arXiv:2101.11565v5, p. 9, on flows
`y : ℰ → ℝ` and auxiliary variables `z, z' : ℰ → ℝⁿ`. Values off `ℰ` are never read. -/
structure IsMICPFeasible (G : GCS V n) (y : V × V → ℝ) (z z' : V × V → Fin n → ℝ) : Prop where
  /-- (5.5b), first equation -/
  source : ∑ e ∈ outEdges G G.s, y e = 1
  /-- (5.5b), second equation -/
  target : ∑ e ∈ inEdges G G.t, y e = 1
  /-- (5.5c) -/
  degree : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ outEdges G v, y e ≤ 1
  /-- (5.5d), vector component -/
  conserve_z : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, z' e = ∑ e ∈ outEdges G v, z e
  /-- (5.5d), flow component -/
  conserve_y : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, y e = ∑ e ∈ outEdges G v, y e
  /-- (5.5e) -/
  persp : ∀ e ∈ G.E, (z e, y e) ∈ perspectiveSet (G.X e.1) ∧ (z' e, y e) ∈ perspectiveSet (G.X e.2)
  /-- (5.5f) -/
  binary : ∀ e ∈ G.E, y e = 0 ∨ y e = 1

/-- The objective (5.5a): `∑_{e ∈ ℰ} ℓ̃_e(z_e, z'_e, y_e)`, with `ℓ̃_e` the perspective (Definition 4.4)
of `ℓ_e` as a function on `ℝⁿ × ℝⁿ` (footnote 3, p. 8). -/
noncomputable def micpCost (G : GCS V n) (y : V × V → ℝ) (z z' : V × V → Fin n → ℝ) : EReal :=
  ∑ e ∈ G.E, perspectiveFun (G.ℓ e) (z e, z' e) (y e)

/-- The optimal value of the MICP (5.5): the infimum, in `EReal`, of (5.5a) over (5.5b)–(5.5f). -/
noncomputable def micpValue (G : GCS V n) : EReal :=
  ⨅ (y : V × V → ℝ) (z : V × V → Fin n → ℝ) (z' : V × V → Fin n → ℝ)
    (_ : IsMICPFeasible G y z z'), micpCost G y z z'

/-- The feasible set of the biconvex program (5.2), arXiv:2101.11565v5, p. 8: the constraints
(5.1b)–(5.1d) of the LP (5.1), p. 7, on the flows `y`; `x_v ∈ 𝒳_v` for every vertex (5.2c); and the
bilinear constraints `z_e = y_e x_u`, `z'_e = y_e x_v` for every `e = (u, v) ∈ ℰ` (5.2d). -/
structure IsFeasible52 (G : GCS V n) (y : V × V → ℝ) (x : V → Fin n → ℝ)
    (z z' : V × V → Fin n → ℝ) : Prop where
  /-- (5.1b), first equation -/
  source : ∑ e ∈ outEdges G G.s, y e = 1
  /-- (5.1b), second equation -/
  target : ∑ e ∈ inEdges G G.t, y e = 1
  /-- (5.1c), flow conservation -/
  conserve : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, y e = ∑ e ∈ outEdges G v, y e
  /-- (5.1c), degree constraint -/
  degree : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ outEdges G v, y e ≤ 1
  /-- (5.1d) -/
  nonneg : ∀ e ∈ G.E, 0 ≤ y e
  /-- (5.2c) -/
  mem : ∀ v, x v ∈ G.X v
  /-- (5.2d) -/
  bilinear : ∀ e ∈ G.E, z e = y e • x e.1 ∧ z' e = y e • x e.2

end ShortestGCS.MICP


