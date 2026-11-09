-- Prove2me | Definitions.Def_GirthBethe_Sharp_BipartiteGraph
-- name    : GirthBethe_Sharp_BipartiteGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:40.391373+00:00
-- url     : https://prove2.me/theorems/e3c59f5c-256e-4234-b5b2-75ef0e25a344
-- title:
--   §1.2, (1.2) — bipartite graphs, perfect matchings, $\mathrm{PM}(G)$ and the Bethe entropy $H_B$
-- statement:
--   A finite simple bipartite graph $G=(L\sqcup R,E)$ is given by finite vertex classes $L,R$ and an edge set $E\subseteq L\times R$; its vertex set is $V=L\sqcup R$, and $u\in L$, $w\in R$ are adjacent iff $(u,w)\in E$. No connectedness, regularity or existence of a matching is assumed. The girth of $G$ (length of a shortest cycle, $+\infty$ for a forest) is the extended girth of this simple graph.
--
--   1. A perfect matching $M$ (a set of edges covering every vertex exactly once) is recorded by the bijection $\sigma:L\to R$ sending each $u$ to its partner, with $(u,\sigma(u))\in E$ for every $u$; an edge $e=(u,w)$ lies in $M$ iff $\sigma(u)=w$.
--   2. The fractional perfect matching polytope is
--   $$\mathrm{PM}(G)=\Big\{p\in\mathbb R^{E}_{\ge0}:\ \sum_{e\ni v}p_e=1\ \text{for every }v\in V\Big\}.$$
--   3. For $p\in\mathbb R^E$ and $v\in V$, the local vector is $p_v=(p_e)_{e\ni v}$, indexed by the edges incident to $v$.
--   4. The Bethe entropy (1.2) is
--   $$H_B(p)=\sum_{e\in E}\big[-p_e\log p_e+(1-p_e)\log(1-p_e)\big].$$
--
--   These are the combinatorial objects on which the Bethe permanent and all entropy estimates are built.
--
--   **Formalization Note** $\mathrm{PM}(G)$ is the incidence-equation polytope, not by definition the convex hull of matchings. Natural logarithms with $0\log0=0$.
--
--   For any edge weights $J$, the incident sum $J_v=\sum_{e\ni v}J_e$ is also provided, as used for $J_v^\pm$ in Definition 4.1.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 2, §1.2, PM(G) and equation (1.2); §1.3 (girth); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf; incident sums: p. 11, Definition 4.1 and p. 12 preamble.

import Mathlib

open Finset

namespace GirthBethe.Sharp

/-! Finite simple bipartite graphs `G = (L ⊔ R, E)`, perfect matchings, the fractional perfect
matching polytope `PM(G)`, local marginal vectors and the Bethe entropy (§1.2, equations (1.2)
and (2.1) of Jain–Dong, STOC 2027 submission #705). The edge set is a finset `E ⊆ L × R`, so the
graph is automatically simple and bipartite; nothing about connectedness, regularity or
existence of a perfect matching is assumed. -/

variable {L R : Type*}

/-- The edges of `G`, as a type. -/
abbrev Edge (E : Finset (L × R)) := {e : L × R // e ∈ E}

/-- The underlying simple graph on the vertex set `V = L ⊕ R`: `inl u ∼ inr w` iff `(u, w) ∈ E`.
Its extended girth `SimpleGraph.egirth` is the length of a shortest cycle, `⊤` for a forest. -/
def toGraph (E : Finset (L × R)) : SimpleGraph (L ⊕ R) :=
  SimpleGraph.fromRel fun x y => ∃ u w, x = Sum.inl u ∧ y = Sum.inr w ∧ (u, w) ∈ E

/-- Incidence `v ∈ e` of a vertex `v ∈ L ⊕ R` and a pair `e = (u, w) ∈ L × R`. -/
def Inc : L ⊕ R → L × R → Prop
  | Sum.inl u, e => e.1 = u
  | Sum.inr w, e => e.2 = w

/-- The edges incident to the vertex `v`. -/
abbrev IncEdge (E : Finset (L × R)) (v : L ⊕ R) := {e : Edge E // Inc v e.1}

open scoped Classical in
noncomputable instance instFintypeIncEdge [Fintype L] [Fintype R] (E : Finset (L × R))
    (v : L ⊕ R) : Fintype (IncEdge E v) :=
  Subtype.fintype _

/-- The local vector `p_v = (p_e)_{e ∋ v}` at a vertex `v`. -/
def localVec {E : Finset (L × R)} (p : Edge E → ℝ) (v : L ⊕ R) : IncEdge E v → ℝ :=
  fun e => p e.1

/-- Sum of edge weights at a vertex, used for `J_v^± = ∑_{e ∋ v} J_e^±`
(Definition 4.1 and the arbitrary-weight preamble on p. 12). -/
noncomputable def vertexWeight [Fintype L] [Fintype R] {E : Finset (L × R)}
    (J : Edge E → ℝ) (v : L ⊕ R) : ℝ :=
  ∑ e : IncEdge E v, J e.1

/-- Perfect matchings of `G = (L ⊔ R, E)`: a perfect matching `M` (a set of edges covering every
vertex exactly once) is recorded by the bijection `σ : L ≃ R` sending `u` to its partner, with
`(u, σ u) ∈ E` for every `u`; `e = (u, w) ∈ M` iff `σ u = w`. -/
def PerfMatching (E : Finset (L × R)) := {σ : L ≃ R // ∀ u, (u, σ u) ∈ E}

noncomputable instance instFintypePerfMatching [Fintype L] [Fintype R] [DecidableEq L]
    [DecidableEq R] (E : Finset (L × R)) : Fintype (PerfMatching E) := by
  unfold PerfMatching; classical exact Subtype.fintype _

/-- The fractional perfect matching polytope
`PM(G) = {p ∈ ℝ_{≥0}^{E} : ∑_{e ∋ v} p_e = 1 for every v}` (§1.2). -/
def fracPM [Fintype L] [Fintype R] (E : Finset (L × R)) : Set (Edge E → ℝ) :=
  {p | (∀ e, 0 ≤ p e) ∧ ∀ v : L ⊕ R, ∑ e : IncEdge E v, p e.1 = 1}

/-- The Bethe entropy `H_B(p) = ∑_e [-p_e log p_e + (1 - p_e) log (1 - p_e)]` (equation (1.2)). -/
noncomputable def betheEntropy (E : Finset (L × R)) (p : Edge E → ℝ) : ℝ :=
  ∑ e : Edge E, (-(p e * Real.log (p e)) + (1 - p e) * Real.log (1 - p e))

end GirthBethe.Sharp


