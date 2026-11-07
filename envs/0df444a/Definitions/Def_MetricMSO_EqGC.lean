-- Prove2me | Definitions.Def_MetricMSO_EqGC
-- name    : MetricMSO_EqGC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:19.71399+00:00
-- url     : https://prove2.me/theorems/a69b79bb-3ed8-48dc-bf37-954baa0a7b0b
-- title:
--   Geodesic cycle sets and the meaning of $\mathsf{EqGC}(C,x,y,u,v)$
-- statement:
--   A vertex set $C$ **induces a cycle** if $G[C]$ is a cycle of length at least $3$. It induces a **geodesic** (or isometric) cycle if moreover $d_{G[C]}(x,y)=d_G(x,y)$ for all $x,y\in C$. The guarded equidistance atom $\mathsf{EqGC}(C,x,y,u,v)$ says that $G[C]$ is a geodesic cycle, that $x,y,u,v\in C$, and that $d_G(x,y)=d_G(u,v)$.
--
--   The atom is false whenever $G[C]$ is not a geodesic cycle, in particular on forests.
--
--   **Formalization Note** All four vertices lie on one cycle, so `G.dist` is the true distance on them.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.1, pp.12–13 (PDF 14–15); Definition 2.11, p.18 (PDF 20)

import Mathlib

namespace MetricMSO

/-- **`G[C]` is a cycle** (Chakraborty, Ordyniak, Siebertz, arXiv:2610.41974, sha256 prefix
ad3c5863): there is a cycle `c` of `G` (a closed walk of length at least three
without repeated vertices) whose vertex set is `C`, and every edge of `G` between two vertices of
`C` is an edge of `c`.

§2.1, p.12 (PDF 14): a walk "is a cycle if ℓ ≥ 3, vℓ = v0, and the vertices v0, . . . , vℓ−1 are
pairwise distinct"; §4.1, p.25 (PDF 27): "a vertex set C such that G[C] is a cycle". -/
def IsCycleSet {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.support.toFinset = C ∧
    ∀ u ∈ C, ∀ w ∈ C, G.Adj u w → s(u, w) ∈ c.edges

/-- **`G[C]` is a geodesic (isometric) cycle.**

§2.1, p.13 (PDF 15): "We call a cycle C geodesic, or isometric, if dC(x, y) = dG(x, y) for all
x, y ∈ V(C), where dC denotes distance measured along the cycle." Definition 2.11, p.18 (PDF 20):
"G[C] is a geodesic cycle".

`G[C]` is a cycle, and for all `x, y ∈ C` the distance in the induced subgraph `G[C]` (which is the
cycle) equals the distance in `G`. -/
def IsGeodesicCycleSet {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V) : Prop :=
  IsCycleSet G C ∧
    ∀ x (hx : x ∈ C) y (hy : y ∈ C),
      (G.induce (C : Set V)).dist ⟨x, by simpa using hx⟩ ⟨y, by simpa using hy⟩ = G.dist x y

/-- **The guarded equidistance atom EqGC(C, x, y, u, v)**, Definition 2.11, p.18 (PDF 20): "G[C] is
a geodesic cycle, that all four vertices belong to C, and that dG(x, y) = dG(u, v)."

**Formalization Note** The four vertices lie on the cycle `G[C]`, so they are pairwise reachable
and Mathlib's `G.dist` is the true distance. The atom is false whenever `G[C]` is not a geodesic
cycle, in particular on forests (p.18). -/
def EqGC {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V) (x y u v : V) : Prop :=
  IsGeodesicCycleSet G C ∧ x ∈ C ∧ y ∈ C ∧ u ∈ C ∧ v ∈ C ∧ G.dist x y = G.dist u v

end MetricMSO


