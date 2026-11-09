-- Prove2me | Definitions.Def_HopRamsey_hopDist
-- name    : HopRamsey_hopDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:35.007515+00:00
-- url     : https://prove2.me/theorems/8133bd90-2025-4d31-8dc2-ded52ad3814f
-- title:
--   $h$-hop distances $d^{(h)}_G$, balls $B^{(h)}_G(v,r)$ and diameters $\mathrm{diam}^{(h)}_G(X)$
-- statement:
--   Let $G=(V,E,w)$ be an undirected graph with positive edge weights and let $h\ge 0$ be an integer. The **$h$-hop distance** between $u,v\in V$ is
--
--   $$
--   d^{(h)}_G(u,v)=\min\{w(P)\mid P \text{ a } u\text{–}v \text{ path with at most } h \text{ edges}\}\in[0,\infty],
--   $$
--
--   with $d^{(h)}_G(u,v)=\infty$ when no such path exists. The **$h$-hop ball** of radius $r$ around $v$ is $B^{(h)}_G(v,r)=\{u\mid d^{(h)}_G(u,v)\le r\}$ (empty when $r<0$), the **$h$-hop diameter** of a finite set $X$ is $\mathrm{diam}^{(h)}_G(X)=\max_{u,v\in X}d^{(h)}_G(u,v)$ (the weak diameter: distances are taken in all of $G$), and $\Phi'=\max\{d^{(h)}_G(u,v)\mid d^{(h)}_G(u,v)<\infty\}$ is the largest finite $h$-hop distance.
--
--   These are the distances against which every guarantee of the mission is measured: hop-stretch compares the tree distance with $d^{(\beta h)}_G$, and distortion with $d^{(h)}_G$.
--
--   **Formalization Note** The minimum is an infimum over walks (not only paths) with at most $h$ edges; with positive weights the two agree. Values are in $[0,\infty]$; $d^{(0)}_G(u,u)=0$, and the diameter of the empty set is $0$.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §3 "Bounded hop distances", p.13 (PDF p.15); §4.4, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- The `h`-hop distance `d^{(h)}_G(u, v) ∈ [0, ∞]`: the least weight of a `u`–`v` walk with at most
`h` edges, and `∞` when there is none.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §3,
"Bounded hop distances", p.13 (PDF p.15): "Given a path P = (v_0, v_1, ..., v_q), hop(P) = q is the
number of edges in P, also called hops. The h-hop distance between two vertices u, v is
d^{(h)}_G(u,v) = min{w(P) | P is a path between u and v with hop(P) ≤ h}. If there is no path from u
to v with at most h hops, then d^{(h)}_G(u,v) = ∞."

**Formalization Note.**
1. The infimum ranges over walks (`SimpleGraph.Walk`) of length at most `h`, not only paths. Since
   edge weights are positive, deleting a cycle from a walk lowers both its weight and its number of
   hops, so the infimum over walks equals the minimum over paths; the empty infimum is `∞`.
2. `d^{(0)}(u, u) = 0` (the empty walk) and `d^{(0)}(u, v) = ∞` for `u ≠ v`.
3. Walk weights are sums in `[0, ∞]` of `ENNReal.ofReal` of the (positive) edge weights. -/
noncomputable def hopDist {V : Type} (G : WGraph V) (h : ℕ) (u v : V) : ℝ≥0∞ :=
  ⨅ (p : G.graph.Walk u v) (_ : p.length ≤ h), G.walkWeight p

/-- Membership in the `h`-hop ball `B^{(h)}_G(v, r) = {u | d^{(h)}_G(u, v) ≤ r}` (p.13, PDF p.15),
for a real radius `r`. A negative radius gives the empty ball, as `d^{(h)}_G ≥ 0`. -/
def InHopBall {V : Type} (G : WGraph V) (h : ℕ) (v : V) (r : ℝ) (u : V) : Prop :=
  0 ≤ r ∧ hopDist G h u v ≤ ENNReal.ofReal r

/-- The `h`-hop diameter `diam^{(h)}_G(X) = max_{u,v ∈ X} d^{(h)}_G(u, v)` of a finite vertex set
(p.13, PDF p.15: "the maximum h-hop pairwise distance"), in `[0, ∞]`; it is `0` on `∅` and on
singletons. This is the weak diameter (footnote 4, p.12): distances are measured in the whole
graph `G`. -/
noncomputable def hopDiam {V : Type} (G : WGraph V) (h : ℕ) (X : Finset V) : ℝ≥0∞ :=
  X.sup fun u => X.sup fun v => hopDist G h u v

/-- `Φ′ = max{d^{(h)}_G(u, v) | u, v ∈ V and d^{(h)}_G(u, v) < ∞}`, the largest finite `h`-hop
distance of `G` (§4.4, p.25, PDF p.27). It is `0` when no two distinct vertices are at finite
`h`-hop distance. -/
noncomputable def maxFiniteHopDist {V : Type} [Fintype V] (G : WGraph V) (h : ℕ) : ℝ≥0∞ :=
  (Finset.univ : Finset V).sup fun u => (Finset.univ : Finset V).sup fun v =>
    if hopDist G h u v < ⊤ then hopDist G h u v else 0

end HopRamsey


