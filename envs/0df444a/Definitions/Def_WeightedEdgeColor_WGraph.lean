-- Prove2me | Definitions.Def_WeightedEdgeColor_WGraph
-- name    : WeightedEdgeColor_WGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:25.542442+00:00
-- url     : https://prove2.me/theorems/d9006843-bb6f-4b39-a4a5-4494bfde674d
-- title:
--   Edge-weighted loopless multigraph $G=(V,E)$ with $w:E\to(0,1]$, incident edges $E(v)$ and weighted degree $W_G(v)$
-- statement:
--   A finite **edge-weighted graph** $G=(V,E)$, possibly with parallel edges but without loops, is given by a finite vertex set $V$, a finite edge set $E$, an endpoint map assigning to each edge $e$ an unordered pair of two distinct vertices, and a weight function
--   $$
--   w:E\to(0,1].
--   $$
--   Parallel edges are distinct elements of $E$ with the same endpoints and are counted separately. For a vertex $v$, $E(v)$ is the set of edges incident with $v$, and the **weighted degree** is
--   $$
--   W_G(v)=\sum_{e\ni v} w_e .
--   $$
--   The graph is **simple** if no two edges have the same pair of endpoints.
--
--   This is the common carrier of every statement in the mission: simple graphs (Theorems 1.1 and 3.1) and multigraphs (Lemma A.1) are the same object with or without the simplicity condition.
--
--   **Formalization Note** The endpoint map takes values in unordered pairs `Sym2 V`; looplessness says no edge has equal endpoints. Simplicity is injectivity of the endpoint map. Finiteness of $V$ and $E$ is imposed where the carrier is used.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), §1, p.1; Appendix A, p.24

import Mathlib

set_option autoImplicit false

namespace WeightedEdgeColor

/-- A finite loopless edge-weighted multigraph `G = (V, E)` with weights `w : E → (0, 1]`.

Source: R. Gajjala, A. Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin
Packing*, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped), §1, p.1;
Appendix A (standing conventions), p.24.

**Formalization Note.** Edges are the elements of a type `E`, each with an unordered pair of
endpoints `ends e : Sym2 V`; parallel edges are distinct elements of `E` with equal `ends`, so
they are counted separately, as on p.24. Loops are excluded by `loopless`. Finiteness of `V`
and `E` is imposed by `Fintype` instances at the use sites. -/
structure WGraph (V E : Type) where
  /-- The two endpoints of an edge. -/
  ends : E → Sym2 V
  /-- No edge is a loop. -/
  loopless : ∀ e, ¬ (ends e).IsDiag
  /-- The weight `w_e`. -/
  w : E → ℝ
  w_pos : ∀ e, 0 < w e
  w_le_one : ∀ e, w e ≤ 1

namespace WGraph

variable {V E : Type}

/-- `G` is simple: no two edges have the same pair of endpoints (no parallel edges). -/
def IsSimple (G : WGraph V E) : Prop := Function.Injective G.ends

variable [Fintype E] [DecidableEq V] (G : WGraph V E)

/-- `E(v)`, the set of edges incident with the vertex `v`. -/
def inc (v : V) : Finset E := Finset.univ.filter (fun e => v ∈ G.ends e)

/-- The weighted degree `W_G(v) = ∑_{e ∋ v} w_e`. -/
noncomputable def W (v : V) : ℝ := ∑ e ∈ G.inc v, G.w e

end WGraph

end WeightedEdgeColor


