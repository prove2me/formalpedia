-- Prove2me | Definitions.Def_RevRedSAT_Supplement_IsEdgeListing
-- name    : RevRedSAT_Supplement_IsEdgeListing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:54:23.547566+00:00
-- url     : https://prove2.me/theorems/74fe4b99-f4ec-4f28-8159-457e9a289400
-- title:
--   Listings of the edge set of a graph
-- statement:
--   For a finite simple graph $G$ on the vertices $0,\dots,n-1$, a list $L$ of ordered pairs is a **listing of the edges** of $G$ if every listed pair is an edge, every edge occurs, and no edge occurs twice (in either orientation). Every order and every orientation gives a listing.
--
--   This is the edge part of the published Vertex Cover codes `RevRedSAT.IsVCCode`; it is used here in the codes of the coloring and Steiner Tree instances.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27 (explicit binary encodings); App. C, p.92 (graph conventions)

import Mathlib

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **A listing of the edges of a graph.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27 ("the explicit binary encodings of an instance"); App. C, p.92 ("graphs are finite,
simple, undirected, and unweighted").

`L` lists every edge of `G` exactly once, each as an ordered pair in either orientation, in any
order. This is the edge part of the published `RevRedSAT.IsVCCode`, used by the codes of the
coloring and Steiner Tree instances below. -/
def IsEdgeListing {n : ℕ} (G : SimpleGraph (Fin n)) (L : List (Fin n × Fin n)) : Prop :=
  (L.map fun e => Sym2.mk e).Nodup ∧ (∀ e ∈ L, G.Adj e.1 e.2) ∧
    (∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L)

end RevRedSAT.Supplement


