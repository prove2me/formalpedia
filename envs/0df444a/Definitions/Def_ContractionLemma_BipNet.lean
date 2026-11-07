-- Prove2me | Definitions.Def_ContractionLemma_BipNet
-- name    : ContractionLemma_BipNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:46.381376+00:00
-- url     : https://prove2.me/theorems/75c0bb08-e043-41a3-b46e-821164015e8f
-- title:
--   Bipartite network: row and column vertices
-- statement:
--   A **bipartite network** has row vertices $U$ and column vertices $W$; every edge $e$ joins its row vertex to its column vertex. A row vertex $u$ carries a table reading the bits of $\{e:\mathrm{row}(e)=u\}$, and a column vertex $w$ one reading the bits of $\{e:\mathrm{col}(e)=w\}$. Its contraction is that of the underlying network on the vertices $U\sqcup W$.
--
--   All steps of the proof of the contraction lemma work on bipartite networks.
--
--   **Formalization Note** Bipartiteness holds by construction, since no edge can join two vertices of the same side.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.3.1–A.3.2, pp.51–52

import Mathlib
import Definitions.Def_ContractionLemma_Net

set_option autoImplicit false

namespace ContractionLemma

/-- **Bipartite network** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), App. A.3.1–A.3.2, pp.51–52.

A bipartite network has row vertices `U` and column vertices `W`; every edge `e` joins its row
vertex `rowOf e` to its column vertex `colOf e`. The row vertex `u` carries a table reading
the bits of its edges `{e | rowOf e = u}`, the column vertex `w` one reading the bits of
`{e | colOf e = w}`.

**Formalization Note.** A bipartite network is bipartite by construction (no edge joins two
row vertices or two column vertices); `toNet` is the underlying network, on the vertex type
`U ⊕ W`. -/
structure BipNet (U W E R : Type*) where
  /-- the row endpoint of each edge -/
  rowOf : E → U
  /-- the column endpoint of each edge -/
  colOf : E → W
  /-- the table of a row vertex -/
  rowTable : (u : U) → ({e : E // rowOf e = u} → Bool) → R
  /-- the table of a column vertex -/
  colTable : (w : W) → ({e : E // colOf e = w} → Bool) → R

namespace BipNet

variable {U W E R : Type*}

/-- The underlying network of a bipartite network, on the vertices `U ⊕ W`. -/
def toNet (G : BipNet U W E R) : Net (U ⊕ W) E R where
  ends e := (Sum.inl (G.rowOf e), Sum.inr (G.colOf e))
  loopless _ := Sum.inl_ne_inr
  table
    | Sum.inl u => fun z => G.rowTable u (fun e => z ⟨e.1, Or.inl (congrArg Sum.inl e.2)⟩)
    | Sum.inr w => fun z => G.colTable w (fun e => z ⟨e.1, Or.inr (congrArg Sum.inr e.2)⟩)

/-- The contraction of a bipartite network: that of its underlying network (p.52). -/
def Z [Fintype U] [Fintype W] [Fintype E] [DecidableEq E] [CommSemiring R]
    (G : BipNet U W E R) : R :=
  G.toNet.Z

/-- The degree of a row vertex. -/
def rowDeg [Fintype E] [DecidableEq U] (G : BipNet U W E R) (u : U) : ℕ :=
  (Finset.univ.filter fun e => G.rowOf e = u).card

/-- The degree of a column vertex. -/
def colDeg [Fintype E] [DecidableEq W] (G : BipNet U W E R) (w : W) : ℕ :=
  (Finset.univ.filter fun e => G.colOf e = w).card

end BipNet

end ContractionLemma


