-- Prove2me | Definitions.Def_GeoQAC_Pos
-- name    : GeoQAC_Pos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:56.769637+00:00
-- url     : https://prove2.me/theorems/6caec53d-970c-4159-9216-7146b2ab766c
-- title:
--   The qubit grid $[w]\times[h]$, connected regions, column projections, boundary
-- statement:
--   The qubits of a $[w,h]$-2D-QAC circuit fill a rectangle $\Lambda=[w]\times[h]$ of $w$ rows and $h$ columns. A position is a pair $(r,c)$ with the row index $r$ first and the column index $c$ second; $w$ is the **width** and $h$ the **length**.
--
--   Two positions are **adjacent** when they differ by one in exactly one coordinate. A **connected region** is a nonempty set $R\subseteq\Lambda$ whose induced nearest-neighbour graph is connected. The **column projection** of a region is
--   $$
--   I(R)=\{c\in[h] : (r,c)\in R \text{ for some } r\in[w]\}.
--   $$
--   A **boundary position** lies in the first or last row or the first or last column, and a **boundary column** is the first (left) or the last (right) column.
--
--   These notions carry the geometry of the paper: the gate supports of a 2D-QAC circuit, the regions in the definition of the local measurement variance $\Gamma$, and the placement clauses of the conversions.
--
--   **Formalization Note** Positions are `Fin w × Fin h`, indexed from $0$. Adjacency is the box product of two path graphs; a boundary column is column $0$ or column $h-1$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.3, p.11; §3.2, p.14; Proposition 2.7, p.12

import Mathlib

namespace GeoQAC

/-!
# The qubit grid `[w] × [h]`, connected regions and column projections

Dong, Ou, Yao, *On the Computational Power of Geometrically Local QAC circuits*, arXiv:2604.07178
(version of 2026-11-03), Definition 2.3, p.11, and §3.2, p.14.

**Formalization Note.** A position is `(r, c) : Fin w × Fin h`, the row first (p.14), so `w` is the
number of rows (the *width*) and `h` the number of columns (the *length*). Rows and columns are
indexed from `0`, not from `1`. Two positions are adjacent when they differ by one in exactly one
coordinate: this is the box product of two path graphs.
-/

/-- The qubit positions `Λ = [w] × [h]` of a `[w, h]`-2D-QAC layout: row index first, column index
second (arXiv:2604.07178, version of 2026-11-03, Definition 2.3, p.11; §3.2, p.14). -/
abbrev Pos (w h : ℕ) : Type := Fin w × Fin h

/-- The two-dimensional nearest-neighbour graph on `Λ`: positions are adjacent when they differ by
one in exactly one coordinate (p.14). -/
def gridGraph (w h : ℕ) : SimpleGraph (Pos w h) :=
  (SimpleGraph.pathGraph w).boxProd (SimpleGraph.pathGraph h)

/-- A connected region (p.14): a nonempty set `R ⊆ Λ` whose induced nearest-neighbour graph is
connected. -/
def IsConnectedRegion {w h : ℕ} (R : Finset (Pos w h)) : Prop :=
  R.Nonempty ∧ ((gridGraph w h).induce (R : Set (Pos w h))).Connected

/-- The column projection `I(R) = {c ∈ [h] : ∃ r, (r, c) ∈ R}` (p.14). -/
def colProj {w h : ℕ} (R : Finset (Pos w h)) : Finset (Fin h) :=
  R.image Prod.snd

/-- A boundary position of the rectangle: in the first or last row, or in the first or last
column (Proposition 2.7, p.12). -/
def IsBoundary {w h : ℕ} (v : Pos w h) : Prop :=
  v.1.val = 0 ∨ v.1.val + 1 = w ∨ v.2.val = 0 ∨ v.2.val + 1 = h

/-- A boundary column of the rectangle: the first (left) or the last (right) column
(Proposition 2.7 and Lemma 2.8, p.12). -/
def IsBoundaryCol {h : ℕ} (c : Fin h) : Prop :=
  c.val = 0 ∨ c.val + 1 = h

end GeoQAC


