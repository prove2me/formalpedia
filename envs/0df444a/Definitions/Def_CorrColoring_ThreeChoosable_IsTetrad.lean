-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_IsTetrad
-- name    : CorrColoring_ThreeChoosable_IsTetrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:03:08.934421+00:00
-- url     : https://prove2.me/theorems/39a0fa8b-5e85-4e5f-8b9f-642dc3889d30
-- title:
--   Tetrads in plane graphs
-- statement:
--   Let $G$ be a plane graph. A **tetrad** is a path $v_1 v_2 v_3 v_4$ of four distinct vertices, each of degree three, such that
--
--   1. the path is contained in the boundary of a face $f$ of $G$: the segments of the edges $v_1v_2$, $v_2v_3$, $v_3v_4$ lie in $\partial f$;
--   2. both $v_1 v_2$ and $v_3 v_4$ are edges of triangles, i.e. there are vertices $x_1, x_4$ with $x_1$ adjacent to $v_1$ and $v_2$, and $x_4$ adjacent to $v_3$ and $v_4$.
--
--   The tetrad is the main reducible configuration of the proof of Theorem 8 of Dvořák and Postle (Lemma 12).
--
--   **Formalization Note** The degree of $v$ is the cardinality of its neighbour set; "contained in the boundary of a face" is encoded by requiring each edge segment of the path to lie in the topological frontier of one face of the drawing.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 16, definition of a tetrad (Figure 2)

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_StraightLineDrawing

namespace CorrColoring.ThreeChoosable

/-- A tetrad (Dvořák–Postle, p. 16): a path `v₁v₂v₃v₄` of four distinct vertices of degree
three whose three edges are contained in the boundary of one face of the drawing, such that
both `v₁v₂` and `v₃v₄` are edges of triangles. -/
def IsTetrad {V : Type*} {G : SimpleGraph V} (D : StraightLineDrawing G)
    (v₁ v₂ v₃ v₄ : V) : Prop :=
  [v₁, v₂, v₃, v₄].Nodup ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v₄ ∧
    (∀ v ∈ [v₁, v₂, v₃, v₄], (G.neighborSet v).ncard = 3) ∧
    (∃ f, D.IsFace f ∧ segment ℝ (D.pos v₁) (D.pos v₂) ⊆ frontier f ∧
      segment ℝ (D.pos v₂) (D.pos v₃) ⊆ frontier f ∧
      segment ℝ (D.pos v₃) (D.pos v₄) ⊆ frontier f) ∧
    (∃ x, G.Adj v₁ x ∧ G.Adj v₂ x) ∧ (∃ x, G.Adj v₃ x ∧ G.Adj v₄ x)

end CorrColoring.ThreeChoosable


