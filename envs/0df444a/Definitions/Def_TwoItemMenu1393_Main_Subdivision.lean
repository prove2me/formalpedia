-- Prove2me | Definitions.Def_TwoItemMenu1393_Main_Subdivision
-- name    : TwoItemMenu1393_Main_Subdivision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:41.22217+00:00
-- url     : https://prove2.me/theorems/de95e91f-f91e-4604-add9-88ca9b084ce7
-- title:
--   Full planar cells, geometric edges and finite vertices
-- statement:
--   For a finite set $S$ of affine allocation-price pairs, define
--   $$P_e=\{v\in\mathbb R^2:A_e(v)\ge A_f(v)\text{ for all }f\in S\},\qquad A_{(q,p)}(v)=q\cdot v-p.$$
--   A full cell has nonempty interior. Edges are nondegenerate one-dimensional intersections of distinct full cells, counted once as geometric sets; bounded segments, rays and full lines are included. A finite vertex is a point where active full-cell gradients span two independent directions. A full-cell sample chooses an adjacent full-cell gradient, including at a tie. These definitions use the whole plane and contain no bound on the number of edges or vertices. The same construction applies to arbitrary finite affine maxima, without allocation or price restrictions, in Lemma 4.3.
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), B.4, p. 19; §4.3, pp. 12–13; D.5, pp. 33–35. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf

import Definitions.Def_TwoItemMenu1393_Main_Fields
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped Topology

namespace TwoItemMenu1393.Main

/-! Chan–Guo–Thach, submission #1393 (October 2026), B.4 p. 19,
§4.3 pp. 12–13 and D.5 pp. 33–35. No clipping to the type square. -/
def det (x y : Vec) : ℝ := x 0 * y 1 - x 1 * y 0
def affineCell (S : Finset Entry) (e : Entry) : Set Vec :=
  {v | ∀ f ∈ S, entryUtility f v ≤ entryUtility e v}
def FullCell (S : Finset Entry) (e : Entry) : Prop :=
  e ∈ S ∧ (interior (affineCell S e)).Nonempty
def OneDimensional (C : Set Vec) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, y ≠ x) ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, det (y-x) (z-x) = 0

/-- Nondegenerate one-dimensional intersections of distinct full cells. These are
their geometric faces, including unbounded rays and full lines; identical sets are
counted once. A split occurs where another full cell meets the edge. -/
def subdivisionEdges (S : Finset Entry) : Finset (Set Vec) := by
  classical
  let C := S.filter (FullCell S)
  exact ((C.product C).filter (fun ef => ef.1 ≠ ef.2 ∧
    OneDimensional (affineCell S ef.1 ∩ affineCell S ef.2))).image
      (fun ef => affineCell S ef.1 ∩ affineCell S ef.2)

/-- A finite meeting point has three active full-cell gradients spanning two
directions. Collinear active gradients give an edge, not a vertex. -/
def subdivisionVertices (S : Finset Entry) : Set Vec :=
  {v | ∃ e ∈ S, ∃ f ∈ S, ∃ k ∈ S,
    FullCell S e ∧ FullCell S f ∧ FullCell S k ∧
    v ∈ affineCell S e ∧ v ∈ affineCell S f ∧ v ∈ affineCell S k ∧
    det (f.1-e.1) (k.1-e.1) ≠ 0}
def FullCellSample (S : Finset Entry) (T G : Triangle) : Prop :=
  ∀ i, ∃ e ∈ S, FullCell S e ∧ T i ∈ affineCell S e ∧ G i = e.1

end TwoItemMenu1393.Main


