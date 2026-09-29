-- Prove2me | Definitions.Def_ArcCrossingEarlierPrefix
-- name    : ArcCrossingEarlierPrefix
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:37:06.111044+00:00
-- url     : https://prove2.me/theorems/b5d396e6-5a86-499d-b71f-4a6ebe280726
-- title:
--   Earlier prefix of a polygonal arc
-- statement:
--   The union of all polygonal-arc segments strictly preceding a specified segment index. This records the part of the arc before the first crossing segment.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingEarlierPrefix.lean

import Mathlib.Tactic
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingEarlierPrefix]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingEarlierPrefix.lean#L1-L14
def ArcCrossingEarlierPrefix (δ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < δ.vertices.length) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i : {i : ℕ // i < j},
    segment ℝ
      (δ.vertices[i.1]'(by omega))
      (δ.vertices[i.1 + 1]'(by omega))


