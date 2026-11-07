-- Prove2me | Definitions.Def_PolygonPack_IsRectPacking
-- name    : PolygonPack_IsRectPacking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:15.68267+00:00
-- url     : https://prove2.me/theorems/48358931-51cd-4151-9cc6-ebb82e790d6a
-- title:
--   Rectangle packing with quarter turns
-- statement:
--   A family of rectangles of widths $r_i$ and heights $z_i$ is **packed in the unit square by translations and quarter turns** if each rectangle, turned a quarter or not, is given a lower left corner so that it lies in $[0,1]^2$ and interiors are pairwise disjoint.
--
--   `encRects` and `encRectOut` are the binary encoders of the rational version.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem D.2, p.42

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PolygonPack_encInstance
open OnlineCRS.Combine

namespace PolygonPack

/-- **Rectangle packing with quarter turns.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem D.2, p.42: "can be packed in a unit square by translations
and quarter turns".

`IsRectPacking r z rot x y`: rectangle `i` of width `r i` and height `z i`, turned a quarter if `rot i`, with lower left
corner `(x i, y i)`, lies in the unit square, and interiors are pairwise disjoint.

**Formalization Note.** Boxes are axis-parallel, so an interior is a product of open intervals. -/
def IsRectPacking {ι : Type} (r z : ι → ℝ) (rot : ι → Bool) (x y : ι → ℝ) : Prop :=
  let w : ι → ℝ := fun i => if rot i then z i else r i
  let l : ι → ℝ := fun i => if rot i then r i else z i
  (∀ i, 0 ≤ x i ∧ x i + w i ≤ 1 ∧ 0 ≤ y i ∧ y i + l i ≤ 1) ∧
    ∀ i j, i ≠ j →
      Disjoint (Set.Ioo (x i) (x i + w i) ×ˢ Set.Ioo (y i) (y i + l i))
        (Set.Ioo (x j) (x j + w j) ×ˢ Set.Ioo (y j) (y j + l j))

/-- Rational rectangles `(r, z)`, in a list. -/
def encRects (l : List (ℚ × ℚ)) : List Sym := encList encPt l

/-- A rectangle packing: entries `(rot, x, y)`. -/
def encRectOut (l : List (Bool × ℚ × ℚ)) : List Sym :=
  encList (fun e => [if e.1 then (1 : Sym) else (0 : Sym)] ++ [(3 : Sym)] ++ encPt e.2) l

end PolygonPack


