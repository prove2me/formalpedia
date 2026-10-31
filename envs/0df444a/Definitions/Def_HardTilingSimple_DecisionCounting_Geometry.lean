-- Prove2me | Definitions.Def_HardTilingSimple_DecisionCounting_Geometry
-- name    : HardTilingSimple_DecisionCounting_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:30:50.596048+00:00
-- url     : https://prove2.me/theorems/ee1c2515-9882-4ce0-8efb-65f3fe679b80
-- title:
--   Finite square-lattice regions and rotated placements
-- statement:
--   A cell is an integer coordinate pair, representing one unit square. A region is any finite set of cells. For any finite shape, a placement is the set of cells obtained by one of the four quarter-turn rotations and an arbitrary integer translation. There are no connectivity, positivity, diameter or bounding-box restrictions. Shared edges are allowed; overlap means sharing a cell.
--
--   This is the general geometric layer, independent of the choice of tile set. Rotations act on cell indices about the origin; translating the result gives exactly the same collection of cell footprints as rotating the unit squares about a suitable centre.
-- source:
--   Moore and Robson, Hard Tiling Problems with Simple Tiles, Discrete & Computational Geometry 26, 573–590 (2001), published DOI https://doi.org/10.1007/s00454-001-0047-6, §1, p. 573 (PDF 1), and §2, p. 574 (PDF 2), standing tiling setting.

import Mathlib

namespace HardTilingSimple.DecisionCounting

abbrev Cell := ℤ × ℤ
abbrev Region := Finset Cell

/-- A quarter-turn acts on cell indices; translation absorbs the choice of centre. -/
def rotate (k : Fin 4) (p : Cell) : Cell :=
  match k.val with
  | 0 => p
  | 1 => (-p.2, p.1)
  | 2 => (-p.1, -p.2)
  | _ => (p.2, -p.1)

/-- The geometric footprint of a rotated and translated finite shape. -/
def placement (S : Region) (k : Fin 4) (t : Cell) : Region :=
  S.image (fun p => let q := rotate k p; (t.1 + q.1, t.2 + q.2))

end HardTilingSimple.DecisionCounting


