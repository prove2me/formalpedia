-- Prove2me | Definitions.Def_HardTilingSimple_DecisionCounting_Tiles
-- name    : HardTilingSimple_DecisionCounting_Tiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:32:17.001961+00:00
-- url     : https://prove2.me/theorems/93576c8f-3942-4da5-9bf7-a2a23653855e
-- title:
--   The fixed right-tromino and square-tetromino tiling problem
-- statement:
--   The right tromino has cells {(0,0),(1,0),(0,1)}, and the square tetromino has cells {(0,0),(1,0),(0,1),(1,1)}. The fixed tile set consists of exactly these two shapes. For any finite region R, its tilings and tiling count are the general unordered geometric tilings and finite count specialized to this set, with all quarter-turn rotations and integer translations permitted.
--
--   There are unlimited copies of each shape. No inventory, movement, insertion order or gravity rule is imposed. The L-shaped tromino has all four orientations, and the square's different rotational descriptions are identified as the same footprint. The empty region has count one; a single cell has count zero; the base right tromino and the 2-by-2 square each have count one.
-- source:
--   Moore and Robson, Hard Tiling Problems with Simple Tiles, Discrete & Computational Geometry 26, 573–590 (2001), published DOI https://doi.org/10.1007/s00454-001-0047-6, §2, p. 574 (PDF 2), Figure 1 and the sentence specifying rotations.

import Definitions.Def_HardTilingSimple_DecisionCounting_Tilings

namespace HardTilingSimple.DecisionCounting

/-- The right tromino of Figure 1. -/
def rightTromino : Region := {(0, 0), (1, 0), (0, 1)}

/-- The square tetromino of Figure 1. -/
def squareTetromino : Region := {(0, 0), (1, 0), (0, 1), (1, 1)}

def tileSet : Finset Region := {rightTromino, squareTetromino}

def tilings (R : Region) : Finset (Finset Region) := geometricTilings tileSet R

def tilingCount (R : Region) : ℕ := geometricCount tileSet R

end HardTilingSimple.DecisionCounting


