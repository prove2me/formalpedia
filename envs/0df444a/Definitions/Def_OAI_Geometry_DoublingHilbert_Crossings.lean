-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
-- name    : OAI_Geometry_DoublingHilbert_Crossings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:15:23.519827+00:00
-- url     : https://prove2.me/theorems/688cd1d0-497a-4d61-be18-cd2012b8ab46
-- title:
--   Period color blocks containing one row and one column of each color
-- statement:
--   Fix a level $j$ of the strip set, with scale $r_j$, $N_j$ colors, vertical strip width $W_jr_j$, and periods $X_j=N_jW_jr_j$ and $Y_j=N_jr_j$.
--
--   1. **Color block.** A level-$j$ color block is given by integers $a_x,a_y$; its rectangle is the full period block
--   $$
--   P=[a_xX_j,\,a_xX_j+N_jW_jr_j]\times[a_yY_j,\,a_yY_j+N_jr_j].
--   $$
--
--   2. **Columns and rows.** For a color $i\in\{0,\dots,N_j-1\}$, the $i$-th column of the block is given by the $x$-interval $[a_xX_j+iW_jr_j,\ a_xX_j+(i+1)W_jr_j]$ and the $i$-th row by the $y$-interval $[a_yY_j+ir_j,\ a_yY_j+(i+1)r_j]$. The column (respectively row) spans the vertical strip of index $a_xN_j+i$ (respectively the horizontal strip of index $a_yN_j+i$), whose color is $i$.
--
--   3. **Blocks of a period grid.** For a level-$j$ period grid with origin $(a_x,a_y)$ and $0\le a<n_x$, $0\le b<n_y$, the $(a,b)$ color block is the color block with integer origins $(a_x+a,\,a_y+b)$.
--
--   Each color block therefore contains exactly one row and one column of every color. At the crossing of the row of color $i$ with the column of color $m\neq i$, both displacements are allowed, which is how small energy on a single block is converted into many well-separated vectors in the target space.
--
--   **Formalization Note** The structure is `ColorBlock j` with `ColorBlock.rectangle`, `ColorBlock.column` and `ColorBlock.row` (segments built with `Segment.grid` and `Segment.cell`), and `PeriodGrid.colorBlock`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Crossings.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Crossings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

open Metric

/-! Selected period crossings and finite-dimensional obstruction. -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

/-- One full period, recording its integral horizontal and vertical origins. -/
structure ColorBlock (j : ℕ) where
  ax : ℤ
  ay : ℤ

namespace ColorBlock
variable {j : ℕ}

def rectangle (B : ColorBlock j) : Rectangle :=
  ⟨Segment.grid (B.ax * xPeriod j) (stripWidth j) (colors j)
      (stripWidth_pos j) (colors_pos j),
   Segment.grid (B.ay * yPeriod j) (scale j) (colors j)
      (scale_pos j) (colors_pos j)⟩

def column (B : ColorBlock j) (i : Fin (colors j)) : Segment :=
  Segment.cell (B.ax * xPeriod j) (stripWidth j) (stripWidth_pos j) i

def row (B : ColorBlock j) (i : Fin (colors j)) : Segment :=
  Segment.cell (B.ay * yPeriod j) (scale j) (scale_pos j) i

end ColorBlock

namespace PeriodGrid
variable {j : ℕ}

def colorBlock (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) : ColorBlock j :=
  ⟨G.ax + a, G.ay + b⟩

end PeriodGrid

section LineSelection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end LineSelection
end DoublingHilbert

namespace DoublingHilbert
section BlockSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end BlockSelection
end DoublingHilbert

namespace DoublingHilbert

section CrossingPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end CrossingPacking
end DoublingHilbert

end

end OAI


