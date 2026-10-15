-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
-- name    : OAI_Geometry_DoublingHilbert_SelectedSheets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:12:15.223443+00:00
-- url     : https://prove2.me/theorems/c3bba862-df0e-42a9-9271-06c552270d7e
-- title:
--   Period grids at level $j$ and derivative columns of strip-selected added sheets
-- statement:
--   Fix the strip set $S\subseteq\ell^2$ with scales $r_j=1000^{-(j+1)}$, color counts $N_j\ge1$ and width factors $W_j\ge1$. Let $E$ be a finite-dimensional real normed space, $f:S\to E$ a $D$-Lipschitz map, and $\widetilde F_w$ the global (Lipschitz-extended) sheet of $f$ for the tuple $w$.
--
--   1. **Strip widths and periods.** The vertical strip width at level $j$ is $W_jr_j$; the horizontal and vertical periods are
--   $$
--   X_j=N_jW_jr_j,\qquad Y_j=N_jr_j ,
--   $$
--   all positive. A rectangle $[aX_j,(a+1)X_j]\times[bY_j,(b+1)Y_j]$ with $a,b\in\mathbb{Z}$ is a level-$j$ period block: it contains exactly one horizontal strip and one vertical strip of each color.
--
--   2. **Period grids.** A level-$j$ period grid is given by integers $a_x,a_y$ and positive integers $n_x,n_y$. Its rectangle is $[a_xX_j,(a_x+n_x)X_j]\times[a_yY_j,(a_y+n_y)Y_j]$, and for $0\le a<n_x$, $0\le b<n_y$ its block $(a,b)$ is $[(a_x+a)X_j,(a_x+a+1)X_j]\times[(a_y+b)Y_j,(a_y+b+1)Y_j]$.
--
--   3. **Residue color.** For $N>0$ and $q\in\mathbb{Z}$, the residue color is $q\bmod N\in\{0,\dots,N-1\}$.
--
--   4. **Added sheets.** For a level $j$ and a color $i\in\{0,\dots,N_j-1\}$, the added sheet $\widetilde F^{(i)}=\widetilde F_{w[j\mapsto i+1]}$ is the global sheet of the tuple obtained from $w$ by setting its level-$j$ entry to $i+1$, that is, by adding the displacement of color $i$ at level $j$.
--
--   5. **Strip-selected columns.** For a direction $v\in\mathbb{R}^2$, the horizontally selected and vertically selected columns are
--   $$
--   H_v(p)=D\widetilde F^{(\kappa_H(p))}(p)\,v,\qquad V_v(p)=D\widetilde F^{(\kappa_V(p))}(p)\,v,
--   $$
--   where $\kappa_H(p)=\lfloor p_2/r_j\rfloor\bmod N_j$ is the color of the horizontal strip containing $p$ and $\kappa_V(p)=\lfloor p_1/(W_jr_j)\rfloor\bmod N_j$ is the color of the vertical strip containing $p$.
--
--   On each horizontal (respectively vertical) strip of color $i$ the selected field is the derivative of the single added sheet $\widetilde F^{(i)}$, whose values stay within distance proportional to $r_j$ of those of $\widetilde F_w$ wherever the displacement is allowed. Comparing $H_{(1,0)}$ and $V_{(0,1)}$ with the derivatives of $\widetilde F_w$ is the core of the anisotropic energy estimates.
--
--   **Formalization Note** The definitions are `stripWidth`, `xPeriod`, `yPeriod` (with positivity lemmas), the structure `PeriodGrid j` with `PeriodGrid.rectangle` and `PeriodGrid.block`, `residueColor` (valued in `Fin N`), `addedSheet` (using `Finsupp.update`), `horizontalColumn` and `verticalColumn`; derivatives are `fderiv`, equal to $0$ where the map is not differentiable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean by skeleton subtraction
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

namespace OAI

/-! Periodic selections of sheets and stripewise derivative means. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace IsBoundedField
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

end IsBoundedField

section StripeMeans
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

end StripeMeans
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

def stripWidth (j : ℕ) : ℝ := (widthFactor j : ℝ) * scale j

theorem stripWidth_pos (j : ℕ) : 0 < stripWidth j :=
  mul_pos (by exact_mod_cast widthFactor_pos j) (scale_pos j)

def xPeriod (j : ℕ) : ℝ := (colors j : ℝ) * stripWidth j

def yPeriod (j : ℕ) : ℝ := (colors j : ℝ) * scale j

theorem xPeriod_pos (j : ℕ) : 0 < xPeriod j :=
  mul_pos (by exact_mod_cast colors_pos j) (stripWidth_pos j)

theorem yPeriod_pos (j : ℕ) : 0 < yPeriod j :=
  mul_pos (by exact_mod_cast colors_pos j) (scale_pos j)

/-- A finite rectangle of complete level-j period blocks. -/
structure PeriodGrid (j : ℕ) where
  ax : ℤ
  ay : ℤ
  nx : ℕ
  ny : ℕ
  nx_pos : 0 < nx
  ny_pos : 0 < ny

namespace PeriodGrid
variable {j : ℕ}

def rectangle (G : PeriodGrid j) : Rectangle :=
  ⟨Segment.grid (G.ax * xPeriod j) (xPeriod j) G.nx (xPeriod_pos j) G.nx_pos,
   Segment.grid (G.ay * yPeriod j) (yPeriod j) G.ny (yPeriod_pos j) G.ny_pos⟩

def block (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) : Rectangle :=
  ⟨Segment.cell (G.ax * xPeriod j) (xPeriod j) (xPeriod_pos j) a,
   Segment.cell (G.ay * yPeriod j) (yPeriod j) (yPeriod_pos j) b⟩

end PeriodGrid

def residueColor (N : ℕ) (hN : 0 < N) (q : ℤ) : Fin N :=
  ⟨(q % (N : ℤ)).toNat, by
    exact (Int.toNat_lt' hN).mpr
      (Int.emod_lt_of_pos q (by exact_mod_cast hN))⟩

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace Rectangle

end Rectangle

section SelectedSheets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def addedSheet {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (i : Fin (colors j)) : Base → E :=
  globalSheet hf (w.update j ((i : ℕ) + 1))

def horizontalColumn {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (v : Base) (p : Base) : E :=
  column (addedSheet hf w j (stripColor (colors j) (colors_pos j) (scale j) p.2)) v p

def verticalColumn {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (v : Base) (p : Base) : E :=
  column (addedSheet hf w j (stripColor (colors j) (colors_pos j) (stripWidth j) p.1)) v p

end SelectedSheets
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section VerticalStripeMean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end VerticalStripeMean
end
end DoublingHilbert

end OAI


