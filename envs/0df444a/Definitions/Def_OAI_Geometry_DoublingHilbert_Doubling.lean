-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
-- name    : OAI_Geometry_DoublingHilbert_Doubling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:17:05.541418+00:00
-- url     : https://prove2.me/theorems/191c3646-c2e7-4eac-861d-c0a505d4df9b
-- title:
--   Nearby strip indices, base cells and level labels for covering balls of the strip set
-- statement:
--   These are the finite bookkeeping sets used to cover a ball of the strip set $S\subseteq\ell^2$ by boundedly many balls of half the radius. Recall that level $j$ has scale $r_j$, $N_j$ colors and vertical strip width $W_jr_j$, and that an admissible tuple $w$ has entries $w_j\in\{0,1,\dots,N_j\}$.
--
--   1. **Nearby strip indices.** For $c\in\mathbb{R}$ and a width $h$, the set
--   $$
--   I(c,h)=\bigl\{q\in\mathbb{Z}:\ \lfloor c/h\rfloor-65\le q\le\lfloor c/h\rfloor+65\bigr\}
--   $$
--   has $131$ elements. If $h>0$, $t/64<h$ and $|x-c|<t$, then every open strip $(qh,(q+1)h)$ containing $x$ has index $q\in I(c,h)$.
--
--   2. **Base cells.** For $c\in\mathbb{R}$ and $t>0$, the cell of $x\in\mathbb{R}$ is $\lfloor 8(x-(c-t))/t\rfloor$, the index of the interval of length $t/8$, counted from $c-t$, that contains $x$. When $|x-c|<t$ this index lies in $\{0,\dots,15\}$, and two points in the same cell are less than $t/8$ apart.
--
--   3. **Nearby labels.** For a base point $c=(c_1,c_2)$ and a level $j$, the label set is
--   $$
--   \Lambda(c,j)=\{0\}\cup\bigl\{(q\bmod N_j)+1:\ q\in I(c_2,r_j)\bigr\}\cup\bigl\{(q\bmod N_j)+1:\ q\in I(c_1,W_jr_j)\bigr\},
--   $$
--   which has at most $300$ elements. If $t/64<r_j$ and $p$ is within distance $t$ of $c$ in each coordinate, then the level-$j$ entry of every tuple admissible at $p$ belongs to $\Lambda(c,j)$.
--
--   4. **Source coordinates.** For every $z\in S$ a representation $z=z(p,w)$ with $(p,w)$ admissible is fixed by choice; its base point and tuple are denoted $p(z)$ and $w(z)$.
--
--   In a ball of radius $t$, the coordinates at levels with $r_j\ge t$ are fixed, at most one level has $t/64<r_j\le t$, and the finer levels are negligible. Grouping points by the cells of their two base coordinates ($16^2$ choices) and by their label at the intermediate level (at most $300$ choices) gives the doubling bound $16^2\cdot300=76800$.
--
--   **Formalization Note** The definitions are `nearbyStripIndices`, `coordinateCell`, `nearbyLabels`, `sourceBase` and `sourceTuple`; the last two are defined by `Classical.choose` from membership in `constructedSet`. The residue $q\bmod N_j$ is the natural-number value of `Int.emod`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Doubling.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Doubling.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! Intrinsic doubling of the same fixed Hilbert subset. -/

open Set
noncomputable section
namespace DoublingHilbert

/-- A uniform finite set of strips meeting an interval shorter than 128 strip widths. -/
def nearbyStripIndices (c width : ℝ) : Finset ℤ :=
  Finset.Icc (⌊c / width⌋ - 65) (⌊c / width⌋ + 65)

/-- Sixteen cells of width `t/8` cover the coordinate projection of a radius-`t` ball. -/
def coordinateCell (c t x : ℝ) : ℤ := ⌊8 * (x - (c - t)) / t⌋

end DoublingHilbert

open Set Metric
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

namespace DoublingHilbert
open Set
open scoped BigOperators

/-- The finite list of intermediate-level choices near a base point. -/
def nearbyLabels (c : Base) (j : ℕ) : Finset ℕ :=
  insert 0 ((nearbyStripIndices c.2 (scale j)).image
    (fun q => (q % (colors j : ℤ)).toNat + 1) ∪
    (nearbyStripIndices c.1 ((widthFactor j : ℝ) * scale j)).image
      (fun q => (q % (colors j : ℤ)).toNat + 1))

noncomputable def sourceBase (z : constructedSet) : Base := Classical.choose z.prop
noncomputable def sourceTuple (z : constructedSet) : Tuple :=
  Classical.choose (Classical.choose_spec z.prop)

end DoublingHilbert

end
end

end OAI


