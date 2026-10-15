-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
-- name    : OAI_Geometry_DoublingHilbert_Grids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:11:04.253267+00:00
-- url     : https://prove2.me/theorems/7ee8d24c-65cf-42d0-93e3-33e6c297d015
-- title:
--   The periodic strip-color selector $\lfloor t/h\rfloor \bmod N$
-- statement:
--   Let $N$ be a positive integer and $h$ a real number (a strip width). The strip-color selector assigns to each $t\in\mathbb{R}$ the color
--   $$
--   \kappa_{N,h}(t)=\Bigl\lfloor \frac{t}{h}\Bigr\rfloor \bmod N\ \in\{0,1,\dots,N-1\}.
--   $$
--   For $h>0$, this is the color, modulo $N$, of the strip $[qh,(q+1)h)$ containing $t$; on each open strip $(qh,(q+1)h)$ it equals $q\bmod N$, which is the coloring used to define the strip set, and points on strip boundaries are assigned to the strip on their right.
--
--   The selector is a measurable function of $t$ with finitely many values. It is used to choose, at each point of the plane, which of the $N$ added sheets to differentiate: the color of the horizontal strip of width $r_j$ containing the second coordinate, or the color of the vertical strip of width $W_jr_j$ containing the first coordinate. Since strip boundaries form a null set, the arbitrary choice made there plays no role in any integral.
--
--   **Formalization Note** The definition is `stripColor N hN h t`, valued in `Fin N`, computed as the natural-number value of the integer remainder `Int.emod` of `⌊t / h⌋` by $N$. Lean's convention $t/0=0$ gives color $0$ when $h=0$. The module also records the extensionality lemma `Segment.ext` (segments with equal endpoints are equal).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Grids.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Grids.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles

namespace OAI

/-! Fine period grids, energy sampling, and sheet separation. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- The measurable periodic selector; boundary values play no role. -/
def stripColor (N : ℕ) (hN : 0 < N) (h t : ℝ) : Fin N :=
  ⟨Int.toNat (⌊t / h⌋ % (N : ℤ)), by
    have hnonneg := Int.emod_nonneg ⌊t / h⌋ (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos ⌊t / h⌋ (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩

namespace Segment

end Segment

end
end DoublingHilbert

namespace DoublingHilbert
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace Segment

@[ext] theorem ext {I J : Segment} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  cases I; cases J; simp_all

end Segment

namespace Rectangle

end Rectangle

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section SheetGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

end SheetGeometry

end
end DoublingHilbert

end OAI


