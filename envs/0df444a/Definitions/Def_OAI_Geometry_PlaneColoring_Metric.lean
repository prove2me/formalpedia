-- Prove2me | Definitions.Def_OAI_Geometry_PlaneColoring_Metric
-- name    : OAI_Geometry_PlaneColoring_Metric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:38:20.642954+00:00
-- url     : https://prove2.me/theorems/c1be5333-92f1-4516-b40a-3799078124a5
-- title:
--   Triangular lattice in the plane with nearest-neighbor spacing $4/5$
-- statement:
--   The file defines a scaled copy of the triangular lattice in the Euclidean plane $\mathbb{R}^2$. For integers $a,b\in\mathbb{Z}$ put
--   $$T(a,b)=\Bigl(\tfrac45\bigl(a+\tfrac b2\bigr),\ \tfrac{2\sqrt3}{5}\,b\Bigr)=\tfrac45\,\bigl(a\,e_1+b\,e_2\bigr),\qquad e_1=(1,0),\quad e_2=\bigl(\tfrac12,\tfrac{\sqrt3}{2}\bigr).$$
--   The image $\{T(a,b):\ a,b\in\mathbb{Z}\}$ is the triangular lattice whose nearest neighbors are at distance $\tfrac45$; for instance $\|T(1,0)\|=\|T(0,1)\|=\tfrac45$. The file also records the first and second coordinates of $T(a,b)$ as simplification rules.
--
--   The map $T$ is additive, $T(a,b)-T(c,d)=T(a-c,b-d)$, and $\|T(a,b)\|^2=\tfrac{16}{25}\,(a^2+ab+b^2)$, so distances between lattice points reduce to the integer norm form $a^2+ab+b^2$. In the seven-coloring of the plane the points $T(a,b)$ serve as cell centers: the scale $\tfrac45$ is small enough that every point of the plane lies within distance $\tfrac{4}{5\sqrt3}<\tfrac12$ of some center, and large enough that two distinct centers of the same color under $(a,b)\mapsto a+3b \bmod 7$ are more than $2$ apart.
--
--   **Formalization Note** `triangularLattice a b` is a point of `EuclideanSpace ℝ (Fin 2)`. The simp lemmas `triangularLattice_zero` and `triangularLattice_one` evaluate its coordinates with indices `0` and `1`; both hold by definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/Metric.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/Metric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PlaneColoring mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
import Definitions.Def_OAI_Geometry_PlaneColoring_Basic

namespace OAI

noncomputable section

namespace Problem160

/-- Triangular lattice with nearest-neighbor spacing `4/5`. -/
def triangularLattice (a b : ℤ) : Plane :=
  WithLp.toLp 2 ![(4 / 5 : ℝ) * ((a : ℝ) + (b : ℝ)/2),
    (2 * Real.sqrt 3 / 5 : ℝ) * b]

@[simp] theorem triangularLattice_zero (a b : ℤ) :
    triangularLattice a b 0 = (4 / 5 : ℝ) * ((a : ℝ) + (b : ℝ)/2) := rfl

@[simp] theorem triangularLattice_one (a b : ℤ) :
    triangularLattice a b 1 = (2 * Real.sqrt 3 / 5 : ℝ) * b := rfl

end Problem160

end

end OAI


