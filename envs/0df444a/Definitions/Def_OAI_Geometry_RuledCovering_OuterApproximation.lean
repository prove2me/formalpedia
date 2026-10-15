-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
-- name    : OAI_Geometry_RuledCovering_OuterApproximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:16:30.478923+00:00
-- url     : https://prove2.me/theorems/d965e738-46c4-4254-b4e1-6fbf7f08a673
-- title:
--   The scaled square lattice $\tfrac1n\mathbb{Z}^2$ in parameter coordinates
-- statement:
--   Let $\mathbb{R}^2_\infty$ be the coordinate plane of pairs of reals with the maximum norm. For a natural number $n$, the coordinate grid of mesh $1/n$ is
--   $$\Lambda_n=\tfrac{1}{n}\,\mathbb{Z}^2=\Bigl\{\bigl(\tfrac{i}{n},\tfrac{j}{n}\bigr):\ i,j\in\mathbb{Z}\Bigr\}\subseteq\mathbb{R}^2_\infty,$$
--   the dilation by the factor $1/n$ of the integer lattice, i.e. of the $\mathbb{Z}$-span of the two standard basis vectors.
--
--   The points $b\in\Lambda_n$ serve as centres of the square cells $\{x:\ \|x-b\|_\infty\le 1/(2n)\}$ of side $1/n$ from which local cylinder covers are assembled. The same module shows that a bounded set meets $\Lambda_n$ in finitely many points, and that for a compact set $K$ with an open neighbourhood $U$, a continuous weight $F\ge 0$, a radius $R$ and any $\varepsilon>0$, for all large $n$ there is a finite set $S\subseteq U\cap\Lambda_n$ containing every grid point within distance $R/n$ of $K$ and satisfying $n^{-2}\sum_{b\in S}F(b)<\int_K F+\varepsilon$. No regularity of the boundary of $K$ is needed for this.
--
--   **Formalization Note** `coordinateGrid n` is `(n : ℝ)⁻¹ • span ℤ (range (Pi.basisFun ℝ (Fin 2)))`, viewed as a subset of `Fin 2 → ℝ`. Because Lean sets $0^{-1}=0$, the case $n=0$ gives $\Lambda_0=\{0\}$; all uses assume $n\ge 1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/OuterApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/OuterApproximation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The square lattice in the displayed (possibly nonorthonormal) parameter coordinates. -/
def coordinateGrid (n : ℕ) : Set (Fin 2 → ℝ) :=
  (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))

end RuledApproximation

end

end OAI


