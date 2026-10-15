-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
-- name    : OAI_Geometry_RuledCovering_HyperbolicCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:20:57.800263+00:00
-- url     : https://prove2.me/theorems/3d2896fa-b6d4-4081-aa6a-ac690a52bc87
-- title:
--   Sum-and-difference coordinates conjugating a hyperbolic derivative to a swap
-- statement:
--   The sum-and-difference map is the linear automorphism $\Sigma$ of the coordinate plane $\mathbb{R}^2_\infty$ given by
--   $$\Sigma(x_1,x_2)=(x_1+x_2,\ x_1-x_2),\qquad \Sigma^{-1}(y_1,y_2)=\Bigl(\frac{y_1+y_2}{2},\ \frac{y_1-y_2}{2}\Bigr).$$
--
--   It conjugates a diagonal hyperbolic matrix to a multiple of the coordinate swap $S(z_1,z_2)=(z_2,z_1)$: $\Sigma^{-1}\operatorname{diag}(\lambda,-\lambda)\,\Sigma=\lambda S$. Concretely, if a linear operator $A$ on the Euclidean plane has eigenvalues $\lambda$ and $-\lambda$ with $\lambda>0$ and eigenvectors $e_+$, $e_-$, then the frame $M(z)=(z_1+z_2)\,e_++(z_1-z_2)\,e_-$, which is $\Sigma$ followed by the coordinate map of the eigenbasis, satisfies $M^{-1}AM(z_1,z_2)=(\lambda z_2,\lambda z_1)$ (shown in the same module). This is how a field that is hyperbolic at a point, with derivative eigenvalues $\pm\lambda$ and $0<L\lambda<1$, is brought to the symmetric lattice template, after which the local covers are glued over compact patches.
--
--   **Formalization Note** `sumDifference` is a linear equivalence `Coordinates ≃ₗ[ℝ] Coordinates` with forward map `![x 0 + x 1, x 0 - x 1]` and inverse `![(y 0 + y 1) / 2, (y 0 - y 1) / 2]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Sum-and-difference coordinates conjugate a hyperbolic derivative to the square lattice template. -/
def sumDifference : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun x := ![x 0 + x 1, x 0 - x 1]
  invFun y := ![(y 0 + y 1) / 2, (y 0 - y 1) / 2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

end RuledApproximation

end

end OAI


