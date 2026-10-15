-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_SingularField
-- name    : OAI_Geometry_RuledCovering_SingularField
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:28:09.659995+00:00
-- url     : https://prove2.me/theorems/72cc1876-be6e-46f8-b7ee-638ffdd23754
-- title:
--   The planar linear operator with a prescribed $2\times 2$ matrix
-- statement:
--   For real numbers $a,b,c,d$, let $T_{a,b,c,d}$ be the continuous linear operator on the Euclidean plane $\mathbb{R}^2$ whose matrix in the standard basis is $\begin{pmatrix}a&b\\c&d\end{pmatrix}$:
--   $$T_{a,b,c,d}(z)=(a z_1+b z_2,\ c z_1+d z_2).$$
--   The file defines the operator and records this coordinate formula as a simplification rule.
--
--   It is used to write the derivative of the explicit singular vector field in closed form. For $p\in\mathbb{R}$ and $z_2>0$ that field is $W_p(z)=\bigl(\tfrac14(2z_2)^{p-1}(p+(2-p)(z_1/z_2)^2),\ (2z_2)^{p-2}z_1\bigr)$; the module computes its derivative at such $z$ as an operator $T_{a,b,c,d}$ with explicit entries and reads off the trace $a+d=0$ and the determinant $ad-bc=\tfrac12(p-1)(2z_2)^{2(p-2)}\bigl((2-p)(z_1/z_2)^2-p\bigr)$, which is negative on the cone $|z_1|\le z_2$ when $1<p<2$. Consequently, at such points every multiple $cW_p$ with $c\neq0$ and $|c|\,\|DW_p(z)\|<1$ is hyperbolic with time bound $L=1$.
--
--   **Formalization Note** `matrixCLM a b c d` is built from the coordinate projections `EuclideanSpace.proj` and `smulRight` with the basis vectors `vec2 1 0` and `vec2 0 1`; `matrixCLM_apply` is the coordinate formula.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularField.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularField.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def matrixCLM (a b c d : ℝ) : Plane →L[ℝ] Plane :=
  (a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 1 0) +
  (c • EuclideanSpace.proj 0 + d • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 0 1)

@[simp] lemma matrixCLM_apply (a b c d : ℝ) (z : Plane) :
    matrixCLM a b c d z = vec2 (a*z 0+b*z 1) (c*z 0+d*z 1) := by
  ext i
  fin_cases i <;> simp [matrixCLM,vec2]

end RuledApproximation

end

end OAI


