-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
-- name    : OAI_Geometry_RuledCovering_HyperbolicLattice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:19:38.741476+00:00
-- url     : https://prove2.me/theorems/7ab5913d-b019-405a-a76c-cf1f9eb93f93
-- title:
--   Coordinate swap on the parameter plane
-- statement:
--   The coordinate swap is the linear map $S$ of the coordinate plane $\mathbb{R}^2_\infty$ (pairs of reals with the maximum norm) that exchanges the two coordinates:
--   $$S(x_1,x_2)=(x_2,x_1),\qquad [S]=\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$
--   The file defines $S$ both as a linear map and as the associated continuous linear map.
--
--   For $\lambda>0$, the operator $\lambda S$ is the normal form, in sum-and-difference coordinates, of a planar derivative with eigenvalues $\lambda$ and $-\lambda$. The symmetric lattice template is stated for $A=\lambda S$: in the same module it is shown that if $L>0$ and $0<L\lambda<1$, then the lattice model $\mathrm{LM}(\lambda S,\,L,\,1/(2(1-L\lambda)))$ holds. Indeed $(p-b)+r\lambda S(p-b)$ has coordinates $x+ay$ and $y+ax$ with $a=r\lambda$ and $|a|\le L\lambda<1$, a symmetric lattice problem solved by integer rounding.
--
--   **Formalization Note** `swapLinear` sends `p` to `![p 1, p 0]`, and `swapCLM` is `swapLinear.toContinuousLinearMap`, both on `Parameter = Fin 2 → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/HyperbolicLattice.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicLattice.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def swapLinear : Parameter →ₗ[ℝ] Parameter where
  toFun p := ![p 1, p 0]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' c p := by ext i; fin_cases i <;> rfl

def swapCLM : Parameter →L[ℝ] Parameter := swapLinear.toContinuousLinearMap

end RuledApproximation

end

end OAI


