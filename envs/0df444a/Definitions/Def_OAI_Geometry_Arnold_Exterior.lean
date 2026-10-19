-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Exterior
-- name    : OAI_Geometry_Arnold_Exterior
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:36:58.427016+00:00
-- url     : https://prove2.me/theorems/86eaf1b8-e335-4c51-ac2d-fcb481f21631
-- title:
--   Alternating products of a bilinear form with itself: the forms $B\wedge\eta$, $B^{\wedge2}$, $B^{\wedge3}$
-- statement:
--   Let $E$ be a real normed vector space and $B:E\times E\to\mathbb{R}$ a continuous bilinear form.
--
--   1. **Pair product.** For a continuous alternating $n$-form $\eta$ on $E$, $B\wedge\eta$ is the continuous alternating $(n+2)$-form obtained by alternatizing
--   $$
--   (u_0,u_1,\dots,u_{n+1})\mapsto B(u_0,u_1)\,\eta(u_2,\dots,u_{n+1}),
--   $$
--   in two stages: first in the slot of $u_1$ together with $\eta$'s arguments, then in all slots. The result is the wedge product of $B$ (as a $2$-form) with $\eta$, up to a fixed integer normalization.
--   2. **Square and cube.** $B^{\wedge2}=B\wedge(B\wedge1)$, an alternating $4$-form, and $B^{\wedge3}=B\wedge B^{\wedge2}$, an alternating $6$-form.
--
--   For a symplectic form $B$, the top power $B^{\wedge3}$ is a volume form in dimension six. The topological obstruction is phrased as the nonvanishing of its integral.
--
--   **Formalization Note** The names are `pairForm B η`, `squareForm B` and `cubeForm B`, built from Mathlib's `alternatizeUncurryFin`. The normalization is the one these alternatizations produce, with no factorial division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Exterior.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Exterior.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation

namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The alternating product of a bilinear form and an n-form, with an integer
normalization convenient for the six-dimensional obstruction. -/
def pairForm {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin n]→L[ℝ] ℝ) : E [⋀^Fin (n + 2)]→L[ℝ] ℝ :=
  alternatizeUncurryFin ((alternatizeUncurryFinCLM ℝ E ℝ).comp
    (((ContinuousLinearMap.smulRightL ℝ E (E [⋀^Fin n]→L[ℝ] ℝ)).flip η).comp B))

def squareForm (B : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 4]→L[ℝ] ℝ :=
  pairForm B (pairForm B (constOfIsEmpty ℝ E (Fin 0) 1))

def cubeForm (B : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 6]→L[ℝ] ℝ :=
  pairForm B (squareForm B)

end ArnoldCounterexample.Forms

end

end OAI


