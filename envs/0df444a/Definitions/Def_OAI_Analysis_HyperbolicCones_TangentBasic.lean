-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic
-- name    : OAI_Analysis_HyperbolicCones_TangentBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:02:30.840635+00:00
-- url     : https://prove2.me/theorems/ff71a854-dbef-4bf0-a809-08c60d39c4e0
-- title:
--   Wedge coordinates on the orthogonal complement of a vector in $\mathbb{R}^4$
-- statement:
--   Equip $\mathbb{R}^4$ with its standard inner product $\langle\cdot,\cdot\rangle$ and index coordinates as $v=(v_0,v_1,v_2,v_3)$. For $v\in\mathbb{R}^4$ let
--   $$T_v=\{h\in\mathbb{R}^4:\ \langle v,h\rangle=0\}$$
--   be the orthogonal complement of $v$ (for a unit vector $v$, the tangent space of the unit sphere $S^3$ at $v$). For any $u\in\mathbb{R}^4$ the *wedge coordinates* of the pair $(v,u)$ are the three numbers $v_0u_i-u_0v_i$, $i=1,2,3$, i.e. the coefficients of $v\wedge u$ on $e_0\wedge e_1$, $e_0\wedge e_2$, $e_0\wedge e_3$.
--
--   1. **Tangent coordinates.** The file defines the linear map $\tau_v:T_v\to\mathbb{R}^3$ that restricts the wedge coordinates to $T_v$:
--   $$\tau_v(h)=\bigl(v_0h_1-h_0v_1,\ v_0h_2-h_0v_2,\ v_0h_3-h_0v_3\bigr),\qquad h\in T_v .$$
--   Additivity and homogeneity in $h$ are immediate from the formula.
--
--   When $v_0\neq0$ the map $\tau_v$ is injective: $\tau_v(h)=0$ forces $h=(h_0/v_0)\,v$, and then $\langle v,h\rangle=0$ forces $h=0$. Since $\dim T_v=3$ for $v\neq0$, $\tau_v$ is then a linear isomorphism $T_v\cong\mathbb{R}^3$. These coordinates parametrize tangent directions at a point of the unit sphere and are used in the tangent-space computations of the surrounding development, where the kernel of a matrix pencil is followed along curves on $S^3$.
--
--   **Formalization Note** $\mathbb{R}^4$ is `Vec 4`, i.e. `EuclideanSpace ℝ (Fin 4)`; $T_v$ is `tangentSpace v`, defined as the kernel of the continuous linear functional `innerSL ℝ v`; the pointwise formula is `wedgeCoordinates v u`, and the map of this file is `tangentCoordinates v`, a linear map from the subspace `tangentSpace v` to `Fin 3 → ℝ`. The index `i : Fin 3` refers to the coordinate `i.succ` of $\mathbb{R}^4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/TangentBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/TangentBasic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth

namespace OAI

noncomputable section

open scoped RealInnerProductSpace

namespace Paper256

def tangentCoordinates (v : Vec 4) : tangentSpace v →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun h := wedgeCoordinates v h.val
  map_add' h k := by ext i; simp [wedgeCoordinates]; ring
  map_smul' s h := by ext i; simp [wedgeCoordinates]; ring

end Paper256

end

end OAI


