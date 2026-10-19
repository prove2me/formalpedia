-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Coordinates
-- name    : OAI_Geometry_Arnold_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:32:27.757862+00:00
-- url     : https://prove2.me/theorems/4d931baf-448f-465b-abf6-36f915525c4c
-- title:
--   Rotation derivatives, gradient deformation and skew lifts of tangent vectors on $\mathbb{C}^5$
-- statement:
--   Real $5\times5$ matrices act on $\mathbb{C}^5$ by $z\mapsto Az$, and $R_{ab}=E_{ba}-E_{ab}$ is the elementary rotation of the $(a,b)$ plane. Let $G:\mathbb{C}^5\to\mathbb{R}$.
--
--   1. **Matrix action.** The jointly continuous real-bilinear map $(A,z)\mapsto Az$.
--   2. **Rotation derivatives.** $\partial_{ab}G(z)=dG(z)[R_{ab}z]$, the derivative of $G$ along the infinitesimal rotation of the $(a,b)$ plane.
--   3. **Negative gradient matrix and squared gradient.**
--   $$
--   N_G(z)=-\sum_{a,b}\partial_{ab}G(z)\,R_{ab},\qquad |\nabla G|^2(z)=\sum_{a,b}\bigl(\partial_{ab}G(z)\bigr)^2 .
--   $$
--   4. **Gradient deformation.** $\Phi_G(t,z)=\exp\bigl(t\,N_G(z)\bigr)\,z$. It is defined for all $t$, with $\Phi_G(0,z)=z$. Since $N_G(z)$ is skew, $\exp(tN_G(z))$ is orthogonal, so $\Phi_G$ preserves the unit quadric.
--   5. **Skew lift of a tangent vector.** For $z,v\in\mathbb{C}^5$, the real matrix
--   $$
--   T(z,v)_{ij}=2\operatorname{Re}\bigl(v_i\bar z_j-z_i\bar v_j\bigr).
--   $$
--
--   The gradient deformation pushes points of the quadric in the direction of decreasing $G$ using only orthogonal motions. The skew lift shows that every horizontal vector at $z$ is the velocity of such a motion. Both are ingredients of the critical-point lower bound.
--
--   **Formalization Note** The names are `matrixAction`, `rotationDerivative`, `negativeRotationMatrix`, `gradientSquare`, `gradientCurve` and `tangentMatrix`. The exponential is `NormedSpace.exp` in the operator-normed matrix algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Coordinates.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

local instance instTopologicalSpaceRM_1 : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The actual real-matrix action on C5, jointly continuous bilinear. -/
def matrixAction : RM →L[ℝ] CV →L[ℝ] CV :=
  ({ toFun := fun A ↦ ((complexMat A).mulVecLin.restrictScalars ℝ).toContinuousLinearMap
     map_add' := by intro A B; apply ContinuousLinearMap.ext; intro z; exact act_add_left A B z
     map_smul' := by intro c A; apply ContinuousLinearMap.ext; intro z; exact act_real_smul_left c A z } :
      RM →ₗ[ℝ] CV →L[ℝ] CV).toContinuousLinearMap

@[simp] lemma matrixAction_apply (A : RM) (z : CV) : matrixAction A z = act A z := rfl

/-- Intrinsic derivative along the genuine coordinate-plane rotation. -/
def rotationDerivative (G : CV → ℝ) (a b : Fin 5) (z : CV) : ℝ :=
  fderiv ℝ G z (matrixAction (rotGen a b) z)

/-- Smooth negative gradient written in the spanning infinitesimal rotations. -/
def negativeRotationMatrix (G : CV → ℝ) (z : CV) : RM :=
  -(∑ a : Fin 5, ∑ b : Fin 5, rotationDerivative G a b z • rotGen a b)

def gradientSquare (G : CV → ℝ) (z : CV) : ℝ :=
  ∑ a : Fin 5, ∑ b : Fin 5, rotationDerivative G a b z ^ 2

/-- Orthogonal exponential is a globally defined smooth deformation of K. -/
def gradientCurve (G : CV → ℝ) (p : ℝ × CV) : CV :=
  matrixAction (NormedSpace.exp (p.1 • negativeRotationMatrix G p.2)) p.2

@[simp] lemma gradientCurve_zero (G : CV → ℝ) (z : CV) : gradientCurve G (0, z) = z := by
  simp only [gradientCurve, zero_smul, NormedSpace.exp_zero, matrixAction_apply, act,
    complexMat_one, Matrix.one_mulVec]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

local instance instTopologicalSpaceRM_2 : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

/-- A literal real skew matrix lifting any horizontal vector. -/
def tangentMatrix (z v : CV) : RM := fun i j ↦ 2 * (v i * star (z j) - z i * star (v j)).re

end ArnoldCounterexample.CriticalBound

end

end OAI


