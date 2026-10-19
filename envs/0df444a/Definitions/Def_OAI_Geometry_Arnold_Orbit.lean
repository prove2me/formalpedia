-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Orbit
-- name    : OAI_Geometry_Arnold_Orbit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:28:45.121232+00:00
-- url     : https://prove2.me/theorems/f9b65ac4-eb09-4ba0-818b-919b2ddf78f4
-- title:
--   The orthogonal group action on $\mathbb{C}^5$ and the orbit of a unit isotropic vector
-- statement:
--   Let $M_5(\mathbb{R})$ be the real $5\times5$ matrices.
--
--   1. **Action.** A real matrix $A$ acts on $\mathbb{C}^5$ by $z\mapsto Az$, its complexification. The action is additive and real-homogeneous in $A$, and the identity acts trivially.
--   2. **Elementary rotations.** For $a,b\in\{0,\dots,4\}$, $R_{ab}=E_{ba}-E_{ab}$ is the skew matrix rotating the $(a,b)$ coordinate plane.
--   3. **Base point and its orbit data.** $\beta=\frac1{\sqrt2}(1,i,0,0,0)$, a unit isotropic vector. There are six generators $R_{02},R_{12},R_{03},R_{13},R_{04},R_{14}$, with velocities
--   $$
--   R_{02}\beta=\tfrac{1}{\sqrt2}e_2,\ R_{12}\beta=\tfrac{i}{\sqrt2}e_2,\ R_{03}\beta=\tfrac{1}{\sqrt2}e_3,\ R_{13}\beta=\tfrac{i}{\sqrt2}e_3,\ R_{04}\beta=\tfrac{1}{\sqrt2}e_4,\ R_{14}\beta=\tfrac{i}{\sqrt2}e_4,
--   $$
--   and the $6\times6$ coefficient matrix $c=\mathrm{diag}\bigl(J,J,J\bigr)$ with $J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. This matrix records the brackets of the generators at the base point: $(X_kX_l-X_lX_k)\beta=c_{kl}\,i\beta$.
--   4. **Orbit map.** The real-linear map $A\mapsto A\beta$ from $M_5(\mathbb{R})$ to $\mathbb{C}^5$.
--
--   The horizontal space at $\beta$ is $\mathbb{C}e_2\oplus\mathbb{C}e_3\oplus\mathbb{C}e_4$, which the six velocities span over $\mathbb{R}$. The vertical direction $i\beta$ is reached only through brackets. These data feed the orbit computation of the volume obstruction.
--
--   **Formalization Note** The velocities and coefficient matrix are given as explicit vectors `velocities` and matrix `bracketCoefficient`. A local instance equips the matrix space with its operator-norm topology for continuity of the orbit map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Orbit.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Orbit.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample

namespace CriticalBound
open Matrix

/-- Complexification of a real matrix, with the actual complex-linear action. -/
def complexMat (A : RM) : Matrix (Fin 5) (Fin 5) ℂ := A.map Complex.ofReal

def act (A : RM) (z : CV) : CV := (complexMat A).mulVec z

lemma complexMat_one : complexMat 1 = 1 := by
  ext i j
  simp [complexMat, Matrix.one_apply, apply_ite Complex.ofReal]

/-- Elementary skew matrix rotating the `(a,b)` coordinate plane. -/
def rotGen (a b : Fin 5) : RM := Matrix.single b a 1 - Matrix.single a b 1

end CriticalBound
end ArnoldCounterexample

namespace ArnoldCounterexample.CriticalBound

noncomputable def baseScale : ℝ := Real.sqrt (1 / 2)

def base : CV := ![(baseScale : ℂ), baseScale * Complex.I, 0, 0, 0]

def generators : Fin 6 → RM :=
  ![rotGen 0 2, rotGen 1 2, rotGen 0 3, rotGen 1 3, rotGen 0 4, rotGen 1 4]

def velocities : Fin 6 → CV :=
  ![Pi.single 2 (baseScale : ℂ), Pi.single 2 (baseScale * Complex.I),
    Pi.single 3 (baseScale : ℂ), Pi.single 3 (baseScale * Complex.I),
    Pi.single 4 (baseScale : ℂ), Pi.single 4 (baseScale * Complex.I)]

def bracketCoefficient : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

lemma act_add_left (A B : RM) (z : CV) : act (A + B) z = act A z + act B z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

lemma act_real_smul_left (c : ℝ) (A : RM) (z : CV) :
    act (c • A) z = c • act A z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
    Complex.real_smul]

local instance instTopologicalSpaceRM : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The orbit map at the literal unit isotropic vector, extended linearly. -/
def orbitProjection : RM →L[ℝ] CV :=
  ({ toFun := fun A ↦ act A base
     map_add' := fun A B ↦ act_add_left A B base
     map_smul' := fun c A ↦ act_real_smul_left c A base } : RM →ₗ[ℝ] CV).toContinuousLinearMap

@[simp] lemma orbitProjection_apply (A : RM) : orbitProjection A = act A base := rfl

end ArnoldCounterexample.CriticalBound

end

end OAI


