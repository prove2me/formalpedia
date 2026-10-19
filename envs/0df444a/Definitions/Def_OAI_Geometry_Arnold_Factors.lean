-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Factors
-- name    : OAI_Geometry_Arnold_Factors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:48:25.895973+00:00
-- url     : https://prove2.me/theorems/fe79032d-36f9-4b5f-994e-509dc8c0ce52
-- title:
--   Plane coordinates and the two sphere factors of an isotropic vector in $\mathbb{C}^5$
-- statement:
--   For $z\in\mathbb{C}^5$ the file defines the following.
--
--   1. **Plane (moment) coordinates.** For $a,b\in\{0,\dots,4\}$,
--   $$
--   p_{ab}(z)=2\operatorname{Im}\bigl(\bar z_a\,z_b\bigr)=2\bigl(\operatorname{Re}z_a\operatorname{Im}z_b-\operatorname{Im}z_a\operatorname{Re}z_b\bigr),
--   $$
--   and the real $5\times5$ matrix $(p_{ab}(z))_{a,b}$. For a unit isotropic $z=(x+iy)/\sqrt2$, these are the Plücker coordinates $x_ay_b-x_by_a$ of the oriented plane spanned by $x$ and $y$. Each $p_{ab}$ is smooth.
--   2. **Sphere factors.** Using only the coordinates $1,\dots,4$,
--   $$
--   L(z)=\bigl(p_{12}+p_{34},\ p_{13}-p_{24},\ p_{14}+p_{23}\bigr),\qquad R(z)=\bigl(p_{12}-p_{34},\ p_{13}+p_{24},\ p_{14}-p_{23}\bigr),
--   $$
--   the self-dual and anti-self-dual parts of the plane. The map $z\mapsto(L(z),R(z))\in\mathbb{R}^3\times\mathbb{R}^3$ is smooth.
--   3. **Partial norm and quadric.** $\sum_{i=1}^4|z_i|^2$ and $\sum_{i=1}^4z_i^2$, which ignore the coordinate $z_0$.
--   4. **Pairings.** The Hermitian product $\langle z,w\rangle=\sum_i\bar z_iw_i$ and the complex dot product $\sum_iz_iw_i$.
--
--   On the part of the quadric with $z_0=0$, which is the fixed locus of the involution, oriented planes in $\mathbb{R}^4$ correspond to pairs of points of $S^2\times S^2$ via $(L,R)$. This identifies the fixed locus with the sphere product on which the three critical points live.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Factors.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Factors.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints

/-- Oriented-plane coordinates of a unit isotropic vector. -/
def moment (a b : Fin 5) (z : CV) : ℝ := 2 * (star (z a) * z b).im

def planeMatrix (z : CV) : Matrix (Fin 5) (Fin 5) ℝ := fun a b ↦ moment a b z

lemma moment_real (a b : Fin 5) (z : CV) :
    moment a b z = 2 * ((z a).re * (z b).im - (z a).im * (z b).re) := by
  simp [moment, Complex.mul_im, sub_eq_add_neg]

lemma moment_smooth (a b : Fin 5) : ContDiff ℝ ∞ (moment a b) := by
  unfold moment
  fun_prop

/-- The two sphere factors, in self-dual / anti-self-dual plane coordinates. -/
def leftSphere (z : CV) : R3 :=
  ![moment 1 2 z + moment 3 4 z, moment 1 3 z - moment 2 4 z,
    moment 1 4 z + moment 2 3 z]

def rightSphere (z : CV) : R3 :=
  ![moment 1 2 z - moment 3 4 z, moment 1 3 z + moment 2 4 z,
    moment 1 4 z - moment 2 3 z]

def sphereFactors (z : CV) : Pair := (leftSphere z, rightSphere z)

def fourNorm (z : CV) : ℝ := ∑ i : Fin 4, Complex.normSq (z i.succ)
def fourPolynomial (z : CV) : ℂ := ∑ i : Fin 4, z i.succ ^ 2

lemma sphereFactors_smooth : ContDiff ℝ ∞ sphereFactors := by
  apply ContDiff.prodMk
  all_goals
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [leftSphere, rightSphere]
    all_goals first | exact (moment_smooth _ _).add (moment_smooth _ _) | exact (moment_smooth _ _).sub (moment_smooth _ _)

end ArnoldCounterexample.Factors

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric

def hermitian (z w : CV) : ℂ := ∑ i, star (z i) * w i

def complexDot (z w : CV) : ℂ := ∑ i, z i * w i

end ArnoldCounterexample.Factors

end

end OAI


