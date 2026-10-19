-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_CriticalLifts
-- name    : OAI_Geometry_Arnold_CriticalLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T09:11:39.228601+00:00
-- url     : https://prove2.me/theorems/f3cd94d9-6d48-4baf-a35f-be25c7c4de0a
-- title:
--   Explicit unit representatives of the three critical points on the fixed quadric
-- statement:
--   Write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$ on $\mathbb{C}^5$. The file defines the vectors
--   $$
--   \zeta_0=\Bigl(0,\tfrac12,-\tfrac i2,\tfrac12,\tfrac i2\Bigr),\qquad \zeta(r)=\Bigl(0,\tfrac{1+r}{4},\tfrac i2,\tfrac{1-r}{4},-\tfrac i2\Bigr)\quad(r\in\mathbb{R}).
--   $$
--
--   1. $\zeta_0$ is unit isotropic: $|\zeta_0|^2=1$ and $q(\zeta_0)=0$.
--   2. If $r^2=3$, then $\zeta(r)$ is unit isotropic.
--   3. The three lifts are $\zeta_0$, $\zeta_+=\zeta(\sqrt3)$ and $\zeta_-=\zeta(-\sqrt3)$.
--
--   All three vectors have $z_0=0$, so they lie on the quadric fixed by the coordinate involution. They are the unit representatives used for the three critical points, which become the three fixed points of the counterexample map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/CriticalLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/CriticalLifts.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
import Definitions.Def_OAI_Geometry_Arnold_Parameter
import Definitions.Def_OAI_Geometry_Arnold_Quotient
import Definitions.Def_OAI_Geometry_Arnold_Hamiltonian

namespace OAI

universe uα

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

def zeroVector : CV := ![0, 1/2, -Complex.I/2, 1/2, Complex.I/2]
def otherVector (r : ℝ) : CV := ![0, (1+(r:ℂ))/4, Complex.I/2, (1-(r:ℂ))/4, -Complex.I/2]

lemma zeroVector_unit : IsUnitQuadric zeroVector := by
  constructor
  · norm_num [normSquared, zeroVector, Fin.sum_univ_succ, Complex.normSq_apply]
  · apply Complex.ext <;> norm_num [quadricPolynomial, zeroVector, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two]

lemma otherVector_unit (r : ℝ) (hr : r^2 = 3) : IsUnitQuadric (otherVector r) := by
  constructor
  · norm_num [normSquared, otherVector, Fin.sum_univ_succ, Complex.normSq_apply]
    nlinarith
  · apply Complex.ext <;> norm_num [quadricPolynomial, otherVector, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith

def zeroLift : UnitQuadric := ⟨zeroVector,zeroVector_unit⟩
def plusLift : UnitQuadric := ⟨otherVector (Real.sqrt 3),otherVector_unit _ (Real.sq_sqrt (by norm_num))⟩
def minusLift : UnitQuadric := ⟨otherVector (-Real.sqrt 3),otherVector_unit _ (by rw [neg_sq]; exact Real.sq_sqrt (by norm_num))⟩

end ArnoldCounterexample.Construction

end

end OAI


