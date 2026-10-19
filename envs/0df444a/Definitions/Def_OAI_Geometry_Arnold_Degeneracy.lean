-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Degeneracy
-- name    : OAI_Geometry_Arnold_Degeneracy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T09:16:56.46007+00:00
-- url     : https://prove2.me/theorems/0ef5de6d-cfec-4ae4-ada2-9e0816fc300a
-- title:
--   A phase-normalized lift of the counterexample map near its degenerate fixed point
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}=S/U(1)$. Let $F(1,\cdot)$ be the time-one map of the Hamiltonian isotopy, which descends to the counterexample map $\varphi$ of $Q_3$. Define
--   $$
--   \widetilde\varphi(w)=-F(1,w)\qquad(w\in\mathbb{C}^5).
--   $$
--   For every $z\in S$, $\widetilde\varphi(z)\in S$.
--
--   Since $-1$ is a unit scalar, $\widetilde\varphi$ is again a lift of $\varphi$. The sign fixes the phase, so that $\widetilde\varphi$ fixes the chosen representative of the degenerate fixed point instead of mapping it to a phase multiple. This is the smooth local lift $G$ with $G(z)=z$ that the definition of a degenerate fixed point asks for.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Degeneracy.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Degeneracy.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_Arnold_CriticalLifts
import Definitions.Def_OAI_Geometry_Arnold_Kernel

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology

/-- Fix the phase of the lift at the degenerate point. -/
def degenerateLift (w : CV) : CV := -forward (1,w)

lemma degenerateLift_preserves (z : UnitQuadric) : IsUnitQuadric (degenerateLift z) := by
  have hu := forward_preserves 1 z
  change IsUnitQuadric (-forward (1,z))
  rw [← neg_one_smul ℂ (forward (1,z))]
  constructor
  · rw [normSquared_smul, Complex.normSq_neg, Complex.normSq_one, one_mul]
    exact hu.1
  · rw [quadricPolynomial_smul, hu.2, mul_zero]

end ArnoldCounterexample.Construction

end

end OAI


