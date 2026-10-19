-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Deformation
-- name    : OAI_Geometry_Arnold_Deformation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:34:46.402986+00:00
-- url     : https://prove2.me/theorems/47bfdd1f-948b-4ba2-891d-deb6b75648d1
-- title:
--   Unit phases preserve the unit isotropic quadric
-- statement:
--   For $z\in\mathbb{C}^5$ with $|z|^2=1$ and $\sum_jz_j^2=0$, and for $a\in\mathbb{C}$ with $|a|=1$, the vector $az$ again satisfies
--   $$
--   |az|^2=1,\qquad\sum_j(az_j)^2=0 .
--   $$
--
--   So the unit circle acts on the unit isotropic quadric by phase multiplication, and the quadric $Q_3$ is its quotient. This invariance is used when deforming representatives while keeping track of the projective point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Deformation.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Deformation.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric

lemma unit_phase (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    IsUnitQuadric (a • (z : CV)) := by
  constructor
  · rw [normSquared_smul, ha, z.property.1, mul_one]
  · rw [quadricPolynomial_smul, z.property.2, mul_zero]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
-- [generator] trimmed: open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent
open ArnoldCounterexample.Quadric

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
-- [generator] trimmed: open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms

end ArnoldCounterexample.CriticalBound

end

end OAI


