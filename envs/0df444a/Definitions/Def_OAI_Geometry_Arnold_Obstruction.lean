-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Obstruction
-- name    : OAI_Geometry_Arnold_Obstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:42:29.968696+00:00
-- url     : https://prove2.me/theorems/6ade42e2-e98c-4ea8-94a1-7ff67cd6e665
-- title:
--   The orthogonal action as a linear map and the join homotopy of two equivariant maps
-- statement:
--   Let $\beta=\frac1{\sqrt2}(1,i,0,0,0)$ and let real $5\times5$ matrices act on $\mathbb{C}^5$ by $z\mapsto Az$.
--
--   1. **Action as a linear map.** For each matrix $A$, $z\mapsto Az$ as a continuous real-linear map of $\mathbb{C}^5$.
--   2. **Join homotopy.** For a map $F:\mathbb{C}^5\to\mathbb{C}^3$, define on $\mathbb{R}\times M_5(\mathbb{R})$
--   $$
--   J_F(\theta,A)=\bigl(\cos\theta\cdot A\beta,\ \sin\theta\cdot F(A\beta)\bigr)\in\mathbb{C}^5\times\mathbb{C}^3 .
--   $$
--
--   As $\theta$ runs from $0$ to $\pi/2$, this interpolates between the orbit map $A\mapsto(A\beta,0)$ and $A\mapsto(0,F(A\beta))$ inside the join of the two spheres. It is the standard join construction used to compare two equivariant sphere maps in the topological obstruction to too few critical points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Obstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Obstruction.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

local instance instTopologicalSpaceRM_4 : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The literal orthogonal action, bundled as a real continuous linear map. -/
def actCLM (A : RM) : CV →L[ℝ] CV :=
  ((complexMat A).mulVecLin.restrictScalars ℝ).toContinuousLinearMap

@[simp] lemma actCLM_apply (A : RM) (z : CV) : actCLM A z = act A z := rfl

/-- Standard join homotopy of the two equivariant sphere maps. -/
def joinHomotopy (F : CV → CSpace 3) (p : ℝ × RM) : ProductSpace :=
  (Real.cos p.1 • orbitProjection p.2, Real.sin p.1 • F (orbitProjection p.2))

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

local instance instTopologicalSpaceRM_5 : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample
open CriticalBound

end ArnoldCounterexample

end

end OAI


