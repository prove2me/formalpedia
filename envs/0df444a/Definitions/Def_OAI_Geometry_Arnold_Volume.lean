-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Volume
-- name    : OAI_Geometry_Arnold_Volume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:41:16.855975+00:00
-- url     : https://prove2.me/theorems/5e922d30-631f-47c8-99d6-83acc6188cf0
-- title:
--   The product symplectic form and squared norm on $\mathbb{C}^5\times\mathbb{C}^3$
-- statement:
--   Let $P=\mathbb{C}^5\times\mathbb{C}^3$. For $u=(u_1,u_2)$ and $v=(v_1,v_2)$ in $P$,
--   $$
--   \Omega(u,v)=\omega_5(u_1,v_1)+\omega_3(u_2,v_2),\qquad \|(z,w)\|^2=|z|^2+|w|^2,
--   $$
--   where $\omega_n(u,v)=2\operatorname{Im}\sum_i\bar u_iv_i$ is the standard symplectic form on $\mathbb{C}^n$ and $|\cdot|^2$ the Euclidean squared norm.
--
--   This is the ambient space of the join of the quadric with the unit sphere of $\mathbb{C}^3$, on which the volume computation of the obstruction takes place.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Volume.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Volume.lean by skeleton subtraction
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

namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

local instance instTopologicalSpaceRM_3 : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

abbrev ProductSpace := CSpace 5 × CSpace 3

def productSymplectic : ProductSpace →L[ℝ] ProductSpace →L[ℝ] ℝ :=
  (symplectic 5).bilinearComp (.fst ℝ (CSpace 5) (CSpace 3)) (.fst ℝ (CSpace 5) (CSpace 3)) +
  (symplectic 3).bilinearComp (.snd ℝ (CSpace 5) (CSpace 3)) (.snd ℝ (CSpace 5) (CSpace 3))

@[simp] lemma productSymplectic_apply (u v : ProductSpace) :
    productSymplectic u v = symplectic 5 u.1 v.1 + symplectic 3 u.2 v.2 := rfl

def productNormSq (z : ProductSpace) : ℝ := normSq 5 z.1 + normSq 3 z.2

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

end

end OAI


