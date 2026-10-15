-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_TipCylinders
-- name    : OAI_Geometry_RuledCovering_TipCylinders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:39:30.629252+00:00
-- url     : https://prove2.me/theorems/3686cef8-2431-4a3a-a67f-3803db6737a0
-- title:
--   Triangular tip cylinders at the two edges of the regular tetrahedron
-- statement:
--   Let $d\in\mathbb{R}$, let $\Delta(a)=\{b\in\mathbb{R}^2:\ 0\le b_2\le a,\ |b_1|\le b_2\}$ be the cone triangle, and let $\mathcal{C}_{h,g}(P)$ be the cylinder with axis parallel to $(1,g_1,hg_2)$ whose base is the orthogonal projection of $\{(0,b_1,hb_2):\ b\in P\}$ onto the plane perpendicular to that axis.
--
--   1. **Lower tip cylinder.** $\mathcal{C}_{\sqrt2,0}\bigl(\Delta(2d)\bigr)$. Since the slope is $g=0$, the axis is $e_1=(1,0,0)$ and the points $(0,b_1,\sqrt2\,b_2)$ already lie in $e_1^{\perp}$, so this is the cylinder with axis $e_1$ and base
--   $$\{(0,\ y,\ \sqrt2\,t):\ 0\le t\le 2d,\ |y|\le t\}.$$
--   2. **Upper tip cylinder.** The lower tip cylinder rotated by the isometry $\sigma(z_1,z_2,z_3)=(z_2,z_1,-z_3)$ and then translated by $(0,0,\sqrt2)$; its axis is $e_2=(0,1,0)$ and its base is $\{(x,\ 0,\ \sqrt2(1-s)):\ 0\le s\le 2d,\ |x|\le s\}$.
--
--   The regular tetrahedron of edge $2$ in physical coordinates is $\{z:\ \exists t\in[0,1],\ |z_1|\le 1-t,\ |z_2|\le t,\ z_3=\sqrt2\,t\}$, with its bottom edge on the $z_1$-axis and its top edge on the line $z_1=0,\ z_3=\sqrt2$. The same module shows that the carriers of the two cylinders are exactly the prisms $\{z:\ \exists t\in[0,2d],\ |z_2|\le t,\ z_3=\sqrt2\,t\}$ and $\{z:\ \exists s\in[0,2d],\ |z_1|\le s,\ z_3=\sqrt2(1-s)\}$, which contain the parts of the tetrahedron with $t\le 2d$ and with $1-t\le 2d$ respectively, that both bases are triangles when $d>0$, and that each cylinder has area $4\sqrt2\,d^2$ for $d\ge 0$. With $d=c^{\gamma}$ they are the two triangular cylinders of the singular statement, contributing $8\sqrt2\,c^{2\gamma}$ to the total area.
--
--   **Formalization Note** `lowerTipCylinder d` is `projectedCylinder (Real.sqrt 2) 0 (coneTriangle (2 * d))`, and `upperTipCylinder d` is `((lowerTipCylinder d).rotate swapReflect).translate (vec3 0 0 (Real.sqrt 2))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/TipCylinders.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/TipCylinders.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
import Definitions.Def_OAI_Geometry_RuledCovering_EnergyIntegral

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def lowerTipCylinder (d : ℝ) : Cylinder :=
  projectedCylinder (Real.sqrt 2) 0 (coneTriangle (2*d))

def upperTipCylinder (d : ℝ) : Cylinder :=
  ((lowerTipCylinder d).rotate swapReflect).translate (vec3 0 0 (Real.sqrt 2))

end RuledApproximation

end

end OAI


