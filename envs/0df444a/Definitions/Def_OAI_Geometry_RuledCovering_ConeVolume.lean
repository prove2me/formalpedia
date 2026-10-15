-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
-- name    : OAI_Geometry_RuledCovering_ConeVolume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:31:14.951449+00:00
-- url     : https://prove2.me/theorems/96e04df4-01d9-4a11-ab90-8acff4f1de3d
-- title:
--   Isosceles cone triangles and bands in the plane
-- statement:
--   Let $a,d\in\mathbb{R}$ and write points of the Euclidean plane as $z=(z_1,z_2)$.
--
--   1. **Cone triangle.**
--   $$\Delta(a)=\{z\in\mathbb{R}^2:\ 0\le z_2\le a,\ |z_1|\le z_2\}.$$
--   For $a\ge 0$ this is the closed isosceles right triangle with apex at the origin and vertices $(-a,a)$ and $(a,a)$; it is empty for $a<0$.
--   2. **Cone band.**
--   $$\Delta(d,a)=\{z\in\mathbb{R}^2:\ d\le z_2\le a,\ |z_1|\le z_2\},$$
--   the part of the cone $\{|z_1|\le z_2\}$ between the heights $d$ and $a$; for $0\le d\le a$ it is a trapezoid.
--
--   The same module shows that $\Delta(a)$ is compact with area $a^2$ for $a\ge 0$, and that $\Delta(d,a)$ is compact with area $a^2-d^2$ for $0\le d\le a$. In the singular construction the parameter domain is contained in $\Delta(2)$, and for $0\le p\le 2$ and small $c>0$ it consists of the band $\Delta(c^{\gamma},\tfrac12)$, of area $\tfrac14-c^{2\gamma}$, plus a thin cap along its top side; this band is the comparison region in the second-order area expansion. The triangles $\Delta(2d)$ are the bases of the two tip cylinders.
--
--   **Formalization Note** `coneTriangle a` and `coneBand d a` are subsets of `Plane`, with coordinates `z 0`, `z 1` corresponding to $z_1,z_2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/ConeVolume.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/ConeVolume.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def coneTriangle (a : ℝ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1}

def coneBand (d a : ℝ) : Set Plane :=
  {z | d ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1}

end RuledApproximation

end

end OAI


