-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
-- name    : OAI_Combinatorics_HoneycombCorridor_VisitRecursion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:14:07.732389+00:00
-- url     : https://prove2.me/theorems/036afd48-2080-4f8e-99af-9dbcfd0bc945
-- title:
--   Positivity of the critical honeycomb activity
-- statement:
--   The critical activity of self-avoiding walks on the honeycomb lattice is
--   $$
--   \lambda=\frac1{2\cos(\pi/8)}=\frac1{\sqrt{2+\sqrt2}} .
--   $$
--
--   This bundle records that $\lambda>0$, since $\cos(\pi/8)>0$. Positivity of $\lambda$ is used throughout the visit recursion, where walk weights $\lambda^{|w|}$ are compared and divided, and where the identity $\lambda(e^{i\pi/8}+e^{-i\pi/8})=1$ makes the two turn weights at a vertex sum to one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/VisitRecursion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/VisitRecursion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem criticalActivity_pos : 0 < criticalActivity := by
  unfold criticalActivity
  exact inv_pos.mpr (mul_pos (by norm_num) critical_cos_pos)

end PolynomialVacuumBridge.Corridor

end

end OAI


