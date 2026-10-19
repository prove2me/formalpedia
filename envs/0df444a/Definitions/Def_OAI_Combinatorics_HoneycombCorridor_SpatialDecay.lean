-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_SpatialDecay
-- name    : OAI_Combinatorics_HoneycombCorridor_SpatialDecay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:37:31.263992+00:00
-- url     : https://prove2.me/theorems/bda85f7b-999c-4ce5-88cb-7152ac8be4ab
-- title:
--   Shell decomposition constants for strip walks
-- statement:
--   Constants and shell indices used to sum the exponential lateral tail over a strip of height $h$. Let $c$ be the tail rate.
--
--   1. **Shell ratio.** $r=e^{-c}\in(0,1)$.
--   2. **Spatial constant.**
--   $$
--   C_{\mathrm{sp}}=20\Bigl(1+\sum_{n\ge0}(n+1)\,r^n\Bigr),
--   $$
--   which is finite because $r<1$.
--   3. **Shell index.** A vertex with horizontal position $x$ lies in shell
--   $$
--   \mathrm{shellIndex}(h,v)=\Bigl\lfloor\frac{|x|}{2(h+1)}\Bigr\rfloor,
--   $$
--   so shell $n$ is at horizontal distance about $2n(h+1)$ from the origin, where the lateral mass is at most a constant times $r^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/SpatialDecay.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/SpatialDecay.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripWindows

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def shellRatio : ℝ := Real.exp (-tailRate)
noncomputable def spatialConstant : ℝ :=
  20 * (1 + ∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n)

noncomputable def shellIndex (h : ℕ) (v : Vertex) : ℕ :=
  ⌊|(position v).1|/(2*((h : ℝ)+1))⌋₊

end PolynomialVacuumBridge.Corridor

end

end OAI


