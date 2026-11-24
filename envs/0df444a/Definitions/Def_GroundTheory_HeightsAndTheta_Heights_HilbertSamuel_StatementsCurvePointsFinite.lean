-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsCurvePointsFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsCurvePointsFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:13.556379+00:00
-- url     : https://prove2.me/theorems/18c80402-5f95-42c1-b2a5-c47912ca5cdf
-- title:
--   Statements Curve Points Finite
-- statement:
--   Definitions and structural lemmas for Statements Curve Points Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsCurvePointsFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveComplexPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo
def CurvePointsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → Finite (GroundTheory.Heights₂.Heights.projPts W)
end GroundTheory.Heights₂.Heights.HilbertSamuel


