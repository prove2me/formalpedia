-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveComplexPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveComplexPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:43.26627+00:00
-- url     : https://prove2.me/theorems/4b4b775d-c71b-4dfa-93ef-77490cd36faa
-- title:
--   Curve Complex Point
-- statement:
--   Definitions and structural lemmas for Curve Complex Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/CurveComplexPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def CurveComplexPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → (mcPts W).Nonempty
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


