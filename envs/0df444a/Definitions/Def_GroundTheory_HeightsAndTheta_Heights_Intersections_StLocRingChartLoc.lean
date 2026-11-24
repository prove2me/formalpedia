-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingChartLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingChartLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:32.030921+00:00
-- url     : https://prove2.me/theorems/e6c6292b-9c57-4b29-b6ce-251cfbff2741
-- title:
--   St Loc Ring Chart Loc
-- statement:
--   Definitions and structural lemmas for St Loc Ring Chart Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StLocRingChartLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingNoeth
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def LocRingChartLoc.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) [P.IsPrime],
    W.IsPrime → P ≤ W → IsRelevant W →
    ∃ T : Finset (FractionRing (MRing ι ⧸ P)),
      Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))) ≤ locRing P W ∧
      ∀ z ∈ locRing P W, ∃ b ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))),
        ∃ c ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))), c ≠ 0 ∧ c⁻¹ ∈ locRing P W ∧ z * c = b
end GroundTheory.Heights₂.Heights.Inter


