-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:11.882968+00:00
-- url     : https://prove2.me/theorems/e0cb0bbc-fc6d-45d3-a8f8-ab156a03f45a
-- title:
--   Exists Int Valuation Lt One
-- statement:
--   Definitions and structural lemmas for Exists Int Valuation Lt One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsIntValuationLtOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def RegularityValuationCentre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsMultiProjPrime P → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ] (v : Valuation (funField P) Γ) (n : ℤ),
    v (n : funField P) < 1 →
    ∃ W : Ideal (MRing ι), IsMultiProjPrime W ∧ P ≤ W ∧ C n ∈ W ∧
      ∀ z : funField P, (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W → v z ≤ 1
end
end GroundTheory.Heights₂.Heights.Inter


