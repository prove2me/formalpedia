-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:20.201939+00:00
-- url     : https://prove2.me/theorems/977668cc-7f36-472f-9201-7a12744ce4b4
-- title:
--   Imports Ter Ter
-- statement:
--   Definitions and structural lemmas for Imports Ter Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerTer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
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
def RegularityDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (x : funField P),
    IsArithVar P 1 → ∃ c : funField P, c ≠ 0 ∧ ∀ W, IsClosedPt W → P ≤ W →
      (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W ∧ ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W
end
end GroundTheory.Heights₂.Heights.Inter


