-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:48.792835+00:00
-- url     : https://prove2.me/theorems/7710a367-bf59-4a6b-aee3-48b89e89e566
-- title:
--   Imports More Alt
-- statement:
--   Definitions and structural lemmas for Imports More Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsMoreAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemRegRingSpecZ
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
def RegularityLocalPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℤ) (y : funField P),
    IsArithVar P 1 → Prime p →
    (∀ W, IsClosedPt W → P ≤ W → C p ∈ W → (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    ∃ n : ℤ, ¬ p ∣ n ∧ (n : funField P) * y ∈ regRing P
end
end GroundTheory.Heights₂.Heights.Inter


