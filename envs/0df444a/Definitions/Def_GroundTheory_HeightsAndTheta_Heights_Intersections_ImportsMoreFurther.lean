-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:09.251896+00:00
-- url     : https://prove2.me/theorems/dc2952ae-ac83-496d-bc71-7f1b5bb8f788
-- title:
--   Imports More Further
-- statement:
--   Definitions and structural lemmas for Imports More Further, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsMoreFurther.lean

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
def RegularityMaximalSurjective.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ m : Ideal (regRing P), m.IsMaximal →
    ∃ W : Ideal (MRing ι), IsClosedPt W ∧ P ≤ W ∧ ∀ x ∈ m, ∀ z ∈ locRing P W,
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z ≠ 1
end
end GroundTheory.Heights₂.Heights.Inter


