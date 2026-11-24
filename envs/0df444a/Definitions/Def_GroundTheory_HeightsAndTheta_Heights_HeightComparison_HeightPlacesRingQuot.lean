-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRingQuot
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRingQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:35.76182+00:00
-- url     : https://prove2.me/theorems/e79ba9d5-3497-4501-8492-829734c0cb0a
-- title:
--   Height Places Ring Quot
-- statement:
--   Definitions and structural lemmas for Height Places Ring Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPlacesRingQuot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
def PlacesRingQuot.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Set (FinitePlace L)), S.Finite →
    ∀ g : placesRing S, g ≠ 0 →
      Real.log (Nat.card (placesRing S ⧸ Ideal.span {g})) = ∑ᶠ w ∈ S, -Real.log (w (g : L))
example : ∃ (S : Set (FinitePlace ℚ)) (g : placesRing S), S.Finite ∧ g ≠ 0 :=
  ⟨∅, 1, Set.finite_empty, one_ne_zero⟩
end GroundTheory.Heights₂.Heights


