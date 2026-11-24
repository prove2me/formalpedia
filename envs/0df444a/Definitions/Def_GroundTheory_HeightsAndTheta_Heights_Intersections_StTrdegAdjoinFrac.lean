-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:25.574095+00:00
-- url     : https://prove2.me/theorems/a0a83ca6-1b1c-4931-a149-f1fbd988576d
-- title:
--   St Trdeg Adjoin Frac
-- statement:
--   Definitions and structural lemmas for St Trdeg Adjoin Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StTrdegAdjoinFrac.lean

import Mathlib
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
def TrdegAdjoinFrac.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ D] (E : Type) [CommRing E] [IsDomain E] [Algebra ℤ E]
    [Algebra (FractionRing D) E] (s : Set E),
    Function.Injective (algebraMap ℤ D) →
    Algebra.trdeg ℤ (Algebra.adjoin ℤ
        (Set.range (fun d : D => algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d)) ∪ s)) =
      Algebra.trdeg ℤ D + Algebra.trdeg (FractionRing D) (Algebra.adjoin (FractionRing D) s)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


