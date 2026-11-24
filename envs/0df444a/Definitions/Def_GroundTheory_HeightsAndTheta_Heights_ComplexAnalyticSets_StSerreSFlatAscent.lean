-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:46.075119+00:00
-- url     : https://prove2.me/theorems/4d2227f4-7475-4997-a7ab-95c148accd3d
-- title:
--   St Serre SFlat Ascent
-- statement:
--   Definitions and structural lemmas for St Serre SFlat Ascent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSerreSFlatAscent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def SerreSFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreS A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreSAt (primeFibreLocalRing A P) k) → SerreS B k
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


