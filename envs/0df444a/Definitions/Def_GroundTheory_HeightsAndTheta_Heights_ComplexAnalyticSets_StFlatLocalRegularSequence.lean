-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:43.561671+00:00
-- url     : https://prove2.me/theorems/0fdbd831-aeff-4475-af95-dba0e2d06fdd
-- title:
--   St Flat Local Regular Sequence
-- statement:
--   Definitions and structural lemmas for St Flat Local Regular Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFlatLocalRegularSequence.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatDimFormula
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
open IsLocalRing RingTheory.Sequence
def FlatLocalRegularSequence.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ∀ (rs : List A) (ys : List B), (∀ r ∈ rs, r ∈ maximalIdeal A) → IsWeaklyRegular A rs →
        (∀ y ∈ ys, y ∈ maximalIdeal B) →
        IsWeaklyRegular (B ⧸ (maximalIdeal A).map (algebraMap A B))
          (ys.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))) →
        IsWeaklyRegular B (rs.map (algebraMap A B) ++ ys)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


