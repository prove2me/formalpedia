-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:59.907554+00:00
-- url     : https://prove2.me/theorems/44ba8ec9-a893-4d63-8784-8497dba39130
-- title:
--   St Rank Frac Degree
-- statement:
--   Definitions and structural lemmas for St Rank Frac Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StRankFracDegree.lean

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
namespace GroundTheory.Heights₂.Heights.Inter
def RankFracDegree.Statement : Prop :=
  ∀ (F Ω A B : Type) [Field F] [Field Ω] [Algebra F Ω] [CommRing A] [CommRing B] [Algebra A B]
    (L₀ L : IntermediateField F Ω) (f : A →+* Ω) (g : B →+* Ω),
    Function.Injective f → Function.Injective g → (∀ a, g (algebraMap A B a) = f a) →
    (∀ a, f a ∈ L₀) → (∀ b, g b ∈ L) →
    L₀.toSubfield ≤ Subfield.closure (Set.range f) → L.toSubfield ≤ Subfield.closure (Set.range g) →
    Module.Finite A B → Module.finrank A B = IntermediateField.relfinrank L₀ L
end GroundTheory.Heights₂.Heights.Inter


