-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:07.186175+00:00
-- url     : https://prove2.me/theorems/ff7807d3-b5aa-461c-adde-ad72b927ea93
-- title:
--   St Slice Reduced Away
-- statement:
--   Definitions and structural lemmas for St Slice Reduced Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceReducedAway.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
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
open MvPolynomial Matrix
noncomputable section
def SliceReducedAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
      ∀ L ∈ O, ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
        P ≠ RingHom.ker (eval q) →
          ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q
end
end GroundTheory.Heights₂.Heights


