-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:28.215668+00:00
-- url     : https://prove2.me/theorems/dc01ef9a-9a57-4c21-9d88-9369887c0883
-- title:
--   St CMLocus Open
-- statement:
--   Definitions and structural lemmas for St CMLocus Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMLocusOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
open MvPolynomial
def CMLocusOpen.Statement : Prop :=
  ∀ (n : ℕ) (I P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime], I ≤ P →
    IsCohenMacaulayLocalRing (Localization.AtPrime P ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime P))) →
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ P ∧ ∀ (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q → g ∉ Q →
      IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))
end GroundTheory.Heights₂.Heights


