-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:04.697471+00:00
-- url     : https://prove2.me/theorems/e882ce06-e987-4f3e-b5c1-8d1858d1b152
-- title:
--   St CMProj Dim Criterion
-- statement:
--   Definitions and structural lemmas for St CMProj Dim Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMProjDimCriterion.lean

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
open MvPolynomial CategoryTheory
def CMProjDimCriterion.Statement : Prop :=
  ∀ (n : ℕ) (I Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q →
    (IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
          I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))) ℓ ∧
        (ℓ : ℕ∞) ≤ (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))).height)
end GroundTheory.Heights₂.Heights


