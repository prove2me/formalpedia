-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationMinorOfDetection
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationMinorOfDetection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:12.035133+00:00
-- url     : https://prove2.me/theorems/6e3a2428-3480-4489-b597-5b6d9e5d55ad
-- title:
--   St Derivation Minor Of Detection
-- statement:
--   Definitions and structural lemmas for St Derivation Minor Of Detection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDerivationMinorOfDetection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyOriginIdeal_isMaximal_f9e3f262b184

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
open IsLocalRing
theorem DerivationMinorOfDetection.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime
attribute [local instance] DerivationMinorOfDetection.polyOriginIdeal_isPrime
def DerivationMinorOfDetection.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) →
    (∀ a : Fin h → Localization.AtPrime P,
      ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
        ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)) →
    (∀ g ∈ P, (∀ D : Derivation ℤ T T, D g ∈ P) →
      algebraMap T (Localization.AtPrime P) g ∈ maximalIdeal (Localization.AtPrime P) ^ 2) →
    ∃ D : Fin h → Derivation ℤ T T, (Matrix.of fun i j => D j (f i)).det ∉ P
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


