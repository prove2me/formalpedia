-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveMinimalPrimeQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveMinimalPrimeQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:25.945853+00:00
-- url     : https://prove2.me/theorems/fa99fb7b-0395-471a-98e9-eff472aaa42f
-- title:
--   St Curve Minimal Prime Quotient
-- statement:
--   Definitions and structural lemmas for St Curve Minimal Prime Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveMinimalPrimeQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
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
open MvPolynomial ComplexSets
noncomputable section
def CurveMinimalPrimeQuotient.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (p : Ideal (curveLocalRing I q)),
    p ∈ minimalPrimes (curveLocalRing I q) →
      ∃ J : Ideal (MvPolynomial (Fin n) ℂ), J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧
        ∃ φ : curveLocalRing I q →+* curveLocalRing J q, Function.Surjective φ ∧ RingHom.ker φ = p ∧
          ∀ f : MvPolynomial (Fin n) ℂ, φ (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) =
            algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f
end
end GroundTheory.Heights₂.Heights


