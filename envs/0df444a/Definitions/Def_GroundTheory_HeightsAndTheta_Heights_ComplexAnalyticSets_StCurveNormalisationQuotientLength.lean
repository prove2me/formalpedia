-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:13.840383+00:00
-- url     : https://prove2.me/theorems/d9724dbd-bb87-4ba3-8830-5aea4bd2e28c
-- title:
--   St Curve Normalisation Quotient Length
-- statement:
--   Definitions and structural lemmas for St Curve Normalisation Quotient Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationQuotientLength.lean

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
def CurveNormalisationQuotientLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), IsRadicalAt I q →
    ringKrullDim (curveLocalRing I q) = 1 →
    Module.length (curveLocalRing I q)
        (curveNormalisation I q ⧸
          LinearMap.range (Algebra.linearMap (curveLocalRing I q) (curveNormalisation I q))) ≠ ⊤
end GroundTheory.Heights₂.Heights


