-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:19.062667+00:00
-- url     : https://prove2.me/theorems/effcf485-0f8a-4ded-ab6e-da5a215916b0
-- title:
--   St CMGeneral Point
-- statement:
--   Definitions and structural lemmas for St CMGeneral Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMGeneralPoint.lean

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
open MvPolynomial ComplexSets
def CMGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
      (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) ∧ IsCohenMacaulayAt I q
end GroundTheory.Heights₂.Heights


