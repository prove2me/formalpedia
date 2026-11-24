-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousSectionHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousSectionHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:53.459498+00:00
-- url     : https://prove2.me/theorems/9e2c6ebd-bc2d-4f34-bc08-46c1457fe825
-- title:
--   St Continuous Section Holomorphic
-- statement:
--   Definitions and structural lemmas for St Continuous Section Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StContinuousSectionHolomorphic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
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
open MvPolynomial Filter Topology Matrix
noncomputable section
def ContinuousSectionHolomorphic.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ)
    (O : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin n → ℂ),
    IsAffVariety J k → IsOpen O → ContinuousOn g O → (∀ y ∈ O, g y ∈ zeroLocus J) →
    (∀ y ∈ O, A *ᵥ g y = y) → DifferentiableOn ℂ g O
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


