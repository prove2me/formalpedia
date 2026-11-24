-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:10.857892+00:00
-- url     : https://prove2.me/theorems/944b3285-f274-4998-a610-827a2169ee47
-- title:
--   St Curve Germ Components
-- statement:
--   Definitions and structural lemmas for St Curve Germ Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveGermComponents.lean

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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def CurveGermComponents.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet I ∩ N, ∃ W ∈ I.minimalPrimes,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 ∧ q ∈ zeroSet W ∧ x ∈ zeroSet W
end
end GroundTheory.Heights₂.Heights


