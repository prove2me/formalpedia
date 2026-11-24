-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:56.025193+00:00
-- url     : https://prove2.me/theorems/793082e3-d33b-4b23-9297-b527247948c2
-- title:
--   St Local Dim Component Bound
-- statement:
--   Definitions and structural lemmas for St Local Dim Component Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalDimComponentBound.lean

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
def LocalDimComponentBound.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), q ∈ zeroSet I →
    ∃ W : Ideal (MvPolynomial (Fin n) ℂ), W.IsPrime ∧ I ≤ W ∧ q ∈ zeroSet W ∧
      ringKrullDim (curveLocalRing I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)
end
end GroundTheory.Heights₂.Heights


