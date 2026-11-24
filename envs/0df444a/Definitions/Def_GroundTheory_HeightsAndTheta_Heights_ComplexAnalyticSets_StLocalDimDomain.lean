-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:18.599603+00:00
-- url     : https://prove2.me/theorems/300c93e4-8bd0-4b9e-b584-cf855733a817
-- title:
--   St Local Dim Domain
-- statement:
--   Definitions and structural lemmas for St Local Dim Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalDimDomain.lean

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
def LocalDimDomain.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) → ∀ q ∈ zeroSet J,
      ringKrullDim (localRingAt J q) = (e : ℕ)
end GroundTheory.Heights₂.Heights


