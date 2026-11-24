-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCountPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCountPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:28.29552+00:00
-- url     : https://prove2.me/theorems/815a9317-f7b3-4d3d-89a6-af461a4d0d78
-- title:
--   St Isolated Points Count Prime
-- statement:
--   Definitions and structural lemmas for St Isolated Points Count Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIsolatedPointsCountPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCount
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
open MvPolynomial Topology ComplexSets
noncomputable section
def IsolatedPointsCountPrime.Statement : Prop :=
  ∀ (n m : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)), P.IsPrime → ∀ (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N
end
end GroundTheory.Heights₂.Heights


