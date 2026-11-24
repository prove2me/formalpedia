-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SameFactorDegreeClauseOfValue
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SameFactorDegreeClauseOfValue
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:01:37.179233+00:00
-- url     : https://prove2.me/theorems/56460df2-869e-4611-b23b-7b2a7d6da30b
-- title:
--   Same Factor Degree Clause Of Value
-- statement:
--   Definitions and structural lemmas for Same Factor Degree Clause Of Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SameFactorDegreeClauseOfValue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset FlagEq DegreeValueAlt
noncomputable section
def SameFactorDegreeClause.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f
end
end GroundTheory.Heights₂.Heights.RestTerms


