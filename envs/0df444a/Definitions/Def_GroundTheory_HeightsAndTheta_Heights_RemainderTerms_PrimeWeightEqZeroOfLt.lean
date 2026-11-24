-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:35.883968+00:00
-- url     : https://prove2.me/theorems/776ca92d-310d-421f-9bd6-22c512cb0f77
-- title:
--   Prime Weight Eq Zero Of Lt
-- statement:
--   Definitions and structural lemmas for Prime Weight Eq Zero Of Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
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
namespace RestTerms
open Finset
noncomputable section
namespace Elem
def primeWeight (B : ℝ) (i : ℕ) : ℝ := if i.Prime ∧ B < i then Real.log i else 0
end Elem
namespace Elem
def phiT (t : ℝ) : ℝ := (1 + Real.log t) / t
def intWeight (B₀ : ℝ) (m : ℕ) : ℝ := if B₀ < m then Real.log m / (m : ℝ) ^ 2 else 0
end Elem
end
end RestTerms
end GroundTheory.Heights₂.Heights


