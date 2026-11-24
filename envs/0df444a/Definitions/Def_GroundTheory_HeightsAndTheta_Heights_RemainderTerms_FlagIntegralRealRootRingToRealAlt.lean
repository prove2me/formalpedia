-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:59.625213+00:00
-- url     : https://prove2.me/theorems/f42dd167-6543-4458-93c4-040d078e955b
-- title:
--   Flag Integral Real Root Ring To Real Alt
-- statement:
--   Definitions and structural lemmas for Flag Integral Real Root Ring To Real Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
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
open MvPolynomial Finset
noncomputable section
namespace TermBoundEq
def coeffMap {σ : Type*} (φ : Module.Dual ℚ ℝ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ d ∈ P.support, monomial d (φ (coeff d P))
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)
end TermBoundEq
end
end GroundTheory.Heights₂.Heights.RestTerms


