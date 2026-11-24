-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:23.016811+00:00
-- url     : https://prove2.me/theorems/beb4e652-0b66-4ad7-9c42-c5c2c8125699
-- title:
--   Deg Polynomial Is Homogeneous
-- statement:
--   Definitions and structural lemmas for Deg Polynomial Is Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
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
namespace RestBoundEq
def lieSign (bot b : Bool) (m : ℕ) : ℚ := if bot = b then (-1) ^ m else -1
end RestBoundEq
end
end GroundTheory.Heights₂.Heights.RestTerms


