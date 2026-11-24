-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_TenNinthsLe
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_TenNinthsLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:25.029616+00:00
-- url     : https://prove2.me/theorems/2bd3d709-3f65-4f48-9801-9d2968622bc1
-- title:
--   Ten Ninths Le
-- statement:
--   Definitions and structural lemmas for Ten Ninths Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/TenNinthsLe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
open Finset GroundTheory.Heights₂.Heights.RestTerms.Elem
noncomputable section
namespace IntegerTail
def w (m : ℕ) : ℝ := Real.log m / (m : ℝ) ^ 2
end IntegerTail
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms


