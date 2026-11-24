-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:55.848927+00:00
-- url     : https://prove2.me/theorems/e75eb135-d380-4f90-acc8-0ba3dbb30633
-- title:
--   Is Power Sum Decomposition Homogeneous Component
-- statement:
--   Definitions and structural lemmas for Is Power Sum Decomposition Homogeneous Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
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
def rootRingToReal (f N j k : ℕ) (h : N = j + k) : RootRing f N →+* IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  (rename (R := ℝ) (Prod.map id (finCongr h))).toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℝ))
end
end GroundTheory.Heights₂.Heights.RestTerms


