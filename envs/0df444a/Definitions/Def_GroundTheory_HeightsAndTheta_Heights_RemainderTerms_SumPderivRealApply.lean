-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:38.550708+00:00
-- url     : https://prove2.me/theorems/8b710559-e613-4979-86ff-6f1f0f8856b5
-- title:
--   Sum Pderiv Real Apply
-- statement:
--   Definitions and structural lemmas for Sum Pderiv Real Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
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
namespace TwoCasesDerivatives
open MvPolynomial Finset
noncomputable section
variable (f j k : ℕ)
def sumPderivReal {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k)) :
    Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :=
  ∑ l ∈ s, pderiv (τ, g l)
end
end TwoCasesDerivatives
open MvPolynomial Finset TwoCasesDerivatives
end GroundTheory.Heights₂.Heights.RestTerms


