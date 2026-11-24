-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:17.014352+00:00
-- url     : https://prove2.me/theorems/ad8d1241-47a9-433c-aefa-0852c2aeee49
-- title:
--   Cyc Eval Eq Add Mul Of Cycle
-- statement:
--   Definitions and structural lemmas for Cyc Eval Eq Add Mul Of Cycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
section SlopeTestRemainingChoices
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
end SlopeTestRemainingChoices
section VNum
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end VNum
end
end GroundTheory.Heights₂.Heights.NumbersDVR


