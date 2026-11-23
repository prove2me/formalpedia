-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:19.887492+00:00
-- url     : https://prove2.me/theorems/285bae6a-35dc-4b33-afd9-3fac4cfd3105
-- title:
--   Weight Two Derivative Eisenstein Term Uniform Bound
-- statement:
--   Definitions and structural lemmas for Weight Two Derivative Eisenstein Term Uniform Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightTwoDerivativeEisensteinTermUniformBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory.WeightTwoSum.Bound
end GlobalTheory.WeightTwoSum.Bound


