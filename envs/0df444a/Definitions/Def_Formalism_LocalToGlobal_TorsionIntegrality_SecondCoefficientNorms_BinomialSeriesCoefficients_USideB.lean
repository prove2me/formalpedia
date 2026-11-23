-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:10.607874+00:00
-- url     : https://prove2.me/theorems/1de0a509-bf59-4de1-b975-b0d3a9633603
-- title:
--   USide B
-- statement:
--   Definitions and structural lemmas for USide B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
namespace Formalism.L2.Th1.C
namespace USideB
section SlopeTestRemainingChoices
variable {K : Type} [Field K]
end SlopeTestRemainingChoices
section FormalExponential
variable {K : Type} [Field K] [CharZero K]
end FormalExponential
end USideB
open USideB
section Main
end Main
namespace USideB
section Integral
variable {K : Type} [Field K]
def intSub (R : Subring K) : Subring (PowerSeries K) where
  carrier := {f | IntPS R f}
  mul_mem' := by
    intro f g hf hg n
    rw [PowerSeries.coeff_mul]
    exact R.sum_mem fun p _ => R.mul_mem (hf _) (hg _)
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  add_mem' := by
    intro f g hf hg n
    rw [map_add]
    exact R.add_mem (hf _) (hg _)
  zero_mem' := by
    intro n
    rw [map_zero]
    exact R.zero_mem
  neg_mem' := by
    intro f hf n
    rw [map_neg]
    exact R.neg_mem (hf _)
end Integral
end USideB
section Main2
end Main2
end Formalism.L2.Th1.C


