-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HankelDeterminantIntegralOfQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HankelDeterminantIntegralOfQuotient
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:55.567276+00:00
-- url     : https://prove2.me/theorems/67ed9fda-2a81-4b6c-b0ed-ae989e7a2bba
-- title:
--   Hankel Determinant Integral Of Quotient
-- statement:
--   Definitions and structural lemmas for Hankel Determinant Integral Of Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HankelDeterminantIntegralOfQuotient.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
namespace GlobalTheory.Nef
open PowerSeries Finset
end GlobalTheory.Nef


