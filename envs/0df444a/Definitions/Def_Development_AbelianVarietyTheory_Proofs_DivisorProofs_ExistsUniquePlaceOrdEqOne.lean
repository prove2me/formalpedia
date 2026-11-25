-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:07.379106+00:00
-- url     : https://prove2.me/theorems/912ecb0d-2b6d-4463-82d5-5d232e4e3791
-- title:
--   Exists Unique Place Ord Eq One
-- statement:
--   Definitions and structural lemmas for Exists Unique Place Ord Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniquePlaceOrdEqOne.lean

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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef
open Polynomial
variable {k L : Type} [Field k] [Field L] [Algebra k L]
end GlobalTheory.Nef
namespace GlobalTheory.Nef
open Polynomial
end GlobalTheory.Nef


