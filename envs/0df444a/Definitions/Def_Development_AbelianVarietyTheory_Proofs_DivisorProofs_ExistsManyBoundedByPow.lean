-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:28.731099+00:00
-- url     : https://prove2.me/theorems/9a14b491-6fda-41fe-bdc5-b4d999c68eb5
-- title:
--   Exists Many Bounded By Pow
-- statement:
--   Definitions and structural lemmas for Exists Many Bounded By Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean

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
namespace GlobalTheory.Nef.PolesOfT
open Polynomial
variable {k F : Type} [Field k] [Field F] [Algebra k F]
abbrev Mx (t : F) (v : Place k F) : WithZero (Multiplicative ℤ) := max 1 (v.1 t)
end GlobalTheory.Nef.PolesOfT
namespace GlobalTheory.Nef.PolesOfT
open Polynomial
variable {k F : Type} [Field k] [Field F] [Algebra k F]
end GlobalTheory.Nef.PolesOfT
namespace GlobalTheory.Nef
open Polynomial PolesOfT
end GlobalTheory.Nef


