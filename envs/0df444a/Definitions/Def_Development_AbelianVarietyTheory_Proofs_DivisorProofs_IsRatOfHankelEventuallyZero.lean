-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:01.899199+00:00
-- url     : https://prove2.me/theorems/d270025f-44fe-49e4-a0ea-0637dad4e57f
-- title:
--   Is Rat Of Hankel Eventually Zero
-- statement:
--   Definitions and structural lemmas for Is Rat Of Hankel Eventually Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean

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
namespace GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)
def ev : F[X] →ₗ[F] F := Polynomial.lsum fun i => c i • LinearMap.id
end GlobalTheory.Nef.Kron
namespace GlobalTheory.Nef
end GlobalTheory.Nef


