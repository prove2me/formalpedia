-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:28.491072+00:00
-- url     : https://prove2.me/theorems/b122bcdc-932c-4203-b44d-1f64f9ab0fd1
-- title:
--   Card Zmod Tensor Eq Card Quot Prime Multiples
-- statement:
--   Definitions and structural lemmas for Card Zmod Tensor Eq Card Quot Prime Multiples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
namespace GlobalTheory
noncomputable def intQuotSpanNatLinearEquivZMod (p : ℕ) :
    (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃ₗ[ℤ] ZMod p :=
  LinearEquiv.ofBijective (Int.quotientSpanNatEquivZMod p).toRingHom.toIntAlgHom.toLinearMap
    (Int.quotientSpanNatEquivZMod p).bijective
end GlobalTheory


