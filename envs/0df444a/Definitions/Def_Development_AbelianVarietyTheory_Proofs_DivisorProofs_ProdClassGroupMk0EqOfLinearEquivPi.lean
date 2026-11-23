-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:40.703014+00:00
-- url     : https://prove2.me/theorems/574619ba-8006-4bc4-ad7b-8ed170efd5ca
-- title:
--   Prod Class Group Mk0 Eq Of Linear Equiv Pi
-- statement:
--   Definitions and structural lemmas for Prod Class Group Mk0 Eq Of Linear Equiv Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
namespace GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
def mat {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i)) (a : (i : ι) → I i) :
    Matrix ι ι R := fun j i => (φ (Pi.single i (a i)) j : R)
end GlobalTheory.DetClass


