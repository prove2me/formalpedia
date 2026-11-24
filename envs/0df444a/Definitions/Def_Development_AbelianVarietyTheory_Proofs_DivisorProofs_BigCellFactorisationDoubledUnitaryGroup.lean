-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:57.201714+00:00
-- url     : https://prove2.me/theorems/693a0358-1627-4907-a5d2-2fd5cbdef81e
-- title:
--   Big Cell Factorisation Doubled Unitary Group
-- statement:
--   Definitions and structural lemmas for Big Cell Factorisation Doubled Unitary Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
namespace GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
theorem e3 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * dbl J =
    J * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) := by
  simp [dbl, fromCols_mul_fromBlocks, mul_fromCols]
theorem e4 (J : Matrix β β R) : dbl J * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) =
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * J := by
  simp [dbl, fromBlocks_mul_fromRows, fromRows_mul]
theorem e6 (J : Matrix β β R) : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * J * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * J * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) =
    (2 : R) • dbl J := by
  simp only [Matrix.mul_assoc, fromRows_mul, mul_fromCols, fromRows_fromCols_eq_fromBlocks, dbl, fromBlocks_smul]
  simp
  rw [fromBlocks_add]
  congr 1 <;> ext i j <;> simp <;> ring
theorem e7 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * dbl J * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) = 0 := by
  simp [dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
theorem e5 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * dbl J * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = 0 := by
  simp [dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
variable [Invertible (2 : R)]
section Abstract
variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)
end Abstract
section Abstract2
variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)
end Abstract2
end GlobalTheory.BigCell


