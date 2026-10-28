-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
-- name    : IntMul_Kappa_R8_Data_BitOppbankKAlgebra
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:00:34.091476+00:00
-- url     : https://prove2.me/theorems/312e86ee-eb6b-4e55-b58a-a912e640b9f4
-- title:
--   KAlgebra: conjugated Kronecker projector idempotence
-- statement:
--   Idempotence of densified conjugated Kronecker projectors \(K(S,S^{-1};A,B)=S(A\otimes B)S^{-1}\) when \(A,B\) are idempotent and \(S\) is invertible, including the rank-one label case \(\mathrm{Pl}_a\otimes\mathrm{Pl}_s\).
--
--   **Formalization Note.** Supporting algebra for OneRunPE2 / PE inhabitance.

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# Algebra of conjugated Kronecker projectors `K S Si A B`
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.KAlgebra

open Matrix
open scoped Kronecker
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

theorem kronecker_mul_idem {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℚ) (hA : A * A = A) (hB : B * B = B) :
    (A ⊗ₖ B) * (A ⊗ₖ B) = A ⊗ₖ B := by
  have h := (mul_kronecker_mul A A B B).symm
  -- h : A ⊗ₖ B * A ⊗ₖ B = (A * A) ⊗ₖ (B * B)
  simpa [hA, hB] using h

theorem K_idem (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (_hS : S * Si = 1) (hSi : Si * S = 1) (A B : M23)
    (hA : A * A = A) (hB : B * B = B) :
    K S Si A B * K S Si A B = K S Si A B := by
  unfold K
  calc
    S * (A ⊗ₖ B) * Si * (S * (A ⊗ₖ B) * Si)
        = S * (A ⊗ₖ B) * (Si * S) * (A ⊗ₖ B) * Si := by
            simp only [Matrix.mul_assoc]
    _ = S * (A ⊗ₖ B) * (A ⊗ₖ B) * Si := by simp [hSi, Matrix.mul_assoc]
    _ = S * ((A ⊗ₖ B) * (A ⊗ₖ B)) * Si := by simp [Matrix.mul_assoc]
    _ = S * (A ⊗ₖ B) * Si := by rw [kronecker_mul_idem A B hA hB]

theorem K_Pl_Pl_idem (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a s : ℕ} (ha : a < 1771) (hs : s < 1771) :
    K S Si (Pl a) (Pl s) * K S Si (Pl a) (Pl s) = K S Si (Pl a) (Pl s) :=
  K_idem S Si hS hSi (Pl a) (Pl s) (Pl_idem ha) (Pl_idem hs)

end IntMul.Kappa.R8.Bit.Oppbank.KAlgebra


