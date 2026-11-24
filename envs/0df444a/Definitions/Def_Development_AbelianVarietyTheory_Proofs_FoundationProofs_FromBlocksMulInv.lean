-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:00.2201+00:00
-- url     : https://prove2.me/theorems/43ac24c9-b5e8-4057-8def-3ae17741236e
-- title:
--   From Blocks Mul Inv
-- statement:
--   Definitions and structural lemmas for From Blocks Mul Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
theorem fromBlocks_mul_inv (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) *
      fromBlocks ((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        (-(((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * b *
          ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))) 0
        ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1 := by
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, neg_add_cancel, neg_zero, fromBlocks_one]
def blockUnit (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    GL (Fin r ⊕ Fin t) k :=
  ⟨_, _, fromBlocks_mul_inv p b d, mul_eq_one_comm.1 (fromBlocks_mul_inv p b d)⟩
def blockPar (t : ℕ) (Q : Subgroup (GL (Fin r) k)) : Subgroup (GL (Fin r ⊕ Fin t) k) where
  carrier := {h | ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
    (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
      fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k)}
  one_mem' := ⟨1, Q.one_mem, 0, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨p, hp, b, d, e⟩ ⟨p', hp', b', d', e'⟩
    refine ⟨p * p', Q.mul_mem hp hp', (p : Matrix (Fin r) (Fin r) k) * b' +
      b * (d' : Matrix (Fin t) (Fin t) k), d * d', ?_⟩
    rw [Units.val_mul, e, e', fromBlocks_multiply]
    simp
  inv_mem' := by
    rintro x ⟨p, hp, b, d, e⟩
    exact ⟨p⁻¹, Q.inv_mem hp, _, d⁻¹,
      Units.inv_eq_of_mul_eq_one_right (e ▸ fromBlocks_mul_inv p b d)⟩
end GlobalTheory.SingleBlock


