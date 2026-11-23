-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_E8invTranspose
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_E8invTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:55.596369+00:00
-- url     : https://prove2.me/theorems/9dc0caf2-c15f-4b10-91d6-de342916ac50
-- title:
--   E8inv Transpose
-- statement:
--   Definitions and structural lemmas for E8inv Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/E8invTranspose.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Theorems.Thm_GlobalTheory_e8_mul_e8inv
import Theorems.Thm_GlobalTheory_e8_transpose
import Theorems.Thm_GlobalTheory_e8inv_mul_e8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mum.E8Ring
open Matrix
theorem E8inv_transpose : GlobalTheory.E8invᵀ = GlobalTheory.E8inv := by decide
def O8 : Type := Matrix (Fin 8) (Fin 8) ℤ
instance : Ring O8 := inferInstanceAs (Ring (Matrix (Fin 8) (Fin 8) ℤ))
def adj (a : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := GlobalTheory.E8inv * aᵀ * GlobalTheory.E8
theorem adj_adj (a : Matrix (Fin 8) (Fin 8) ℤ) : adj (adj a) = a := by
  unfold adj
  rw [transpose_mul, transpose_mul, transpose_transpose, GlobalTheory.e8_transpose, E8inv_transpose]
  simp only [Matrix.mul_assoc]
  rw [GlobalTheory.e8inv_mul_e8, Matrix.mul_one, ← Matrix.mul_assoc, GlobalTheory.e8inv_mul_e8, Matrix.one_mul]
theorem adj_mul (a b : Matrix (Fin 8) (Fin 8) ℤ) : adj (a * b) = adj b * adj a := by
  unfold adj
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GlobalTheory.E8 GlobalTheory.E8inv, GlobalTheory.e8_mul_e8inv, Matrix.one_mul]
theorem adj_add (a b : Matrix (Fin 8) (Fin 8) ℤ) : adj (a + b) = adj a + adj b := by
  unfold adj
  rw [transpose_add, Matrix.mul_add, Matrix.add_mul]
instance : StarRing O8 where
  star a := adj a
  star_involutive a := adj_adj a
  star_mul a b := adj_mul a b
  star_add a b := adj_add a b
def e8 : O8 := Matrix.single (0 : Fin 8) (0 : Fin 8) (1 : ℤ)
def f8 : O8 := -Matrix.single (2 : Fin 8) (0 : Fin 8) (1 : ℤ)
end GlobalTheory.Mum.E8Ring


