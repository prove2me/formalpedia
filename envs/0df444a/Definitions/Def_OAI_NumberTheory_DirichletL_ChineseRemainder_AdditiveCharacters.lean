-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
-- name    : OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:16:22.534467+00:00
-- url     : https://prove2.me/theorems/3cd4a159-4c39-4435-9190-7254b0a5651f
-- title:
--   Additive Characters
-- statement:
--   Definitions and structural lemmas for Additive Characters, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
def crossDen (c₀ : R) : List (R × R) → R
  | [] => c₀
  | (p, _) :: xs => crossDen c₀ xs * p
def crossNum (a c₀ : R) : List (R × R) → R
  | [] => a
  | (p, h) :: xs => crossNum a c₀ xs * p + h * crossDen c₀ xs
def GoodRows (c₀ : R) : List (R × R) → Prop
  | [] => True
  | (p, h) :: xs =>
      GoodRows c₀ xs ∧ IsCoprime h p ∧ IsCoprime (crossDen c₀ xs) p
end ShortDraftCRT
namespace ShortDraftDescent
end ShortDraftDescent
namespace ShortDraftTrace
open Complex
open scoped ComplexConjugate
section Generic
variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)
include hω hconj
end Generic
noncomputable def ω₃ : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2
theorem omega_sq : ω₃ ^ 2 = -ω₃ - 1 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
  have hquad : ω₃ ^ 2 + ω₃ + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold ω₃
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  linear_combination hquad
noncomputable def breveE : AddChar ℂ ℂ where
  toFun z := Complex.exp (2 * Real.pi * Complex.I * (z + conj z))
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    have harg : 2 * Real.pi * Complex.I * (z + w + conj (z + w)) =
        2 * Real.pi * Complex.I * (z + conj z) +
          2 * Real.pi * Complex.I * (w + conj w) := by
      rw [map_add]
      ring
    rw [harg, Complex.exp_add]
def eisensteinSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * ω₃}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * omega_sq
noncomputable def lamEis : eisensteinSubring :=
  ⟨1 + 2 * ω₃, ⟨1, 2, by norm_num⟩⟩
end ShortDraftTrace
end OAI


