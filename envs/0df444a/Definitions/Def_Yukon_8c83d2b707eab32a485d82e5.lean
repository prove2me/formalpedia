-- Prove2me | Definitions.Def_Yukon_8c83d2b707eab32a485d82e5
-- name    : Yukon_8c83d2b707eab32a485d82e5
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:37:39.13269+00:00
-- url     : https://prove2.me/theorems/1962787d-823c-4189-b5be-a0637f3b8e74
-- title:
--   YukonModule.CompPoly.Fields.Basic.part0
-- statement:
--   Source module CompPoly.Fields.Basic.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/Basic.lean
--
--   provider-v8:4c46e91d3c5e598b23d7c8461ed8f0d2af603d200f44fbe2371385585402e3bc
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODo0YzQ2ZTkxZDNjNWU1OThiMjNkN2M4NDYxZWQ4ZjBkMmFmNjAzZDIwMGY0NGZiZTIzNzEzODU1ODU0MDJlM2JjIiwiaGFzaCI6ImUwNTJmY2IxNjNlNWJiMmJiMzA2NzU0MjYwMzIzNDZlZGMxNzYxNjJiMjA5ZTFmOTAxYTJkMDJjZTBmMmU1MDYiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzhjODNkMmI3MDdlYWIzMmE0ODVkODJlNSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Non-binary fields and polynomial utilities

This module defines `NonBinaryField` (fields with char ≠ 2) and provides lemmas about
polynomial composition with `-X` and `X²`.
-/

@[expose] public section

/-- A type class for fields of characteristic ≠ 2, extending `Field`. -/
class NonBinaryField (F : Type*) extends Field F where
  char_neq_2 : (2 : F) ≠ 0

export NonBinaryField (char_neq_2)

attribute [simp] char_neq_2

section NonBinaryField

variable {F : Type*} [NonBinaryField F]

@[simp]
lemma two_mul_inv_two : (2 : F) * 2⁻¹ = 1 := by simp

@[simp]
lemma inv_two_mul_two : 2⁻¹ * (2 : F) = 1 := by simp

end NonBinaryField

section

variable {F : Type*} [Field F]

open Polynomial

private lemma coeffs_of_comp_minus_x_pos_degree {f : Polynomial F} {n : ℕ} (h : 0 < f.degree) :
    (f.comp (-X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
  revert n
  apply degree_pos_induction_on (h0 := h) (P := fun f => _)
  · aesop (add simp coeff_X)
  · rintro _ _ _ (_ | _) <;> aesop (add simp [Nat.even_add_one, Nat.even_iff])
  · rintro _ _ _ _ (_ | _) <;> aesop

theorem coeffs_of_comp_minus_x {f : Polynomial F} {n : ℕ} :
    (f.comp (-X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
    by_cases hpos : 0 < f.degree
    · rw [coeffs_of_comp_minus_x_pos_degree hpos]
    · have : f.natDegree = 0 := by aesop (add simp natDegree_pos_iff_degree_pos.symm)
      cases n <;> aesop (add simp natDegree_eq_zero)

private lemma comp_x_square_coeff_pos_deg {f : Polynomial F} {n : ℕ} (h : 0 < f.degree) :
    (f.comp (X * X)).coeff n = if Even n then f.coeff (n / 2) else 0 := by
  revert n
  apply degree_pos_induction_on (h0 := h) (P := fun f => _)
  · rintro _ _ (_ | n) <;>
    aesop (add simp [coeff_X, Even]) (add safe [(by existsi 1), (by omega)])
  · rintro _ _ _ (_ | _ | n) <;> try simp [←mul_assoc]
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    split <;> aesop (add safe (by omega)) (add simp [Nat.even_iff])
  · rintro _ _ _ _ (_ | _ | n) <;> try simp_all
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    simp_all only [coeff_C_succ, add_zero]

theorem comp_x_square_coeff {f : Polynomial F} {n : ℕ} :
    (f.comp (X * X)).coeff n = if Even n then f.coeff (n / 2) else 0 := by
  by_cases hpos : 0 < f.degree
  · rw [comp_x_square_coeff_pos_deg hpos]
  · obtain ⟨_, hx⟩ :=
      show ∃ x, C x = f by
        aesop (add simp [natDegree_pos_iff_degree_pos.symm, natDegree_eq_zero])
    rcases n with _ | _ | n <;> (subst hx; simp_all)
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    aesop

lemma eq_poly_deg_one {a b c d : F} {x₁ x₂ : F}
    (h1 : a + b * x₁ = c + d * x₁)
    (h2 : a + b * x₂ = c + d * x₂)
    (h1_2 : x₁ ≠ x₂) :
    Polynomial.C a + Polynomial.C b * Polynomial.X =
      Polynomial.C c + Polynomial.C d * Polynomial.X := by
  by_cases h_b_d : b = d
  · aesop
  · exact absurd
            (by apply mul_left_cancel₀ (sub_ne_zero_of_ne (show d ≠ b by aesop))
                linear_combination -(1 * h1) + h2)
            h1_2

end


