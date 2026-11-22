-- Prove2me | solution 1 for Auto.sum_three_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:50:22.617994+00:00
-- url     : https://prove2.me/submissions/8a3f8aa3-6998-4c09-b2db-83fd148f76db

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution (v : Fin 3) (p : Fin 3 → ℝ) :
    p 0 + p 1 + p 2 = p v + p (v + 1) + p (v - 1) ∧ p 0 + p 1 + p 2 = p v + p (v - 1) + p (v +
      1) ∧ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = p v ^ 2 + p (v + 1) ^ 2 + p (v - 1) ^ 2 ∧ p 0 ^ 2 + p 1 ^
      2 + p 2 ^ 2 = p v ^ 2 + p (v - 1) ^ 2 + p (v + 1) ^ 2 := by
  have : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
  rcases this with rfl | rfl | rfl
  · have h1 : (0 : Fin 3) + 1 = 1 := rfl
    have h2 : (0 : Fin 3) - 1 = 2 := rfl
    rw [h1, h2]; exact ⟨by ring, by ring, by ring, by ring⟩
  · have h1 : (1 : Fin 3) + 1 = 2 := rfl
    have h2 : (1 : Fin 3) - 1 = 0 := rfl
    rw [h1, h2]; exact ⟨by ring, by ring, by ring, by ring⟩
  · have h1 : (2 : Fin 3) + 1 = 0 := rfl
    have h2 : (2 : Fin 3) - 1 = 1 := rfl
    rw [h1, h2]; exact ⟨by ring, by ring, by ring, by ring⟩
end Auto
