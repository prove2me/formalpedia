-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
-- name    : LeanPool_LowWeightPauliDynamics_Rotation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:47.512089+00:00
-- url     : https://prove2.me/theorems/1ab200a8-e10e-45f9-b47e-7f368b8f4e27
-- title:
--   Rotation
-- statement:
--   Definitions and structural lemmas for Rotation, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean

module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}
noncomputable def rot (G : A) (θ : ℝ) : A :=
  (Real.cos (θ / 2) : ℂ) • 1 + (Complex.I * Real.sin (θ / 2)) • G
@[simp]
lemma rot_zero : rot G 0 = 1 := by
  simp [rot]
lemma mul_I_mul_I (a b : ℂ) : Complex.I * a * (Complex.I * b) = -(a * b) := by
  rw [show Complex.I * a * (Complex.I * b) = Complex.I * Complex.I * (a * b) by ring,
    Complex.I_mul_I]
  ring
lemma rot_mul_rot (hG : G * G = 1) : rot G θ₁ * rot G θ₂ = rot G (θ₁ + θ₂) := by
  have hhalf : (θ₁ + θ₂) / 2 = θ₁ / 2 + θ₂ / 2 := by ring
  have hc : ((Real.cos ((θ₁ + θ₂) / 2) : ℝ) : ℂ)
      = (Real.cos (θ₁ / 2) : ℂ) * (Real.cos (θ₂ / 2) : ℂ)
        - (Real.sin (θ₁ / 2) : ℂ) * (Real.sin (θ₂ / 2) : ℂ) := by
    rw [hhalf, Real.cos_add]; push_cast; ring
  have hs : ((Real.sin ((θ₁ + θ₂) / 2) : ℝ) : ℂ)
      = (Real.sin (θ₁ / 2) : ℂ) * (Real.cos (θ₂ / 2) : ℂ)
        + (Real.cos (θ₁ / 2) : ℂ) * (Real.sin (θ₂ / 2) : ℂ) := by
    rw [hhalf, Real.sin_add]; push_cast; ring
  simp only [rot, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hG, mul_I_mul_I, hc, hs]
  module
lemma rot_mul_eq_mul_rot_neg (h : G * P = -(P * G)) : rot G θ * P = P * rot G (-θ) := by
  have hPG : P * G = -(G * P) := by rw [h, neg_neg]
  simp only [rot, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    neg_div, Real.cos_neg, Real.sin_neg, hPG]
  push_cast
  module
theorem rot_conj_of_anticommute (hG : G * G = 1) (h : G * P = -(P * G)) :
    rot G θ * P * rot G (-θ)
      = (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) := by
  rw [mul_assoc, ← rot_mul_eq_mul_rot_neg h, ← mul_assoc, rot_mul_rot hG]
  simp only [rot, add_mul, smul_mul_assoc, one_mul, show (θ + θ) / 2 = θ by ring]
section Star
variable [StarRing A] [StarModule ℂ A]
end Star
example (n : ℕ) (G P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (θ : ℝ)
    (hG : G * G = 1) (h : G * P = -(P * G)) :
    rot G θ * P * rot G (-θ)
      = (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) :=
  rot_conj_of_anticommute hG h
end Lean4LPD


