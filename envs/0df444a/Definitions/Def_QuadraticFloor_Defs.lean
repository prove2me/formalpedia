-- Prove2me | Definitions.Def_QuadraticFloor_Defs
-- name    : QuadraticFloor_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:42:42.349213+00:00
-- url     : https://prove2.me/theorems/41989f38-74fe-51e7-822b-8681cf8ac526
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/QuadraticFloor; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuadraticFloor: quadratic floor sums and the trace of a quartic Bernoulli number development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuadraticFloor
open Finset
def floorSum (A B C : ℤ) (p : ℕ) : ℤ :=
  ∑ n ∈ range p, (((A * n ^ 2 + B * n + C) / (p : ℤ)).negOnePow : ℤ)
def Admissible (A : ℕ) (B C : ℤ) : Prop :=
  Odd B ∧ Int.gcd B A = 1 ∧ 1 ≤ B ^ 2 - 4 * A * C ∧ B ^ 2 - 4 * A * C < 4 * A
def eta (p x : ℕ) : ℤ := if Even x then 0 else jacobiSym (-8 * p) x
noncomputable def bern (q : ℕ) (f : ℕ → ℂ) : ℂ :=
  (1 / (q : ℂ)) * ∑ x ∈ Icc 1 q, (x : ℂ) * f x
open Classical in
/-- `ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ`, where `ψ(-1) = (-1)^{δ_ψ}`; here `χ_{-4}^1 = χ_{-4}` and
`χ_{-4}^0 = χ_{-4}²` is the principal character modulo `4`. -/
noncomputable def vartheta {A : ℕ} (p : ℕ) (ψ : DirichletCharacter ℂ A) (x : ℕ) : ℂ :=
  (eta p x : ℂ) *
    (if ψ (-1) = -1 then (ZMod.χ₄ (x : ZMod 4) : ℂ) else (ZMod.χ₄ (x : ZMod 4) : ℂ) ^ 2) *
    ψ (x : ZMod A)
def lg5 (x : ZMod 5) : ℕ := if x = 2 then 1 else if x = 4 then 2 else if x = 3 then 3 else 0
noncomputable def xiFun (x : ZMod 5) : ℂ := if x = 0 then 0 else Complex.I ^ lg5 x
noncomputable def xi : DirichletCharacter ℂ 5 where
  toFun := xiFun
  map_one' := by
    simp only [xiFun, show (1 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 1 = 0 by decide,
      pow_zero]
  map_mul' := by
    intro a b
    by_cases ha : a = 0
    · simp [xiFun, ha]
    by_cases hb : b = 0
    · simp [xiFun, hb]
    have hab : a * b ≠ 0 := by revert a b; decide
    have hlg : lg5 (a * b) % 4 = (lg5 a + lg5 b) % 4 := by revert a b; decide
    simp only [xiFun, ha, hb, hab, ite_false, ← pow_add]
    rw [← Nat.mod_add_div (lg5 (a * b)) 4, ← Nat.mod_add_div (lg5 a + lg5 b) 4, hlg, pow_add,
      pow_add, pow_mul, pow_mul, Complex.I_pow_four, one_pow, one_pow]
  map_nonunit' := by
    intro a ha
    by_cases h0 : a = 0
    · simp [xiFun, h0]
    · exfalso
      apply ha
      obtain ⟨b, hb⟩ : ∃ b : ZMod 5, a * b = 1 := by revert a; decide
      exact IsUnit.of_mul_eq_one b hb
noncomputable def Theta (p x : ℕ) : ℂ :=
  (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) * xi (x : ZMod 5)
def zB (B : ℤ) (p : ℕ) : ℤ :=
  if ∃ j ∈ range ((p + 1) / 2), (p : ℤ) ∣ B ^ 2 + 40 * j then 1 else 0
noncomputable def osum (t : ℤ) (g : ℤ → ℤ) : ℤ :=
  if 0 ≤ t then ∑ j ∈ Ico 0 t, g j else -∑ j ∈ Ico t 0, g j
end QuadraticFloor


