-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:44.69042+00:00
-- url     : https://prove2.me/theorems/605e0a5d-ed31-491c-8f52-ebb84377503b
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
def signPhase (a : ZMod 2) : ZMod 4 := 2 * (a.val : ZMod 4)
@[simp] lemma signPhase_zero : signPhase 0 = 0 := rfl
@[simp] lemma signPhase_one : signPhase 1 = 2 := rfl
lemma signPhase_add (a b : ZMod 2) : signPhase (a + b) = signPhase a + signPhase b := by
  revert a b; decide
@[simp] lemma signPhase_eq_zero_iff {a : ZMod 2} : signPhase a = 0 ↔ a = 0 := by
  revert a; decide
@[simp] lemma neg_signPhase (a : ZMod 2) : -signPhase a = signPhase a := by revert a; decide
@[simp] lemma signPhase_add_self (a : ZMod 2) : signPhase a + signPhase a = 0 := by
  revert a; decide
lemma bit_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide
lemma bits_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i; exact bit_add_self (v i)
structure PauliString (n : ℕ) where
  /-- The `X`-part: `x i = 1` where the string carries an `X` or a `Y`. -/
  x : Fin n → ZMod 2
  /-- The `Z`-part: `z i = 1` where the string carries a `Z` or a `Y`. -/
  z : Fin n → ZMod 2
  /-- The phase exponent: the string is `i^{phase} X^{x} Z^{z}`. -/
  phase : ZMod 4
namespace PauliString
variable {n : ℕ} {s t u : PauliString n}
@[ext]
theorem ext' {s t : PauliString n} (hx : s.x = t.x) (hz : s.z = t.z)
    (hp : s.phase = t.phase) : s = t := by
  cases s; cases t; simp_all
instance : DecidableEq (PauliString n) := fun s t =>
  decidable_of_iff (s.x = t.x ∧ s.z = t.z ∧ s.phase = t.phase)
    ⟨fun h => ext' h.1 h.2.1 h.2.2, fun h => by subst h; exact ⟨rfl, rfl, rfl⟩⟩
instance : Mul (PauliString n) where
  mul s t := ⟨s.x + t.x, s.z + t.z, s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x)⟩
@[simp] lemma mul_x (s t : PauliString n) : (s * t).x = s.x + t.x := rfl
@[simp] lemma mul_z (s t : PauliString n) : (s * t).z = s.z + t.z := rfl
lemma mul_phase (s t : PauliString n) :
    (s * t).phase = s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x) := rfl
instance : One (PauliString n) where one := ⟨0, 0, 0⟩
@[simp] lemma one_x : (1 : PauliString n).x = 0 := rfl
@[simp] lemma one_z : (1 : PauliString n).z = 0 := rfl
@[simp] lemma one_phase : (1 : PauliString n).phase = 0 := rfl
instance : Inv (PauliString n) where
  inv s := ⟨s.x, s.z, -s.phase + signPhase (s.z ⬝ᵥ s.x)⟩
@[simp] lemma inv_x (s : PauliString n) : s⁻¹.x = s.x := rfl
@[simp] lemma inv_z (s : PauliString n) : s⁻¹.z = s.z := rfl
instance : Group (PauliString n) where
  mul_assoc s t u := by
    refine ext' ?_ ?_ ?_
    · simp [add_assoc]
    · simp [add_assoc]
    · simp only [mul_phase, mul_z, mul_x, add_dotProduct, dotProduct_add, signPhase_add]
      ring
  one_mul s := by refine ext' ?_ ?_ ?_ <;> simp [mul_phase]
  mul_one s := by refine ext' ?_ ?_ ?_ <;> simp [mul_phase]
  inv_mul_cancel s := by
    refine ext' ?_ ?_ ?_
    · simpa using bits_add_self s.x
    · simpa using bits_add_self s.z
    · change -s.phase + signPhase (s.z ⬝ᵥ s.x) + s.phase + signPhase (s.z ⬝ᵥ s.x)
        = (1 : PauliString n).phase
      rw [show -s.phase + signPhase (s.z ⬝ᵥ s.x) + s.phase + signPhase (s.z ⬝ᵥ s.x)
          = signPhase (s.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ s.x) by ring]
      simp
instance : Star (PauliString n) where star s := s⁻¹
instance : InvolutiveStar (PauliString n) where
  star_involutive s := inv_inv s
instance : StarMul (PauliString n) where
  star_mul s t := mul_inv_rev s t
def sympForm (s t : PauliString n) : ZMod 2 := s.x ⬝ᵥ t.z + s.z ⬝ᵥ t.x
def phaseMul (k : ZMod 4) (s : PauliString n) : PauliString n := ⟨s.x, s.z, s.phase + k⟩
def X1 : PauliString 1 := ⟨1, 0, 0⟩
def Z1 : PauliString 1 := ⟨0, 1, 0⟩
def Y1 : PauliString 1 := ⟨1, 1, 1⟩
end PauliString
end Lean4LPD


