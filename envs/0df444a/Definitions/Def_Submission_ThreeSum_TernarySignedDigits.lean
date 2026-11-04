-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySignedDigits
-- name    : Submission_ThreeSum_TernarySignedDigits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:40.417957+00:00
-- url     : https://prove2.me/theorems/84266352-9d91-4fdc-a173-234eea894afb
-- title:
--   Ternary Signed Digits
-- statement:
--   Definitions and structural lemmas for Ternary Signed Digits, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
def quotient (b x j : ℕ) : ℕ := x/b^j
def digit (b x j : ℕ) : ℕ := quotient b x j%b
def carryNat (b x y j : ℕ) : ℕ := quotient b (x+y) j-(quotient b x j+quotient b y j)
theorem carryNat_le_one (b x y j : ℕ) : carryNat b x y j ≤ 1 := by
  have h := Nat.add_div_le_div_add_div_add_one x y (b^j)
  unfold carryNat quotient
  omega
def evaluate (b J : ℕ) (f : ℕ → ℤ) : ℤ := ∑ j ∈ range J, f j*(b : ℤ)^j
abbrev CarryWord (J : ℕ) := Fin (J+1) → Fin 2
def carryAt {J : ℕ} (c : CarryWord J) (j : ℕ) : ℤ :=
  if hj : j<J+1 then ((c ⟨j,hj⟩).val : ℤ) else 0
def ValidCarry {J : ℕ} (c : CarryWord J) : Prop := carryAt c 0=0 ∧ carryAt c J=0
instance {J : ℕ} (c : CarryWord J) : Decidable (ValidCarry c) := by unfold ValidCarry; infer_instance
def canonicalCarry (b x y J : ℕ) : CarryWord J := fun j =>
  ⟨carryNat b x y j,by have := carryNat_le_one b x y j; omega⟩
def DigitRelation (b J x y z : ℕ) (c : CarryWord J) : Prop :=
  ∀ j : Fin J, (digit b x j : ℤ)+(digit b y j : ℤ)+carryAt c j=
    (digit b z j : ℤ)+(b : ℤ)*carryAt c (j+1)
end ThreeSum.TernarySignedDigits


