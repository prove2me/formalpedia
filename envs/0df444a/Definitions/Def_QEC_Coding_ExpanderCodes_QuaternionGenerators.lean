-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
-- name    : QEC_Coding_ExpanderCodes_QuaternionGenerators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:43:20.269917+00:00
-- url     : https://prove2.me/theorems/094b9be0-d58e-45a5-9182-94fb38f8d592
-- title:
--   Quaternion Generators
-- statement:
--   Definitions and structural lemmas for Quaternion Generators, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
abbrev Model (epsilon y : K) := QuaternionAlgebra K epsilon 0 (1 + y)
def alpha (epsilon y : K) : Model epsilon y := ⟨0, 1, 0, 0⟩
def z (epsilon y : K) : Model epsilon y := ⟨0, 0, 1, 0⟩
def base (epsilon y : K) : Model epsilon y := ⟨1, 0, -(1 + y)⁻¹, 0⟩
def prime (epsilon y : K) : Model epsilon y := ⟨0, 1, 0, -(1 + y)⁻¹⟩
def alphaUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0) : (Model epsilon y)ˣ where
  val := alpha epsilon y
  inv := ⟨0, epsilon⁻¹, 0, 0⟩
  val_inv := by ext <;> simp [alpha, hEpsilon]
  inv_val := by ext <;> simp [alpha, hEpsilon]
def baseUnit (epsilon y : K) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (Model epsilon y)ˣ where
  val := base epsilon y
  inv := ⟨(1 + y) / y, 0, y⁻¹, 0⟩
  val_inv := by ext <;> simp [base] <;> field_simp <;> ring
  inv_val := by ext <;> simp [base] <;> field_simp <;> ring
def primeUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : (Model epsilon y)ˣ :=
  alphaUnit epsilon y hEpsilon * baseUnit epsilon y hY hOne
abbrev ProjectiveGroup (epsilon y : K) :=
  (Model epsilon y)ˣ ⧸ Subgroup.center (Model epsilon y)ˣ
def projectiveBase (epsilon y : K) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    ProjectiveGroup epsilon y :=
  QuotientGroup.mk' _ (baseUnit epsilon y hY hOne)
def projectivePrime (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : ProjectiveGroup epsilon y :=
  QuotientGroup.mk' _ (primeUnit epsilon y hEpsilon hY hOne)
section Group
variable {H : Type*} [Group H]
end Group
end QEC.Coding.ExpanderCodes.QuaternionGenerators


