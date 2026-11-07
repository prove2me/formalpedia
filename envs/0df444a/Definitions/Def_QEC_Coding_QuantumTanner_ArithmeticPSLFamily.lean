-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
-- name    : QEC_Coding_QuantumTanner_ArithmeticPSLFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:25:40.224991+00:00
-- url     : https://prove2.me/theorems/eef7f4b4-40d2-4dee-812b-7d5ccfbcf419
-- title:
--   Arithmetic PSLFamily
-- statement:
--   Definitions and structural lemmas for Arithmetic PSLFamily, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLFamily.lean

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslLeft_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslLeft_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_psl_total_nonconjugacy
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_even_psl_parameters

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
abbrev FieldAt (p n : ℕ) [Fact p.Prime] := GaloisField p (2 * (n + 2))
abbrev GroupAt (p n : ℕ) [Fact p.Prime] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FieldAt p n)
variable (p : ℕ) [hPrime : Fact p.Prime]
instance fieldAtFintype (n : ℕ) : Fintype (FieldAt p n) := Fintype.ofFinite _
instance groupAtFintype (n : ℕ) : Fintype (GroupAt p n) := Fintype.ofFinite _
attribute [irreducible] fieldAtFintype groupAtFintype
structure Specialization (epsilon : ZMod p) (n : ℕ) where
  y : FieldAt p n
  r : FieldAt p n
  s : FieldAt p n
  i : FieldAt p n
  y_ne_zero : y ≠ 0
  one_add_y_ne_zero : 1 + y ≠ 0
  r_ne_zero : r ≠ 0
  root : r ^ 2 = algebraMap (ZMod p) (FieldAt p n) epsilon
  ratio : s ^ 2 = y / (1 + y)
  sqrt_neg_one : i ^ 2 = -1
  irreducible : Irreducible (minpoly (ZMod p) y)
  minpoly_degree : (minpoly (ZMod p) y).natDegree = 2 * (n + 2)
@[irreducible] def specialization (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) (n : ℕ) :
    Specialization p epsilon n := by
  apply Classical.choice
  obtain ⟨y, r, s, i, hY, hOne, hR, _, hRoot, hRatio, hI, hIrred, hDegree⟩ :=
    exists_even_psl_parameters p (n + 2) (by omega) epsilon hEpsilon
  exact ⟨⟨y, r, s, i, hY, hOne, hR, hRoot, hRatio, hI, hIrred, hDegree⟩⟩
omit hPrime in
theorem two_ne_zero {K : Type*} [Field K] [CharP K p]
    (hOdd : 3 ≤ p) : (2 : K) ≠ 0 := by
  intro hZero
  have hDvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hZero
  have := Nat.le_of_dvd (by decide : 0 < 2) hDvd
  omega
variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
def left (n : ℕ) : TorusIndex epsilon → GroupAt p n :=
  let a := specialization p epsilon hEpsilon n
  pslLeft (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one
def right (n : ℕ) : TorusIndex epsilon → GroupAt p n :=
  let a := specialization p epsilon hEpsilon n
  pslRight (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one
theorem left_injective (n : ℕ) : Function.Injective (left p hOdd epsilon hEpsilon n) := by
  let a := specialization p epsilon hEpsilon n
  exact pslLeft_injective (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one
theorem right_injective (n : ℕ) : Function.Injective (right p hOdd epsilon hEpsilon n) := by
  let a := specialization p epsilon hEpsilon n
  exact pslRight_injective (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one
theorem left_inverse (n : ℕ) (a : TorusIndex epsilon) :
    left p hOdd epsilon hEpsilon n (indexedLeftInverse epsilon hEpsilon a) =
      (left p hOdd epsilon hEpsilon n a)⁻¹ := by
  let x := specialization p epsilon hEpsilon n
  exact pslLeft_inverse (algebraMap (ZMod p) (FieldAt p n)) epsilon x.r x.y x.s x.i
    hEpsilon x.root x.r_ne_zero (two_ne_zero p hOdd) x.y_ne_zero
    x.one_add_y_ne_zero (two_ne_zero p hOdd) x.ratio x.sqrt_neg_one a
theorem right_inverse (n : ℕ) (a : TorusIndex epsilon) :
    right p hOdd epsilon hEpsilon n a = (right p hOdd epsilon hEpsilon n a)⁻¹ := by
  let x := specialization p epsilon hEpsilon n
  exact pslRight_inverse (algebraMap (ZMod p) (FieldAt p n)) epsilon x.r x.y x.s x.i
    hEpsilon x.root x.r_ne_zero (two_ne_zero p hOdd) x.y_ne_zero
    x.one_add_y_ne_zero (two_ne_zero p hOdd) x.ratio x.sqrt_neg_one a
theorem total_nonconjugacy (n : ℕ) (g : GroupAt p n) (a b : TorusIndex epsilon) :
    left p hOdd epsilon hEpsilon n a * g ≠ g * right p hOdd epsilon hEpsilon n b := by
  let x := specialization p epsilon hEpsilon n
  exact psl_total_nonconjugacy (algebraMap (ZMod p) (FieldAt p n)) epsilon x.r x.y x.s x.i
    hEpsilon x.root x.r_ne_zero (two_ne_zero p hOdd) x.y_ne_zero
    x.one_add_y_ne_zero (two_ne_zero p hOdd) x.ratio x.sqrt_neg_one a b g
def squareComplex (n : ℕ) :
    LeftRightCayleySquareComplex (GroupAt p n) (TorusIndex epsilon) (TorusIndex epsilon)
      (CayleySquare (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)) :=
  cayleySquareComplex (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon n) (right_injective p hOdd epsilon hEpsilon n)
    (left_inverse p hOdd epsilon hEpsilon n) (right_inverse p hOdd epsilon hEpsilon n)
    (total_nonconjugacy p hOdd epsilon hEpsilon n)
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily


