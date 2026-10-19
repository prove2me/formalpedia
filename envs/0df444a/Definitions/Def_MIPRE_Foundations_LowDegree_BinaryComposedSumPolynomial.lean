-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
-- name    : MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:30:33.507828+00:00
-- url     : https://prove2.me/theorems/0c547a82-9961-4704-93bf-3340bde6a777
-- title:
--   Definitions of BinaryComposedSumPolynomial: Binary composed-sum polynomials as products of Frobenius translates
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryComposedSumPolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Binary composed-sum polynomials as products of Frobenius translates
--
--   **Definitions** (2): `MIPRE.LowDegree.BinaryQuotient.composedSumPolynomial` (Product of all specified Frobenius translates of a binary polynomial.); `MIPRE.LowDegree.BinaryQuotient.translatedPolynomial` (Translate a binary polynomial by an element of the ambient binary algebra.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `composedSumPolynomial_monic`, `composedSumPolynomial_succ`, `composedSumPolynomial_zero`, `natDegree_composedSumPolynomial`, `natDegree_translatedPolynomial`, `translatedPolynomial_monic`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryComposedSumPolynomial` (`MIPRE/Foundations/LowDegree/BinaryComposedSumPolynomial.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 37 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryComposedSumPolynomial.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComposedSumPolynomial.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree

/-! # Binary composed-sum polynomials as products of Frobenius translates -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Polynomial

variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]

/-- Translate a binary polynomial by an element of the ambient binary algebra. -/
def translatedPolynomial (g : Polynomial (ZMod 2)) (x : R) : Polynomial R :=
  (g.map (algebraMap (ZMod 2) R)).comp (X + C x)

/-- Product of all specified Frobenius translates of a binary polynomial. -/
def composedSumPolynomial (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) : Polynomial R :=
  (List.ofFn (fun i : Fin n => translatedPolynomial g (x ^ (2 ^ (i : ℕ))))).prod

@[simp] theorem composedSumPolynomial_zero (g : Polynomial (ZMod 2)) (x : R) :
    composedSumPolynomial g x 0 = 1 := rfl

theorem composedSumPolynomial_succ (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    composedSumPolynomial g x (n + 1) = translatedPolynomial g x * composedSumPolynomial g (x ^ 2) n := by
  rw [composedSumPolynomial, List.ofFn_succ, List.prod_cons]
  simp only [Fin.val_zero, pow_zero, pow_one, Fin.val_succ]
  congr 1
  congr 1
  congr 1
  funext i
  rw [pow_succ, Nat.mul_comm (2 ^ (i : ℕ)) 2, pow_mul]

/-- Translating a monic polynomial preserves monicity. -/
theorem translatedPolynomial_monic (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) :
    (translatedPolynomial g x).Monic := by
  nontriviality R
  exact (hg.map _).comp (monic_X_add_C x) (by simp)

@[simp] theorem natDegree_translatedPolynomial [IsDomain R]
    (g : Polynomial (ZMod 2)) (x : R) : (translatedPolynomial g x).natDegree = g.natDegree := by
  rw [translatedPolynomial, natDegree_comp, natDegree_X_add_C, mul_one, natDegree_map]

/-- The product is monic even when its translates repeat. -/
theorem composedSumPolynomial_monic (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).Monic := by
  induction n generalizing x with
  | zero => exact monic_one
  | succ n ih =>
    rw [composedSumPolynomial_succ]
    exact (translatedPolynomial_monic g hg x).mul (ih _)

@[simp] theorem natDegree_composedSumPolynomial [IsDomain R]
    (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).natDegree = n * g.natDegree := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [composedSumPolynomial_succ,
      (translatedPolynomial_monic g hg x).natDegree_mul (composedSumPolynomial_monic g hg _ _),
      natDegree_translatedPolynomial, ih]
    ring

variable {S : Type*} [CommRing S] [Algebra (ZMod 2) S]

end MIPRE.LowDegree.BinaryQuotient

end


