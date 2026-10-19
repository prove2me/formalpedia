-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
-- name    : MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:00.890877+00:00
-- url     : https://prove2.me/theorems/2a69ce76-018b-4c18-86ae-84d4df0b9b6c
-- title:
--   Definitions of BinaryOrbitPolynomial: Algebra of closed binary Frobenius-orbit polynomials
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryOrbitPolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Algebra of closed binary Frobenius-orbit polynomials
--
--   **Definitions** (1): `MIPRE.LowDegree.BinaryQuotient.orbitPolynomial` (The monic polynomial product over a specified initial Frobenius orbit.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `natDegree_orbitPolynomial`, `orbitPolynomial_monic`, `orbitPolynomial_succ`, `orbitPolynomial_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryOrbitPolynomial` (`MIPRE/Foundations/LowDegree/BinaryOrbitPolynomial.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryOrbitPolynomial.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOrbitPolynomial.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Algebra of closed binary Frobenius-orbit polynomials -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Polynomial

variable {R : Type*} [CommRing R]

/-- The monic polynomial product over a specified initial Frobenius orbit. -/
def orbitPolynomial (x : R) (n : ℕ) : Polynomial R :=
  (List.ofFn (fun i : Fin n => X + C (x ^ (2 ^ (i : ℕ))))).prod

@[simp] theorem orbitPolynomial_zero (x : R) : orbitPolynomial x 0 = 1 := rfl

/-- Splitting off the first conjugate shifts the remaining orbit by squaring. -/
theorem orbitPolynomial_succ (x : R) (n : ℕ) :
    orbitPolynomial x (n + 1) = (X + C x) * orbitPolynomial (x ^ 2) n := by
  rw [orbitPolynomial, List.ofFn_succ, List.prod_cons]
  simp only [Fin.val_zero, pow_zero, pow_one, Fin.val_succ]
  congr 1
  congr 1
  congr 1
  funext i
  rw [pow_succ, Nat.mul_comm (2 ^ (i : ℕ)) 2, pow_mul]

/-- Every orbit polynomial is monic, including the empty orbit. -/
theorem orbitPolynomial_monic (x : R) (n : ℕ) : (orbitPolynomial x n).Monic := by
  induction n generalizing x with
  | zero => exact monic_one
  | succ n ih => rw [orbitPolynomial_succ]; exact (monic_X_add_C x).mul (ih _)

/-- The degree is the specified orbit length even when conjugates repeat. -/
@[simp] theorem natDegree_orbitPolynomial [Nontrivial R] (x : R) (n : ℕ) :
    (orbitPolynomial x n).natDegree = n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [orbitPolynomial_succ, (monic_X_add_C x).natDegree_mul (orbitPolynomial_monic _ _),
      natDegree_X_add_C, ih]
    omega

end MIPRE.LowDegree.BinaryQuotient

end


