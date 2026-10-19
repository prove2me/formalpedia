-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
-- name    : MIPRE_Foundations_Introspection_HonestMagicSquare
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:50.551259+00:00
-- url     : https://prove2.me/theorems/8e929986-9b90-4d10-b025-174781cf0599
-- title:
--   Definitions of HonestMagicSquare: The Magic Square extension of an arbitrary anticommuting pair This is the concrete operator construction needed by the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HonestMagicSquare` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Magic Square extension of an arbitrary anticommuting pair. This is the concrete operator construction needed by the honest Pauli test. It adds one qubit and retains the original observables at cells zero and four. The row and column identities use the actual Magic Square layout and parity. No game completeness statement is assumed.
--
--   **Definitions** (5): `MIPRE.Introspection.HonestMagicSquare.cellIndex` (The actual Magic Square cell, with its fixed nine-cell carrier exposed.); `MIPRE.Introspection.HonestMagicSquare.constraintOp` (The joint measurement of the three cells of a row or column.); `MIPRE.Introspection.HonestMagicSquare.grid` (The nine observables, on the original space tensor one additional qubit.); `MIPRE.Introspection.HonestMagicSquare.variableOp` (The binary measurement of an arbitrary cell.); `_private.MIPRE.Foundations.Introspection.HonestMagicSquare.0.MIPRE.Introspection.HonestMagicSquare.tripleEquiv`.
--
--   **Embedded lemmas** (10): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `grid_four`, `grid_zero`, `ZX_anticomm`, `observable_commute_projector`, `observable_kronecker`, `observable_mul`, `observable_one`, `sign_injective`, `tensor_anticommute`, `tensor_commute`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HonestMagicSquare` (`MIPRE/Foundations/Introspection/HonestMagicSquare.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HonestMagicSquare.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestMagicSquare.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LCS_Pauli_X_anticomm_Z
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one

/-! # The Magic Square extension of an arbitrary anticommuting pair

This is the concrete operator construction needed by the honest Pauli test.
It adds one qubit and retains the original observables at cells zero and four.
The row and column identities use the actual Magic Square layout and parity.
No game completeness statement is assumed.
-/

noncomputable section

namespace MIPRE.Introspection.HonestMagicSquare

open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker

/-- The actual Magic Square cell, with its fixed nine-cell carrier exposed. -/
def cellIndex (c : Fin layout.r) (j : Fin 3) : Fin 9 := cell c j

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem observable_kronecker {J : Type*} [Fintype J] [DecidableEq J]
    {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : IsObservable A) (hB : IsObservable B) : IsObservable (A ⊗ₖ B) where
  involutive := by rw [← mul_kronecker_mul, hA.involutive, hB.involutive, one_kronecker_one]
  self_adjoint := by
    change (A ⊗ₖ B)ᴴ = A ⊗ₖ B
    rw [conjTranspose_kronecker]
    exact congrArg₂ (fun A B => A ⊗ₖ B) hA.self_adjoint hB.self_adjoint

theorem observable_one : IsObservable (1 : Matrix I I ℂ) :=
  ⟨one_mul _, star_one _⟩

theorem observable_mul {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hc : Commute A B) :
    IsObservable (A * B) where
  involutive := by
    calc A * B * (A * B) = A * (B * A) * B := by simp only [mul_assoc]
      _ = A * (A * B) * B := by rw [hc.eq]
      _ = (A * A) * (B * B) := by simp only [mul_assoc]
      _ = 1 := by rw [hA.involutive, hB.involutive, one_mul]
  self_adjoint := by rw [star_mul, hA.self_adjoint, hB.self_adjoint, hc.eq]

omit [DecidableEq I] in
theorem tensor_commute {A B : Matrix I I ℂ}
    {C D : Matrix (Fin 2) (Fin 2) ℂ} (hAB : Commute A B) (hCD : Commute C D) :
    Commute (A ⊗ₖ C) (B ⊗ₖ D) := by
  change (A ⊗ₖ C) * (B ⊗ₖ D) = (B ⊗ₖ D) * (A ⊗ₖ C)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, hAB.eq, hCD.eq]

omit [DecidableEq I] in
theorem tensor_anticommute {A B : Matrix I I ℂ}
    {C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hAB : A * B = -(B * A)) (hCD : C * D = -(D * C)) :
    Commute (A ⊗ₖ C) (B ⊗ₖ D) := by
  change (A ⊗ₖ C) * (B ⊗ₖ D) = (B ⊗ₖ D) * (A ⊗ₖ C)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, hAB, hCD]
  ext i j
  exact neg_mul_neg _ _

/-- The nine observables, on the original space tensor one additional qubit. -/
def grid (A B : Matrix I I ℂ) : Fin 9 → Matrix (I × Fin 2) (I × Fin 2) ℂ
  | 0 => A ⊗ₖ 1
  | 1 => 1 ⊗ₖ Pauli.X
  | 2 => A ⊗ₖ Pauli.X
  | 3 => 1 ⊗ₖ Pauli.Z
  | 4 => B ⊗ₖ 1
  | 5 => B ⊗ₖ Pauli.Z
  | 6 => A ⊗ₖ Pauli.Z
  | 7 => B ⊗ₖ Pauli.X
  | 8 => (A * B) ⊗ₖ (Pauli.Z * Pauli.X)

@[simp] theorem grid_zero (A B : Matrix I I ℂ) : grid A B 0 = A ⊗ₖ 1 := rfl
@[simp] theorem grid_four (A B : Matrix I I ℂ) : grid A B 4 = B ⊗ₖ 1 := rfl

theorem ZX_anticomm : Pauli.Z * Pauli.X = -(Pauli.X * Pauli.Z) := by
  rw [Pauli.X_anticomm_Z]
  simp

/-- The binary measurement of an arbitrary cell. -/
def variableOp (A B : Matrix I I ℂ) (j : Fin 9) (b : ZMod 2) :
    Matrix (I × Fin 2) (I × Fin 2) ℂ := observableToProjector (grid A B j) b

/-- The joint measurement of the three cells of a row or column. -/
def constraintOp (A B : Matrix I I ℂ) (c : Fin layout.r) (a : Fin 3 → ZMod 2) :
    Matrix (I × Fin 2) (I × Fin 2) ℂ :=
  variableOp A B (cellIndex c 0) (a 0) * variableOp A B (cellIndex c 1) (a 1) *
    variableOp A B (cellIndex c 2) (a 2)

def tripleEquiv : (Fin 3 → ZMod 2) ≃ (ZMod 2 × ZMod 2) × ZMod 2 where
  toFun a := ((a 0, a 1), a 2)
  invFun a := ![a.1.1, a.1.2, a.2]
  left_inv a := by funext j; fin_cases j <;> rfl
  right_inv a := by rcases a with ⟨⟨a, b⟩, c⟩; rfl

theorem observable_commute_projector {A B : Matrix I I ℂ} (h : Commute A B)
    (b : ZMod 2) : Commute A (observableToProjector B b) := by
  unfold observableToProjector
  exact ((Commute.one_right _).add_right (h.smul_right _)).smul_right _

theorem sign_injective : Function.Injective (fun b : ZMod 2 => (-1 : ℂ) ^ b.val) := by
  intro x y h
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one y with rfl | rfl <;>
      simp_all [ZMod.val_zero, zmod_two_val_one]
  all_goals norm_num at h

end MIPRE.Introspection.HonestMagicSquare


