-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
-- name    : MIPRE_Foundations_Introspection_IsometricStrategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:15.520811+00:00
-- url     : https://prove2.me/theorems/5463a033-e441-4ad3-995e-a90f64c3adcb
-- title:
--   Definitions of IsometricStrategy: Transporting a strategy through local isometries Conjugating a PVM by a rectangular isometry normalizes it only on the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.IsometricStrategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Transporting a strategy through local isometries. Conjugating a PVM by a rectangular isometry normalizes it only on the isometry's image. Assigning the image complement to a fixed outcome gives an actual projective measurement on the whole target space. On the embedded state this completion preserves all probabilities and every intertwining identity exactly, including after an outcome map.
--
--   **Definitions** (5): `MIPRE.Introspection.isometricComplement` (The orthogonal complement of the image of an isometry.); `MIPRE.Introspection.isometricEffect` (Put the image complement at one fixed outcome.); `MIPRE.Introspection.isometricImage` (Conjugation into the image of a rectangular linear map.); `MIPRE.Introspection.isometricPOVM` (The concrete projective POVM on the isometry's target.); `MIPRE.Introspection.isometricState` (Tensor both local isometries into the actual state vector.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `isometricComplement_conjTranspose`, `isometricComplement_idem`, `isometricComplement_mul_image`, `isometricEffect_isPVM`, `isometricImage_conjTranspose`, `isometricImage_mul`, `isometricImage_mul_complement`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.IsometricStrategy` (`MIPRE/Foundations/Introspection/IsometricStrategy.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/IsometricStrategy.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/IsometricStrategy.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability

/-! # Transporting a strategy through local isometries

Conjugating a PVM by a rectangular isometry normalizes it only on the
isometry's image. Assigning the image complement to a fixed outcome gives
an actual projective measurement on the whole target space. On the embedded
state this completion preserves all probabilities and every intertwining
identity exactly, including after an outcome map.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false

section Local
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]

/-- Conjugation into the image of a rectangular linear map. -/
def isometricImage (V : Matrix R H ℂ) (M : Matrix H H ℂ) : Matrix R R ℂ :=
  V * M * Vᴴ

theorem isometricImage_mul (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (M N : Matrix H H ℂ) :
    isometricImage V M * isometricImage V N = isometricImage V (M * N) := by
  unfold isometricImage
  calc
    _ = V * M * (Vᴴ * V) * N * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem isometricImage_conjTranspose (V : Matrix R H ℂ) (M : Matrix H H ℂ) :
    (isometricImage V M)ᴴ = isometricImage V Mᴴ := by
  simp only [isometricImage, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The orthogonal complement of the image of an isometry. -/
def isometricComplement (V : Matrix R H ℂ) : Matrix R R ℂ :=
  1 - isometricImage V 1

theorem isometricComplement_conjTranspose (V : Matrix R H ℂ) :
    (isometricComplement V)ᴴ = isometricComplement V := by
  rw [isometricComplement, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    isometricImage_conjTranspose, Matrix.conjTranspose_one]

theorem isometricComplement_mul_image (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix H H ℂ) : isometricComplement V * isometricImage V M = 0 := by
  rw [isometricComplement, Matrix.sub_mul, Matrix.one_mul,
    isometricImage_mul V hV, Matrix.one_mul, sub_self]

theorem isometricImage_mul_complement (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix H H ℂ) : isometricImage V M * isometricComplement V = 0 := by
  rw [isometricComplement, Matrix.mul_sub, Matrix.mul_one,
    isometricImage_mul V hV, Matrix.mul_one, sub_self]

theorem isometricComplement_idem (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    isometricComplement V * isometricComplement V = isometricComplement V := by
  unfold isometricComplement
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    isometricImage_mul V hV, Matrix.one_mul, sub_self, sub_zero]

/-- Put the image complement at one fixed outcome. -/
def isometricEffect (V : Matrix R H ℂ) (a₀ : A)
    (M : A → Matrix H H ℂ) (a : A) : Matrix R R ℂ :=
  isometricImage V (M a) + if a = a₀ then isometricComplement V else 0

/-- Completion of the conjugated effects is a PVM on the whole target. -/
theorem isometricEffect_isPVM (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) {M : A → Matrix H H ℂ} (hM : IsPVM M) :
    IsPVM (isometricEffect V a₀ M) where
  isSelfAdjoint a := by
    unfold isometricEffect
    split_ifs <;> simp only [Matrix.conjTranspose_add, isometricImage_conjTranspose,
      hM.isSelfAdjoint, isometricComplement_conjTranspose, Matrix.conjTranspose_zero]
  idem a := by
    unfold isometricEffect
    split_ifs
    · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        isometricImage_mul V hV, hM.idem, isometricImage_mul_complement V hV,
        isometricComplement_mul_image V hV, isometricComplement_idem V hV,
        add_zero, zero_add]
    · rw [add_zero, isometricImage_mul V hV, hM.idem]
  sum_eq_one := by
    simp only [isometricEffect, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    rw [show (∑ a, isometricImage V (M a)) = isometricImage V (∑ a, M a) by
      simp only [isometricImage, Matrix.mul_sum, Matrix.sum_mul], hM.sum_eq_one]
    unfold isometricComplement
    abel

/-- The concrete projective POVM on the isometry's target. -/
def isometricPOVM (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) : POVM A R :=
  (isometricEffect_isPVM V hV a₀ hM).toPOVM

end Local

section Bipartite
variable {H K R S A B X Y : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]

/-- Tensor both local isometries into the actual state vector. -/
def isometricState (V : Matrix R H ℂ) (W : Matrix S K ℂ) (ψ : H × K → ℂ) :
    R × S → ℂ := (V ⊗ₖ W) *ᵥ ψ

end Bipartite
end MIPRE.Introspection
end


