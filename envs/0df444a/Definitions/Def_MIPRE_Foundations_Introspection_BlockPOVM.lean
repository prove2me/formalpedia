-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
-- name    : MIPRE_Foundations_Introspection_BlockPOVM
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:06.34227+00:00
-- url     : https://prove2.me/theorems/96680016-e4ab-47ee-b056-395847a3ee5b
-- title:
--   Definitions of BlockPOVM: The ancillary blocks of a twirled POVM are POVMs
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.BlockPOVM` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The ancillary blocks of a twirled POVM are POVMs
--
--   **Definitions** (1): `MIPRE.Introspection.blockPOVM` (The actual ancillary POVM at a selected fiber, obtained by compressing and averaging.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `averagedBlock_one`, `averagedBlock_posSemidef`, `averagedBlock_sum`, `blockPOVM_mats`, `sum_averagedBlock_eq_one`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.BlockPOVM` (`MIPRE/Foundations/Introspection/BlockPOVM.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 10 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/BlockPOVM.lean; blueprint lem:pauli-linear-mixing

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockPOVM.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl

/-! # The ancillary blocks of a twirled POVM are POVMs -/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical Matrix
open scoped ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- Averaging diagonal compressions preserves positivity. -/
theorem averagedBlock_posSemidef (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (hM : M.PosSemidef) (x : Fin n → F) : (averagedBlock K M x).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum _ (fun v _ => hM.submatrix (fun a => (x + v.1, a)))
  · positivity

theorem averagedBlock_sum {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (M : A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) (x : Fin n → F) :
    averagedBlock K (∑ a, M a) x = ∑ a, averagedBlock K (M a) x := by
  ext i j
  simp only [averagedBlock, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem averagedBlock_one (K : Submodule F (Fin n → F)) (x : Fin n → F) :
    averagedBlock K (1 : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) x = 1 := by
  have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := K)).ne'
  ext i j
  simp only [averagedBlock, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Prod.mk.injEq, true_and, smul_eq_mul]
  by_cases hij : i = j
  · simp [hij, hc]
  · simp [hij]

/-- Each averaged diagonal block of a normalized positive family is itself normalized. -/
theorem sum_averagedBlock_eq_one {A : Type*} [Fintype A]
    (K : Submodule F (Fin n → F))
    (M : A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) (hM : ∑ a, M a = 1)
    (x : Fin n → F) : (∑ a, averagedBlock K (M a) x) = 1 := by
  rw [← averagedBlock_sum, hM, averagedBlock_one]

set_option maxHeartbeats 800000 in
/-- The actual ancillary POVM at a selected fiber, obtained by compressing and averaging. -/
def blockPOVM {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (P : POVM A ((Fin n → F) × H)) (x : Fin n → F) : POVM A H where
  mats a := ⟨averagedBlock (H := H) K (P.mats a) x, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (averagedBlock_posSemidef K _
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (P.nonneg a))) x).isHermitian⟩
  nonneg a := by
    change (0 : Matrix H H ℂ) ≤ averagedBlock (H := H) K (P.mats a) x
    exact Matrix.nonneg_iff_posSemidef.mpr (averagedBlock_posSemidef K _
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (P.nonneg a))) x)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ a, averagedBlock (H := H) K (P.mats a) x) = 1
    apply sum_averagedBlock_eq_one
    simpa only [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] using
      congrArg (fun M : selfAdjoint (Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) =>
      (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)) P.normalized

@[simp] theorem blockPOVM_mats {A : Type*} [Fintype A] (K : Submodule F (Fin n → F))
    (P : POVM A ((Fin n → F) × H)) (x : Fin n → F) (a : A) :
    ((blockPOVM K P x).mats a : Matrix H H ℂ) = averagedBlock (H := H) K (P.mats a) x := rfl

end MIPRE.Introspection

end


