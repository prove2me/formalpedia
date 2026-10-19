-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
-- name    : MIPRE_Foundations_Introspection_RegisterTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:58.820986+00:00
-- url     : https://prove2.me/theorems/df2a9dda-9a40-4646-85b8-f674899752f5
-- title:
--   Definitions of RegisterTransport: Transporting finite register operators and their state distances All transports below are explicit permutations of…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.RegisterTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Transporting finite register operators and their state distances. All transports below are explicit permutations of computational basis labels. In particular they preserve positivity, projectivity and squared state norms.
--
--   **Definitions** (2): `MIPRE.Introspection.registerOp` (Pull an operator back along a bijective labelling of the basis.); `MIPRE.Introspection.registerPOVM` (Transport the actual normalized positive measurement, rather than only its matrices.).
--
--   **Embedded lemmas** (10): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `registerOp_apply`, `registerOp_conjTranspose`, `registerOp_inv`, `registerOp_mul`, `registerOp_one`, `registerOp_posSemidef`, `registerOp_sub`, `registerOp_sum`, `registerOp_symm`, `registerPOVM_mats`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.RegisterTransport` (`MIPRE/Foundations/Introspection/RegisterTransport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 35 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/RegisterTransport.lean; blueprint lem:pauli-mixing

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RegisterTransport.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing

/-! # Transporting finite register operators and their state distances

All transports below are explicit permutations of computational basis labels.
In particular they preserve positivity, projectivity and squared state norms.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {I J K L A : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]

/-- Pull an operator back along a bijective labelling of the basis. -/
def registerOp (e : I ≃ J) (M : Matrix J J ℂ) : Matrix I I ℂ :=
  M.submatrix e e

@[simp] theorem registerOp_apply (e : I ≃ J) (M : Matrix J J ℂ) (i j : I) :
    registerOp e M i j = M (e i) (e j) := rfl

@[simp] theorem registerOp_one (e : I ≃ J) : registerOp e (1 : Matrix J J ℂ) = 1 :=
  Matrix.submatrix_one_equiv e

@[simp] theorem registerOp_sub (e : I ≃ J) (M N : Matrix J J ℂ) :
    registerOp e (M - N) = registerOp e M - registerOp e N := rfl

@[simp] theorem registerOp_mul (e : I ≃ J) (M N : Matrix J J ℂ) :
    registerOp e (M * N) = registerOp e M * registerOp e N := by
  exact (Matrix.submatrix_mul_equiv M N e e e).symm

@[simp] theorem registerOp_sum (e : I ≃ J) (M : A → Matrix J J ℂ) :
    registerOp e (∑ a, M a) = ∑ a, registerOp e (M a) := by
  ext i j
  simp only [registerOp_apply, Matrix.sum_apply]

@[simp] theorem registerOp_conjTranspose (e : I ≃ J) (M : Matrix J J ℂ) :
    registerOp e Mᴴ = (registerOp e M)ᴴ := rfl

@[simp] theorem registerOp_symm (e : I ≃ J) (M : Matrix I I ℂ) :
    registerOp e (registerOp e.symm M) = M := by
  ext i j
  simp only [registerOp_apply, Equiv.symm_apply_apply]

@[simp] theorem registerOp_inv (e : I ≃ J) (M : Matrix J J ℂ) :
    registerOp e.symm (registerOp e M) = M := registerOp_symm e.symm M

/-- Positivity is preserved without changing any eigenvalues. -/
theorem registerOp_posSemidef (e : I ≃ J) {M : Matrix J J ℂ} (hM : M.PosSemidef) :
    (registerOp e M).PosSemidef := hM.submatrix e

/-- Transport the actual normalized positive measurement, rather than only its matrices. -/
def registerPOVM (e : I ≃ J) (M : POVM A J) : POVM A I where
  mats a := ⟨registerOp e (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (registerOp_posSemidef e
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a)))).isHermitian⟩
  nonneg a := by
    change (0 : Matrix I I ℂ) ≤ registerOp e (M.mats a).val
    exact Matrix.nonneg_iff_posSemidef.mpr (registerOp_posSemidef e
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a))))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ a, registerOp e (M.mats a).val) = 1
    rw [← registerOp_sum]
    have hM : (∑ a, (M.mats a).val) = (1 : Matrix J J ℂ) := by
      simpa only [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] using
        congrArg Subtype.val M.normalized
    rw [hM, registerOp_one]

@[simp] theorem registerPOVM_mats (e : I ≃ J) (M : POVM A J) (a : A) :
    ((registerPOVM e M).mats a).val = registerOp e (M.mats a).val := rfl

end MIPRE.Introspection

end


