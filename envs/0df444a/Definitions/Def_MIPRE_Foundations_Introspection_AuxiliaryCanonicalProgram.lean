-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
-- name    : MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:17.045776+00:00
-- url     : https://prove2.me/theorems/0e81676d-fa67-4b99-a32b-7f79f4c9ea6c
-- title:
--   Definitions of AuxiliaryCanonicalProgram: Verified canonical binary elimination for auxiliary dual checks The effective elimination library chooses the first…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliaryCanonicalProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Verified canonical binary elimination for auxiliary dual checks. The effective elimination library chooses the first nonzero coordinate at each insertion. Its resulting pivot set is exactly the dimension-defined canonical pivot set used by `CL.canonLin`. Thus its residual, not merely an arbitrary equivalent quotient representative, computes that canonical map.
--
--   **Definitions** (2): `MIPRE.Introspection.AuxiliaryCanonical.Leading`; `MIPRE.Introspection.AuxiliaryCanonical.canonicalProg` (A single uniform polynomial-time program for the exact canonical quotient representative.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `firstOne_before`, `firstOne_vector_before`, `reduce_sub_mem`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliaryCanonicalProgram` (`MIPRE/Foundations/Introspection/AuxiliaryCanonicalProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryCanonicalProgram.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryCanonicalProgram.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span

/-! # Verified canonical binary elimination for auxiliary dual checks

The effective elimination library chooses the first nonzero coordinate at
each insertion. Its resulting pivot set is exactly the dimension-defined
canonical pivot set used by `CL.canonLin`. Thus its residual, not merely an
arbitrary equivalent quotient representative, computes that canonical map.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryCanonical
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}

theorem firstOne_before (bs : BitStr) (j : ℕ) (hj : j < firstOne bs) :
    bs.getD j false = false := by
  induction bs generalizing j with
  | nil => simp [firstOne] at hj
  | cons b bs ih =>
    cases b with
    | false =>
      cases j with
      | zero => rfl
      | succ j =>
        apply ih j
        simpa [firstOne,List.findIdx_cons] using hj
    | true => simp [firstOne,List.findIdx_cons] at hj

theorem firstOne_vector_before (v : Fin n → ZMod 2) (i : Fin n)
    (hi : i.val < firstOne (vectorBits v)) : v i = 0 := by
  have h := firstOne_before (vectorBits v) i hi
  rw [getD_vectorBits] at h
  rcases binary_eq_zero_or_one (v i) with hz | ho
  · exact hz
  · simp [bit,ho] at h

def Leading (b : List (Pivot n t)) : Prop :=
  ∀ p ∈ b, ∀ i : Fin n, i < p.1 → p.2.1 i = 0

theorem reduce_sub_mem (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : ∀ p ∈ b, p.2.1 ∈ S) (r : Row n t) :
    r.1 - (typedReduce b r).1 ∈ S := by
  induction b generalizing r with
  | nil => change r.1-r.1 ∈ S; simp
  | cons p b ih =>
    have hp : r.1 - (typedReduceStep r p).1 ∈ S := by
      unfold typedReduceStep
      split
      · simpa using S.neg_mem (hb p (by simp))
      · simp
    have hr := ih (fun q hq => hb q (by simp [hq])) (typedReduceStep r p)
    change r.1 - (typedReduce b (typedReduceStep r p)).1 ∈ S
    simpa only [sub_add_sub_cancel] using S.add_mem hp hr

/-- A single uniform polynomial-time program for the exact canonical quotient
representative. The coefficient width is zero, since no certificate is output. -/
def canonicalProg : PolyTimeFun (List BitStr × BitStr) BitStr :=
  let rows := (map ((PolyTimeFun.id BitStr).pair (const ([] : BitStr)))).comp fst
  fst.comp (reduceRowsProg.comp ((basisRowsProg.comp rows).pair (snd.pair (const ([] : BitStr)))))

end MIPRE.Introspection.AuxiliaryCanonical
end


