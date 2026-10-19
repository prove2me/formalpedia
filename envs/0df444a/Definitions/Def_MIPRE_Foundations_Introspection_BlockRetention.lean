-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
-- name    : MIPRE_Foundations_Introspection_BlockRetention
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:10.610649+00:00
-- url     : https://prove2.me/theorems/d3094408-ac28-4f7c-bbfd-3b465d7ef96c
-- title:
--   Definitions of BlockRetention: Completing the matching blocks of a twirled measurement
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.BlockRetention` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Completing the matching blocks of a twirled measurement
--
--   **Definitions** (1): `MIPRE.Introspection.controlledPOVM` (Read a projective register, then use the POVM selected by its outcome on the ancilla.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.BlockRetention` (`MIPRE/Foundations/Introspection/BlockRetention.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 29 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/BlockRetention.lean; blueprint lem:pauli-mixing-coordinates

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockRetention.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! # Completing the matching blocks of a twirled measurement -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

/-- Read a projective register, then use the POVM selected by its outcome on the ancilla. -/
def controlledPOVM (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVM A H) :
    POVM (Y × A) (V × H) where
  mats p := ⟨P p.1 ⊗ₖ ((Q p.1).mats p.2).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact ((hP.posSemidef p.1).kronecker (Matrix.nonneg_iff_posSemidef.mp
      (Subtype.coe_le_coe.mpr ((Q p.1).nonneg p.2)))).isHermitian⟩
  nonneg p := by
    apply Subtype.coe_le_coe.mp
    exact ((hP.posSemidef p.1).kronecker (Matrix.nonneg_iff_posSemidef.mp
      (Subtype.coe_le_coe.mpr ((Q p.1).nonneg p.2)))).nonneg
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ p : Y × A, P p.1 ⊗ₖ ((Q p.1).mats p.2).val) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, POVM.sum_val]
    rw [← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]

variable {B : Type*} [Fintype B] [DecidableEq B]

end MIPRE.Introspection

end


