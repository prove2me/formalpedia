-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
-- name    : MIPRE_Foundations_Introspection_RegisterEPR
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:04.273984+00:00
-- url     : https://prove2.me/theorems/9eb88715-ad33-43b0-867c-ae907a8e3d1b
-- title:
--   Definitions of RegisterEPR: Splitting the maximally entangled state along computational registers
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.RegisterEPR` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Splitting the maximally entangled state along computational registers
--
--   **Definitions** (5): `MIPRE.Introspection.registerEPR` (The maximally entangled state, indexed by an arbitrary finite basis.); `MIPRE.Introspection.registerExtend` (Put a local operator on the first register, leaving the complement untouched.); `MIPRE.Introspection.registerOutside` (The complementary register is moved behind the original auxiliary register.); `MIPRE.Introspection.registerParty` (Split a local basis and keep the original ancilla last.); `MIPRE.Introspection.registerState` (EPR together with the original ancillary state, in the original basis.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `registerExtend_mul`, `registerExtend_sub`, `registerExtend_sum`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.RegisterEPR` (`MIPRE/Foundations/Introspection/RegisterEPR.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 36 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/RegisterEPR.lean; blueprint def:register-model

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RegisterEPR.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport

/-! # Splitting the maximally entangled state along computational registers -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

/-- The maximally entangled state, indexed by an arbitrary finite basis. -/
def registerEPR (I : Type*) [Fintype I] [DecidableEq I] : I × I → ℂ :=
  fun p => if p.1 = p.2 then (((Real.sqrt (Fintype.card I))⁻¹ : ℝ) : ℂ) else 0

/-- EPR together with the original ancillary state, in the original basis. -/
def registerState (I : Type*) [Fintype I] [DecidableEq I] (ξ : H × K → ℂ) :
    (I × H) × (I × K) → ℂ := expVec (registerEPR I) ξ

/-- Split a local basis and keep the original ancilla last. -/
def registerParty (e : I ≃ J × R) (H : Type*) : I × H ≃ J × (R × H) :=
  (e.prodCongr (Equiv.refl H)).trans (Equiv.prodAssoc J R H)

/-- The complementary register is moved behind the original auxiliary register. -/
def registerOutside (e : I ≃ J × R) (H : Type*) : I × H ≃ (J × H) × R :=
  ((registerParty e H).trans
    ((Equiv.refl J).prodCongr (Equiv.prodComm R H))).trans (Equiv.prodAssoc J H R).symm

/-- Put a local operator on the first register, leaving the complement untouched. -/
def registerExtend (e : I ≃ J × R) (M : Matrix (J × H) (J × H) ℂ) :
    Matrix (I × H) (I × H) ℂ :=
  registerOp (registerOutside e H) (M ⊗ₖ (1 : Matrix R R ℂ))

@[simp] theorem registerExtend_sub (e : I ≃ J × R)
    (M N : Matrix (J × H) (J × H) ℂ) :
    registerExtend e (M - N) = registerExtend e M - registerExtend e N := by
  ext i j
  simp only [registerExtend, registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

@[simp] theorem registerExtend_mul (e : I ≃ J × R)
    (M N : Matrix (J × H) (J × H) ℂ) :
    registerExtend e (M * N) = registerExtend e M * registerExtend e N := by
  unfold registerExtend
  rw [← registerOp_mul, ← Matrix.mul_kronecker_mul, one_mul]

@[simp] theorem registerExtend_sum {A : Type*} [Fintype A] (e : I ≃ J × R)
    (M : A → Matrix (J × H) (J × H) ℂ) :
    registerExtend e (∑ a, M a) = ∑ a, registerExtend e (M a) := by
  ext i j
  simp only [registerExtend, registerOp_apply, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Finset.sum_mul]

end MIPRE.Introspection

end


