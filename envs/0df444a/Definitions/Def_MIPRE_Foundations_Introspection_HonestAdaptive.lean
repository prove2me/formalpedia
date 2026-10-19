-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
-- name    : MIPRE_Foundations_Introspection_HonestAdaptive
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:11.308549+00:00
-- url     : https://prove2.me/theorems/4961a82f-c822-40f7-97e1-fcb8e5187bb2
-- title:
--   Definitions of HonestAdaptive: The adaptive honest Read and Hide measurements The recursion follows the CL presentation itself
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HonestAdaptive` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The adaptive honest Read and Hide measurements. The recursion follows the CL presentation itself. At a `cons` node the joint Z/linear and X/dual-linear measurement is made on the current register. Its Z outcome selects the continuation on the complementary register. These are actual projective measurements; no commutation assumption on different continuations is needed.
--
--   **Definitions** (11): `MIPRE.Introspection.Honest.HideLabel`; `MIPRE.Introspection.Honest.ReadLabel`; `MIPRE.Introspection.Honest.adaptiveTensor` (Measure one register and use its outcome to select a measurement of the other.); `MIPRE.Introspection.Honest.hideRegister` (The honest Hide measurement at zero-based stage `k`.); `MIPRE.Introspection.Honest.insertRegister` (Extend an assignment on an active register by zero to the ambient space.); `MIPRE.Introspection.Honest.joinHide`; `MIPRE.Introspection.Honest.joinRead`; `MIPRE.Introspection.Honest.localRead` (The honest commuting local Z/linear and X/dual-linear measurement.); `MIPRE.Introspection.Honest.readRegister` (The register part of the honest Read measurement, including all adaptive stages.); `MIPRE.Introspection.Honest.stopHide`; `MIPRE.Introspection.Honest.stopHideAnswer` (At a stopping node, retain the full X tail and the first dual value, without reading Z.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `hideRegister_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HonestAdaptive` (`MIPRE/Foundations/Introspection/HonestAdaptive.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 47 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HonestAdaptive.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestAdaptive.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
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
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Theorems.Thm_MIPRE_IsPVM_coarse

/-! # The adaptive honest Read and Hide measurements

The recursion follows the CL presentation itself. At a `cons` node the joint
Z/linear and X/dual-linear measurement is made on the current register. Its Z
outcome selects the continuation on the complementary register. These are
actual projective measurements; no commutation assumption on different
continuations is needed.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section AdaptiveTensor

variable {I J A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

/-- Measure one register and use its outcome to select a measurement of the other. -/
def adaptiveTensor (P : A → Matrix I I ℂ) (Q : A → B → Matrix J J ℂ)
    (ab : A × B) : Matrix (I × J) (I × J) ℂ := P ab.1 ⊗ₖ Q ab.1 ab.2

end AdaptiveTensor

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]

abbrev ReadLabel (F ι : Type*) := (ι → F) × (ι → F)
abbrev HideLabel (F ι : Type*) := (ι → F) × (ι → F) × (ι → F)

/-- Extend an assignment on an active register by zero to the ambient space. -/
def insertRegister (V : Finset ι) (x : V → F) : ι → F :=
  fun i => if h : i ∈ V then x ⟨i, h⟩ else 0

/-- The honest commuting local Z/linear and X/dual-linear measurement. -/
def localRead {S : Finset ι} (L : CL.RegLinear F S)
    (ab : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    Matrix (Fin (Fintype.card S) → F) (Fin (Fintype.card S) → F) ℂ :=
  synOf wZ (coordinateLinear L) ab.1 * synOf wX (CL.lperp (coordinateLinear L)) ab.2

def joinRead (S : Finset ι)
    (a : ((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) × ReadLabel F ι) :
    ReadLabel F ι :=
  (coordinateInsert S a.1.1 + a.2.1, coordinateInsert S a.1.2 + a.2.2)

def joinHide (S : Finset ι)
    (a : ((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) × HideLabel F ι) :
    HideLabel F ι :=
  (coordinateInsert S a.1.1 + a.2.1, coordinateInsert S a.1.2 + a.2.2.1, a.2.2.2)

/-- The register part of the honest Read measurement, including all adaptive stages. -/
def readRegister : {ℓ : ℕ} → (P : CL.CLFun F ι ℓ) → (V : Finset ι) →
    P.SupportedOn V → ReadLabel F ι → Matrix (V → F) (V → F) ℂ
  | _, .zero, _, _, a => if a = (0, 0) then 1 else 0
  | _, .cons S L next, V, h, a =>
      registerOp (coordinateSplit S V h.1)
        (∑ q ∈ Finset.univ.filter (fun q => joinRead S q = a),
          adaptiveTensor (localRead L)
            (fun z => readRegister (next (coordinateInsert S z.1)) (V \ S)
              (h.2 (coordinateInsert S z.1))) q)

/-- At a stopping node, retain the full X tail and the first dual value, without reading Z. -/
def stopHideAnswer {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) (x : V → F) :
    HideLabel F ι := firstHideAnswer P (insertRegister V x)

def stopHide {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) :
    HideLabel F ι → Matrix (V → F) (V → F) ℂ := synOf wX (stopHideAnswer P V)

/-- The honest Hide measurement at zero-based stage `k`. Earlier stages read joint
Z/linear and X/dual-linear outcomes; the current stage and remaining tail use X only. -/
def hideRegister : {ℓ : ℕ} → (P : CL.CLFun F ι ℓ) → (k : ℕ) → (V : Finset ι) →
    P.SupportedOn V → HideLabel F ι → Matrix (V → F) (V → F) ℂ
  | _, P, 0, V, _, a => stopHide P V a
  | _, .zero, _ + 1, V, _, a => stopHide .zero V a
  | _, .cons S L next, k + 1, V, h, a =>
      registerOp (coordinateSplit S V h.1)
        (∑ q ∈ Finset.univ.filter (fun q => joinHide S q = a),
          adaptiveTensor (localRead L)
            (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S)
              (h.2 (coordinateInsert S z.1))) q)

@[simp] theorem hideRegister_zero {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) :
    hideRegister P 0 V h a = stopHide P V a := by
  cases P <;> rfl

end MIPRE.Introspection.Honest


