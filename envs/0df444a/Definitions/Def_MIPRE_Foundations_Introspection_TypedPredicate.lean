-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
-- name    : MIPRE_Foundations_Introspection_TypedPredicate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:51:31.394386+00:00
-- url     : https://prove2.me/theorems/c177c91c-14b4-42ef-8fe5-e51348d34e02
-- title:
--   Definitions of TypedPredicate: The parsed typed introspection predicate This supplies the actual finite decision predicate, including both…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.TypedPredicate` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The parsed typed introspection predicate. This supplies the actual finite decision predicate, including both orientations of every auxiliary test and the original game test. The Pauli predicate and its X/Z answer projection are supplied by the Pauli test. This semantic layer does not assert the remaining byte parser, answer clock, or program compiler.
--
--   **Definitions** (4): `MIPRE.Introspection.ParsedAnswer` (The four parsed answer formats.); `MIPRE.Introspection.TypedPredicate.check` (The actual parsed predicate: format, consistency, Pauli, and both auxiliary orientations.); `MIPRE.Introspection.TypedPredicate.directed` (One orientation of all sampling/hiding/game comparisons.); `MIPRE.Introspection.TypedPredicate.fits` (Check the parsed answer constructor against the question type.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.TypedPredicate` (`MIPRE/Foundations/Introspection/TypedPredicate.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 45 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedPredicate.lean; blueprint lem:intro-parsed-predicate

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPredicate.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # The parsed typed introspection predicate

This supplies the actual finite decision predicate, including both orientations
of every auxiliary test and the original game test. The Pauli predicate and
its X/Z answer projection are supplied by the Pauli test. This semantic layer
does not assert the remaining byte parser, answer clock, or program compiler.
-/

namespace MIPRE.Introspection

/-- The four parsed answer formats. Sample and Introspect share the pair format. -/
inductive ParsedAnswer (V A P : Type*)
  | pauli (a : P)
  | pair (y : V) (a : A)
  | read (y yp : V) (a : A)
  | hide (y yp x : V)
  deriving DecidableEq, Fintype

noncomputable section

namespace TypedPredicate

open Classical

variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Check the parsed answer constructor against the question type. -/
def fits : QuestionType PauliType ℓ → ParsedAnswer (ι → F) A PauliAnswer → Bool
  | .inl _, .pauli _ => true
  | .inr (.introspect, _), .pair _ _ => true
  | .inr (.sample, _), .pair _ _ => true
  | .inr (.read, _), .read _ _ _ => true
  | .inr (.hide _, _), .hide _ _ _ => true
  | _, _ => false

/-- One orientation of all sampling/hiding/game comparisons.
The caller checks both orientations, as required by the symmetric type graph. -/
def directed (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool) :
    QuestionType PauliType ℓ → QuestionType PauliType ℓ →
      ParsedAnswer (ι → F) A PauliAnswer → ParsedAnswer (ι → F) A PauliAnswer → Bool
  | .inl p, .inr (.sample, _), .pauli a, .pair z _ =>
      if p = Z then decide (projectPauli a = z) else true
  | .inr (.introspect, w), .inr (.sample, v), .pair y a, .pair z b =>
      if w = v then decide (CLChecks.sampling (L w) (y, a) (z, b)) else true
  | .inr (.introspect, w), .inr (.read, v), .pair y a, .read z zp b =>
      if w = v then decide (CLChecks.reading (y, a) (z, zp, b)) else true
  | .inr (.hide k, w), .inr (.read, v), .hide y yp x, .read z zp a =>
      if w = v ∧ k.val + 1 = ℓ then decide (CLChecks.hidingRead (L w) (y, yp, x) (z, zp, a))
      else true
  | .inr (.hide k, w), .inr (.hide j, v), .hide y yp x, .hide z zp t =>
      if w = v ∧ k.val + 1 = j.val then
        decide (CLChecks.hidingNext (L w) k.val (y, yp, x) (z, zp, t)) else true
  | .inl p, .inr (.hide k, w), .pauli a, .hide y yp x =>
      if p = X ∧ k.val = 0 then decide (CLChecks.hidingPauli (L w) (projectPauli a) (y, yp, x))
      else true
  | .inr (.introspect, false), .inr (.introspect, true), .pair x a, .pair y b => D x y a b
  | _, _, _, _ => true

/-- The actual parsed predicate: format, consistency, Pauli, and both auxiliary orientations. -/
def check (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) : Bool :=
  fits t a && fits u b && (if t = u then decide (a = b) else true) &&
    (match t, u, a, b with | .inl p, .inl q, .pauli x, .pauli y => DP p q x y | _, _, _, _ => true) &&
    directed L X Z projectPauli D t u a b && directed L X Z projectPauli D u t b a

variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)

end TypedPredicate
end
end MIPRE.Introspection


