-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
-- name    : MIPRE_Foundations_Introspection_TypedQuotientPredicate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:56:08.070934+00:00
-- url     : https://prove2.me/theorems/3922c43a-45ef-45b9-9a9b-dcc3b8ee8c98
-- title:
--   Definitions of TypedQuotientPredicate: Quotient hiding comparisons in the complete typed predicate The quotient comparisons accept every legacy accepted tuple
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.TypedQuotientPredicate` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Quotient hiding comparisons in the complete typed predicate. The quotient comparisons accept every legacy accepted tuple. Deterministic answer decoding restores legacy acceptance on every raw question and answer, including consistency loops and both orientations of auxiliary edges.
--
--   **Definitions** (3): `MIPRE.Introspection.AuxiliaryQuotient.check` (Complete typed predicate with quotient hiding comparisons.); `MIPRE.Introspection.AuxiliaryQuotient.decodeAnswer` (Decode only dual coordinates, with the CL function selected by question side.); `MIPRE.Introspection.AuxiliaryQuotient.directed` (The directed tests with the two exact dual comparisons replaced by quotient comparisons.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fits_decodeAnswer`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.TypedQuotientPredicate` (`MIPRE/Foundations/Introspection/TypedQuotientPredicate.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 95 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedQuotientPredicate.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedQuotientPredicate.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks

/-! # Quotient hiding comparisons in the complete typed predicate

The quotient comparisons accept every legacy accepted tuple. Deterministic
answer decoding restores legacy acceptance on every raw question and answer,
including consistency loops and both orientations of auxiliary edges.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient
open Classical
set_option backward.isDefEq.respectTransparency false
variable {PauliType PauliAnswer F A : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Decode only dual coordinates, with the CL function selected by question side. -/
def decodeAnswer (L : Bool → CL.CLFun F (ι) ℓ) :
    QuestionType PauliType ℓ → ParsedAnswer (ι → F) A PauliAnswer →
      ParsedAnswer (ι → F) A PauliAnswer
  | .inr (_, w), .read y yp a => .read y (AuxiliaryDual.decodeDual (L w) y yp) a
  | .inr (_, w), .hide y yp x => .hide y (AuxiliaryDual.decodeDual (L w) y yp) x
  | _, a => a

/-- Decoding preserves the answer constructor and hence the format check. -/
@[simp] theorem fits_decodeAnswer (L : Bool → CL.CLFun F (ι) ℓ)
    (t : QuestionType PauliType ℓ) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedPredicate.fits t (decodeAnswer L t a) = TypedPredicate.fits t a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> rfl

/-- The directed tests with the two exact dual comparisons replaced by quotient comparisons. -/
def directed (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → (ι) → F)
    (D : ((ι) → F) → ((ι) → F) → A → A → Bool) :
    QuestionType PauliType ℓ → QuestionType PauliType ℓ →
      ParsedAnswer ((ι) → F) A PauliAnswer → ParsedAnswer ((ι) → F) A PauliAnswer → Bool
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
        decide (hidingNext (L w) k.val (y, yp, x) (z, zp, t)) else true
  | .inl p, .inr (.hide k, w), .pauli a, .hide y yp x =>
      if p = X ∧ k.val = 0 then decide (hidingPauli (L w) (projectPauli a) (y, yp, x))
      else true
  | .inr (.introspect, false), .inr (.introspect, true), .pair x a, .pair y b => D x y a b
  | _, _, _, _ => true

variable (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)

/-- Complete typed predicate with quotient hiding comparisons. All format,
consistency, Pauli and source-game checks are unchanged. -/
def check (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) : Bool :=
  TypedPredicate.fits t a && TypedPredicate.fits u b &&
    (if t = u then decide (a = b) else true) &&
    (match t, u, a, b with
      | .inl p, .inl q, .pauli x, .pauli y => DP p q x y
      | _, _, _, _ => true) &&
    directed L X Z project D t u a b && directed L X Z project D u t b a

end MIPRE.Introspection.AuxiliaryQuotient


