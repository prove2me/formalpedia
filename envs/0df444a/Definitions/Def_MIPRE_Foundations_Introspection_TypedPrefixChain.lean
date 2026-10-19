-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
-- name    : MIPRE_Foundations_Introspection_TypedPrefixChain
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:56.290284+00:00
-- url     : https://prove2.me/theorems/f09eaaf0-8e34-42e6-b288-168601c62bfe
-- title:
--   Definitions of TypedPrefixChain: Propagating reported question prefixes through the actual hiding chain The adjacent hiding, terminal hiding/Read, and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.TypedPrefixChain` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Propagating reported question prefixes through the actual hiding chain. The adjacent hiding, terminal hiding/Read, and Read/Introspect tests preserve every earlier question prefix. Coarse-graining these accepted-answer relations before using consistency loops gives a polynomial chain loss, without an answer-cardinality factor or an assumption that claimed answers are CL images.
--
--   **Definitions** (2): `MIPRE.Introspection.TypedEstimates.prefixChainType` (The actual auxiliary path starting at hiding level `j`, followed by Read and Introspect.); `MIPRE.Introspection.TypedEstimates.reportedPrefix` (The reported question prefix, with a shared dummy outcome for answer constructors that do not fit the specified auxiliary question type.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `prefixChainType_end`, `prefixChainType_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.TypedPrefixChain` (`MIPRE/Foundations/Introspection/TypedPrefixChain.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 59 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedPrefixChain.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPrefixChain.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
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
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
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

/-! # Propagating reported question prefixes through the actual hiding chain

The adjacent hiding, terminal hiding/Read, and Read/Introspect tests preserve
every earlier question prefix. Coarse-graining these accepted-answer relations
before using consistency loops gives a polynomial chain loss, without an
answer-cardinality factor or an assumption that claimed answers are CL images.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The reported question prefix, with a shared dummy outcome for answer
constructors that do not fit the specified auxiliary question type. -/
def reportedPrefix (P : CL.CLFun F ι ℓ) (m : ℕ) :
    AuxType ℓ → ParsedAnswer (ι → F) A PauliAnswer → Option (ι → F)
  | .introspect, .pair y _ => some (P.outputPrefix m y)
  | .sample, .pair y _ => some (P.outputPrefix m y)
  | .read, .read y _ _ => some (P.outputPrefix m y)
  | .hide _, .hide y _ _ => some (P.outputPrefix m y)
  | _, _ => none

variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)

/-- The actual auxiliary path starting at hiding level `j`, followed by Read
and Introspect. Beyond the endpoint it remains at Introspect. -/
def prefixChainType (j : Fin ℓ) (i : ℕ) : AuxType ℓ :=
  if h : j.val + i < ℓ then .hide ⟨j.val + i, h⟩
  else if j.val + i = ℓ then .read else .introspect

@[simp] theorem prefixChainType_zero (j : Fin ℓ) : prefixChainType j 0 = .hide j := by
  simp [prefixChainType, j.isLt]

@[simp] theorem prefixChainType_end (j : Fin ℓ) :
    prefixChainType j (ℓ - j.val + 1) = .introspect := by
  have he : j.val + (ℓ - j.val + 1) = ℓ + 1 := by omega
  simp [prefixChainType, he]

variable [DecidableEq PauliType]

end MIPRE.Introspection.TypedEstimates

end


