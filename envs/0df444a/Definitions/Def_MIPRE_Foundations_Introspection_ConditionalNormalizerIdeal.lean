-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
-- name    : MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:06:36.498437+00:00
-- url     : https://prove2.me/theorems/3ef19758-0f41-4b7b-9af9-b42bac7dafbb
-- title:
--   Definitions of ConditionalNormalizerIdeal: Concrete ideal prefixes for honest hiding The next Z prefix is a marginal of the adjacent honest hiding PVM
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Concrete ideal prefixes for honest hiding. The next Z prefix is a marginal of the adjacent honest hiding PVM. Thus its commutation with the preceding honest hiding family follows from the proved adjacent commutation, without a new commutation assumption.
--
--   **Definitions** (6): `MIPRE.Introspection.Honest.hideCoarseOp` (The preceding ideal hiding family retains precisely the fine label used by the parsed soundness induction.); `MIPRE.Introspection.Honest.hideLabelAnswer` (Interpret a register hiding label as a correctly formatted parsed answer.); `MIPRE.Introspection.Honest.hideLabelCoarse`; `MIPRE.Introspection.Honest.hideLabelNext`; `MIPRE.Introspection.Honest.hideNextRetain` (Discard the now redundant old prefix and retain the new prefix, current dual label, and tail.); `MIPRE.Introspection.Honest.hidingPrefixOp` (The ideal prefix retains an explicit zero operator for malformed labels.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `hidingPrefixOp_none`, `hidingPrefixOp_some`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal` (`MIPRE/Foundations/Introspection/ConditionalNormalizerIdeal.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 78 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizerIdeal.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizerIdeal.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps

/-! # Concrete ideal prefixes for honest hiding

The next Z prefix is a marginal of the adjacent honest hiding PVM. Thus its
commutation with the preceding honest hiding family follows from the proved
adjacent commutation, without a new commutation assumption.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The ideal prefix retains an explicit zero operator for malformed labels. -/
def hidingPrefixOp (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Option (ι → F) → Matrix (ι → F) (ι → F) ℂ :=
  readout (fun x => some ((P.truncate k).eval x))

@[simp] theorem hidingPrefixOp_none (P : CL.CLFun F ι ℓ) (k : ℕ) :
    hidingPrefixOp P k none = 0 := by
  ext x x'
  simp [hidingPrefixOp, readout, Matrix.diagonal_apply]

@[simp] theorem hidingPrefixOp_some (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    hidingPrefixOp P k (some y) = readout (P.truncate k).eval y := by
  ext x x'
  simp [hidingPrefixOp, readout, Matrix.diagonal_apply]

/-- Interpret a register hiding label as a correctly formatted parsed answer. -/
def hideLabelAnswer (a : HideLabel F ι) : ParsedAnswer (ι → F) Unit Unit :=
  .hide a.1 a.2.1 a.2.2

def hideLabelCoarse (P : CL.CLFun F ι ℓ) (k : ℕ) (a : HideLabel F ι) :
    Option (HideLabel F ι) := TypedEstimates.hidingCoarse P k (hideLabelAnswer a)

def hideLabelNext (P : CL.CLFun F ι ℓ) (k : ℕ) (a : HideLabel F ι) :
    Option (ι → F) × Option (HideLabel F ι) :=
  TypedEstimates.hidingNextLater P k (hideLabelAnswer a)

/-- The preceding ideal hiding family retains precisely the fine label used
by the parsed soundness induction. -/
def hideCoarseOp (P : CL.CLFun F ι ℓ) (k : ℕ) (h : P.SupportedOn univ) :
    Option (HideLabel F ι) → Matrix (ι → F) (ι → F) ℂ :=
  fibSum (hideOp P k h) (hideLabelCoarse P k)

/-- Discard the now redundant old prefix and retain the new prefix, current
dual label, and tail. Dummy or inconsistent formats remain a dummy outcome. -/
def hideNextRetain : Option (ι → F) × Option (HideLabel F ι) → Option (HideLabel F ι)
  | (some y, some (_, yp, x)) => some (y, yp, x)
  | _ => none

end MIPRE.Introspection.Honest


