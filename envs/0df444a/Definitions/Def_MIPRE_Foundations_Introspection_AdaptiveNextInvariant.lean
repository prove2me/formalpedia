-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
-- name    : MIPRE_Foundations_Introspection_AdaptiveNextInvariant
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:44:30.502757+00:00
-- url     : https://prove2.me/theorems/819a7f15-d5f3-41c0-b9d6-68dbb273bef5
-- title:
--   Definitions of AdaptiveNextInvariant: Closing the next-prefix measurement invariant The next residual PVM is constructed from the previous prefix and current…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptiveNextInvariant` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Closing the next-prefix measurement invariant. The next residual PVM is constructed from the previous prefix and current coordinate branch. Unattainable next prefixes receive a fixed default PVM; their ambient operators are zero. The answer component, including any dummy answer, is retained without an additional support assumption.
--
--   **Definitions** (5): `MIPRE.Introspection.AttainableStageCoordinate`; `MIPRE.Introspection.advanceStageAnswer` (Retain the original residual answer and advance only the prefix label.); `MIPRE.Introspection.nextPrefixResidual` (The residual projectors after advancing to the next prefix.); `MIPRE.Introspection.nextPrefixSource`; `MIPRE.Introspection.nextResidualOpAt` (Transport the already constructed residual block to an equal next label.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `exists_advancePrefix_source`, `nextPrefixSource_advance`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptiveNextInvariant` (`MIPRE/Foundations/Introspection/AdaptiveNextInvariant.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 104 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveNextInvariant.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveNextInvariant.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_StrategyDilation
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
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Theorems.Thm_MIPRE_Introspection_advancePrefix_eval

/-! # Closing the next-prefix measurement invariant

The next residual PVM is constructed from the previous prefix and current
coordinate branch. Unattainable next prefixes receive a fixed default PVM;
their ambient operators are zero. The answer component, including any dummy
answer, is retained without an additional support assumption.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}

abbrev AttainableStageCoordinate (P : CL.CLFun F ι ℓ) (k : ℕ) :=
  (y : ↥(prefixOutcomes P k)) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)

theorem exists_advancePrefix_source (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) (hv : v ∈ prefixOutcomes P (k + 1)) :
    ∃ p : AttainableStageCoordinate P k, advancePrefix P k p.1 p.2 = v := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hv
  exact ⟨⟨⟨(P.truncate k).eval x, mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩,
    (adaptiveLinearOutcome P k x).2⟩, advancePrefix_eval hP k x⟩

def nextPrefixSource (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) (hv : v ∈ prefixOutcomes P (k + 1)) :
    AttainableStageCoordinate P k := (exists_advancePrefix_source P hP k v hv).choose

theorem nextPrefixSource_advance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) (hv : v ∈ prefixOutcomes P (k + 1)) :
    advancePrefix P k (nextPrefixSource P hP k v hv).1
      (nextPrefixSource P hP k v hv).2 = v :=
  (exists_advancePrefix_source P hP k v hv).choose_spec

/-- Transport the already constructed residual block to an equal next label. -/
def nextResidualOpAt (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (v : ι → F) (hv : advancePrefix P k y z = v)
    (N : Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
      (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ) :
    Matrix ((stageRemaining P (k + 1) v → F) × (H × A))
      ((stageRemaining P (k + 1) v → F) × (H × A)) ℂ :=
  hv ▸ nextResidualOp P hP k y z N

/-- The residual projectors after advancing to the next prefix. -/
def nextPrefixResidual (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A) (v : ι → F) (a : A) :
    Matrix ((stageRemaining P (k + 1) v → F) × (H × A))
      ((stageRemaining P (k + 1) v → F) × (H × A)) ℂ :=
  if hv : v ∈ prefixOutcomes P (k + 1) then
    let p := nextPrefixSource P hP k v hv
    nextResidualOpAt P hP k p.1 p.2 v (nextPrefixSource_advance P hP k v hv) (D p.1 p.2 a)
  else readout (fun _ => a₀) a

/-- Retain the original residual answer and advance only the prefix label. -/
def advanceStageAnswer (P : CL.CLFun F ι ℓ) (k : ℕ) (p : AdaptiveStageAnswer P k A) :
    (ι → F) × A := (advancePrefix P k p.1 p.2.1, p.2.2)

end MIPRE.Introspection
end


