-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
-- name    : MIPRE_Foundations_Introspection_AdaptivePrefixMixing
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:49:04.100679+00:00
-- url     : https://prove2.me/theorems/f99a2c3f-33cf-4dca-b8f1-9386bdd29043
-- title:
--   Definitions of AdaptivePrefixMixing: Mixing on the actual adaptive continuation The prefix law, next linear map, and remaining coordinates are computed from…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptivePrefixMixing` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mixing on the actual adaptive continuation. The prefix law, next linear map, and remaining coordinates are computed from the CL presentation. Full-carrier errors of prefix-conditioned operators give the weighted hypotheses of mixing exactly. The constructed residual POVM acts on the complement of the next prefix, with the original ancilla.
--
--   **Definitions** (4): `MIPRE.Introspection.prefixStageCommutatorError` (Full-carrier commutation error with the actual prefix left in place.); `MIPRE.Introspection.prefixStageMarginalError` (Full-carrier marginal error, retaining its actual adaptive prefix projector.); `MIPRE.Introspection.stageRemaining` (The unvisited coordinates at an actual claimed prefix.); `MIPRE.Introspection.stageSplit` (Split the actual remaining register into its next factor and its continuation.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `stageFactor_subset_remaining`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptivePrefixMixing` (`MIPRE/Foundations/Introspection/AdaptivePrefixMixing.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 86 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptivePrefixMixing.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePrefixMixing.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Theorems.Thm_MIPRE_Introspection_CLChecks_stageFactor_subset_residual

/-! # Mixing on the actual adaptive continuation

The prefix law, next linear map, and remaining coordinates are computed from
the CL presentation. Full-carrier errors of prefix-conditioned operators
give the weighted hypotheses of mixing exactly. The constructed residual
POVM acts on the complement of the next prefix, with the original ancilla.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- The unvisited coordinates at an actual claimed prefix. -/
abbrev stageRemaining (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) : Finset ι :=
  (CLChecks.prefixRegister P k y)ᶜ

theorem stageFactor_subset_remaining (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k y ⊆ stageRemaining P k y := by
  simpa only [stageRemaining, Finset.compl_eq_univ_sdiff] using
    CLChecks.stageFactor_subset_residual hP k y

/-- Split the actual remaining register into its next factor and its continuation. -/
def stageSplit (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    (stageRemaining P k y → F) ≃ (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ×
      ((↥(stageRemaining P k y \ P.factorOfPrefix k y)) → F) :=
  coordinateSplit _ _ (stageFactor_subset_remaining P hP k y)

/-- Full-carrier marginal error, retaining its actual adaptive prefix projector. -/
def prefixStageMarginalError (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ) : ℝ :=
  ∑ y, ∑ z, stateSqNorm (registerState (ι → F) ξ)
    (prefixResidualOp P k y (∑ a, M y (z, a)) -
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y)
        wZ (coordinateLinear (CLChecks.stageLinear P k y)) z))

/-- Full-carrier commutation error with the actual prefix left in place. -/
def prefixStageCommutatorError (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F)
        (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) : ℝ :=
  ∑ y, ∑ p, ∑ z, stateSqNorm (registerState (ι → F) ξ)
    (prefixResidualOp P k y (M y p) *
        prefixResidualOp P k y (registerReadout (stageSplit P hP k y) (w y) (L y) z) -
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y) (w y) (L y) z) *
        prefixResidualOp P k y (M y p))

end MIPRE.Introspection

end


