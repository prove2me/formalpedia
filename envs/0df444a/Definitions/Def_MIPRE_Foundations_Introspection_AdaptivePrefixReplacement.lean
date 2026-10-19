-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
-- name    : MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:45:31.526021+00:00
-- url     : https://prove2.me/theorems/6c1f53a0-b03c-4685-af68-26d5074c6985
-- title:
--   Definitions of AdaptivePrefixReplacement: Actual adaptive residual projectors after mixing Every conditioned prefix uses its actual remaining coordinates
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptivePrefixReplacement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Actual adaptive residual projectors after mixing. Every conditioned prefix uses its actual remaining coordinates. Naimark produces projective residual measurements with the single ancilla alphabet `A` and fixed state `a₀`. The original prefix and the next Z readout remain explicit tensor factors, and the error is averaged with the actual CL law.
--
--   **Definitions** (5): `MIPRE.Introspection.AdaptiveDilationFamily`; `MIPRE.Introspection.AdaptiveStageAnswer` (Joint outcomes retain the actual prefix and the next factor's outcome.); `MIPRE.Introspection.adaptiveOldJointPOVM` (The actual old joint PVM, with dependent local outcome spaces.); `MIPRE.Introspection.adaptiveReplacementJointOp` (The next joint PVM on one ambient register, retaining both the old prefix and the new Z factor explicitly.); `MIPRE.Introspection.adaptiveReplacementPOVM` (The same actual joint PVM, in the extension ordering used by the replacement-strategy constructor.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `adaptiveReplacementJointOp_isPVM`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptivePrefixReplacement` (`MIPRE/Foundations/Introspection/AdaptivePrefixReplacement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 98 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptivePrefixReplacement.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePrefixReplacement.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_exists_projective_dilation
import Theorems.Thm_MIPRE_Introspection_prefixResidual_isPVM
import Theorems.Thm_MIPRE_Introspection_reassociatedConditionalDilation_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ

/-! # Actual adaptive residual projectors after mixing

Every conditioned prefix uses its actual remaining coordinates. Naimark
produces projective residual measurements with the single ancilla alphabet
`A` and fixed state `a₀`. The original prefix and the next Z readout remain
explicit tensor factors, and the error is averaged with the actual CL law.
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

/-- Joint outcomes retain the actual prefix and the next factor's outcome. -/
abbrev AdaptiveStageAnswer (P : CL.CLFun F ι ℓ) (k : ℕ) (A : Type*) :=
  (y : ι → F) × ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)

abbrev AdaptiveDilationFamily (P : CL.CLFun F ι ℓ) (k : ℕ) (H A : Type*) :=
  (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) → A →
    Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
      (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ

/-- The actual old joint PVM, with dependent local outcome spaces. -/
def adaptiveOldJointPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val)) :
    POVM (AdaptiveStageAnswer P k A) ((ι → F) × H) :=
  (prefixResidual_isPVM P hP k (fun y p => ((M y).mats p).val) hM).toPOVM

/-- The next joint PVM on one ambient register, retaining both the old
prefix and the new Z factor explicitly. -/
def adaptiveReplacementJointOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (p : AdaptiveStageAnswer P k A) :
    Matrix ((ι → F) × (H × A)) ((ι → F) × (H × A)) ℂ :=
  prefixResidualOp P k p.1 (reassociatedConditionalDilation (stageSplit P hP k p.1)
    (synOf wZ (coordinateLinear (CLChecks.stageLinear P k p.1))) (D p.1) p.2)

set_option maxHeartbeats 800000 in
theorem adaptiveReplacementJointOp_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    IsPVM (adaptiveReplacementJointOp P hP k D) :=
  prefixResidual_isPVM P hP k
    (fun y => reassociatedConditionalDilation (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y))
    (fun y => reassociatedConditionalDilation_isPVM (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)))
      (isPVM_synOf isWeylFamily_wZ _) (D y) (hD y))

/-- The same actual joint PVM, in the extension ordering used by the
replacement-strategy constructor. -/
def adaptiveReplacementPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    POVM (AdaptiveStageAnswer P k A) (((ι → F) × H) × A) :=
  (registerOp_isPVM (Equiv.prodAssoc (ι → F) H A)
    (adaptiveReplacementJointOp_isPVM P hP k D hD)).toPOVM

end MIPRE.Introspection
end


