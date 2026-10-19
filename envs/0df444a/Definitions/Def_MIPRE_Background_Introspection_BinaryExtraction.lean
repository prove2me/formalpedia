-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_BinaryExtraction
-- name    : MIPRE_Background_Introspection_BinaryExtraction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:53:50.185338+00:00
-- url     : https://prove2.me/theorems/89a13a5c-2416-4201-bf0e-2fdc0cb4f2c5
-- title:
--   Definitions of BinaryExtraction: Transporting field-register extraction into binary coordinates This is an exact change of computational basis, using a…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.BinaryExtraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Transporting field-register extraction into binary coordinates. This is an exact change of computational basis, using a self-dual field basis. It neither assumes nor proves the existence of QLD extraction witnesses.
--
--   **Definitions** (3): `MIPRE.Introspection.RestrictedSoundness.FieldExtraction` (The same three extraction estimates in the field computational basis, with ideal generalized Pauli projectors and genuine full-register…); `MIPRE.Introspection.RestrictedSoundness.FieldExtraction.mono` (Increasing the common error bound leaves the actual extraction data unchanged.); `MIPRE.Introspection.RestrictedSoundness.FieldExtraction.toBinary` (Exact field-to-binary conversion of the full extraction witness.).
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `binaryX`, `binaryZ`, `binary_alice_error`, `binary_bob_error`, `binary_state_error`, `image_pull`, `pull_isometry`, `registerOp_aOp`, `registerOp_bOp`, `registerState_pull`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.BinaryExtraction` (`MIPRE/Background/Introspection/BinaryExtraction.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 210 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/BinaryExtraction.lean; blueprint cor:qld-binary, cor:qld-valid

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/BinaryExtraction.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
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
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInitialInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Definitions.Def_MIPRE_Foundations_Introspection_IntrospectCanonicalization
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDecodedInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualFactor
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageReadTests
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXTest
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_RegisteredExtensionErrors
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityOrientation
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityIteration
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityGame
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionStep
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePlayerSwap
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveBobIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTwoSidedIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTerminalInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_TerminalOptionExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_PrimitiveSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ExtractedStateSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ValidPauliSoundness
import Definitions.Def_MIPRE_Background_Introspection_RestrictedSoundness
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
import Definitions.Def_MIPRE_Foundations_GameTransportProjection
import Definitions.Def_MIPRE_Background_Introspection_ExplicitGame
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingValue
import Definitions.Def_MIPRE_Background_Introspection_RestrictedProfileSoundness
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_Weyl_proj_wX_binEquiv
import Theorems.Thm_MIPRE_Weyl_proj_wZ
import Theorems.Thm_MIPRE_Weyl_proj_wZ_binEquiv

/-! # Transporting field-register extraction into binary coordinates

This is an exact change of computational basis, using a self-dual field basis.
It neither assumes nor proves the existence of QLD extraction witnesses.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
open scoped Kronecker
set_option linter.unusedSectionVars false

section Reindex
variable {I J H K R S R' S' : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype R'] [DecidableEq R'] [Fintype S'] [DecidableEq S']

theorem pull_isometry (e : R' ≃ R) (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    (V.submatrix e id)ᴴ * V.submatrix e id = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV]
  rfl

theorem image_pull (e : R' ≃ R) (V : Matrix R H ℂ) (M : Matrix H H ℂ) :
    isometricImage (V.submatrix e id) M = registerOp e (isometricImage V M) := by
  unfold isometricImage registerOp
  rw [Matrix.conjTranspose_submatrix]
  change V.submatrix e (Equiv.refl H) * M.submatrix (Equiv.refl H) (Equiv.refl H) *
    Vᴴ.submatrix (Equiv.refl H) e = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem state_pull (e : R' ≃ R) (f : S' ≃ S)
    (V : Matrix R H ℂ) (W : Matrix S K ℂ) (ψ : H × K → ℂ) :
    isometricState (V.submatrix e id) (W.submatrix f id) ψ =
      isometricState V W ψ ∘ e.prodCongr f := rfl

theorem registerState_pull (e : J ≃ I) (ξ : H × K → ℂ) :
    registerState I ξ ∘ (e.prodCongr (Equiv.refl H)).prodCongr (e.prodCongr (Equiv.refl K)) =
      registerState J ξ := by
  funext p
  exact congrArg (fun z => z * ξ (p.1.2, p.2.2))
    (congrFun (registerEPR_equiv e) (p.1.1, p.2.1))

theorem snorm_pull (e : R' ≃ R) (ψ : R → ℂ) (M : Matrix R R ℂ) :
    snorm (ψ ∘ e) (registerOp e M) = snorm ψ M := by
  unfold snorm
  rw [registerOp_mulVec, norm_evec_comp_equiv]

theorem registerOp_aOp (e : R' ≃ R) (f : S' ≃ S) (M : Matrix R R ℂ) :
    registerOp (e.prodCongr f) (aOp M) = aOp (registerOp e M) := by
  simp only [aOp, registerOp_kronecker, registerOp_one]

theorem registerOp_bOp (e : R' ≃ R) (f : S' ≃ S) (M : Matrix S S ℂ) :
    registerOp (e.prodCongr f) (bOp M) = bOp (registerOp f M) := by
  simp only [bOp, registerOp_kronecker, registerOp_one]

end Reindex

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d : ℕ} [NeZero m]

/-- The same three extraction estimates in the field computational basis,
with ideal generalized Pauli projectors and genuine full-register answers. -/
structure FieldExtraction (hm : m ∣ Fintype.card F)
    (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (δ : ℝ) where
  dA : ℕ
  dB : ℕ
  ξ : Fin dA × Fin dB → ℂ
  ξ_unit : star ξ ⬝ᵥ ξ = 1
  VA : Matrix (QLD.Honest.Register F m × Fin dA) (Fin R.dA) ℂ
  VB : Matrix (QLD.Honest.Register F m × Fin dB) (Fin R.dB) ℂ
  VA_isometry : VAᴴ * VA = 1
  VB_isometry : VBᴴ * VB = 1
  state_error : ‖evec (isometricState VA VB R.ψ -
    registerState (QLD.Honest.Register F m) ξ)‖ ≤ δ
  X_error : ∑ x : QLD.Honest.Register F m,
    snorm (registerState (QLD.Honest.Register F m) ξ) (aOp
      (isometricImage VA (R.PA.M (.pauli .X) (.pauliAns x)) -
        (aOp (Weyl.proj Weyl.wX x) : Matrix (QLD.Honest.Register F m × Fin dA) _ ℂ))) ^ 2 ≤ δ
  Z_error : ∑ z : QLD.Honest.Register F m,
    snorm (registerState (QLD.Honest.Register F m) ξ) (bOp
      (isometricImage VB (R.PB.M (.pauli .Z) (.pauliAns z)) -
        (aOp (Weyl.proj Weyl.wZ z) : Matrix (QLD.Honest.Register F m × Fin dB) _ ℂ))) ^ 2 ≤ δ

/-- Increasing the common error bound leaves the actual extraction data unchanged. -/
def FieldExtraction.mono {hm : m ∣ Fintype.card F}
    {R : TensorProductStrategy (QLD.qldGame (d := d) hm)} {δ δ' : ℝ}
    (w : FieldExtraction hm R δ) (h : δ ≤ δ') : FieldExtraction hm R δ' where
  dA := w.dA
  dB := w.dB
  ξ := w.ξ
  ξ_unit := w.ξ_unit
  VA := w.VA
  VB := w.VB
  VA_isometry := w.VA_isometry
  VB_isometry := w.VB_isometry
  state_error := w.state_error.trans h
  X_error := w.X_error.trans h
  Z_error := w.Z_error.trans h

theorem binaryX (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (x : Seed m t) :
    registerOp (Weyl.binEquiv b).symm
      (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x)) = Honest.pauliXReadout (some x) := by
  have h := Weyl.proj_wX_binEquiv hb ((Weyl.binEquiv (n := Fin m → Bool) b).symm x)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h, Honest.pauliXReadout_some]
  exact registerOp_inv (Weyl.binEquiv b) _

theorem binaryZ (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (x : Seed m t) :
    registerOp (Weyl.binEquiv b).symm
      (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm x)) =
      readout (some : Seed m t → Option (Seed m t)) (some x) := by
  have h := Weyl.proj_wZ_binEquiv hb ((Weyl.binEquiv (n := Fin m → Bool) b).symm x)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h]
  change registerOp (Weyl.binEquiv b).symm (registerOp (Weyl.binEquiv b) _) = _
  rw [registerOp_inv]
  ext i j
  by_cases hij : i = j <;> simp [hij, Weyl.proj_wZ, Weyl.zProj_apply, readout]

section ErrorTransport
variable {H K H₀ K₀ : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H₀] [DecidableEq H₀] [Fintype K₀] [DecidableEq K₀]
  (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
  (ξ : H × K → ℂ)

theorem binary_state_error
    (V : Matrix (QLD.Honest.Register F m × H) H₀ ℂ)
    (W : Matrix (QLD.Honest.Register F m × K) K₀ ℂ) (ψ : H₀ × K₀ → ℂ) :
    ‖evec (isometricState
      (V.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)) id)
      (W.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)) id) ψ -
        registerState (Seed m t) ξ)‖ =
      ‖evec (isometricState V W ψ - registerState (QLD.Honest.Register F m) ξ)‖ := by
  rw [state_pull, ← registerState_pull (Weyl.binEquiv b).symm ξ]
  exact norm_evec_comp_equiv
    (((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)).prodCongr
      ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)))
    (isometricState V W ψ - registerState (QLD.Honest.Register F m) ξ)

include hb in
theorem binary_alice_error
    (V : Matrix (QLD.Honest.Register F m × H) H₀ ℂ) (M : Matrix H₀ H₀ ℂ) (x : Seed m t) :
    snorm (registerState (Seed m t) ξ) (aOp
      (isometricImage (V.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)) id) M -
        (aOp (Honest.pauliXReadout (some x)) : Matrix (Seed m t × H) _ ℂ))) =
    snorm (registerState (QLD.Honest.Register F m) ξ) (aOp
      (isometricImage V M -
        (aOp (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x)) :
          Matrix (QLD.Honest.Register F m × H) _ ℂ))) := by
  rw [image_pull, ← binaryX b hb x,
    ← registerOp_aOp (Weyl.binEquiv b).symm (Equiv.refl H), ← registerOp_sub,
    ← registerState_pull (Weyl.binEquiv b).symm ξ,
    ← registerOp_aOp _ ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)), snorm_pull]

include hb in
theorem binary_bob_error
    (V : Matrix (QLD.Honest.Register F m × K) K₀ ℂ) (M : Matrix K₀ K₀ ℂ) (x : Seed m t) :
    snorm (registerState (Seed m t) ξ) (bOp
      (isometricImage (V.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)) id) M -
        (aOp (readout (some : Seed m t → Option (Seed m t)) (some x)) :
          Matrix (Seed m t × K) _ ℂ))) =
    snorm (registerState (QLD.Honest.Register F m) ξ) (bOp
      (isometricImage V M -
        (aOp (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm x)) :
          Matrix (QLD.Honest.Register F m × K) _ ℂ))) := by
  rw [image_pull, ← binaryZ b hb x,
    ← registerOp_aOp (Weyl.binEquiv b).symm (Equiv.refl K), ← registerOp_sub,
    ← registerState_pull (Weyl.binEquiv b).symm ξ,
    ← registerOp_bOp ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)) _, snorm_pull]

end ErrorTransport

/-- Exact field-to-binary conversion of the full extraction witness. State
distance and both valid-answer error sums keep precisely the same bound. -/
def FieldExtraction.toBinary {hm : m ∣ Fintype.card F}
    {R : TensorProductStrategy (QLD.qldGame (d := d) hm)} {δ : ℝ}
    (w : FieldExtraction hm R δ) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) : Extraction hm b R δ where
  dA := w.dA
  dB := w.dB
  ξ := w.ξ
  ξ_unit := w.ξ_unit
  VA := w.VA.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl (Fin w.dA))) id
  VB := w.VB.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl (Fin w.dB))) id
  VA_isometry := pull_isometry _ _ w.VA_isometry
  VB_isometry := pull_isometry _ _ w.VB_isometry
  state_error := by rw [binary_state_error b w.ξ]; exact w.state_error
  X_error := by
    simp only [binary_alice_error b hb w.ξ, validAnswer]
    have he := Equiv.sum_comp (Weyl.binEquiv (n := Fin m → Bool) b).symm
      (fun x => snorm (registerState (QLD.Honest.Register F m) w.ξ) (aOp
        (isometricImage w.VA (R.PA.M (.pauli .X) (.pauliAns x)) -
          (aOp (Weyl.proj Weyl.wX x) : Matrix (QLD.Honest.Register F m × Fin w.dA) _ ℂ))) ^ 2)
    exact he.le.trans w.X_error
  Z_error := by
    simp only [binary_bob_error b hb w.ξ, validAnswer]
    have he := Equiv.sum_comp (Weyl.binEquiv (n := Fin m → Bool) b).symm
      (fun x => snorm (registerState (QLD.Honest.Register F m) w.ξ) (bOp
        (isometricImage w.VB (R.PB.M (.pauli .Z) (.pauliAns x)) -
          (aOp (Weyl.proj Weyl.wZ x) : Matrix (QLD.Honest.Register F m × Fin w.dB) _ ℂ))) ^ 2)
    exact he.le.trans w.Z_error

section SourceSoundness
variable {A I : Type} [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype I] [DecidableEq I] {ℓ : ℕ}

end SourceSoundness

end MIPRE.Introspection.RestrictedSoundness
end


