-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
-- name    : LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:16:49.645734+00:00
-- url     : https://prove2.me/theorems/d18f5362-a84c-4889-a267-8627ad1d7d78
-- title:
--   LIDT definitions: LDT / Pasting / ComparisonLemmas / CommuteGHalfSandwich / MoveChain / Lifting
-- statement:
--   This bundle supplies the equivalences and lifted families used to extend the commute-G-half-sandwich move chain by one slice.
--
--   Principal definitions:
--   - `swappedFrontQuestionEquiv`: swaps the distinguished front question coordinates.
--   - `swappedFrontOutcomeEquiv`: reindexes the corresponding outcome coordinates.
--   - `moveTailSwappedFrontQuestionEquiv`: reindexes a moved tail question.
--   - `moveTailSwappedFrontOutcomeEquiv`: reindexes its outcome.
--   - `commuteGHalfSandwich_splitSuccLiftFamily`: lifts a family through the successor split.
--   - `commuteGHalfSandwich_prefixSecondSliceLeftFamily`: inserts the second slice on the left.
--   - `commuteGHalfSandwich_secondSliceLiftFamily`: inserts the second completed-slice factor.
--   - `commuteGHalfSandwich_moveChainLiftQuestionEquiv`: reindexes the extended move-chain question.
--   - `commuteGHalfSandwich_moveChainLiftOutcomeEquiv`: reindexes the extended move-chain outcome.
--   - `commuteGHalfSandwich_moveChainLiftFamily`: lifts the operator family to the extended chain.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Lifting.lean#L36-L409

-- Generated from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Lifting.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.Commutativity
end MIPStarRE.LDT.Commutativity
namespace MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints
namespace MIPStarRE.LDT.Pasting
end MIPStarRE.LDT.Pasting
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 12 pasting: half-sandwich lifting constructions

This module contains the reindexing equivalences and lifted operator families
which transport an `r`-step half-sandwich move comparison to the corresponding
`r+1`-step comparison.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Lifting families for the half-sandwich chain

Lifting constructions: swapped-front equivalences, `splitSuccLiftFamily`,
`prefixSecondSliceLeftFamily`, `secondSliceLiftFamily`, and the
`moveChainLift` construction that lifts an `r`-step chain to `r+1`.
-/
/-- Swap the first two distinguished slice coordinates after exposing the tail
coordinate of a move-chain question. -/
def swappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (MoveTailQ params r) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
          PointTuple params r) where
  toFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  invFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

/-- Outcome analogue of `swappedFrontQuestionEquiv`. -/
def swappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (MoveTailO params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) where
  toFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  invFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

/-- Expose the tail coordinate of an `(r+1)`-move question and put the first two
distinguished slice coordinates in swapped-front order. -/
def moveTailSwappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (MoveQ params (r + 1)) ≃
      (MoveTailQ params r) :=
  (moveTailQuestionEquiv params r).trans (swappedFrontQuestionEquiv params r)

/-- Outcome analogue of `moveTailSwappedFrontQuestionEquiv`. -/
def moveTailSwappedFrontOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (MoveO params (r + 1)) ≃
      (MoveTailO params r) :=
  (moveTailOutcomeEquiv params r).trans (swappedFrontOutcomeEquiv params r)

/-- Reindex an `r`-move operator family along the split-successor equivalences. -/
noncomputable def commuteGHalfSandwich_splitSuccLiftFamily
    (params : Parameters) [FieldModel params.q]
    (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        (F ((splitSuccQuestionEquiv params r) q)).outcome ((splitSuccOutcomeEquiv params r) ogs)
      total := (F ((splitSuccQuestionEquiv params r) q)).total }

/-- Add a completed-slice factor on the left of an operator family, with the new
slice coordinate placed in the second distinguished position. -/
noncomputable def commuteGHalfSandwich_prefixSecondSliceLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2)).total }





/-- Lift an `r`-move operator family to the `(r+1)`-move questions by inserting
the new second distinguished slice factor. -/
noncomputable def commuteGHalfSandwich_secondSliceLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).total }





/-- Reindex a question pair consisting of an `r`-move state and a new leading
slice coordinate as an `(r+1)`-move state. -/
def commuteGHalfSandwich_moveChainLiftQuestionEquiv (params : Parameters) (r : ℕ) :
    ((MoveQ params r) × SliceQuestion params) ≃
      (MoveQ params (r + 1)) :=
  (firstSliceBackQuestionEquiv params r).trans (moveTailQuestionEquiv params r).symm

/-- Outcome analogue of `commuteGHalfSandwich_moveChainLiftQuestionEquiv`. -/
def commuteGHalfSandwich_moveChainLiftOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((MoveO params r) × GHatOutcome params) ≃
      (MoveO params (r + 1)) :=
  (firstSliceBackOutcomeEquiv params r).trans (moveTailOutcomeEquiv params r).symm

/-- Lift an `r`-move chain family by adjoining a new leading completed-slice
factor on the left tensor register. -/
noncomputable def commuteGHalfSandwich_moveChainLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).total }









end MIPStarRE.LDT.Pasting

end

end LIDT


