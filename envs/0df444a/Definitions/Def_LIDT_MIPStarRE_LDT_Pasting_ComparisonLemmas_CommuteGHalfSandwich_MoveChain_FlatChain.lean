-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
-- name    : LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:24:31.165922+00:00
-- url     : https://prove2.me/theorems/07089298-bd77-47f0-909b-10a2e607540e
-- title:
--   LIDT definitions: LDT / Pasting / ComparisonLemmas / CommuteGHalfSandwich / MoveChain / FlatChain
-- statement:
--   This bundle constructs the finite operator-family chain used to commute a completed G factor through a half-sandwich. It separates the post-move recursive segment from the initial move chain, then concatenates their lengths, families, and edge errors into one flat chain.
--
--   Principal definitions:
--   - `commuteGHalfSandwich_postMoveFlatLength`: The number of edges in the recursive post-move segment.
--   - `commuteGHalfSandwich_postMoveFlatFamily`: The indexed operator families at the successive post-move positions.
--   - `commuteGHalfSandwich_postMoveFlatError`: The error assigned to each post-move edge.
--   - `commuteGHalfSandwich_flatChainLength`: The total length obtained by adjoining the move-chain length to the post-move length.
--   - `commuteGHalfSandwich_flatChainFamily`: The operator-family sequence formed by concatenating the move chain with the post-move family sequence.
--   - `commuteGHalfSandwich_flatChainError`: The corresponding concatenated sequence of edge errors.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean#L38-L144

-- Generated from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
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
# Section 12 pasting: half-sandwich flat chain

This module defines the post-move and combined flat chains used after the
distinguished completed-slice factor has been moved to the right tensor
register.  The chain alternates between pairwise commutation and
self-consistency steps, with an explicit error sequence for the final
composition.

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


/-! ## Post-move flat chain and flat-chain definitions

The post-move flat chain (`postMoveFlatFamily`, `postMoveFlatError`) and the
combined flat chain (`flatChainFamily`, `flatChainError`) together with their
endpoint and summation lemmas.
-/
/-- Length of the post-move part of the flat chain. -/
@[reducible] def commuteGHalfSandwich_postMoveFlatLength : ℕ → ℕ
  | 0 => 1
  | r + 1 => commuteGHalfSandwich_postMoveFlatLength r + 2

/-- Operator-family sequence for the post-move part of the flat chain. -/
noncomputable def commuteGHalfSandwich_postMoveFlatFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r + 1) → IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)
  | 0, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily params family 0
      else
        commuteGHalfSandwich_recursiveTargetFamily params family 0
  | r + 1, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily params family (r + 1)
      else if i.1 = 1 then
        commuteGHalfSandwich_commuteFamily params family (r + 1)
      else
        commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
          (commuteGHalfSandwich_splitSuccLiftFamily params r
            ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                ⟨i.1 - 2, by
                  have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 3 := by
                    exact i.2
                  omega⟩))

/-- Error sequence for the post-move flat chain. -/
noncomputable def commuteGHalfSandwich_postMoveFlatError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r) → Error
  | 0, _ => gHatCommutationError params gamma zeta
  | r + 1, i =>
      if hi0 : i.1 = 0 then
        gHatCommutationError params gamma zeta
      else if hi1 : i.1 = 1 then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r
          ⟨i.1 - 2, by
            have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
              exact i.2
            omega⟩



/-- Length of the combined move and post-move flat chain. -/
@[reducible] def commuteGHalfSandwich_flatChainLength (r : ℕ) : ℕ :=
  r + commuteGHalfSandwich_postMoveFlatLength r

/-- Operator-family sequence obtained by concatenating the move chain and the
post-move flat chain. -/
noncomputable def commuteGHalfSandwich_flatChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r + 1) → IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)
  | i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainFamily params family r ⟨i.1, hi⟩
      else
        commuteGHalfSandwich_postMoveFlatFamily params family r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r + 1 := i.2
            omega⟩

/-- Error sequence for the combined flat chain. -/
noncomputable def commuteGHalfSandwich_flatChainError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r) → Error
  | i =>
      if hi : i.1 < r then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r := i.2
            omega⟩





















end MIPStarRE.LDT.Pasting

end

end LIDT


