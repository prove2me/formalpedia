-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
-- name    : LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:41:46.003992+00:00
-- url     : https://prove2.me/theorems/4ab07a40-ffdb-41b1-867b-e05a366ade5d
-- title:
--   LIDT definitions: LDT / Pasting / ComparisonLemmas / OverAllOutcomes / NonglobalDecomposition
-- statement:
--   This bundle decomposes the mass of interpolation-eligible but globally nonglobal tuples in the over-all-outcomes argument. It separates tuples that fail line consistency from those that remain line-consistent but are not global, and it records the local and distinct-tuple averages needed to bound both pieces.
--
--   Principal definitions:
--   - `overAllOutcomesDistinctNonglobalMass`: The distinct-height average of interpolation-eligible outcome tuples that do not represent a globally consistent polynomial.
--   - `overAllOutcomesDistinctBadLineMass`: The distinct-height mass of tuples witnessing a mismatch with the inserted vertical-line measurement.
--   - `overAllOutcomesLineConsistentNonglobalLocal`: The local nonglobal mass after removing the bad-line contribution for a fixed tuple and vertical-line question.
--   - `overAllOutcomesDistinctLineConsistentNonglobalMass`: The distinct-tuple average of that line-consistent nonglobal residual.
--   - `overAllOutcomesLineConsistentIndicatorLocal`: The local indicator mass obtained after summing out the inserted vertical-line outcome.
--   - `overAllOutcomesDistinctLineConsistentIndicatorMass`: The corresponding distinct-tuple average of the consistency-indicator mass.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean#L29-L240

-- Generated from MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
# Section 12 pasting: over all outcomes — nonglobal-mass decomposition

Nonglobal-mass definitions, the vertical-line insertion, and the line-consistency
decomposition that splits the nonglobal eligible mass into the bad-line event and
the line-consistent residual.

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

/-- Distinct-tuple mass of interpolation-eligible but globally inconsistent outcomes.

This is the scalar quantity bounded in `ld-pasting.tex` lines 1174--1275 when the
proof removes the `Global_τ(x)` restriction.  It is the exact local residual
between the all-outcomes expansion over distinct tuples and the pasted/global
part. -/
noncomputable def overAllOutcomesDistinctNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (distinctTupleDistribution params k) (fun xs =>
    subMeasMass strategy.state
      ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft))





/-- The distinct-tuple line-mismatch mass that appears after inserting the
vertical-line measurement in `ld-pasting.tex` lines 1178--1202.

This is the part paid for by the already-available one-point line comparison
statements.  The remaining `md/q` Schwartz--Zippel term is kept separate below. -/
noncomputable def overAllOutcomesDistinctBadLineMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs))





/-- Local version of `eq:B-appears-out-of-thin-air` for one distinct tuple `xs` and
one vertical-line question `u`.

It inserts the vertical-line measurement into the nonglobal eligible mass. -/
 noncomputable def overAllOutcomesNonglobalInsertedMassLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
          if IsGloballyConsistent params xs gs then 0
          else (interpolationEligibleSandwichFamily params family k xs).outcome gs)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- The residual line-consistent nonglobal mass after the line-mismatch event has
been split off.

This is the formal version of the `consistent indicator` term in
`ld-pasting.tex` lines 1204--1232, before applying the interpolant witness and
Schwartz--Zippel.  It keeps the inserted vertical-line measurement explicit: for
each line answer `f`, we retain exactly the nonglobal eligible outcomes for which
no supported slice disagrees with `f` along the sampled vertical line. -/
noncomputable def overAllOutcomesLineConsistentNonglobalLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
          if (¬ IsGloballyConsistent params xs gs) ∧
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- Distinct-tuple average of the line-consistent nonglobal mass.

Paper anchor: this is the explicit line-answer term just before the
`Consistent_τ(g,y,u)` indicator in `ld-pasting.tex` lines 1204--1232.  The next
lemmas sum out the inserted measurement and reduce it to that indicator. -/
noncomputable def overAllOutcomesDistinctLineConsistentNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs))

/-- Local consistency-indicator mass after summing out the inserted vertical-line
measurement.

For fixed `u` and `xs`, it retains nonglobal eligible tuples for which there
exists some degree-`d` vertical-line answer matching every supported slice at `u`.
This is the Lean counterpart of the indicator
`Consistent_τ(g,y,u)` introduced at `ld-pasting.tex` lines 1204--1219. -/
noncomputable def overAllOutcomesLineConsistentIndicatorLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : Error :=
  subMeasMass strategy.state
    ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
      (fun gs => (¬ IsGloballyConsistent params xs gs) ∧
        ∃ f : AxisLinePolynomial params.next,
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i)))).liftLeft)

/-- Distinct-tuple average of the consistency-indicator nonglobal mass. -/
noncomputable def overAllOutcomesDistinctLineConsistentIndicatorMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))











end MIPStarRE.LDT.Pasting

end

end LIDT


