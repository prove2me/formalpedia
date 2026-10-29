-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
-- name    : LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:59:08.658508+00:00
-- url     : https://prove2.me/theorems/e56c2fca-3cce-49ed-98f2-60598e8cca5d
-- title:
--   LIDT definitions: LDT / Commutativity / ScalarApproximation / PaperChainPhaseFive
-- statement:
--   This bundle names the intermediate operator expressions in phases five through eight of the paper-style scalar approximation chain. The definitions expose the removal, reversal, projector simplification, and right-register transport steps, together with ordered and swapped missing-mass defects.
--
--   Principal definitions:
--   - `evaluatedSlicePhaseFivePaperRemoved`: the phase-five endpoint after removing the trailing total factor.
--   - `evaluatedSlicePhaseSixFirstReverse`: the endpoint after reversing the first insertion.
--   - `evaluatedSlicePhaseSixFirstRemoved`: the endpoint after simplifying the first-coordinate projector.
--   - `evaluatedSlicePhaseSevenGonnaCite`: the phase-seven endpoint used by the later comparison.
--   - `evaluatedSlicePhaseEightTailRight`: the endpoint after moving the second factor to the right register.
--   - `evaluatedSlicePhaseFivePaperOrderedDefect`: the ordered missing-mass defect.
--   - `evaluatedSlicePhaseFivePaperSwappedDefect`: the swapped missing-mass defect.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean#L28-L141

-- Generated from MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.Commutativity
end MIPStarRE.LDT.Commutativity
namespace MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/

/-- Paper line-87 endpoint after removing the trailing `G^x.total`.

At question `q = ((u,x),(v,y))` and outcome `(a,b)`, this is
`G^{u,x}_a G^{v,y}_b ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Paper line 101 endpoint after reversing the first `eq:add-an-a` insertion. -/
noncomputable def evaluatedSlicePhaseSixFirstReverse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 102 endpoint after simplifying the first-coordinate projector. -/
noncomputable def evaluatedSlicePhaseSixFirstRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 104 endpoint `eq:gonna-cite-this-in-just-a-bit`. -/
noncomputable def evaluatedSlicePhaseSevenGonnaCite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceSecondFactor params family q).outcome b)))

/-- Paper line 118 endpoint after moving the second factor to the right register. -/
noncomputable def evaluatedSlicePhaseEightTailRight
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSliceSecondFactor params family q).outcome b))

/-- Ordered missing-mass defect for the paper phase-five removal.

This is the defect before swapping the two right-register point measurements:
`G^{u,x}_a G^{v,y}_b (1-G^x) ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperOrderedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Swapped missing-mass defect for the paper phase-five removal.

After the right-register point swap, this reindexes to
`gCommStabilityTwoRawScalarDefect`: the right register is
`A^{v,y}_b A^{u,x}_a`. -/
noncomputable def evaluatedSlicePhaseFivePaperSwappedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
            ((evaluatedSlicePointMeas params strategy q.1).outcome a)))











end MIPStarRE.LDT.Commutativity

end

end LIDT


