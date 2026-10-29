-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:42:21.711797+00:00
-- url     : https://prove2.me/theorems/3c971585-36ef-4cf6-a1a9-d7b786a30c40
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperSSC / PostDeleteA
-- statement:
--   This bundle contains the post-delete-A estimates in the helper strong-self-consistency proof. It controls pair sandwiches and mass factors, compares a cloned independent-point quantity, and transports that quantity to the opposite tensor register.
--
--   Principal definitions:
--   - `helper_pair_sandwich_operator_sum_le`: the operator-order bound for the sum of helper pair sandwiches.
--   - `helper_pair_tensor_mass_le_one`: the corresponding helper pair tensor mass bound by one.
--   - `helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum`: the cloned variance factor bounded by the global-variance deviation sum.
--   - `helperDeleteA_clone_mass_factor_le_one`: the cloned mass factor bounded by one.
--   - `helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt`: replacing the remaining point by an independent point costs the square root of the variance error.
--   - `helper_moveOverV_C_contraction`: the contraction bound for the operator used in the move-over-V step.
--   - `helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta`: moving the cloned delete-an-A quantity to the right register costs `sqrt (2 delta)` from point self-consistency.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/PostDeleteA.lean#L31-L705

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/PostDeleteA.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Helper strong self-consistency bounds: post-delete transports

Post-`delete-an-A` transport lemmas culminating in the moved-quantity bound
used before the residual-chain assembly.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Post-`delete-an-A` transports -/

private lemma helper_pair_sandwich_operator_sum_le
    (params : Parameters) [FieldModel params.q]
    (H T : SubMeas (Polynomial params) ι)
    (X : Polynomial params → MIPStarRE.Quantum.Op ι)
    (hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h) :
    (∑ hh : Polynomial params × Polynomial params,
        opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1)) ≤
      ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
  classical
  calc
    (∑ hh : Polynomial params × Polynomial params,
        opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1))
        = ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              opTensor (X h * H.outcome h' * X h) (T.outcome h) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ h : Polynomial params,
          opTensor (X h * H.total * X h) (T.outcome h) := by
          refine Finset.sum_congr rfl ?_
          intro h _
          rw [← opTensor_sum_left_univ]
          congr 1
          rw [← H.sum_eq_total, Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ h : Polynomial params,
          opTensor (X h * 1 * X h) (T.outcome h) := by
          refine Finset.sum_le_sum ?_
          intro h _
          exact opTensor_mono_left
            (IsSelfAdjoint.conjugate_le_conjugate H.total_le_one (hX_herm h))
            (T.outcome_pos h)
    _ = ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
          simp

private lemma helper_pair_tensor_mass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H T : SubMeas (Polynomial params) ι) :
    (∑ hh : Polynomial params × Polynomial params,
        ev strategy.state (opTensor (H.outcome hh.2) (T.outcome hh.1))) ≤ 1 := by
  classical
  have hop_eq :
      (∑ hh : Polynomial params × Polynomial params,
          opTensor (H.outcome hh.2) (T.outcome hh.1)) =
        opTensor H.total T.total := by
    calc
      (∑ hh : Polynomial params × Polynomial params,
          opTensor (H.outcome hh.2) (T.outcome hh.1))
          = ∑ h : Polynomial params,
              ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ h : Polynomial params, opTensor H.total (T.outcome h) := by
            refine Finset.sum_congr rfl ?_
            intro h _
            rw [← H.sum_eq_total, opTensor_sum_left_univ]
      _ = opTensor H.total T.total := by
            rw [← T.sum_eq_total, opTensor_sum_right_univ]
  have hop_le_one : opTensor H.total T.total ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
    le_trans
      (opTensor_le_leftTensor (SubMeas.total_nonneg H) T.total_le_one)
      (leftTensor_le_one (ι₂ := ι) H.total_le_one)
  calc
    (∑ hh : Polynomial params × Polynomial params,
        ev strategy.state (opTensor (H.outcome hh.2) (T.outcome hh.1)))
        = ev strategy.state
            (∑ hh : Polynomial params × Polynomial params,
              opTensor (H.outcome hh.2) (T.outcome hh.1)) := by
          rw [ev_finset_sum]
    _ = ev strategy.state (opTensor H.total T.total) := by
          rw [hop_eq]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
          ev_mono strategy.state _ _ hop_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

private lemma helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : Polynomial params × Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Error := fun uv =>
    ∑ hh : Polynomial params × Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))
  let squaredTerm : Point params × Point params → Polynomial params → Error := fun uv h =>
    let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ uv : Point params × Point params,
      varianceTerm uv ≤ ∑ h : Polynomial params, squaredTerm uv h := by
    intro uv
    let H := sandwichedPolynomialSubMeasAt params strategy T uv.1
    let X : Polynomial params → MIPStarRE.Quantum.Op ι := fun h =>
      pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      have hAu :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      dsimp [X]
      rw [Matrix.conjTranspose_sub, hAu, hAv]
    have hop_le :
        (∑ hh : Polynomial params × Polynomial params,
          opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1)) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      helper_pair_sandwich_operator_sum_le params H T X hX_herm
    calc
      varianceTerm uv =
          ev strategy.state
            (∑ hh : Polynomial params × Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial
                params strategy hh.1 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial
                params strategy hh.1 uv.2
              let Hh' := H.outcome hh.2
              opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1)) := by
            dsimp [varianceTerm, H]
            rw [ev_finset_sum]
      _ ≤ ev strategy.state (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) := by
            exact ev_mono strategy.state _ _ (by simpa [X, H] using hop_le)
      _ = ∑ h : Polynomial params, squaredTerm uv h := by
            rw [ev_finset_sum]
            refine Finset.sum_congr rfl ?_
            intro h _
            dsimp [squaredTerm, X]
            rw [hX_herm h]
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) varianceTerm ≤
        avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := by
    exact avgOver_mono _ _ _ hpointwise
  have hsquared_eq :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) =
        ∑ h : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T h := by
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    unfold globalVarianceDeviationAtPolynomial
    rw [avgOver_independentPointPair_eq_uniform_prod]
    refine avgOver_congr _ _ _ ?_
    intro uv
    simp only [squaredTerm]
    rw [← weightedPointConditionedOperator_sq]
  calc
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : Polynomial params × Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1)))
        = avgOver (uniformDistribution (Point params × Point params)) varianceTerm := rfl
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

private lemma helperDeleteA_clone_mass_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : Polynomial params × Polynomial params,
        ev strategy.state
          (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1))) ≤ 1 := by
  classical
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ hh : Polynomial params × Polynomial params,
        ev strategy.state
          (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1))) ≤ 1 := by
    intro uv
    exact helper_pair_tensor_mass_le_one params strategy
      (sandwichedPolynomialSubMeasAt params strategy T uv.1) T
  exact avgOver_uniform_le_const _ 1 hpointwise

-- This post-delete transport combines the clone variance factor estimate with
-- the local-to-global variance transfer.
/-- Paper `eq:swap-u-for-v-attack-of-the-clones`: after `delete-an-A`, the
remaining point projector may be evaluated at an independent point at cost
`√ζ_variance`. -/
theorem helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperDeleteAQuantity params strategy T -
      helperDeleteAClonedQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  classical
  let 𝒟 := uniformDistribution (Point params × Point params)
  let t : Point params × Point params → Polynomial params × Polynomial params → Error :=
    fun uv hh =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor ((Au - Av) * Hh') (T.outcome hh.1))
  let x : Point params × Point params → Polynomial params × Polynomial params → Error :=
    fun uv hh =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))
  let y : Point params × Point params → Polynomial params × Polynomial params → Error :=
    fun uv hh =>
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor Hh' (T.outcome hh.1))
  have hdiff_eq :
      helperDeleteAQuantity params strategy T - helperDeleteAClonedQuantity params strategy T =
        avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, t uv hh) := by
    have hdelete_prod :
        helperDeleteAQuantity params strategy T =
          avgOver 𝒟 (fun uv =>
            ∑ hh : Polynomial params × Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
              let Hh' :=
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
              ev strategy.state (opTensor (Hh' * Au) (T.outcome hh.1))) := by
      unfold helperDeleteAQuantity
      rw [← avgOver_uniform_fst (α := Point params) (β := Point params)
        (f := fun u =>
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
              ev strategy.state
                (opTensor (((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
                  (T.outcome h)))]
      refine avgOver_congr 𝒟 _ _ ?_
      intro uv
      rw [Fintype.sum_prod_type]
    have hclone_prod :
        helperDeleteAClonedQuantity params strategy T =
          avgOver 𝒟 (fun uv =>
            ∑ hh : Polynomial params × Polynomial params,
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
              let Hh' :=
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
              ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1))) := by
      unfold helperDeleteAClonedQuantity
      refine avgOver_congr 𝒟 _ _ ?_
      intro uv
      rw [Fintype.sum_prod_type]
    rw [hdelete_prod, hclone_prod, ← avgOver_sub]
    refine avgOver_congr 𝒟 _ _ ?_
    intro uv
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro hh _
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
    set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
    have hAu : Auᴴ = Au := by
      dsimp [Au]
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (hh.1 uv.1)
    have hAv : Avᴴ = Av := by
      dsimp [Av]
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
    have hH : Hh'ᴴ = Hh' := by
      dsimp [Hh']
      exact SubMeas.outcome_hermitian (sandwichedPolynomialSubMeasAt params strategy T uv.1) hh.2
    have hT : (T.outcome hh.1)ᴴ = T.outcome hh.1 := SubMeas.outcome_hermitian T hh.1
    have hdiff_herm : (Au - Av)ᴴ = Au - Av := by
      rw [Matrix.conjTranspose_sub, hAu, hAv]
    calc
      ev strategy.state (opTensor (Hh' * Au) (T.outcome hh.1)) -
          ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1))
          = ev strategy.state (opTensor (Hh' * (Au - Av)) (T.outcome hh.1)) := by
            rw [← ev_sub, opTensor_sub_left]
            congr 1
            noncomm_ring
      _ = t uv hh := by
            dsimp [t, Au, Av, Hh']
            rw [← ev_conjTranspose strategy.state]
            rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, hdiff_herm, hH, hT]
  have hcs :
      |avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, t uv hh)| ≤
        Real.sqrt (avgOver 𝒟 (fun uv =>
          ∑ hh : Polynomial params × Polynomial params, x uv hh)) *
        Real.sqrt (avgOver 𝒟 (fun uv =>
          ∑ hh : Polynomial params × Polynomial params, y uv hh)) := by
    refine MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟 t x y ?_ ?_ ?_
    · intro uv hh
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      have hAu : Auᴴ = Au := by
        dsimp [Au]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (hh.1 uv.1)
      have hAv : Avᴴ = Av := by
        dsimp [Av]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
      have hdiff_herm : (Au - Av)ᴴ = Au - Av := by
        rw [Matrix.conjTranspose_sub, hAu, hAv]
      have hsandwich :=
        ev_opTensor_sandwich_abs_le_sqrt strategy.state (Au - Av) 1 Hh'
          (T.outcome hh.1)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2)
          (T.outcome_pos hh.1)
      simpa [t, x, y, Au, Av, Hh', hdiff_herm] using hsandwich
    · intro uv hh
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      have hH_pos : 0 ≤ Hh' :=
        (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2
      have hT_pos : 0 ≤ T.outcome hh.1 := T.outcome_pos hh.1
      have hAu : Auᴴ = Au := by
        dsimp [Au]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (hh.1 uv.1)
      have hAv : Avᴴ = Av := by
        dsimp [Av]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
      have hdiff_herm : (Au - Av)ᴴ = Au - Av := by
        rw [Matrix.conjTranspose_sub, hAu, hAv]
      have hleft_pos : 0 ≤ (Au - Av) * Hh' * (Au - Av) := by
        have this : 0 ≤ (Au - Av)ᴴ * Hh' * (Au - Av) := by
          simpa [Matrix.star_eq_conjTranspose] using
            star_left_conjugate_nonneg hH_pos (Au - Av)
        rwa [hdiff_herm] at this
      exact ev_nonneg_of_psd strategy.state _ (opTensor_nonneg hleft_pos hT_pos)
    · intro uv hh
      exact ev_nonneg_of_psd strategy.state _ <|
        opTensor_nonneg
          ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2)
          (T.outcome_pos hh.1)
  have hvariance :
      avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, x uv hh) ≤
        ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
    simpa [𝒟, x] using
      helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum params strategy T
  have hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        selfImprovementVarianceError params eps delta := by
    simpa [selfImprovementVarianceError] using
      globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal
  have hmass :
      avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, y uv hh) ≤ 1 := by
    simpa [𝒟, y] using helperDeleteA_clone_mass_factor_le_one params strategy T
  have hbound := addInU_le_sqrt_of_factor_bounds_right hcs (le_trans hvariance hglobal) hmass
  simpa [hdiff_eq] using hbound

private lemma helper_moveOverV_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0))ᴴ *
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ hh : Polynomial params × Polynomial params,
      if hh.1 uv.2 = a then
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
          (T.outcome hh.1)
      else 0
  have hsum_eq : ∀ a : Fq params,
      (∑ hh : Polynomial params × Polynomial params,
        (if hh.1 uv.2 = a then
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1)
        else 0)) = K a := by
    intro a
    rfl
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hH_herm : ∀ h : Polynomial params,
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)ᴴ =
          (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h :=
      SubMeas.outcome_hermitian (sandwichedPolynomialSubMeasAt params strategy T uv.1)
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h :=
      SubMeas.outcome_hermitian T
    dsimp [K]
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl ?_
    intro hh _
    by_cases hmem : hh.1 uv.2 = a
    · simp [hmem, conjTranspose_opTensor, hH_herm hh.2, hT_herm hh.1]
    · simp [hmem]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro hh _
    by_cases hmem : hh.1 uv.2 = a
    · simp [hmem, opTensor_nonneg
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2)
        (T.outcome_pos hh.1)]
    · simp [hmem]
  have hK_sum_le_one : (∑ a : Fq params, K a) ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    have hsum_all :
        (∑ a : Fq params, K a) =
          ∑ hh : Polynomial params × Polynomial params,
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1) := by
      dsimp [K]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro hh _
      rw [Finset.sum_eq_single (hh.1 uv.2)]
      · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    have hop_le_one :
        (∑ hh : Polynomial params × Polynomial params,
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1)) ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      let H := sandwichedPolynomialSubMeasAt params strategy T uv.1
      have hop_eq :
          (∑ hh : Polynomial params × Polynomial params,
              opTensor (H.outcome hh.2) (T.outcome hh.1)) =
            opTensor H.total T.total := by
        calc
          (∑ hh : Polynomial params × Polynomial params,
              opTensor (H.outcome hh.2) (T.outcome hh.1)) =
              ∑ h : Polynomial params,
                ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h) := by
                rw [Fintype.sum_prod_type]
          _ = ∑ h : Polynomial params, opTensor H.total (T.outcome h) := by
                refine Finset.sum_congr rfl ?_
                intro h _
                rw [← H.sum_eq_total, opTensor_sum_left_univ]
          _ = opTensor H.total T.total := by
                rw [← T.sum_eq_total, opTensor_sum_right_univ]
      simpa [H, hop_eq] using
        (le_trans
          (opTensor_le_leftTensor
            (SubMeas.total_nonneg (sandwichedPolynomialSubMeasAt params strategy T uv.1))
            T.total_le_one)
          (leftTensor_le_one (ι₂ := ι)
            (sandwichedPolynomialSubMeasAt params strategy T uv.1).total_le_one))
    exact hsum_all.trans_le hop_le_one
  have hK_le_one : ∀ a, K a ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    intro a
    calc
      K a ≤ ∑ b : Fq params, K b := by
        exact Finset.single_le_sum (fun b _ => hK_nonneg b) (Finset.mem_univ a)
      _ ≤ 1 := hK_sum_le_one
  have hsq_le : ∀ a, K a * K a ≤ K a := by
    intro a
    exact MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)
  calc
    ∑ a : Fq params,
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0))ᴴ *
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0))
        = ∑ a : Fq params, K a * K a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a, hK_herm a]
    _ ≤ ∑ a : Fq params, K a := Finset.sum_le_sum (fun a _ => hsq_le a)
    _ ≤ 1 := hK_sum_le_one

/-- Paper `eq:move-over-v`: the cloned `delete-an-A` quantity can be moved to
the right tensor factor at cost `√(2δ)` from point self-consistency. -/
theorem helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperDeleteAClonedQuantity params strategy T -
      helperMoveOverVQuantity params strategy T| ≤
        Real.sqrt (2 * delta) := by
  classical
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params →
      Polynomial params × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a hh =>
      if hh.1 uv.2 = a then
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
          (T.outcome hh.1)
      else 0
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (strategy.pointMeasurement v).toSubMeas.outcome_hermitian a
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ = _
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ = _
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hfun_A : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Aop uv a)ᴴ) = Aop uv := by
    intro uv
    funext a
    exact hAop_herm uv a
  have hfun_B : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Bop uv a)ᴴ) = Bop uv := by
    intro uv
    funext a
    exact hBop_herm uv a
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ)
          (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    rfl
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
        (∑ hh : Polynomial params × Polynomial params, Cop uv a hh)ᴴ *
          (∑ hh : Polynomial params × Polynomial params, Cop uv a hh)) ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    intro uv
    simpa [Cop] using helper_moveOverV_C_contraction params strategy T uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a hh)) -
        (∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a hh)) =
      (∑ hh : Polynomial params × Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
          let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
          ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1))) -
        (∑ hh : Polynomial params × Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
          let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
          ev strategy.state (opTensor Hh' (T.outcome hh.1 * Av))) := by
    intro uv
    have hAvg : ∀ (X : Fq params → Polynomial params × Polynomial params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∀ a hh, hh.1 uv.2 ≠ a → X a hh = 0) →
        ∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (X a hh) =
          ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (X (hh.1 uv.2) hh) := by
      intro X hX
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro hh _
      rw [Finset.sum_eq_single (hh.1 uv.2)]
      · intro a _ ha
        rw [hX a hh (Ne.symm ha), ev_zero strategy.state]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    have hAC_zero : ∀ a hh, hh.1 uv.2 ≠ a → Aop uv a * Cop uv a hh = 0 := by
      intro a hh ha
      simp [Cop, ha]
    have hBC_zero : ∀ a hh, hh.1 uv.2 ≠ a → Bop uv a * Cop uv a hh = 0 := by
      intro a hh ha
      simp [Cop, ha]
    rw [hAvg (fun a hh => Aop uv a * Cop uv a hh) hAC_zero,
      hAvg (fun a hh => Bop uv a * Cop uv a hh) hBC_zero]
    change
      (∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Aop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh)) -
        (∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Bop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh)) = _
    rw [← Finset.sum_sub_distrib
      (s := (Finset.univ : Finset (Polynomial params × Polynomial params)))
      (f := fun hh : Polynomial params × Polynomial params =>
        ev strategy.state (Aop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh))
      (g := fun hh : Polynomial params × Polynomial params =>
        ev strategy.state (Bop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh))]
    rw [← Finset.sum_sub_distrib
      (s := (Finset.univ : Finset (Polynomial params × Polynomial params)))
      (f := fun hh : Polynomial params × Polynomial params =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1)))
      (g := fun hh : Polynomial params × Polynomial params =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor Hh' (T.outcome hh.1 * Av)))]
    refine Finset.sum_congr rfl ?_
    intro hh _
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
    set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
    have hAv : Avᴴ = Av := by
      dsimp [Av]
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
    have hH : Hh'ᴴ = Hh' := by
      dsimp [Hh']
      exact SubMeas.outcome_hermitian (sandwichedPolynomialSubMeasAt params strategy T uv.1) hh.2
    have hT : (T.outcome hh.1)ᴴ = T.outcome hh.1 := SubMeas.outcome_hermitian T hh.1
    have hCop_at : Cop uv (hh.1 uv.2) hh = opTensor Hh' (T.outcome hh.1) := by
      simp [Cop, Hh']
    have hA_at : Aop uv (hh.1 uv.2) = leftTensor (ι₂ := ι) Av := rfl
    have hB_at : Bop uv (hh.1 uv.2) = rightTensor (ι₁ := ι) Av := rfl
    rw [hCop_at, hA_at, hB_at]
    have hleft :
        ev strategy.state (leftTensor (ι₂ := ι) Av * opTensor Hh' (T.outcome hh.1)) =
          ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1)) := by
      rw [leftTensor_mul_opTensor]
      rw [← ev_conjTranspose strategy.state]
      rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, hAv, hH, hT]
    have hright :
        ev strategy.state (rightTensor (ι₁ := ι) Av * opTensor Hh' (T.outcome hh.1)) =
          ev strategy.state (opTensor Hh' (T.outcome hh.1 * Av)) := by
      rw [rightTensor_mul_opTensor]
      rw [← ev_conjTranspose strategy.state]
      rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, hH, hT, hAv]
    rw [hleft, hright]
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (Aop uv a * Cop uv a hh)) -
        avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (Bop uv a * Cop uv a hh)) =
      helperDeleteAClonedQuantity params strategy T -
        helperMoveOverVQuantity params strategy T := by
    rw [← avgOver_sub]
    unfold helperDeleteAClonedQuantity helperMoveOverVQuantity
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hmatch_pointwise uv]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← hmatch]
  exact hcs

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


