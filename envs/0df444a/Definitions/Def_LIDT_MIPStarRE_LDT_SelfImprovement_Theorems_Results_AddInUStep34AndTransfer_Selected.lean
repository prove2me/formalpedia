-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:30:35.110528+00:00
-- url     : https://prove2.me/theorems/5fae1f2c-8df5-4645-8170-e18b7476ad26
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUStep34AndTransfer / Selected
-- statement:
--   This bundle contains the selected-support estimates for Steps 3 and 4 of the add-in-$u$ argument. Weighted Cauchy-Schwarz bounds reduce the two differences to global-variance deviations, while sandwich bounds control the selected submeasurement factors.
--
--   Principal definitions:
--   - `addInU_selected_weighted_cauchy_schwarz`: Applies weighted finite Cauchy-Schwarz to the selected add-in-$u$ summands.
--   - `addInU_selected_cs_chain_step3_factored_cs`: Bounds the Step 3 transition from $Q_2$ to $Q_3$ after factoring the selected terms.
--   - `addInU_selected_cs_chain_step4_factored_cs`: The corresponding factored bound for the Step 4 transition from $Q_3$ to $Q_4$.
--   - `addInU_selected_sandwich_tensor_if_sum_le`: Bounds a selected sandwich tensor sum by replacing the selected submeasurement sum with the identity when it is at most one.
--   - `addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum`: Bounds the combined variance factor by the sum of global-variance deviations.
--   - `addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum`: Gives the raw absolute Step 3 bound as the square root of that deviation sum.
--   - `addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum`: Gives the analogous raw absolute Step 4 bound.
--   - `addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le`: Combines the two steps under an external bound on the summed global variance.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean#L30-L746

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
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
# Selected add-in-u Step 3/4 global-variance bounds

Selected-family Cauchy--Schwarz estimates and factor bounds for the
`Q₂ → Q₃` and `Q₃ → Q₄` add-in-u moves.

## References

- `references/ldt-paper/self_improvement.tex` lines 299--340
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

/-- Selected-support weighted Cauchy--Schwarz for the add-in-`u` Step 3/4
summands.

The selected Step 3 and Step 4 estimates use the same finite inequality: the
summands are restricted to the selected pairs `S_u`, and are extended by zero
outside this support.  This helper fixes the distribution and the selected
support, leaving only the three summands and their pointwise estimates to be
specified by the two applications. -/
private theorem addInU_selected_weighted_cauchy_schwarz
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : AddInUSelection params Outcome)
    (t x y : Point params × Point params → Outcome × Polynomial params → Error)
    (ht :
      ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 →
        |t uv ah| ≤ Real.sqrt (x uv ah) * Real.sqrt (y uv ah))
    (hx : ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 → 0 ≤ x uv ah)
    (hy : ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 → 0 ≤ y uv ah) :
    |avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then t uv ah else 0)| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then x uv ah else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then y uv ah else 0)) := by
  classical
  exact
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz_on_selectedSupport
      (𝒟 := uniformDistribution (Point params × Point params))
      (selected := fun uv ah => ah ∈ addInUSelectionPairs params S uv.1)
      (t := t) (x := x) (y := y) ht hx hy

/-- Selected factored Cauchy--Schwarz bound for the `Q₂ → Q₃` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q2_q3_factored_cs`.  The summation is over all pairs
`(o,h)`, with the terms outside the selected set `S_u` set to zero; this form is
convenient for the finite Cauchy--Schwarz lemma and is equivalent to the
fiberwise selected sum appearing in the paper. -/
private theorem addInU_selected_cs_chain_step3_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor (Av * Moh * Av) (T.outcome ah.2))
            else 0)) := by
  classical
  rw [addInU_selected_cs_chain_step3_diff_eq params strategy M T S]
  simpa using
    addInU_selected_weighted_cauchy_schwarz (Outcome := Outcome) params S
      (t := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2)))
      (x := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)))
      (y := fun uv ah =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Av * Moh * Av) (T.outcome ah.2)))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hX_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hsandwich :=
          ev_opTensor_sandwich_abs_le_sqrt strategy.state (Av - Au) Av Moh
            (T.outcome ah.2) hMoh_pos hTh_pos
        simpa only [hX_herm, hAv_herm] using hsandwich)
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hX_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hXMohX_pos : 0 ≤ (Av - Au) * Moh * (Av - Au) := by
          have this : 0 ≤ (Av - Au)ᴴ * Moh * (Av - Au) := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos (Av - Au)
          rwa [hX_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hXMohX_pos hTh_pos))
      (by
        intro uv ah _hmem
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hAvMohAv_pos : 0 ≤ Av * Moh * Av := by
          have this : 0 ≤ Avᴴ * Moh * Av := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos Av
          rwa [hAv_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hAvMohAv_pos hTh_pos))

/-- Selected factored Cauchy--Schwarz bound for the `Q₃ → Q₄` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q3_q4_factored_cs`; as in
`addInU_selected_cs_chain_step3_factored_cs`, terms outside the selected set
are represented by zeros in the finite Cauchy--Schwarz sum. -/
private theorem addInU_selected_cs_chain_step4_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) := by
  classical
  rw [addInU_selected_cs_chain_step4_diff_eq params strategy M T S]
  simpa using
    addInU_selected_weighted_cauchy_schwarz (Outcome := Outcome) params S
      (t := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2)))
      (x := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2)))
      (y := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hY_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hsandwich :=
          ev_opTensor_sandwich_abs_le_sqrt strategy.state Au (Av - Au) Moh
            (T.outcome ah.2) hMoh_pos hTh_pos
        simpa only [hAu_herm, hY_herm] using hsandwich)
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAuMohAu_pos : 0 ≤ Au * Moh * Au := by
          have this : 0 ≤ Auᴴ * Moh * Au := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos Au
          rwa [hAu_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hAuMohAu_pos hTh_pos))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hY_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hYMohY_pos : 0 ≤ (Av - Au) * Moh * (Av - Au) := by
          have this : 0 ≤ (Av - Au)ᴴ * Moh * (Av - Au) := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos (Av - Au)
          rwa [hY_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hYMohY_pos hTh_pos))

/-- A selected sandwich tensor sum is bounded by replacing the selected
submeasurement mass with the identity.

For a fixed point `u`, the selected pairs are a subcollection of
`Outcome × Polynomial params`.  Summing over all pairs, the `Outcome`-mass
collapses to `(M u).total`, and the submeasurement inequality
`(M u).total ≤ I` gives the displayed upper bound. -/
private lemma addInU_selected_sandwich_tensor_if_sum_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params)
    (X : Polynomial params → MIPStarRE.Quantum.Op ι)
    (hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h) :
    (∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0) ≤
      ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
  classical
  let s := addInUSelectionPairs params S u
  let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
    opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
  have hf_nonneg : ∀ ah : Outcome × Polynomial params, 0 ≤ f ah := by
    intro ah
    have hM_pos : 0 ≤ (M u).outcome ah.1 := (M u).outcome_pos ah.1
    have hT_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
    have hleft_pos : 0 ≤ X ah.2 * (M u).outcome ah.1 * X ah.2 := by
      have this : 0 ≤ (X ah.2)ᴴ * (M u).outcome ah.1 * X ah.2 := by
        simpa [Matrix.star_eq_conjTranspose] using
          star_left_conjugate_nonneg hM_pos (X ah.2)
      rwa [hX_herm ah.2] at this
    exact opTensor_nonneg hleft_pos hT_pos
  have hif_eq :
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S u then f ah else 0) =
        ∑ ah ∈ s, f ah := by
    simp [s]
  have hselected_le_univ :
      ∑ ah ∈ s, f ah ≤ ∑ ah : Outcome × Polynomial params, f ah :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ah _
        exact Finset.mem_univ ah)
      (by
        intro ah _ _
        exact hf_nonneg ah)
  have huniv_eq :
      (∑ ah : Outcome × Polynomial params, f ah) =
        ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) := by
    calc
      (∑ ah : Outcome × Polynomial params, f ah)
          = ∑ o : Outcome, ∑ h : Polynomial params,
              opTensor (X h * (M u).outcome o * X h) (T.outcome h) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ h : Polynomial params, ∑ o : Outcome,
            opTensor (X h * (M u).outcome o * X h) (T.outcome h) := by
            rw [Finset.sum_comm]
      _ = ∑ h : Polynomial params,
            opTensor (X h * (M u).total * X h) (T.outcome h) := by
            refine Finset.sum_congr rfl ?_
            intro h _
            calc
              ∑ o : Outcome,
                  opTensor (X h * (M u).outcome o * X h) (T.outcome h)
                  = opTensor
                      (∑ o : Outcome, X h * (M u).outcome o * X h)
                      (T.outcome h) := by
                    rw [opTensor_sum_left_univ]
              _ = opTensor (X h * (M u).total * X h) (T.outcome h) := by
                    congr 1
                    rw [← (M u).sum_eq_total, Finset.mul_sum, Finset.sum_mul]
  have htotal_le :
      ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
    refine Finset.sum_le_sum ?_
    intro h _
    have hleft_le : X h * (M u).total * X h ≤ X h * 1 * X h :=
      IsSelfAdjoint.conjugate_le_conjugate (M u).total_le_one (hX_herm h)
    simpa using opTensor_mono_left hleft_le (T.outcome_pos h)
  calc
    (∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0)
        = ∑ ah ∈ s, f ah := hif_eq
    _ ≤ ∑ ah : Outcome × Polynomial params, f ah := hselected_le_univ
    _ = ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) := huniv_eq
    _ ≤ ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := htotal_le

private lemma addInU_selected_cs_chain_self_energy_factor_le_one_at
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (p : Point params × Point params → Point params) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
  classical
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
    intro uv
    let X : Polynomial params → MIPStarRE.Quantum.Op ι :=
      fun h => pointConditionedOutcomeOperatorAtPolynomial params strategy h (p uv)
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement (p uv)).toSubMeas
        (h (p uv))
    have hsum_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2) (T.outcome ah.2)
          else 0) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      addInU_selected_sandwich_tensor_if_sum_le params M T S uv.1 X hX_herm
    have hright_le_one :
        (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) ≤
          (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      calc
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)
            = ∑ h : Polynomial params, opTensor (X h) (T.outcome h) := by
                refine Finset.sum_congr rfl ?_
                intro h _
                have hproj : X h * X h = X h := by
                  dsimp [X, pointConditionedOutcomeOperatorAtPolynomial]
                  exact (strategy.pointMeasurement (p uv)).proj (h (p uv))
                rw [hproj]
        _ ≤ ∑ h : Polynomial params,
              opTensor (1 : MIPStarRE.Quantum.Op ι) (T.outcome h) := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact opTensor_mono_left
                ((strategy.pointMeasurement (p uv)).toSubMeas.outcome_le_one (h (p uv)))
                (T.outcome_pos h)
        _ = rightTensor (ι₁ := ι) T.total := by
              rw [← T.sum_eq_total, ← opTensor_sum_right_univ]
        _ ≤ 1 := rightTensor_le_one (ι₁ := ι) T.total_le_one
    have hop_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
            let Moh := (M uv.1).outcome ah.1
            opTensor (A * Moh * A) (T.outcome ah.2)
          else 0) ≤ 1 := by
      simpa [X] using le_trans hsum_le hright_le_one
    calc
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0)
          = ev strategy.state
              (∑ ah : Outcome × Polynomial params,
                if ah ∈ addInUSelectionPairs params S uv.1 then
                  let A := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 (p uv)
                  let Moh := (M uv.1).outcome ah.1
                  opTensor (A * Moh * A) (T.outcome ah.2)
                else 0) := by
              rw [ev_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro ah _
              by_cases hmem : ah ∈ addInUSelectionPairs params S uv.1
              · simp [hmem]
              · simp [hmem, ev_zero]
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
            ev_mono strategy.state _ _ hop_le
      _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized
  exact avgOver_uniform_le_const _ 1 hpointwise

/-- The selected Step 3/4 variance factor is bounded by the summed
global-variance deviation.

The selected middle operators form a submeasurement after summing over their
outcome coordinate, so the selected sandwich is dominated by the square of
`A^v_{h(v)} - A^u_{h(u)}`.  Averaging over independent points identifies the
result with the global-variance deviation sum. -/
private lemma addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Error := fun uv =>
    ∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S uv.1 then
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
      else 0
  let squaredTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ uv : Point params × Point params,
      varianceTerm uv ≤ ∑ h : Polynomial params, squaredTerm uv h := by
    intro uv
    let X : Polynomial params → MIPStarRE.Quantum.Op ι := fun h =>
      pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      have hAu_herm :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv_herm :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      dsimp [X]
      rw [Matrix.conjTranspose_sub, hAv_herm, hAu_herm]
    have hop_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2) (T.outcome ah.2)
          else 0) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      addInU_selected_sandwich_tensor_if_sum_le params M T S uv.1 X hX_herm
    have hoperator_to_squared :
        (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) =
          ∑ h : Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h) := by
      refine Finset.sum_congr rfl ?_
      intro h _
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      have hAu_herm : Auᴴ = Au :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv_herm : Avᴴ = Av :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      have hsq : (Av - Au) * (Av - Au) = ((Au - Av)ᴴ) * (Au - Av) := by
        rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        noncomm_ring
      simpa [X, Au, Av] using congrArg (fun Z => opTensor Z (T.outcome h)) hsq
    calc
      varianceTerm uv
          = ev strategy.state
              (∑ ah : Outcome × Polynomial params,
                if ah ∈ addInUSelectionPairs params S uv.1 then
                  let Au := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 uv.1
                  let Av := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 uv.2
                  let Moh := (M uv.1).outcome ah.1
                  opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)
                else 0) := by
              dsimp [varianceTerm]
              rw [ev_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro ah _
              by_cases hmem : ah ∈ addInUSelectionPairs params S uv.1
              · simp [hmem]
              · simp [hmem, ev_zero]
      _ ≤ ev strategy.state (∑ h : Polynomial params,
              opTensor (X h * X h) (T.outcome h)) :=
            ev_mono strategy.state _ _ (by simpa [X] using hop_le)
      _ = ev strategy.state (∑ h : Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial
                params strategy h uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial
                params strategy h uv.2
              opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h)) := by
            rw [hoperator_to_squared]
      _ = ∑ h : Polynomial params, squaredTerm uv h := by
            rw [ev_finset_sum]
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) varianceTerm ≤
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) := by
    refine avgOver_mono _ _ _ ?_
    intro uv
    exact hpointwise uv
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
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0)
        = avgOver (uniformDistribution (Point params × Point params)) varianceTerm := by
            rfl
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

/-- Raw selected `Q₂ → Q₃` global-variance Cauchy--Schwarz bound after the
selected variance and self-energy factors have been estimated. -/
lemma addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  by
  classical
  exact addInU_le_sqrt_of_factor_bounds_right
    (addInU_selected_cs_chain_step3_factored_cs params strategy M T S)
    (addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
      params strategy M T S)
    (by
      simpa using
        addInU_selected_cs_chain_self_energy_factor_le_one_at
          params strategy M T S (fun uv : Point params × Point params => uv.2))

/-- Raw selected `Q₃ → Q₄` global-variance Cauchy--Schwarz bound after the
selected self-energy and variance factors have been estimated. -/
lemma addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  by
  classical
  exact addInU_le_sqrt_of_factor_bounds_left
    (addInU_selected_cs_chain_step4_factored_cs params strategy M T S)
    (by
      simpa using
        addInU_selected_cs_chain_self_energy_factor_le_one_at
          params strategy M T S (fun uv : Point params × Point params => uv.1))
    (addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
      params strategy M T S)

/-- Upgrade the selected `Q₂ → Q₃` raw global-variance bound using an external
bound on the summed global-variance deviation. -/
lemma addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ Real.sqrt ζ :=
  by
  classical
  exact le_trans
    (addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum
      params strategy M T S)
    (Real.sqrt_le_sqrt hglobal)

/-- Upgrade the selected `Q₃ → Q₄` raw global-variance bound using an external
bound on the summed global-variance deviation. -/
lemma addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ Real.sqrt ζ :=
  by
  classical
  exact le_trans
    (addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum
      params strategy M T S)
    (Real.sqrt_le_sqrt hglobal)

/-- Combined selected Step 3/4 global-variance bridge.

The two selected replacement steps use the same summed global-variance
hypothesis.  This closed form supplies the raw selected Cauchy--Schwarz
estimates from the factored Step 3/4 proofs in this file and then applies the
external bound on the global-variance sum to both steps. -/
lemma addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ Real.sqrt ζ ∧
      |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ Real.sqrt ζ :=
  ⟨addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy M T S hglobal,
    addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy M T S hglobal⟩

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


