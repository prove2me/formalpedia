-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:39:40.520279+00:00
-- url     : https://prove2.me/theorems/6c5fd36d-1e86-4345-b1b1-21928455f826
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUPointConsistency
-- statement:
--   This bundle defines the off-diagonal selection used to derive helper-stage point consistency from add-in-u transfer. It identifies the two sides of the selected expression, reduces the right side to zero by projectivity, and converts a transfer bound into a bound on the averaged helper off-diagonal mass.
--
--   Principal definitions:
--   - `pointConsistencyAddInUSelection`: the off-diagonal selection for the helper point-consistency application.
--   - `pointConsistencyAddInUSelection_pairs_sum`: the associated pair-sum identity.
--   - `addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg`: identifies the left quantity with averaged off-diagonal helper mass.
--   - `addInURightQuantity_pointConsistencySelection_eq_zero`: proves that the right quantity vanishes.
--   - `pointConsistencyAddInU_off_diagonal_avg_le_of_transfer`: derives the off-diagonal bound from an add-in-u transfer estimate.
--   - `pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer`: derives the helper point-consistency error bound.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUPointConsistency.lean#L48-L503

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUPointConsistency.lean by skeleton subtraction.
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

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Off-diagonal add-in-u selection infrastructure for helper point consistency

This module isolates the theorem-side `add-in-u` specialization with
`Outcome = Fq params`, `M = A`, and the off-diagonal selection
`S_u = {(a, h) : h(u) ≠ a}` used in the proof of the helper-stage
`A`-consistency bound (`eq:explicit-bound-for-A-consistency`).

It does **not** prove the full point-consistency estimate. Instead, it provides
the missing theorem-side selection object, the associated selected scalar
Cauchy--Schwarz chain, and the left/right quantity identities needed by a later
transfer theorem.

The final theorem in this file also records the numerical absorption from the
natural add-in-`u` error `4 sqrt ζ_variance` to the helper-stage error
`ζ_hat`.  Thus the remaining analytic input is precisely the
selection-dependent transfer estimate, not an additional arithmetic comparison.

## References

- `references/ldt-paper/self_improvement.tex` lines 420–437
- `blueprint/src/chapter/ch07_self_improvement.tex` lines 155–179
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The off-diagonal selection used in the helper-stage `A`-consistency
application of `lem:add-in-u`.

At each point `u`, this selects exactly the pairs `(a, h)` with `h u ≠ a`,
matching the paper's choice `S_u = {(a,h) : h(u) ≠ a}` in the proof of
`eq:explicit-bound-for-A-consistency`. -/
noncomputable def pointConsistencyAddInUSelection (params : Parameters)
    [FieldModel params.q] : AddInUSelection params (Fq params) :=
  fun u => {ah | ah.2 u ≠ ah.1}

private theorem pointConsistencyAddInUSelection_pairs_sum
    (params : Parameters) [FieldModel params.q]
    (u : Point params)
    (F : Fq params → Polynomial params → Error) :
    ∑ ah ∈ addInUSelectionPairs params (pointConsistencyAddInUSelection params) u,
        F ah.1 ah.2 =
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u), F a h := by
  classical
  apply Finset.sum_finset_product_right'
    (r := addInUSelectionPairs params (pointConsistencyAddInUSelection params) u)
    (s := (Finset.univ : Finset (Polynomial params)))
    (t := fun h => (Finset.univ : Finset (Fq params)).erase (h u))
  intro p
  rcases p with ⟨a, h⟩
  unfold addInUSelectionPairs pointConsistencyAddInUSelection
  simp [Finset.mem_erase, ne_comm]

/-! ### Off-diagonal selected scalar chain -/

















-- This point-consistency specialization combines the selected add-in-u scalar
-- chain with the global-variance sum estimate.


/-- The left side of the helper point-consistency `add-in-u` application is the
averaged off-diagonal helper-agreement mass.

This is exactly the scalar quantity on the left of
`eq:explicit-bound-for-A-consistency`, written through the generic theorem-side
`addInULeftQuantity` interface for the off-diagonal selection. -/
theorem addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        H
        (pointConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInULeftOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) u)) = _
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  unfold addInULeftOperatorAtPoint
  rw [ev_finset_sum]
  simpa [IdxProjMeas.toIdxSubMeas] using
    pointConsistencyAddInUSelection_pairs_sum params u
      (fun a h =>
        ev strategy.state
          (opTensor ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement u).outcome a)
            (H.outcome h)))

/-- The right side of the helper point-consistency `add-in-u` application is
identically zero by projectivity of the point measurement.

For every selected pair `(a, h)` with `h u ≠ a`, the inner sandwich contains the
factor `A^u_{h(u)} A^u_a = 0`, so every summand vanishes. -/
theorem addInURightQuantity_pointConsistencySelection_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params) = 0 := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInURightOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params) u)) = 0
  have hpoint : ∀ u : Point params,
      ev strategy.state
        (addInURightOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params) u) = 0 := by
    intro u
    unfold addInURightOperatorAtPoint addInUSelectionPairs
    rw [ev_finset_sum]
    refine Finset.sum_eq_zero ?_
    intro ah hh
    rcases ah with ⟨a, h⟩
    have hh' : h u ≠ a := by
      have hmem : (a, h) ∈ pointConsistencyAddInUSelection params u := by
        simpa [addInUSelectionPairs] using hh
      simpa [pointConsistencyAddInUSelection] using hmem
    change ev strategy.state
        (opTensor
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            (strategy.pointMeasurement u).outcome a *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
          (T.outcome h)) = 0
    have hortho :
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            (strategy.pointMeasurement u).outcome a = 0 := by
      simpa [pointConditionedOutcomeOperatorAtPolynomial] using
        ProjMeas.outcome_orthogonal (strategy.pointMeasurement u) (h u) a hh'
    have hsandwich :
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            (strategy.pointMeasurement u).outcome a *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u = 0 := by
      rw [hortho, zero_mul]
    have hzeroTensor : opTensor (0 : MIPStarRE.Quantum.Op ι) (T.outcome h) = 0 := by
      ext i j
      simp [opTensor]
    rw [hsandwich, hzeroTensor, ev_zero]
  have hzeroAvg :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ev strategy.state
          (addInURightOperatorAtPoint params strategy
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            T
            (pointConsistencyAddInUSelection params) u)) =
        avgOver (uniformDistribution (Point params)) (fun _ => 0) := by
    refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
    intro u
    exact hpoint u
  rw [hzeroAvg, avgOver_uniform_const]

/-- Any theorem-side `add-in-u` transfer bound for the off-diagonal selection
immediately bounds the averaged helper off-diagonal mass by `addInUError`.

This is the exact theorem-side wrapper needed to connect a future generic
selection-dependent transfer theorem to the helper `A`-consistency route. -/
theorem pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h))) ≤ addInUError params eps delta := by
  have h := htransfer
  rw [addInURightQuantity_pointConsistencySelection_eq_zero] at h
  rw [addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg] at h
  simpa using (abs_le.mp h).2

/-- Helper-stage point-consistency bound from the off-diagonal `add-in-u`
transfer estimate.

The preceding theorem gives the natural bound `addInUError`, which is equal to
`4 * sqrt ζ_variance` after rewriting by `Real.sqrt_eq_rpow`.  This wrapper
applies the numerical
absorption from `self_improvement.tex`, lines 438--443, so that the resulting
off-diagonal helper mass is already bounded by the helper-stage error
`selfImprovementHelperError`.  The only remaining analytic input is the
selection-dependent `add-in-u` transfer inequality for
`pointConsistencyAddInUSelection`. -/
theorem pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h))) ≤ selfImprovementHelperError params eps delta := by
  have hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) ≤ addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T H htransfer
  have habsorb :
      addInUError params eps delta ≤ selfImprovementHelperError params eps delta := by
    simpa [addInUError, Real.sqrt_eq_rpow] using
      helper_point_consistency_error_le_selfImprovementHelperError
        params eps delta heps hdelta
  exact hoffdiag.trans habsorb

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


