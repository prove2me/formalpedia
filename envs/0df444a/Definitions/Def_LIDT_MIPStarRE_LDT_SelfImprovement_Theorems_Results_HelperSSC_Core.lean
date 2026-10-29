-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:37:39.890693+00:00
-- url     : https://prove2.me/theorems/c0daad58-d46d-43d1-bc59-93485259b078
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperSSC / Core
-- statement:
--   This bundle packages the intermediate estimates for helper strong self-consistency. It defines the off-diagonal mass and selected supports, identifies the selected chain endpoints with indicator quantities, and records the two square-root bounds for swapping variance factors.
--
--   Principal definitions:
--   - `HelperStrongSelfConsistencyBounds`: The collection of helper transport, residual, and square-root bounds.
--   - `helper_strong_self_consistency_bounds_of_selfConsistency_localVariance`: Constructs that collection from self-consistency and local-variance inputs.
--   - `helperOffDiagonalBareQuantity`: The off-diagonal polynomial-pair mass before residual expansion.
--   - `helperOffDiagonalVarianceSwapSelection`: The selected support for the two variance swaps.
--   - `helperOffDiagonalSelectedCSChainQ4_eq_indicator`: Identifies the first selected endpoint with the off-diagonal indicator.
--   - `helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator`: Identifies the one-sided swapped stage.
--   - `helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator`: Identifies the fully swapped stage.
--   - `helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt` and `helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt`: The two square-root swap bounds.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Core.lean#L29-L500

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Core.lean by skeleton subtraction.
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

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Helper strong self-consistency bounds: core reductions

Core bound structures, the bare off-diagonal quantity, and the two
variance-swap identities used in the helper strong self-consistency chain.

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

/-- Named intermediate bounds for the helper-stage strong self-consistency proof.

Paper origin: `references/ldt-paper/self_improvement.tex:255-603`
(`\label{item:self-improvement-self}` and the subsequent add-in-`u`,
self-consistency, and variance-swap chain).

This is an internal record for the helper-stage strong self-consistency proof,
tracked by #1596.  It is not a hypothesis of a source-labelled theorem.  Its
fields are derived from the add-in-`u`, self-consistency, and global-variance
estimates and are not passed across the public statement of
`lem:self-improvement-helper`.

These fields isolate the paper-side intermediate estimates in the proof of
`item:self-improvement-self` once the reduced helper conclusion is fixed:

1. the four scalar transport bounds along the chain
   `Q₀ \to Q₁ \to Q₂ \to Q₃ \to Q₄`, and
2. the final lower bound on the released right-hand side before the arithmetic
   absorption into `selfImprovementHelperError`.

This structure records the actual intermediate estimates used from the
add-in-`u`, self-consistency, and variance calculations, rather than restating
the final `BipartiteSSCRel` conclusion as an input.  It is an internal assembly
record for the helper theorem, not a hypothesis of the paper-aligned helper
theorem; the full assembly of these bounds discharged the former #1514 gap. -/
structure HelperStrongSelfConsistencyBounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (eps delta : Error) : Prop where
  /-- Paper `eq:move-one`: the `Q₀ \to Q₁` transport bound. -/
  step01Bound :
    |addInUCSChainQ0 params strategy T.toSubMeas -
        addInUCSChainQ1 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:move-another`: the `Q₁ \to Q₂` transport bound. -/
  step12Bound :
    |addInUCSChainQ1 params strategy T.toSubMeas -
        addInUCSChainQ2 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:change-one`: the `Q₂ \to Q₃` variance transport bound. -/
  step23Bound :
    |addInUCSChainQ2 params strategy T.toSubMeas -
        addInUCSChainQ3 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- Paper `eq:change-another`: the `Q₃ \to Q₄` variance transport bound. -/
  step34Bound :
    |addInUCSChainQ3 params strategy T.toSubMeas -
        addInUCSChainQ4 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- The released right-hand side is within the paper's pre-absorption helper
  SSC error of the helper mass. -/
  residualLowerBound :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta

-- This constructor fills the helper SSC bounds record by composing the
-- point self-consistency bounds with the local-to-global variance transfer.
/-- Construct the helper-stage bounds from the mathematical inputs after the
add-in-`u` chain has been closed.

The point self-consistency hypothesis supplies the two self-consistency moves
`Q₀ → Q₁` and `Q₁ → Q₂`; the local-variance sum bound supplies the two
global-variance moves `Q₂ → Q₃` and `Q₃ → Q₄`. The only additional scalar input
is the residual lower bound for the released right-hand side. -/
lemma helper_strong_self_consistency_bounds_of_selfConsistency_localVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hresidual :
      subMeasMass strategy.state Hhat.liftLeft -
          addInURightQuantity params strategy
            (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
            T.toSubMeas
            (selfConsistencyAddInUSelection params) ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
          addInUError params eps delta) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta := by
  have hsteps :=
    add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
      params strategy eps delta T.toSubMeas hlocal
  exact
    { step01Bound :=
        addInU_cs_chain_step1_abs_le_sqrt_two_delta
          params strategy T.toSubMeas delta hssc
      step12Bound :=
        addInU_cs_chain_step2_abs_le_sqrt_two_delta
          params strategy T.toSubMeas delta hssc
      step23Bound := hsteps.1
      step34Bound := hsteps.2
      residualLowerBound := hresidual }

/-- The bare off-diagonal polynomial-pair mass appearing after the released
residual is expanded.

This is the right-hand side of
`helper_mass_sub_release_eq_polynomial_off_diagonal`, stated for an arbitrary
polynomial submeasurement `T`. -/
noncomputable def helperOffDiagonalBareQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h)))



/-! ### Off-diagonal variance swaps -/

/-- The selected support for the two off-diagonal variance swaps in the helper
SSC residual estimate.

At the point `u`, it selects precisely the ordered polynomial pairs `(h', h)`
with `h' ≠ h` and `h u = h' u`, matching the indicator support in
`eq:swapped-u-for-v` and
`eq:swapped-u-for-v-this-time-it's-personal`. -/
noncomputable def helperOffDiagonalVarianceSwapSelection
    (params : Parameters) [FieldModel params.q] :
    AddInUSelection params (Polynomial params) :=
  fun u => {hh | hh.1 ≠ hh.2 ∧ hh.2 u = hh.1 u}

private theorem helperOffDiagonalVarianceSwapSelection_pairs_sum
    (params : Parameters) [FieldModel params.q]
    (u : Point params)
    (F : Polynomial params → Polynomial params → Error) :
    ∑ hh ∈ addInUSelectionPairs params
        (helperOffDiagonalVarianceSwapSelection params) u,
        F hh.1 hh.2 =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h u = h' u then (1 : Error) else 0) * F h' h := by
  classical
  unfold addInUSelectionPairs helperOffDiagonalVarianceSwapSelection
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [← Finset.filter_ne' Finset.univ h, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases hne : h' ≠ h
  · by_cases heq : h u = h' u
    · rw [if_pos ⟨hne, heq⟩, if_pos hne, if_pos heq, one_mul]
    · rw [if_pos hne, if_neg heq]
      simp only [Set.mem_ofPred_eq, heq, and_false, ite_false]
      ring
  · have hheq : h' = h := not_not.mp hne
    subst h'
    simp only [Set.mem_ofPred_eq, ne_eq, not_true_eq_false, false_and, ite_false]

/-- The selected-chain endpoint `Q₄` is the off-diagonal indicator quantity. -/
theorem helperOffDiagonalSelectedCSChainQ4_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUSelectedCSChainQ4 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ4, helperOffDiagonalIndicatorQuantity]
  change avgOver (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (fun u : Point params =>
          ∑ ah ∈ addInUSelectionPairs params
              (helperOffDiagonalVarianceSwapSelection params) u,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
            ev strategy.state (opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2))) uv.1) = _
  rw [avgOver_uniform_fst (α := Point params) (β := Point params)
    (f := fun u : Point params =>
      ∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        ev strategy.state (opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [show
      (∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        ev strategy.state (opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2))) =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h u = h' u then (1 : Error) else 0) *
            ev strategy.state
              (opTensor
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
                  T.outcome h' * pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
                (T.outcome h)) by
    simpa using
      helperOffDiagonalVarianceSwapSelection_pairs_sum params u
        (fun h' h =>
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state (opTensor (Au * T.outcome h' * Au) (T.outcome h)))]
  refine Finset.sum_congr rfl ?_
  intro h _
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases heq : h u = h' u
  · simp [heq, sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
      pointConditionedOutcomeOperatorAtPolynomial]
  · simp [heq]

/-- The selected-chain scalar `Q₃` is the one-sided swapped off-diagonal
indicator quantity. -/
theorem helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUSelectedCSChainQ3 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ3, helperOffDiagonalOneSidedSwappedIndicatorQuantity]
  refine avgOver_congr (uniformDistribution (Point params × Point params)) _ _ ?_
  intro uv
  rw [show
      (∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) uv.1,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        ev strategy.state (opTensor (Au * T.outcome ah.1 * Av) (T.outcome ah.2))) =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h uv.1 = h' uv.1 then (1 : Error) else 0) *
            ev strategy.state
              (opTensor
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                  T.outcome h' *
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
                (T.outcome h)) by
    simpa using
      helperOffDiagonalVarianceSwapSelection_pairs_sum params uv.1
        (fun h' h =>
          ev strategy.state
            (opTensor
              (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                T.outcome h' *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
              (T.outcome h)))]
  refine Finset.sum_congr rfl ?_
  intro h _
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases heq : h uv.1 = h' uv.1
  · rw [if_pos heq]
    simp only [one_mul]
    rw [← ev_conjTranspose strategy.state]
    rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have hAu : (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAv : (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hT' : (T.outcome h')ᴴ = T.outcome h' := SubMeas.outcome_hermitian T h'
    have hT : (T.outcome h)ᴴ = T.outcome h := SubMeas.outcome_hermitian T h
    rw [hAu, hAv, hT', hT]
    simp [Matrix.mul_assoc]
  · simp [heq]

/-- The selected-chain scalar `Q₂` is the fully swapped off-diagonal indicator
quantity. -/
theorem helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUSelectedCSChainQ2 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalSwappedIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ2, helperOffDiagonalSwappedIndicatorQuantity]
  change avgOver (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (fun u v =>
          ∑ ah ∈ addInUSelectionPairs params
              (helperOffDiagonalVarianceSwapSelection params) u,
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
            ev strategy.state (opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2)))
          uv.1 uv.2) = _
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) u,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
        ev strategy.state (opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2)))]
  rw [avgOver_comm]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro v
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ ah ∈ addInUSelectionPairs params
            (helperOffDiagonalVarianceSwapSelection params) u,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
          ev strategy.state (opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2))) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            (if h u = h' u then (1 : Error) else 0) *
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                    T.outcome h' * pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (T.outcome h))) := by
        refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
        intro u
        simpa using
          helperOffDiagonalVarianceSwapSelection_pairs_sum params u
            (fun h' h =>
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h v
              ev strategy.state (opTensor (Av * T.outcome h' * Av) (T.outcome h)))
    _ = _ := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [avgOver_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro h' _
        rw [avgOver_mul_const]

-- The off-diagonal swap invokes the selected Step 3/4 bound and the
-- local-to-global variance transfer.
/-- The first off-diagonal variance swap, corresponding to
`eq:swapped-u-for-v` in the helper SSC residual chain. -/
theorem helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperOffDiagonalIndicatorQuantity params strategy T -
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy (fun _ : Point params => T) T
      (helperOffDiagonalVarianceSwapSelection params)
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal)
  simpa [helperOffDiagonalSelectedCSChainQ4_eq_indicator,
    helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator,
    abs_sub_comm, selfImprovementVarianceError] using hsteps.2

-- This is the analogous second off-diagonal swap with the same variance
-- transfer input.
/-- The second off-diagonal variance swap, corresponding to
`eq:swapped-u-for-v-this-time-it's-personal` in the helper SSC residual chain. -/
theorem helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
      helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy (fun _ : Point params => T) T
      (helperOffDiagonalVarianceSwapSelection params)
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal)
  simpa [helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator,
    helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator,
    abs_sub_comm, selfImprovementVarianceError] using hsteps.1


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


