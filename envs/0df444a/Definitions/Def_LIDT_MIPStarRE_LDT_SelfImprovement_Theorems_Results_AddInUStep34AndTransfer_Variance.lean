-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:31:19.616702+00:00
-- url     : https://prove2.me/theorems/c214ed76-da6a-4472-812c-7eb32e210010
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUStep34AndTransfer / Variance
-- statement:
--   This bundle contains variance and self-energy estimates for the Q2-to-Q3 and Q3-to-Q4 add-in-u Cauchy-Schwarz chains. It converts global-variance deviation sums into square-root error bounds at both transfer endpoints.
--
--   Principal definitions:
--   - `add_in_u_cs_chain_q3_q4_self_energy_factor_le_one`: bounds the Q3-to-Q4 self-energy factor by one.
--   - `add_in_u_cs_chain_q2_q3_self_energy_factor_le_one`: bounds the Q2-to-Q3 self-energy factor by one.
--   - `add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum`: bounds the first variance factor by global deviation.
--   - `add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum`: bounds the second variance factor by global deviation.
--   - `add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum`: gives the raw Q2-to-Q3 square-root estimate.
--   - `add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum`: gives the raw Q3-to-Q4 square-root estimate.
--   - `le_sqrt_of_le_sqrt_of_le`: transfers a square-root bound to a larger target error.
--   - `add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le`: gives the Q2-to-Q3 endpoint estimate after deviation control.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Variance.lean#L30-L638

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Variance.lean by skeleton subtraction.
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
# Unselected add-in-u Step 3/4 global-variance bounds

Unselected self-energy estimates, variance-factor comparisons, and the
combined global-variance bridges for the projection-simplified add-in-u chain.

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

/-- Self-energy factor `≤ 1` for the `Q₃ → Q₄` factored Cauchy--Schwarz.

The first square-root factor `D₁` produced by `add_in_u_cs_chain_q3_q4_factored_cs`
is bounded by `1`. The proof collapses the outer projection `A^u_{h(u)}` around
the sandwiched submeasurement `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` via
projectivity, then bounds the per-point sum of `opTensor (H^u_h) (T_h)` by
the submeasurement-opTensor-sum lemma, lifts to expectation via `ev ψ`,
and averages over `(u, v)` with the `v`-average collapsing to unity.

This supplies the `hD₁_le_one` hypothesis required by
`add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds`.  The proof is
fully symmetric in `u` ↔ `v` up to projection renaming, so the same
pattern directly supplies `hD₂_le_one` for the `Q₂ → Q₃` factored
`add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds` analogue. -/
lemma add_in_u_cs_chain_q3_q4_self_energy_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state (opTensor (Au * Mh * Au) (T.outcome h))) ≤ 1 := by
  classical
  let S : Point params → SubMeas (Polynomial params) ι :=
    fun u => sandwichedPolynomialSubMeasAt params strategy T u
  -- Projection collapse: `Au * (S u).outcome h * Au = (S u).outcome h`
  have hcollapse : ∀ (u : Point params) (h : Polynomial params),
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      Au * (S u).outcome h * Au = (S u).outcome h := by
    intro u h Au
    have hproj : Au * Au = Au := by
      dsimp [Au, pointConditionedOutcomeOperatorAtPolynomial]
      exact (strategy.pointMeasurement u).proj (h u)
    have hMh_eq : (S u).outcome h = Au * T.outcome h * Au := rfl
    rw [hMh_eq]
    exact proj_outer_sandwich_eq Au (T.outcome h) hproj
  -- Rewrite D₁ using the collapse
  have hD₁_eq :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state (opTensor (Au * Mh * Au) (T.outcome h))) =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          ev strategy.state (opTensor ((S uv.1).outcome h) (T.outcome h))) := by
    refine avgOver_congr _ _ _ ?_
    intro uv
    refine Finset.sum_congr rfl ?_
    intro h _
    dsimp
    have h_eq := hcollapse uv.1 h
    dsimp at h_eq
    rw [h_eq]
  rw [hD₁_eq]
  -- The integrand depends only on `uv.1`, so the average over `v` collapses
  rw [avgOver_uniform_fst
    (α := Point params) (β := Point params)
    (f := fun u =>
      ∑ h : Polynomial params,
        ev strategy.state (opTensor ((S u).outcome h) (T.outcome h)))]
  -- Per-point bound: the expectation sum is ≤ 1
  have hpointwise : ∀ u : Point params,
      ∑ h : Polynomial params,
        ev strategy.state (opTensor ((S u).outcome h) (T.outcome h)) ≤ 1 := by
    intro u
    have hop_sum_le_one :
        (∑ h : Polynomial params,
          opTensor ((S u).outcome h) (T.outcome h)) ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      have := SubMeas.opTensor_sum_filter_le_one (S u) T
        (fun _ : Polynomial params => True)
      simpa [Finset.filter_true] using this
    calc
      ∑ h : Polynomial params,
          ev strategy.state (opTensor ((S u).outcome h) (T.outcome h))
          = ev strategy.state
              (∑ h : Polynomial params,
                opTensor ((S u).outcome h) (T.outcome h)) := by
            rw [ev_finset_sum]
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
            ev_mono strategy.state _ _ hop_sum_le_one
      _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized
  exact avgOver_uniform_le_const _ 1 hpointwise

/-- Self-energy factor `≤ 1` for the `Q₂ → Q₃` factored Cauchy--Schwarz.

The second square-root factor produced by `add_in_u_cs_chain_q2_q3_factored_cs`
is bounded by `1`. For fixed `(u,v)`, the diagonal summand is one summand of the
nonnegative residual tensor sum
`Σ_{i,r,o} A^v_o H^u_i A^v_o ⊗ T_r`.  The residual sum is at most `1` by
`sandwichTensor_residual_sum_le_one`, applied to the point measurement at `v`,
the sandwiched polynomial submeasurement at `u`, and the original
submeasurement `T`. -/
lemma add_in_u_cs_chain_q2_q3_self_energy_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) ≤ 1 := by
  classical
  let S : Point params → SubMeas (Polynomial params) ι :=
    fun u => sandwichedPolynomialSubMeasAt params strategy T u
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (S uv.1).outcome h
        ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) ≤ 1 := by
    intro uv
    let Outer : SubMeas (Fq params) ι :=
      (strategy.pointMeasurement uv.2).toSubMeas
    let Inner : SubMeas (Polynomial params) ι := S uv.1
    let Right : SubMeas (Polynomial params) ι := T
    let F : Fq params → Polynomial params → Polynomial params → Error := fun o i r =>
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
          rightTensor (ι₁ := ι) (Right.outcome r))
    have hF_nonneg : ∀ o i r, 0 ≤ F o i r := by
      intro o i r
      exact sandwichTensorSummand_nonneg strategy.state Outer Inner Right o i r
    have hdiag_eq :
        (∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (S uv.1).outcome h
          ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) =
        ∑ h : Polynomial params, F (h uv.2) h h := by
      refine Finset.sum_congr rfl ?_
      intro h _
      simp only [F, Outer, Inner, Right, pointConditionedOutcomeOperatorAtPolynomial]
      rw [leftTensor_mul_rightTensor_eq_opTensor]
    have hdiag_le_residual :
        (∑ h : Polynomial params, F (h uv.2) h h) ≤
          ∑ ir : Polynomial params × Polynomial params,
            ∑ o : Fq params, F o ir.1 ir.2 := by
      calc
        ∑ h : Polynomial params, F (h uv.2) h h
            ≤ ∑ h : Polynomial params, ∑ o : Fq params, F o h h := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact Finset.single_le_sum
                (fun o _ => hF_nonneg o h h) (Finset.mem_univ (h uv.2))
        _ ≤ ∑ h : Polynomial params, ∑ r : Polynomial params, ∑ o : Fq params,
              F o h r := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact Finset.single_le_sum
                (fun r _ => Finset.sum_nonneg fun o _ => hF_nonneg o h r)
                (Finset.mem_univ h)
        _ = ∑ ir : Polynomial params × Polynomial params,
              ∑ o : Fq params, F o ir.1 ir.2 := by
              rw [Fintype.sum_prod_type]
    calc
      (∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (S uv.1).outcome h
          ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h)))
          = ∑ h : Polynomial params, F (h uv.2) h h := hdiag_eq
      _ ≤ ∑ ir : Polynomial params × Polynomial params,
            ∑ o : Fq params, F o ir.1 ir.2 := hdiag_le_residual
      _ ≤ 1 := by
            simpa [F] using
              sandwichTensor_residual_sum_le_one strategy.state strategy.isNormalized
                Outer Inner Right
  exact avgOver_uniform_le_const _ 1 hpointwise

/-- The variance factor in the `Q₂ → Q₃` factored Cauchy--Schwarz estimate is
bounded by the polynomial sum of the global-variance deviations.

For each polynomial `h`, the sandwiched operator `H^u_h` is bounded by `1`.
Thus the summand
`(A^v_{h(v)} - A^u_{h(u)}) H^u_h (A^v_{h(v)} - A^u_{h(u)}) ⊗ T_h`
is dominated by the squared point-operator difference tensored with `T_h`.
The latter is exactly the integrand defining
`globalVarianceDeviationAtPolynomial`, after expanding the weighted
point-conditioned operator. -/
lemma add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state
        (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))
  let squaredTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ (h : Polynomial params) (uv : Point params × Point params),
      varianceTerm uv h ≤ squaredTerm uv h := by
    intro h uv
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hAu_herm : Auᴴ = Au := by
      change ((strategy.pointMeasurement uv.1).toSubMeas.outcome (h uv.1))ᴴ =
        (strategy.pointMeasurement uv.1).toSubMeas.outcome (h uv.1)
      exact (strategy.pointMeasurement uv.1).toSubMeas.outcome_hermitian (h uv.1)
    have hAv_herm : Avᴴ = Av := by
      change ((strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2))ᴴ =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2)
      exact (strategy.pointMeasurement uv.2).toSubMeas.outcome_hermitian (h uv.2)
    have hdiff_herm : (Av - Au)ᴴ = Av - Au := by
      rw [Matrix.conjTranspose_sub, hAv_herm, hAu_herm]
    have hleft_le :
        (Av - Au) * Mh * (Av - Au) ≤ (Av - Au) * 1 * (Av - Au) := by
      exact IsSelfAdjoint.conjugate_le_conjugate
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_le_one h)
        hdiff_herm
    have hright_eq :
        (Av - Au) * 1 * (Av - Au) = ((Au - Av)ᴴ) * (Au - Av) := by
      rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
      noncomm_ring
    have hop_le :
        opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h) ≤
          opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h) := by
      exact opTensor_mono_left (le_trans hleft_le (le_of_eq hright_eq)) (T.outcome_pos h)
    exact ev_mono strategy.state _ _ hop_le
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, varianceTerm uv h) ≤
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) := by
    refine avgOver_mono _ _ _ ?_
    intro uv
    exact Finset.sum_le_sum fun h _ => hpointwise h uv
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
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))
        = avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
            ∑ h : Polynomial params, varianceTerm uv h) := by
            refine avgOver_congr _ _ _ ?_
            intro uv
            refine Finset.sum_congr rfl ?_
            intro h _
            rfl
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

/-- The variance factor in the `Q₃ → Q₄` factored Cauchy--Schwarz estimate is
bounded by the polynomial sum of the global-variance deviations.

This is the same variance expression as in the `Q₂ → Q₃` estimate, appearing
as the second square-root factor rather than the first. -/
lemma add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g :=
  add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
    params strategy T

/-- Raw `Q₂ → Q₃` global-variance Cauchy--Schwarz bound after both factors have
been estimated. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds params strategy T _ _
    (add_in_u_cs_chain_q2_q3_factored_cs params strategy T)
    (add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
      params strategy T)
    (add_in_u_cs_chain_q2_q3_self_energy_factor_le_one params strategy T)

/-- Raw `Q₃ → Q₄` global-variance Cauchy--Schwarz bound after both factors have
been estimated. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds params strategy T _ _
    (add_in_u_cs_chain_q3_q4_factored_cs params strategy T)
    (add_in_u_cs_chain_q3_q4_self_energy_factor_le_one params strategy T)
    (add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum
      params strategy T)

/-- Sqrt-monotonicity transit lemma used by the two GlobalVariance endpoint
bridges below: a real bounded by `Real.sqrt s` is bounded by `Real.sqrt ζ`
whenever `s ≤ ζ`. Both `Q₂→Q₃` and `Q₃→Q₄` apply this fact with the same `s`
(the summed `globalVarianceDeviationAtPolynomial`). -/
private lemma le_sqrt_of_le_sqrt_of_le {a : ℝ} {s ζ : Error}
    (hcs : a ≤ Real.sqrt s) (hsum : s ≤ ζ) : a ≤ Real.sqrt ζ :=
  le_trans hcs (Real.sqrt_le_sqrt hsum)

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the first global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-one` in
`references/ldt-paper/self_improvement.tex`, lines 299--318. The hypothesis
`hcs` is the Cauchy--Schwarz estimate `eq:change-one-cauchy-schwarz`
(lines 306--311) **after** the second-square-root has been bounded by `1`
using `(A^v_{h(v)})² ≤ I` and the fact that `T` is a measurement
(lines 312--316, 318); concretely, the right-hand side is the summed
`globalVarianceDeviationAtPolynomial` (the displayed first-square-root
content). This lemma applies only the remaining `≤ ζ_variance` step from
`lem:global-variance-of-points` (line 317) via sqrt-monotonicity. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the second global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-another` in
`references/ldt-paper/self_improvement.tex`, lines 319--340. The hypothesis
`hcs` is the Cauchy--Schwarz estimate of lines 326--332 **after** the
first-square-root has been bounded by `1` using `(A^u_{h(u)})² ≤ I` and the
fact that `T` is a measurement (lines 333--338); concretely, the right-hand
side is the summed `globalVarianceDeviationAtPolynomial` (the displayed
second-square-root content, equal to the first-square-root term of
`eq:change-one-cauchy-schwarz` per line 340). This lemma applies only the
remaining `≤ ζ_variance` step (line 340) via sqrt-monotonicity. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal





/-- Combined Step 3/4 variance bridge for the projection-simplified add-in-u
Cauchy--Schwarz chain.

Given the two raw Cauchy--Schwarz estimates against the summed
independent-points deviation and a GlobalVariance sum bound, this produces the
two `sqrt ζ` absolute-difference bounds needed by
`add_in_u_simplified_transfer_of_cs_chain`. It deliberately does not assemble
the final transfer, so the remaining self-consistency steps and arithmetic
absorption stay separate. -/
lemma add_in_u_cs_chain_global_variance_steps_of_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt ζ ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt ζ := by
  exact
    ⟨add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
        params strategy T hglobal h23cs,
      add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
        params strategy T hglobal h34cs⟩



-- This bridge applies the global-variance sum transfer and the two
-- Cauchy--Schwarz factor bounds, all over the polynomial-indexed family.
/-- Local-variance-sum version of the combined Step 3/4 variance bridge.

This consumes the expected output of the local-variance normalization step
(`expansion.tex`, lines 317--321) through
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`, then applies
the combined Step 3/4 bridge above.  It remains a named bridge because the
blueprint cites this local-sum interface separately from the closed
factor-bound lemma below. -/
lemma add_in_u_cs_chain_global_variance_steps_of_local_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) := by
  exact add_in_u_cs_chain_global_variance_steps_of_sum_bound
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)
    h23cs h34cs

-- This lemma composes the local-to-global sum transfer with the first
-- projection-simplified Cauchy--Schwarz factor estimate.


-- This lemma composes the local-to-global sum transfer with the second
-- projection-simplified Cauchy--Schwarz factor estimate.


/-- Local-variance-sum version of the combined Step 3/4 variance bridge using
the factor estimates proved in this file.

This is the closed local-sum form of
`add_in_u_cs_chain_global_variance_steps_of_sum_bound_from_factor_bounds`: the
only new input is the local-variance sum hypothesis, which is first transported
to the global-variance sum bound. -/
lemma add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    add_in_u_cs_chain_global_variance_steps_of_local_sum_bound
      params strategy eps delta T hlocal
      (add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum params strategy T)
      (add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum params strategy T)
  simpa [selfImprovementVarianceError] using hsteps

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


