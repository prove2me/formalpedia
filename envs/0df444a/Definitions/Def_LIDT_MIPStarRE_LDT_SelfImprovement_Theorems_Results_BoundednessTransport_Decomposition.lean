-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_Decomposition
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_Decomposition
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:44:37.704468+00:00
-- url     : https://prove2.me/theorems/fea2329a-c5db-42a7-8f67-5dd2b76fdf75
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / BoundednessTransport / Decomposition
-- statement:
--   This bundle expands helper-agreement and boundedness expressions into polynomial-indexed sums. It identifies their pointwise and averaged operator forms and separates the boundedness slack into off-diagonal contributions.
--
--   Principal definitions:
--   - `helper_agreement_average_ev_eq_avg`: scalar expansion of the averaged helper-agreement operator.
--   - `helperAgreementOperatorAtPoint_eq_sum_polynomial`: pointwise reindexing of the helper-agreement operator by polynomial outcomes.
--   - `helper_agreement_average_ev_eq_polynomial_sum`: polynomial-indexed expansion of the averaged helper-agreement expectation.
--   - `helperAgreementOperatorAtPoint_off_diagonal_decomposition`: operator decomposition of the pointwise helper boundedness slack.
--   - `helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum`: scalar expectation form of that off-diagonal decomposition.
--   - `helper_boundedness_slack_average_ev_eq_off_diagonal_avg`: averaged scalar form of the helper boundedness slack.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/Decomposition.lean#L38-L321

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/Decomposition.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
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
# Boundedness transport decomposition identities

This file contains the algebraic reindexing and off-diagonal decompositions used
in the final-fields boundedness and point-consistency arguments.  The identities
come from the helper-stage agreement average in the proof of self-improvement.

## References

- `references/ldt-paper/self_improvement.tex` lines 435 and 612--613
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

/-- Scalar expansion of the averaged helper-agreement operator.

The expectation of the averaged agreement operator is the average, over the
point question, of the scalar agreement between the point measurement and the
postprocessed polynomial family. -/
lemma helper_agreement_average_ev_eq_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              ((evaluateAt params u H).outcome a))) := by
  rw [helperAgreementAverageOperator, ev_averageOperatorOverDistribution]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  simp [helperAgreementOperatorAtPoint, ev_sum]

/-- Reindexing identity for the pointwise helper-agreement operator.

The fiberwise definition `H_{[h(u)=a]} := ∑_{h : h(u)=a} H_h` collapses the
`a`-summed expression `∑_a A^u_a ⊗ H_{[h(u)=a]}` to the polynomial-indexed sum
`∑_h A^u_{h(u)} ⊗ H_h`, by expanding the tensor product fiberwise and applying
`Finset.sum_fiberwise` along `h ↦ h u`.

This is the first equality of the boundedness display in the proof of
`\ref{item:self-improvement-boundedness}`:
`references/ldt-paper/self_improvement.tex` line 612, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex` lines 274--282
("Reindexing the sum by~$h$"). It is a purely algebraic identity — no estimate,
no measurement structure used beyond the postprocess fiber decomposition built
into `evaluateAt`. -/
theorem helperAgreementOperatorAtPoint_eq_sum_polynomial
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : Polynomial params,
        opTensor ((strategy.pointMeasurement u).outcome (h u))
          (H.outcome h) := by
  classical
  -- First reduce `helperAgreementOperatorAtPoint`'s `evaluateAt` to the explicit
  -- fiber sum on each summand; everything else then follows from
  -- `Finset.sum_fiberwise` along `h ↦ h u` and bilinearity of `opTensor`.
  have hexpand :
      helperAgreementOperatorAtPoint params strategy H u =
        ∑ a : Fq params,
          opTensor ((strategy.pointMeasurement u).outcome a)
            (∑ h ∈ Finset.univ.filter
                (fun h : Polynomial params => h u = a), H.outcome h) := by
    change (∑ a : Fq params,
        opTensor ((strategy.pointMeasurement u).outcome a)
          ((evaluateAt params u H).outcome a)) = _
    refine Finset.sum_congr rfl ?_
    intro a _
    have hev :
        (evaluateAt params u H).outcome a =
              ∑ h ∈ Finset.univ.filter
                  (fun h : Polynomial params => h u = a), H.outcome h := by
      ext i j
      simp [evaluateAt, postprocess]
    rw [hev]
  rw [hexpand]
  calc
    ∑ a : Fq params,
        opTensor ((strategy.pointMeasurement u).outcome a)
          (∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), H.outcome h)
        = ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a),
            opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [opTensor_sum_right_finset]
      _ = ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a),
            opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro h hh
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
              rw [show h u = a from hh]
      _ = ∑ h : Polynomial params,
            opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) := by
              simpa using (polynomial_sum_fiberwise params u
                (fun h =>
                  opTensor ((strategy.pointMeasurement u).outcome (h u))
                    (H.outcome h))).symm

/-- Reindexed expansion of the averaged helper-agreement operator.

Combining the pointwise reindexing identity
`helperAgreementOperatorAtPoint_eq_sum_polynomial` with
`helper_agreement_average_ev_eq_avg`, the scalar
`⟨ψ| E_u Σ_a A^u_a ⊗ H_{[h(u)=a]} |ψ⟩` equals the polynomial-indexed expectation
`E_u Σ_h ⟨ψ| A^u_{h(u)} ⊗ H_h |ψ⟩` from the second line of the boundedness
display in the proof of `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 612;
`blueprint/src/chapter/ch07_self_improvement.tex` lines 274--282). -/
theorem helper_agreement_average_ev_eq_polynomial_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h))) := by
  rw [helper_agreement_average_ev_eq_avg]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hpt :
      helperAgreementOperatorAtPoint params strategy H u =
        ∑ h : Polynomial params,
          opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) :=
    helperAgreementOperatorAtPoint_eq_sum_polynomial params strategy H u
  have hpt_ev :
      ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h)) := by
    rw [hpt, ev_sum]
  -- The LHS goal is the unfolded `helperAgreementOperatorAtPoint`-summand at `u`.
  simp only [helperAgreementOperatorAtPoint, ev_sum] at hpt_ev
  exact hpt_ev

/-- Off-diagonal decomposition of the pointwise helper boundedness slack.

For each point `u`, the difference between the right-placed total
`I ⊗ H.total = ∑_h I ⊗ H_h` and the pointwise helper-agreement operator
`helperAgreementOperatorAtPoint params strategy H u = ∑_a A^u_a ⊗ H_{[h(u)=a]}`
equals the off-diagonal sum
`∑_h ∑_{a ≠ h(u)} A^u_a ⊗ H_h`,
by combining the polynomial-indexed reindexing of `helperAgreementOperatorAtPoint`
from #1124 (`helperAgreementOperatorAtPoint_eq_sum_polynomial`) with
`∑_a A^u_a = 1` (since `pointMeasurement u` is a measurement) and the bilinearity
of `opTensor`.

This is the operator-level form of the second algebraic identity in the
boundedness display in `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 613, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex` lines 296--300, the step
"Combined with $\sum_a A_a^u = I$ and~\eqref{eq:explicit-bound-for-A-consistency}
this gives ..."). The averaged scalar form of the off-diagonal sum on the right
is the LHS of `eq:explicit-bound-for-A-consistency` (line 435), which the paper
bounds by `4 √ζ_variance`. -/
theorem helperAgreementOperatorAtPoint_off_diagonal_decomposition
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    rightTensor (ι₁ := ι) H.total -
        helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h) := by
  classical
  -- Step 1: rewrite `helperAgreementOperatorAtPoint` via the #1124 reindexing.
  rw [helperAgreementOperatorAtPoint_eq_sum_polynomial]
  -- Step 2: rewrite `rightTensor H.total = ∑_h opTensor 1 (H.outcome h)`.
  have hrhs_total :
      rightTensor (ι₁ := ι) H.total =
        ∑ h : Polynomial params,
          opTensor (1 : MIPStarRE.Quantum.Op ι) (H.outcome h) := by
    change opTensor (1 : MIPStarRE.Quantum.Op ι) H.total = _
    rw [← H.sum_eq_total]
    exact opTensor_sum_right_univ (1 : MIPStarRE.Quantum.Op ι) H.outcome
  rw [hrhs_total, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  -- Pull subtraction inside `opTensor`.
  rw [opTensor_sub_left]
  -- Use `∑_a A^u_a = 1` to expand `1 - A^u_{h(u)} = ∑_{a ≠ h(u)} A^u_a`.
  have htot :
      ∑ a : Fq params, (strategy.pointMeasurement u).outcome a =
        (1 : MIPStarRE.Quantum.Op ι) :=
    (strategy.pointMeasurement u).toMeasurement.sum_eq
  have hsplit :
      (strategy.pointMeasurement u).outcome (h u) +
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            (strategy.pointMeasurement u).outcome a =
        (1 : MIPStarRE.Quantum.Op ι) := by
    rw [← htot]
    exact Finset.add_sum_erase _ _ (Finset.mem_univ (h u))
  have hsubst :
      (1 : MIPStarRE.Quantum.Op ι) -
          (strategy.pointMeasurement u).outcome (h u) =
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          (strategy.pointMeasurement u).outcome a := by
    rw [← hsplit]
    abel
  rw [hsubst]
  -- Pull the sum out of the left factor of `opTensor`.
  exact opTensor_sum_left_finset _ _ _

/-- Scalar form of the pointwise off-diagonal decomposition.

For each evaluation point `u`, the scalar slack
`⟨ψ, I ⊗ H.total, ψ⟩ - ⟨ψ, helperAgreementOperatorAtPoint u, ψ⟩`
is the sum of the off-diagonal masses
`⟨ψ, A^u_a ⊗ H_h, ψ⟩` over the pairs with `a ≠ h(u)`. -/
theorem helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state (rightTensor (ι₁ := ι) H.total) -
        ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h)) := by
  rw [← ev_sub, helperAgreementOperatorAtPoint_off_diagonal_decomposition,
    ev_sum]
  simp only [ev_finset_sum]

/-- Averaged scalar form of the off-diagonal decomposition.

Composed from `helperAgreementOperatorAtPoint_off_diagonal_decomposition` by
applying the bilinearity of `ev`/`avgOver` over subtraction and averaging via
`avgOver_uniform_const`.  The difference
`⟨ψ, I ⊗ H.total, ψ⟩ - ⟨ψ, helperAgreementAverageOperator, ψ⟩` equals the
averaged off-diagonal scalar sum
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ H_h, ψ⟩`,
which is the LHS of `eq:explicit-bound-for-A-consistency`
(`references/ldt-paper/self_improvement.tex` line 435; blueprint
`ch07_self_improvement.tex` lines 153--168). -/
theorem helper_boundedness_slack_average_ev_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (rightTensor (ι₁ := ι) H.total) -
        ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  have h_ev_pointwise (u : Point params) :
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h)) := by
    exact helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  calc
    ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementAverageOperator params strategy H) =
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
        avgOver (uniformDistribution (Point params))
          (fun u => ev strategy.state
            (helperAgreementOperatorAtPoint params strategy H u)) := by
      rw [helperAgreementAverageOperator, ev_averageOperatorOverDistribution]
    _ = avgOver (uniformDistribution (Point params))
          (fun _ => ev strategy.state (rightTensor (ι₁ := ι) H.total)) -
        avgOver (uniformDistribution (Point params))
          (fun u => ev strategy.state
            (helperAgreementOperatorAtPoint params strategy H u)) := by
      rw [avgOver_uniform_const]
    _ = avgOver (uniformDistribution (Point params))
          (fun u => ev strategy.state (rightTensor (ι₁ := ι) H.total) -
            ev strategy.state
              (helperAgreementOperatorAtPoint params strategy H u)) := by
      rw [avgOver_sub]
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
      refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
      intro u
      exact h_ev_pointwise u


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


